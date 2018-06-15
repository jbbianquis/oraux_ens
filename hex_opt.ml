let u0_test = 17
let u0_perso = 1789                

let nmax = 50_000
                 
let tab_u u0 =
  let t = Array.make nmax u0 in
  for i = 1 to nmax - 1 do
    t.(i) <- (15091 * t.(i - 1)) mod 64007
  done;
  t

let tab_test = tab_u u0_test
let tab_perso = tab_u u0_perso
    
let test = ref true

let u n =
  if n >= nmax then failwith (Printf.sprintf "tab_u trop petit, n = %d" n)
  else if !test then tab_test.(n)
  else tab_perso.(n)

                
let index s n =
  let x = n mod (s * s) in
  if x >= 0 then x else x + s * s

(************)                                
(* Partie 1 *)
(************)

let q1 m =
  let s = 17 in
  let j = ref 0 in
  for i = 0 to s * s - 1 do
    if u (i + m) mod 2 = 1 then incr j
  done;
  !j

type joueur = bool
type case = V | XN | XS | X | OO | OE | O

(*                                          
let plateau s m =
  let t = Array.make (s * s) V in
  for i = 0 to s * s - 1 do
    if u (i + m) mod 2 = 0 then t.(i) <- J (X, false)
    else t.(i) <- J (O, false)
  done;
  t
 *)

let voisins i s =
  let ligne = i / s in
  let colonne = i mod s in
  let no = if ligne = 0 then [] else [i - s] in
  let ne = if ligne = 0 || colonne = s - 1 then [] else [i - s + 1] in
  let o = if colonne = 0 then [] else [i - 1] in
  let e = if colonne = s - 1 then [] else [i + 1] in
  let so = if ligne = s - 1 || colonne = 0 then [] else [i + s - 1] in
  let se = if ligne = s - 1 then [] else [i + s] in
  Array.of_list (no @ ne @ o @ e @ so @ se)

let tab_v s =
  Array.init (s * s) (fun i -> voisins i s)

type contenu = C of int [@@unboxed]

let cv = C 1                        
let cx = C 2
let cxs = C 4
let cxn = C 8
let co = C 16
let coo = C 32
let coe = C 64

let a_propager depart arrivee =
  (arrivee = cx && (depart = cxs || depart = cxn))
  || (arrivee = co && (depart = coo || depart = coe))
                     
                        
type vecteur = V of int [@@unboxed]

let vecteur_vide = V 0
                       
let ajoute (C contenu) (V vecteur) =
  V (vecteur lor contenu)

let appartient (C contenu) (V vecteur) =
  vecteur land contenu <> 0
             
let adjacents pl v =
  let x = ref vecteur_vide in
  for i = 0 to Array.length v - 1 do
    x := ajoute pl.(v.(i)) !x
  done;
  !x

let nord s case adj = (case < s || appartient cxn adj)
let sud s case adj = (case >= s * (s - 1) || appartient cxs adj)
let ouest s case adj = (case mod s = 0 || appartient coo adj)
let est s case adj = (case mod s = s - 1 || appartient coe adj)

let gagnant pl s v case jo =
  let adj = adjacents pl v in
  (jo && nord s case adj && sud s case adj)
  || (not jo && est s case adj && ouest s case adj)

let propage pl tab_v case valeur =
  let rec aux nv_case =
    if a_propager valeur pl.(nv_case) then
      begin
        pl.(nv_case) <- valeur;
        Array.iter aux tab_v.(nv_case)
      end in
  pl.(case) <- valeur;
  Array.iter aux tab_v.(case)
    
let joue pl s tab_v case jo =
  let v = tab_v.(case) in
  let adj = adjacents pl v in
  assert (pl.(case) = cv && not (gagnant pl s v case jo));
  if jo then 
    if nord s case adj then propage pl tab_v case cxn
    else if sud s case adj then propage pl tab_v case cxs
    else pl.(case) <- cx
  else
    if est s case adj then propage pl tab_v case coe
    else if ouest s case adj then propage pl tab_v case coo
    else pl.(case) <- co
             
        
let affiche pl s =
  let str case =
    if case = cv then "V"
    else if case = cx then "x"
    else if case = cxn then "N"
    else if case = cxs then "S"
    else if case = co then "o"
    else if case = coo then "O"
    else if case = coe then "E"
    else failwith "affiche" in
  let rec espaces i = if i = 0 then "" else " " ^ espaces (i - 1) in
  for i = 0 to s - 1 do
    print_string (espaces i);
    for case = i * s to i * s + s - 1 do
      print_string (str pl.(case) ^ " ")
    done;
    print_newline ()
  done

let id pl s =
  let x = ref 0 in
  let f valeur =
    if valeur = cv then 0
    else if (valeur = cx || valeur = cxn || valeur = cxs) then 1
    else 2 in
  for i = 0 to s * s - 1 do
    x := (!x lsl 2) + f pl.(i)
  done;
  2 * !x

let nb_coups id_pos =
  let s = ref 0 in
  let x = ref id_pos in
  for i = 0 to 16 do
    s := !s + if !x land 3 = 0 then 0 else 1;
    x := !x lsr 2
  done;
  !s
       
let store id valeur t =
  let i = id mod (Array.length t) in
  let act = t.(i) in
  (* if act = 0 || nb_coups act <= nb_coups id then *)
  t.(i) <- if valeur then id else id + 1;
  act <> 0

let get id t =
  let i = id mod (Array.length t) in
  let x = t.(i) in
  if x = 0 then raise Not_found
  else
    let v = x land 1 in
    if x - v = id then (v = 0)
    else raise Not_found
               
exception Fini
               
let ordre s =
  let case = ref (s / 2, s / 2) in
  let dir = ref (0, -1) in
  let i = ref 0 in
  let enum = Array.make (s * s) 0 in
  let tourne () = match !dir with
    | (1, 0) -> dir := (0, -1)
    | (0, -1) -> dir := (-1, 0)
    | (-1, 0) -> dir := (0, 1)
    | (0, 1) -> dir := (1, 0)
    | _ -> failwith "erreur direction" in
  let step () =
    if !i >= s * s then raise Fini;
    let x, y = !case and dx, dy = !dir in
    enum.(!i) <- s * x + y;
    incr i;
    case := (x + dx, y + dy) in
  let avance k =
    for i = 1 to k do
      step ()
    done in
  try
    let k = ref 1 in
    while true do
      avance !k;
      tourne ();
      avance !k;
      tourne ();
      incr k
    done;
    failwith "Impossible"
  with
  | Fini -> enum
  
  

                                               
let resultat s initiaux =
  let tab_v = tab_v s in
  let t = Array.make_matrix (s * s + 1) (s * s) cv in
  let cache = Array.make 100_003 0 in
  let limite = 9 in
  let permanent = Hashtbl.create 10_000 in
  let cache_hit = ref 0 in
  let cache_miss = ref 0 in
  let cache_collision = ref 0 in
  let permanent_hit = ref 0 in
  let permanent_miss = ref 0 in
  let calls = ref 0 in
  Array.iteri (fun i case -> initiaux.(i) <- index s case) initiaux;
  let jouer niveau case jo =
    let pl = t.(niveau) in
    joue pl s tab_v case jo in
  let enum = ordre s in
  let rec eval niveau jo =
    (* Printf.printf "niveau %d\n" niveau; *)
    incr calls;
    if niveau <= 0 then
      (Printf.printf "Niveau %d, taille du cache permanent %d"
                     niveau (Hashtbl.length permanent);
       print_newline ());
    if niveau <= 0 then
      (affiche t.(niveau) s;
       print_newline ());
    if niveau = s * s then begin
        for i = 0 to s * s do
          affiche t.(i) s;
          print_newline ()
        done;
        failwith "nulle ?"
      end
    else 
      let id_pos = id t.(niveau) s in
      try
        if niveau <= limite then begin
            let res = Hashtbl.find permanent id_pos in
            incr permanent_hit;
            res
          end
        else begin
            let res = get id_pos cache in
            incr cache_hit;
            res
          end
      with
        Not_found ->
        let i = ref 0 in
        let vainqueur = ref (not jo) in
        while !i < s * s && !vainqueur <> jo do
          if t.(niveau).(!i) = cv && gagnant t.(niveau) s tab_v.(!i) !i jo then
            vainqueur := jo;
          incr i
        done;
        if !vainqueur <> jo then begin
            if niveau <= limite then incr permanent_miss
            else incr cache_miss;
            i := 0;            
            while !i < s * s && !vainqueur <> jo do
              let case = enum.(!i) in
              if t.(niveau).(case) = cv then begin
                  Array.blit t.(niveau) 0 t.(niveau + 1) 0 (s * s);
                  jouer (niveau + 1) case jo;
                  vainqueur := eval (niveau + 1) (not jo)
                end;
              incr i      
            done;
            if niveau <= limite then Hashtbl.add permanent id_pos !vainqueur
            else (* if niveau + 4 < s * s then *)
              let collision = store id_pos !vainqueur cache in
              if collision then incr cache_collision
          end;
        !vainqueur in
  let n = Array.length initiaux in
  for i = 0 to n - 1 do
    let joueur = ref true in
    for j = i + 1 to n do
      jouer j initiaux.(i) !joueur;
      joueur := not !joueur
    done
  done;
  let joueur = (n mod 2 = 0) in
  let res =   eval n joueur in
  Printf.printf "Permanent : hits = %d, misses = %d, final size = %d\n"
                !permanent_hit !permanent_miss (Hashtbl.length permanent);
  Printf.printf "Cache : hits = %d, misses = %d, collisions = %d\n"
                !cache_hit !cache_miss !cache_collision;
  Printf.printf "Total calls : %d\n" !calls;
  res

let q7 x =
  let f x = resultat 3 [| x |] in
  Printf.printf  "%b, %b, %b, %b\n\n"
                 (f (u x)) (f (- u x)) (f (- u x + 1)) (f (- u x + 2))
  

let affiche_q7 () =
  Printf.printf "Question 7\n";
  q7 4;
  q7 5;
  q7 3;
  print_newline ()
                 
let q8 x =
  for i = 0 to 2 do
    let jo = resultat 4 [|x; -x + 2*i + 1|] in
    Printf.printf "i = %d, vainqueur %b\n" i jo;
    print_newline ()
  done

let affiche_q8 () =
  Printf.printf "\nQuestion 8\n";
  q8 (u 4);
  q8 (u 5);
  q8 (u 3);
  print_newline ()
     
let q9 x =
  let jo = resultat 4 [|x|] in
  Printf.printf "+, vainqueur %b\n" jo;
  print_newline ();
  let jo = resultat 4 [| -x |] in
  Printf.printf "-, vainqueur %b\n" jo;
  print_newline ()   

let affiche_q9 () =
  Printf.printf "\nQuestion 9\n";
  q9 (u 4);
  q9 (u 5);
  q9 (u 3);
  print_newline ()

let rec parmi k n =
    if k < 0 || k > n then 0
    else if k = 0 then 1
    else (n * parmi (k - 1) (n - 1)) / k 
     
let nb_pos s niveau =
  let x = niveau / 2 in
  let o = niveau - x in
  parmi x (s * s) * parmi o (s * s - x)

let pos_tot s =
  let res = ref 0 in
  for n = 0 to s * s do
    res := !res + nb_pos s n
  done;
  !res

let affiche_tout () =
  affiche_q7 ();
  affiche_q8 ();
  affiche_q9 ()



    
