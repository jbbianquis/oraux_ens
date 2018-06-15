let u0_test = 17
let u0_perso = 1789                

let nmax = 500_000
                 
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

   
type joueur = X | O
type case = V | J of joueur * bool
   
let plateau s m =
  let t = Array.make (s * s) V in
  for i = 0 to s * s - 1 do
    if u (i + m) mod 2 = 0 then t.(i) <- J (X, false)
    else t.(i) <- J (O, false)
  done;
  t

let voisins i s =
  let ligne = i / s in
  let colonne = i mod s in
  let no = if ligne = 0 then [] else [i - s] in
  let ne = if ligne = 0 || colonne = s - 1 then [] else [i - s + 1] in
  let o = if colonne = 0 then [] else [i - 1] in
  let e = if colonne = s - 1 then [] else [i + 1] in
  let so = if ligne = s - 1 || colonne = 0 then [] else [i + s - 1] in
  let se = if ligne = s - 1 then [] else [i + s] in
  no @ ne @ o @ e @ so @ se
                           
let rec propage pl j s i =
  match pl.(i) with
  | V -> ()
  | J (jo, vu) ->
     if jo = j && not vu then begin
         pl.(i) <- J (jo, true);
         List.iter (propage pl j s) (voisins i s)
       end
                                  
let propage_n pl s =
  for i = 0 to s - 1 do
    propage pl X s i
  done

let propage_o pl s =
  for i = 0 to s - 1 do
    propage pl O s (i * s)
  done

let connecte_ns pl s =
  let rec f i =
    if i = s * s then false
    else match pl.(i) with
         | J (X, true) -> true
         | _ -> f (i + 1) in
  f (s * (s - 1))

let connecte_oe pl s =
  let rec f i =
    if i > s * s then false
    else match pl.(i) with
         | J (O, true) -> true
         | _ -> f (i + s) in
  f (s - 1)

let nb_X_connectes pl s =
  let x = ref 0 in
  for i = 0 to s * s - 1 do
    match pl.(i) with
    | J (X, true) -> incr x
    | _ -> ()
  done;
  !x

let q2 m =
  let pl = plateau 171 m in
  propage_n pl 171;
  (connecte_ns pl 171, nb_X_connectes pl 171)
  
let joue case jo pl s =
  pl.(case) <- J (jo, false);
  let v = voisins case s in
  let b = ref false in
  List.iter (fun i -> if pl.(i) = J (jo, true) then b := true) v;
  if !b || (jo = X && case / s = 0) || (jo = O && case mod s = 0) then
    propage pl jo s case

exception Gagne of joueur * int
          
let q3 s m =
  let pl = Array.make (s * s) V in
  let iminX = ref 0 in
  let iminO = ref 0 in
  let rec prochain jo =
    let i = if jo = X then iminX else iminO in
    let j = m + 2 * !i + if jo = X then 0 else 1 in
    let case = index s (u j) in
    if pl.(case) = V then case
    else (incr i; prochain jo) in
  try
    for i = 0 to s * s - 1 do
      if i mod 2 = 0 then begin
          let case = prochain X in
          joue case X pl s;
          if connecte_ns pl s then raise (Gagne (X, i))
        end
      else begin
          let case = prochain O in
          joue case O pl s;
          if connecte_oe pl s then raise (Gagne (O, i))
        end
    done;
    failwith "partie nulle ?"
  with
  | Gagne (jo, i) -> (jo, i)
      
let q4 i =
  let s = 150 in
  let nb_gagnees = ref 0 in
  for j = i to i + 15 do
    let m = u j in
    let (jo, _) = q3 s m in
    if jo = X then incr nb_gagnees
  done;
  float_of_int !nb_gagnees /. 16.
  
  
  
let q5 s m =
  let pl = Array.make (s * s) V in
  let imin = ref 0 in
  let rec prochain jo =
    let j = m + !imin in
    let case = index s (u j) in
    if pl.(case) = V then case
    else (incr imin; prochain jo) in
  try
    for i = 0 to s * s - 1 do
      if i mod 2 = 0 then begin
          let case = prochain X in
          joue case X pl s;
          if connecte_ns pl s then raise (Gagne (X, i))
        end
      else begin
          let case = prochain O in
          joue case O pl s;
          if connecte_oe pl s then raise (Gagne (O, i))
        end
    done;
    failwith "partie nulle ?"
  with
  | Gagne (jo, i) -> (jo, i)

let q6 m =
  let s = 50 in
  let nb_gagnees = ref 0 in
  for i = 0 to s * s - 1 do
    let (jo, _) = q3 s (m + i) in
    if jo = X then incr nb_gagnees
  done;
  !nb_gagnees

let connecte joueur = if joueur = X then connecte_ns else connecte_oe

let autre joueur = if joueur = X then O else X

let affiche pl s =
  let str case = match case with
    | V -> "V"
    | J (X, b) -> if b then "X" else "x"
    | J (O, b) -> if b then "o" else "O" in 
  let rec espaces i = if i = 0 then "" else " " ^ espaces (i - 1) in
  for i = 0 to s - 1 do
    print_string (espaces i);
    for case = i * s to i * s + s - 1 do
      print_string (str pl.(case) ^ " ")
    done;
    print_newline ()
  done
                                               
let resultat s initiaux =
  let t = Array.make_matrix (s * s + 1) (s * s) V in
  Array.iteri (fun i case -> initiaux.(i) <- index s case) initiaux;
  let jouer niveau case joueur =
    let pl = t.(niveau) in
    joue case joueur pl s in
  let rec eval niveau joueur =
    (* Printf.printf "niveau %d\n" niveau; *)
    let opp = autre joueur in
    if connecte opp t.(niveau) s then opp
    else if niveau = s * s then begin
        for i = 0 to s * s do
          affiche t.(i) s;
          print_newline ()
        done;
        failwith "nulle ?"
      end
    else begin
        let i = ref 0 in
        let vainqueur = ref opp in
        while !i < s * s && !vainqueur = opp do
          if t.(niveau).(!i) = V then begin
              Array.blit t.(niveau) 0 t.(niveau + 1) 0 (s * s);
              jouer (niveau + 1) !i joueur;
              vainqueur := eval (niveau + 1) opp
            end;
          incr i      
        done;
        !vainqueur
      end in
  let n = Array.length initiaux in
  for i = 0 to n - 1 do
    let joueur = ref X in
    for j = i + 1 to n do
      jouer j initiaux.(i) !joueur;
      joueur := autre !joueur
    done
  done;
  let joueur = if n mod 2 = 0 then X else O in
  eval n joueur
  
let q8 x =
  let str j = if j = X then "X" else "O" in
  for i = 0 to 2 do
    let j = resultat 4 [|x; -x + 2*i + 1|] in
    Printf.printf "i = %d, vainqueur %s" i (str j);
    print_newline ()
  done

let traite_q8 () =
  q8 (u 4);
  q8 (u 5);
  q8 (u 3)
     
let q9 x =
  let str j = if j = X then "X" else "O" in
  let j = resultat 4 [|x|] in
  Printf.printf "+, vainqueur %s" (str j);
  print_newline ();
  let j = resultat 4 [| -x |] in
  Printf.printf "-, vainqueur %s" (str j);
  print_newline ()   

let traite_q9 () =
  q9 (u 4);
  q9 (u 5);
  q9 (u 3)
