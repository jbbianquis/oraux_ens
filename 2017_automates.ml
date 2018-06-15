open Printf

let u0_test = 1

let nmax = 50_000

let cree_tab u0 =
  let t = Array.make nmax u0 in
  for i = 1 to nmax - 1 do
    t.(i) <- (1103515245 * t.(i - 1) + 12345) land (1 lsl 15 - 1)
  done;
  t

let tab_test = cree_tab u0_test
      
let u i =
  if i >= nmax then failwith "nmax trop petit"
  else tab_test.(i)

let q1 () =
  let f i = printf "u(%d) = %d\n" i (u i) in
  List.iter f [2; 10; 1000; 11_000]

(* Retrospectivement, le type choisi pour auto n'est pas très 
   heureux. *)

type auto =
  {nb_etats : int;
   sigma : int;
   init : int array;
   term : int array;
   delta : int array array array}

let a t n m d =
  let delta = Array.make_matrix n m [| |] in
  for i = 0 to n - 1 do
    for s = 0 to m - 1 do
      let v = ref [] in
      for j = n - 1 downto 0 do
        let x = (271 * u i + 293 * u j + 283 * u s) mod 10_000 in
        let modulo = 1 + (n * n * m) / (d * (n - i + 1)) in
        if u (10 * t + x) mod modulo = 0 then v := j :: !v
      done;
      delta.(i).(s) <- Array.of_list !v
    done
  done;
  {nb_etats = n; sigma = m; init = [| 0 |];
   term = [| n - 1 |]; delta = delta}
    

let nb_transitions {delta; nb_etats; sigma} =
  let s = ref 0 in
  for i = 0 to nb_etats - 1 do
    for j = 0 to sigma - 1 do
      s := !s + Array.length delta.(i).(j)
    done
  done;
  !s

let q2 () =
  let f (t, n, m, d) =
    let x = nb_transitions (a t n m d) in
    printf "t = %d, n = %d, m = %d, d = %d : %d\n" t n m d x in
  List.iter f [(1, 10, 5, 3); (2, 100, 10, 20); (3, 900, 20, 200)]

let accessibles auto =
  let vus = Array.make auto.nb_etats false in
  let rec explore i =
    if not vus.(i) then begin
      vus.(i) <- true;
      for s = 0 to auto.sigma - 1 do
        Array.iter explore auto.delta.(i).(s)
      done
    end in
  Array.iter explore auto.init;
  vus, Array.fold_left (fun acc b -> if b then acc + 1 else acc) 0 vus

let q3 () =
  let f (t, n, m, d) =
    let _, x = accessibles (a t n m d) in
    printf "t = %d, n = %d, m = %d, d = %d : %d\n" t n m d x in
  List.iter f [(1, 10, 5, 3); (2, 100, 10, 5); (3, 200, 10, 6); (4, 1000, 25, 5)]

(** Peu (c-à-d ?) de candidats ont compris le principe des questions 4-6. **)

let auto_inter a1 a2 =
  let n = a1.nb_etats * a2.nb_etats in
  let m = a1.sigma in
  let f i j = i * a2.nb_etats + j in
  let combine t1 t2 =
    let i1 = Array.length t1 in
    let i2 = Array.length t2 in
    let t = Array.make (i1 * i2) 0 in
    for i = 0 to i1 - 1 do
      for j = 0 to i2 - 1 do
        t.(i * i2 + j) <- f t1.(i) t2.(j)
      done
    done;
    t in
  let init = combine a1.init a2.init in
  let term = combine a1.term a2.term in
  let d = Array.make_matrix n m [| |] in
  for i = 0 to a1.nb_etats - 1 do
    for j = 0 to a2.nb_etats - 1 do
      for s = 0 to m - 1 do
        d.(f i j).(s) <- combine a1.delta.(i).(s) a2.delta.(j).(s)
      done
    done
  done;
  {delta = d; nb_etats = n; term; init; sigma = m}
  
let non_vide auto =
  let vus, _ = accessibles auto in
  let i = ref 0 in
  while !i < Array.length auto.term && not vus.(auto.term.(!i)) do
    incr i
  done;
  !i < Array.length auto.term

let q5 () =
  let f (n, d) =
    let last = ref (-1) in
    let nb = ref 0 in
    for t = 100 downto 1 do
      if non_vide (auto_inter (a t n 10 d) (a (t + 1) n 10 d)) then begin
        incr nb;
        last := t
      end
    done;
    printf "n = %d, d = %d : min = %d, nb = %d" n d !last !nb;
    print_newline () in
  List.iter f [(20, 10); (50, 10); (150, 8); (500, 12)]
        

let nb_non_vides k =
  let nb = ref 0 in
  let last = ref (-1) in
  for t = 10 downto 1 do
    let auto = ref (a (5 * t) 10 2 5) in
    for i = 1 to k do
      auto := auto_inter !auto (a (5 * t + i) 10 2 5)
    done;
    if non_vide !auto then (incr nb; last := t)
  done;
  !last, !nb 

let q6 () =
  let f k =
    let last, nb = nb_non_vides k in
    printf "k = %d : (min = %d, nb = %d)" k last nb;
    print_newline () in
  List.iter f [3; 4; 5]

(** Un quart des candidats a réussi la question 7. **)

let inverse {delta = d; nb_etats = n; sigma = m} =
  let e = Array.make_matrix n m [] in
  for i = 0 to n - 1 do
    for s = 0 to m - 1 do
      Array.iter (fun j -> e.(j).(s) <- i :: e.(j).(s)) d.(i).(s)
    done
  done;
  e

let filtre pred t =
  let n = ref 0 in
  Array.iter (fun x -> if pred x then incr n) t;
  let u = Array.make !n t.(0) in
  let j = ref 0 in
  for i = 0 to Array.length t - 1 do
    if pred t.(i) then begin
      u.(!j) <- t.(i);
      incr j
    end
  done;
  u 

let classes ({delta = d; nb_etats = n; sigma = m; term} as auto) =
  let e = inverse auto in
  let partition = Array.make n [| |] in
  let couleurs = Array.make n 0 in
  let nb_couleurs = ref 1 in
  Array.iter (fun j -> couleurs.(j) <- 1) term;
  partition.(1) <- term;
  partition.(0) <- filtre (fun i -> couleurs.(i) = 0) (Array.init n (fun i -> i));
  if Array.length term <> n then incr nb_couleurs;
  let flag = ref true in
  while !flag do
    flag := false;
    for c = 0 to !nb_couleurs - 1 do
      for c' = 0 to !nb_couleurs - 1 do
        for s = 0 to m - 1 do
          let pred = Array.make n false in
          for i = 0 to Array.length partition.(c') - 1 do
            List.iter (fun j -> pred.(j) <- true) e.(partition.(c').(i)).(s)
          done;
          let inter = filtre (fun j -> pred.(j)) partition.(c) in
          let prive = filtre (fun j -> not pred.(j)) partition.(c) in
          if Array.length inter <> 0 && Array.length prive <> 0 then begin
            partition.(c) <- inter;
            incr nb_couleurs;
            partition.(!nb_couleurs - 1) <- prive;
            Array.iter (fun j -> couleurs.(j) <- !nb_couleurs - 1) prive;
            flag := true
          end
        done
      done
    done
  done;
  !nb_couleurs, couleurs

            
let q7 () =
  let f (t, n, m, d) =
    let (x, _) = classes (a t n m d) in
    printf "n = %d : %d\n" n x in
  List.iter f [(1, 20, 2, 40); (2, 40, 3, 70); (3, 75, 3, 150); (4, 100, 5, 200)]

let rec uniques = function
  | [] -> []
  | [x] -> [x]
  | x :: y :: xs ->
    if x = y then uniques (y :: xs)
    else x :: uniques (y :: xs)

let pertube t n m d p =
  let auto = a t n m d in
  for i = 0 to n - 1 do
    let nouvelles = Array.make m [] in
    for s = 0 to m - 1 do
      let f j =
        let y = 41 * i + 31 * j + s in
        if u (5 * t + y) mod p = 0 then
          let s' = u (5 * t + y + 100) mod m in
          nouvelles.(s') <- j :: nouvelles.(s')
        else
          nouvelles.(s) <- j :: nouvelles.(s) in
      Array.iter f auto.delta.(i).(s);
    done;
    auto.delta.(i) <-
      Array.map
        (fun u -> List.sort compare u |> uniques |> Array.of_list)
        nouvelles
  done;
  auto

let q8 () =
  let f (t, n, m, d, p) =
    let auto = pertube t n m d p in
    let x = nb_transitions auto in
    printf "t = %d, n = %d : %d\n" t n x in
  List.iter f [(1, 10, 2, 50, 25); (2, 20, 2, 100, 50);
               (3, 25, 2, 100, 50); (4, 30, 2, 100, 50)]

(** Un seul candidat a fait la question 9. **)

(* On ne gère que le cas où l'alphabet est le même. *)
let union_disjointe a1 a2 =
  let n1 = a1.nb_etats in
  let n = n1 + a2.nb_etats in
  let m = a1.sigma in
  let traduit = Array.map ((+) n1) in
  let init = Array.concat [a1.init; traduit a2.init] in
  let term = Array.concat [a1.term; traduit a2.term] in
  let delta = Array.make_matrix n m [| |] in
  for i = 0 to n1 - 1 do
    delta.(i) <- a1.delta.(i)
  done;
  for i = n1 to n - 1 do
    delta.(i) <- Array.map traduit a2.delta.(i - n1)
  done;
  {nb_etats = n; sigma = m; delta; init; term}

let bisimilaires a1 a2 =
  let auto = union_disjointe a1 a2 in
  let (_, couleurs) = classes auto in
  couleurs.(0) = couleurs.(a1.nb_etats)

let q9 () = 
  let f (n, m, d, p) =
    let nb = ref 0 in
    let last = ref (-1) in
    for t = 100 downto 1 do
      if bisimilaires (a t n m d) (pertube t n m d p) then begin
        incr nb;
        last := t
      end
    done;
    printf "n = %d : min = %d, nb = %d\n" n !last !nb in
  List.iter f [(10, 2, 50, 25); (20, 2, 100, 50);
               (25, 2, 100, 50); (30, 2, 100, 50)]

(** Aucun candidat n'a dépassé ce point. **)

module H = Hashtbl

let determinise {nb_etats = n; sigma = m; delta; init; term} =
  let h = H.create n in
  let d = H.create (n * m) in
  H.add h init 0;
  let est_term = Array.make n false in
  Array.iter (fun j -> est_term.(j) <- true) term;
  let liste_term = ref [] in
  let succ partie s =
    let vus = Array.make n false in
    let ajoute i = Array.iter (fun j -> vus.(j) <- true) delta.(i).(s) in
    Array.iter ajoute partie;
    let taille = Array.fold_left (fun acc b -> if b then acc + 1 else acc) 0 vus in
    let image = Array.make taille 0 in
    let j = ref 0 in
    let terminal = ref false in
    for i = 0 to n - 1 do
      if vus.(i) then begin
        image.(!j) <- i;
        incr j;
        terminal := !terminal || est_term.(i)
      end
    done;
    image, !terminal in
  let count = ref 1 in
  let rec explore partie =
    let i = H.find h partie in
    for s = 0 to m - 1 do
      let image, terminal = succ partie s in
      if not (H.mem h image) then begin
        H.add d (i, s) [| !count |];
        if terminal then liste_term := !count :: !liste_term;
        H.add h image !count;
        incr count;
        explore image
      end
      else
        let j = H.find h image in
        H.add d (i, s) [| j |];
    done in
  explore init;
  let nb_etats = H.length h in
  let delta' = Array.make_matrix nb_etats m [| |] in
  for i = 0 to nb_etats - 1 do
    for s = 0 to m - 1 do
      try
        delta'.(i).(s) <- H.find d (i, s)
      with
      | Not_found -> ()
    done
  done;
  {init = [| 0 |]; term = Array.of_list !liste_term; delta = delta'; nb_etats;
   sigma = m}


let complement {nb_etats; sigma; delta; init; term} =
  let nb_term = nb_etats - Array.length term in
  let t = Array.make nb_term (-1) in
  let i = ref 0 in
  for j = 0 to nb_etats - 1 do
    if not (Array.exists ((=) j) term) then begin
      t.(!i) <- j;
      incr i
    end
  done;
  {nb_etats; sigma; delta; init; term = t}

let inclus a1 a2 =
  let a2bar = complement (determinise a2) in
  not (non_vide (auto_inter a1 a2bar))

let q10 () =
  let f (n, d, d') =
    let last = ref (-1) in
    let nb = ref 0 in
    for t = 50 downto 1 do
      if inclus (a (2 * t) n 2 d) (a (2 * t + 1) n 2 d') then begin
        incr nb;
        last := t
      end
    done;
    printf "n = %d : (min = %d, nb = %d)\n" n !last !nb in
  List.iter f [(10, 3, 8); (15, 5, 10); (60, 5, 10); (90, 10, 15)]

let egal a1 a2 = (inclus a1 a2) && (inclus a2 a1)
  

let q11 () =
  let f (n, d, p) =
    let last = ref (-1) in
    let nb = ref 0 in
    for t = 100 downto 1 do
      let a1 = a t n 2 d in
      let a2 = pertube t n 2 d p in
      if not (bisimilaires a1 a2) && egal a1 a2 then begin
        incr nb;
        last := t
      end
    done;
    printf "n = %d : (min = %d, nb = %d)\n" n !last !nb in
  List.iter f [(10, 50, 50); (15, 75, 50); (20, 100, 50); (25, 100, 50)] 
