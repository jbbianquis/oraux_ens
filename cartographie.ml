open Printf

let u0 = 7
let nmax = 50_000

let _tab_u =
  let t = Array.make nmax u0 in
  for i = 1 to nmax - 1 do
    t.(i) <- (15091 * t.(i - 1)) mod 64007
  done;
  t

let u i =
  if i >= nmax then failwith "nmax trop petit"
  else _tab_u.(i)

(**************)
(* Question 1 *)
(**************)

let q1 () =
  print_endline "Question 1";
  List.iter (fun i -> printf "u(%d) = %d\n" i (u i)) [10; 100; 1000];
  print_newline ()

(**************)
(* Question 2 *)
(**************)

type arbre = F | N of arbre * arbre

let rec a n =
  if n = 0 then F
  else N (a (u (2 * n) mod n), a (u (2 * n + 1) mod n))
                                
let rec noeuds = function
  | F -> 1
  | N (ga, dr) -> 1 + noeuds ga + noeuds dr

let rec feuilles = function
  | F -> 1
  | N (ga, dr) -> feuilles ga + feuilles dr

let q2 () =
  print_endline "Question 2";
  List.iter (fun n ->
      let t = a n in
      printf "A(%d) : %d noeuds, %d feuilles\n" n (noeuds t) (feuilles t))
    [10; 100; 1000];
  print_newline ()

(**************)
(* Question 3 *)
(**************)

type arbre_etiquete =
  | Fe of int
  | No of int * int * arbre_etiquete * arbre_etiquete

let mi = function
  | Fe m -> m
  | No (_, m, _, _) -> m
                                        
let etiquette arbre =
  let rec aux actuel = function
    | F -> Fe actuel
    | N (ga, dr) ->
       let ga' = aux (actuel + 1) ga in
       let mg = mi ga' in
       let dr' = aux (mg + 1) dr in
       No (actuel, mi dr', ga', dr') in
  aux 0 arbre

let ar_eti n = etiquette (a n)

let rec cherche arbre li =
  match arbre with
  | Fe i when i = li -> li
  | No (l, m, ga, dr) ->
    if l = li then m
    else if mi ga >= li then cherche ga li
    else cherche dr li
  | _ -> failwith "pas trouve"

let q3 () =
  print_endline "Question 3";
  List.iter (fun (n, li) -> printf "n = %d, li = %d -> m_i = %d\n"
                n li (cherche (ar_eti n) li))
    [(10, 3); (100, 9); (1000, 30)];
  print_newline ()
  
(**************)
(* Question 4 *)
(**************)

(* Renvoie la profondeur du noeud étiqueté li *)
let rec profondeur arbre li =
  match arbre with
  | Fe i when i = li -> 0
  | No (l, m, ga, dr) ->
     if l = li then 0
     else if mi ga >= li then 1 + profondeur ga li
     else 1 + profondeur dr li
  | _ -> failwith "prof : pas trouvé"

(* Renvoie la distance entre les noeuds li et li'. *)
let rec distance arbre li li' =
  match arbre with
  | Fe i when i = li && i = li' -> 0
  | No (l, m, ga, dr) ->
     if l = li then profondeur arbre li'
     else if l = li' then profondeur arbre li
     else if li <= mi ga && li' <= mi ga then
       distance ga li li'
     else if li > mi ga && li' > mi ga then
       distance dr li li'
     else if li <= mi ga && li' > mi ga then
       1 + profondeur ga li + profondeur dr li'
     else
       1 + profondeur ga li' + profondeur dr li
  | _ -> failwith "distance"

let q4 () =
  print_endline "Question 4";
  List.iter (fun (n, i, j) -> printf "n = %d, i = %d, j = %d -> distance %d\n"
                n i j (distance (ar_eti n) i j))
    [(10, 3, 9); (100, 5, 30); (1000, 30, 90)];
  print_newline ()

(**************)
(* Question 5 *)
(**************)
          
let cout_max arbre p =
  let rec f max_actuel = function
    | Fe i -> if i < max_actuel then 0 else 1
    | No (l, m, ga, dr) ->
      if l < max_actuel then
        max (f max_actuel ga) (f max_actuel dr)
      else
        let nv_max = (l / p + 1) * p  in
        1 + max (f nv_max ga) (f nv_max dr) in
  f 0 arbre

let nb_noeuds = function
  | Fe _ -> 1
  | No (i, m, _, _) -> m + 1 - i
    
let nb_feuilles arbre = (nb_noeuds arbre + 1) / 2
                                                
let cout_moyen arbre p =
  let rec f max_actuel cout = function
    | Fe i -> if i < max_actuel then cout else cout + 1
    | No (l, m, ga, dr) ->
       if l < max_actuel then
         (f max_actuel cout ga) + (f max_actuel cout dr)
       else
         let nv_max = (l / p + 1) * p  in
         (f nv_max (cout + 1) ga) + (f nv_max (cout + 1) dr) in
  let foi = float_of_int in
  foi (f 0 0 arbre) /. foi (nb_feuilles arbre)

let q5 () =
  let f (n, p) =
    let arbre = ar_eti n in
    printf "A(%d), p = %d -> C_moy = %.3f, C_max = %d\n"
      n p (cout_moyen arbre p) (cout_max arbre p) in
  print_endline "Question 5";
  List.iter f [(10, 3); (100, 6); (1000, 9)];
  print_newline ()

(**************)
(* Question 6 *)
(**************)

(* Renvoie (C_max(arbre), p(arbre)) *)
let rec cmax_et_p arbre p =
  match arbre with
  | Fe i -> (1, 1)
  | No (l, m, ga, dr) ->
     let cg, pg = cmax_et_p ga p in
     let cd, pd = cmax_et_p dr p in
     if cg < cd && pd < p then (cd, pd + 1)
     else if cd < cg && pg < p then (cg, pg + 1)
     else if cg < cd then (1 + cd, 1)
     else if cd < cg then (1 + cg, 1)
     else if pg + pd < p then (cg, pg + pd + 1)
     else (* cg = cd, pg + pd + 1 > p *) (1 + cg, 1)

let q6 () =
  let f (n, p) =
    let cm, pracine = cmax_et_p (ar_eti n) p in
    printf "A(%d), p = %d ->  C_max(A) = %d, p(A) = %d\n" n p cm pracine in
  print_endline "Question 6";
  List.iter f [(10, 3); (100, 6); (1000, 9)];
  print_newline ()

(**************)
(* Question 7 *)
(**************)

(* Une première version (on mémoïse les valeurs de C(i, k)). *)
let cmoy arbre p =
  let n = nb_noeuds arbre in
  let t_aux = Array.make_matrix n (p + 1) (-1) in
  let rec aux k = function
    | Fe _ -> 1
    | No (x, _, ga, dr) ->
       if t_aux.(x).(k) <> -1 then t_aux.(x).(k)
       else
         let cout i j =
           let cg = aux i ga in
           let cd = aux j dr in
           let fg = nb_feuilles ga in
           let fd = nb_feuilles dr in
           if i + j < k then
             cg + cd
           else if i >= k && j >= k then
             cg + cd + fg + fd
           else if i < k && (j >= k || fd <= fg) then
             cg + cd + fd
           else if j < k && (i >= k || fg < fd) then
             cg + cd + fg
           else
             failwith "impossible" in
         let cout_opt = ref max_int in
         for i = 1 to p do
           for j = 1 to p do
             cout_opt := min !cout_opt (cout i j)
           done;
         done;
         t_aux.(x).(k) <- !cout_opt;
         !cout_opt in
  let c = aux p arbre in
  (float_of_int c) /. (float_of_int (nb_feuilles arbre))

(* Une deuxième version plus efficace : tous les cout i j ne sont pas utiles. *)

(* Une grande valeur qui ne va pas faire un overflow quand on lui 
   ajoute quelque chose. *)
let inf = 1 lsl 24

let min_array = Array.fold_left min max_int

let cmoy2 arbre p =
  let n = nb_noeuds arbre in
  let t_aux = Array.make_matrix n (p + 1) (-1) in
  let rec aux k arbre =
    if k <= 0 then inf
    else
      match arbre with
      | Fe _ -> 1
      | No (x, _, ga, dr) ->
        if t_aux.(x).(k) <> -1 then t_aux.(x).(k)
        else
          let cout i =
            let cg = if i < k then aux i ga else inf in
            let cg' = aux i ga + nb_feuilles ga in
            (* i + j = k - 1, une seule carte pour x, ga et dr *)
            let cd1 = aux (k - 1 - i) dr in
            (* j = k - 1, la racine va dans la carte de droite *)
            let cdd = aux (k - 1) dr in
            (* j = p, la racine va dans la carte de gauche *)
            let cdg = aux p dr + nb_feuilles dr in
            min_array [| cg + cd1; cg' + cdd; cg + cdg; cg' + cdg |] in
          let cout_opt = ref max_int in
          for i = 1 to p do
            cout_opt := min !cout_opt (cout i)
          done;
          t_aux.(x).(k) <- !cout_opt;
          !cout_opt in
  let c = aux p arbre in
  (float_of_int c) /. (float_of_int (nb_feuilles arbre))


let q7 n p =
  cmoy (etiquette (a n)) p

let cmoy_V arbre p v =
  let n = nb_noeuds arbre in
  let t_aux = Array.init n (fun i -> Array.make_matrix (p + 1) (v + 1) (-1)) in
  let rec aux k u arbre =
    if u <= 0 || k <= 0 then inf
    else
      match arbre with
      | Fe _ -> 1
      | No (x, _, ga, dr) ->
         if t_aux.(x).(k).(u) <> -1 then t_aux.(x).(k).(u)
         else
           let cout i =
             let cg = if i < k then aux i u ga else inf in
             let cg' = aux i (u - 1) ga + nb_feuilles ga in
             (* i + j = k - 1, une seule carte pour x, ga et dr *)
             let cd1 = aux (k - 1 - i) u dr in
             (* j = k - 1, la racine va dans la carte de droite *)
             let cdd = aux (k - 1) u dr in
             (* j = p, la racine va dans la carte de gauche *)
             let cdg = aux p (u - 1) dr + nb_feuilles dr in
             min_array [| cg + cd1; cg' + cdd; cg + cdg; cg' + cdg |] in
           let cout_opt = ref max_int in
           for i = 1 to p do
             cout_opt := min !cout_opt (cout i)
           done;
           t_aux.(x).(k).(u) <- !cout_opt;
           !cout_opt in
  let c = aux p v arbre in
  (float_of_int c) /. (float_of_int (nb_feuilles arbre))                        
                                                    
let q8 n =
  let arbre = etiquette (a n) in
  let rec f p =
    let m = fst (cmax_et_p arbre p) in
    let c = cmoy2 arbre p in
    let c' = cmoy_V arbre p m in
    if c' -. c > 1e-6 then (p, c, c')
    else f (p + 1) in
  let p, c, c' = f 3 in
  Printf.printf "%d, %.3f, %.3f\n" p c c';;

#load "unix.cma";;

let time = Unix.gettimeofday

let chrono f =
  let t0 = time () in
  ignore (f ());
  Printf.printf "Temps : %.3fs\n" (time () -. t0)
  
