open Printf

let u0_test = 42

let nmax = 50_000

let m = 1 lsl 31 - 1

let cree_tab u0 =
  let u = Array.make nmax u0 in
  for i = 1 to nmax - 1 do
    u.(i) <- (16807 * u.(i - 1) + 17) mod m
  done;
  u

let u_test = cree_tab u0_test

let u i =
  if i >= nmax then failwith "nmax trop petit"
  else u_test.(i)


let q1 () =
  let f i = printf "n = %d : %d\n" i (u i mod 101) in
  List.iter f [5; 100; 997]


let v k n =
  1 lsl k + (u n land (1 lsl k - 1))

let q2 ()  =
  let f k = printf "k = %d : %d\n" k (v k (97 * k mod 997) mod 101) in
  List.iter f [5; 30; 61]

type tri =
  | Z
  | U
  | N of tri * tri * tri

let rec impair = function
  | Z -> false
  | U -> true
  | N (g, p, d) -> impair g

let rec sign = function
  | Z -> 0
  | U -> u 10 mod 97
  | N (g, p, d) when impair p -> (sign g + (u 20) * (sign d)) mod 97
  | N (g, p, d) -> (sign g + (u 30) * (sign d)) mod 97

let pmax n =
  let p = ref 0 in
  while 1 lsl !p < 62 && 1 lsl (1 lsl !p) <= n do
    incr p
  done;
  !p - 1

let rec tri_of_int n =
  if n = 0 then Z
  else if n = 1 then U
  else
    let p = pmax n in
    let xp = 1 lsl (1 lsl p) in
    let ga = tri_of_int (n land (xp - 1)) in
    let mi = tri_of_int p in
    let dr = tri_of_int (n lsr (1 lsl p)) in
    N (ga, mi, dr)

let rec int_of_tri = function
  | Z -> 0
  | U -> 1
  | N (g, p, d) -> int_of_tri g
                   + (int_of_tri d
                      * 1 lsl (1 lsl int_of_tri p))

let q3 () =
  let f (k, n) =
    let t = tri_of_int (v k n) in
    printf "(%d, %d) : %d" k n (sign t);
    print_newline () in
  List.iter f [(1, 10); (2, 20); (32, 30); (61, 40)]

let rec h n =
  if n = 0 then U
  else
    let t = h (n - 1) in
    N (t, t, t)

let rec sign_h = function
  | Z -> 0
  | U -> u 10 mod 97
  | N (g, p, d) when impair p ->
    let x = sign_h g in
    (x + (u 20) * x) mod 97
  | N (g, p, d) ->
    let x = sign_h g in
    (x + (u 30) * x) mod 97
    

let q4 () =
  let f k =
    let n = v k (7 * k) in
    printf "k = %d : %d" k (sign_h (h n));
    print_newline () in
  List.iter f [0; 2; 4; 8]

let rec gen k n =
  match k, n with
  | 0, _ when u n mod 7 = 0 -> Z
  | 0, _ -> U
  | _ ->
    let k' = max 0 (k - 1 - (u n mod 2)) in
    let g = gen k' ((n + 1) mod 997) in
    let p = v k' n in
    let d = gen k' ((n + 2) mod 997) in
    if d = Z then g
    else N (g, tri_of_int p, d)

let q5 () =
  let f (k, n) =
    let t = gen k n in
    printf "(%d, %d) : %d" k n (sign t);
    print_newline () in
  List.iter f [(6, 35); (8, 45); (10, 55); (12, 65); (14, 75)]


let rec dec = function
  | U -> Z
  | Z -> failwith "dec 0"
  | N (g, p, d) when g <> Z -> N (dec g, p, d)
  | N (_, p, U) -> x' p
  | N (_, p, d) -> N (x' p, p, dec d)
and x' = function
  | Z -> U
  | p ->
    let q = dec p in
    let q' = x' q in
    N (q', q, q')

let q6 () =
  let f k =
    let t = gen k (19 * k mod 997) in
    let s = sign (dec t) in
    printf "k = %d : %d" k s;
    print_newline () in
  List.iter f [6; 16; 26]

let rec inc = function
  | Z -> U
  | U -> N (Z, Z, U)
  | N (g, p, d) ->
    let g' = inc g in
    if g' <> N (Z, p, U) then N (g', p, d)
    else
      let d' = inc d in
      if d' <> N (Z, p, U) then N (Z, p, d')
      else N (Z, inc p, U)

let q7 () =
  let f k =
    let t = gen k (17 * k mod 997) in
    let x = sign (inc t) in
    printf "k = %d : %d" k x;
    print_newline () in
  List.iter f [6; 7; 16]


let rec compare t t' =
  match t, t' with
  | Z, Z -> 0
  | Z, _ -> -1
  | U, Z -> 1
  | U, U -> 0
  | U, _ -> -1
  | N (g, p, d), N (g', p', d') ->
    let x = compare p p' in
    if x <> 0 then x
    else
      let y = compare d d' in if y <> 0 then y
      else compare g g'
  | N (_, _, _), _ -> 1

let q8 () =
  let f k =
    let t = gen k (29 * k mod 997) in
    let t' = gen k (31 * k mod 997) in
    printf "k = %d : %d" k (compare t t');
    print_newline () in
  List.iter f [6; 8; 16]

let rec add t t' =
  match t, t' with
  | Z, x | x, Z -> x
  | U, x | x, U -> inc x
  | N (g, p, d), N (g', p', d') ->
    if compare p p' = 0 then
      norm (N (add g g', p, add d d'))
    else if compare p p' = -1 then
      norm (N (add t g', p', d'))
    else
      norm (N (add g t', p, d))
and norm = function
  | N (N(gg, gp, gd), p, d) as t->
    let x = compare gp p in
    if x = -1 then normd t
    else if x = 0 then normd (N (gg, p, add gd d))
    else norm (N (norm (N (gg, p, d)), gp, gd))
  | N (g, p, Z) -> g
  | t -> normd t
and normd = function
  | N (g, p, N (dg, dp, dd)) as t ->
    let x = compare dp p in
    if x = - 1 then t
    else if x = 0 && dg <> Z then N (N (g, p, dg), inc p, dd)
    else if x = 0 then N (g, inc p, dd)
    else norm (N (normd (N (g, p, dg)), dp, normd (N (Z, p, dd))))
  | N (g, p, Z) -> g
  | t -> t

let (++) = add


let q9 () =
  let f k =
    let t = gen k (41 * k mod 997) in
    let t' = gen k (43 * k mod 997) in
    let x = sign (add t t') in
    printf "k = %d : %d" k x;
    print_newline () in
  List.iter f [6; 12; 16]

let rec ( ** ) t t' =
  match t, t' with
  | Z, _ -> Z
  | U, _ -> t'
  | N (g, p, d), N (g', p', d') when compare p p' = 0 ->
    norm (N (norm (N (g ** g', p', g ** d' ++ g' ** d)),
             inc p,
             d ** d'))
  | N (g, p, d), N (g', p', d') when compare p p' = -1 ->
    norm (N (norm (N (g ** g', p, g' ** d)),
             p',
             norm (N (g ** d', p, d ** d'))))
  | _ -> t' ** t

let q10 () =
  let f k =
    let t = gen k (41 * k mod 997) in
    let t' = gen k (43 * k mod 997) in
    let x = sign (t ** t') in
    printf "k = %d : %d" k x;
    print_newline () in
  List.iter f [5; 8; 10]

type abr =
  | E
  | No of tri * abr * abr

let rec insere x = function
  | E -> No (x, E, E)
  | No (y, ga, dr) as t ->
    let res = compare x y in 
    if res = 0 then t
    else if res = -1 then No (y, insere x ga, dr)
    else No (y, ga, insere x dr)

let rec repr x = function
  | E -> None
  | No (y, ga, dr) ->
    let res = compare x y in
    if res = 0 then Some y
    else if res = -1 then repr x ga
    else repr x dr
      

let rec card = function
  | E -> 0
  | No (_, ga, dr) -> 1 + card ga + card dr

let rec noeuds = function
  | N (g, p, d) -> 1 + noeuds g + noeuds p + noeuds d
  | _ -> 0

let parties tri =
  let rec aux arbre set = match arbre with
    | N (g, p, d) as t->
      insere t (set |> aux g |> aux p |> aux d)
    | _ -> set in
  card (aux tri E)

let q11 () =
  let f k =
    let t = gen k (23 * k mod 997) in
    printf "k = %d : (s = %d, t = %d)" k (parties t) (noeuds t);
    print_newline () in
  List.iter f [8; 16; 24; 32]


let pop_g k =
  let t = Array.make_matrix (k + 1) 997 (-1) in
  let rec pop k n =
    if t.(k).(n) <> -1 then t.(k).(n)
    else if k = 0 && u n mod 7 = 0 then 0
    else if k = 0 then 1
    else
      let k' = max 0 (k - 1 - u n mod 2) in
      let g = pop k' ((n + 1) mod 997) in
      let d = pop k' ((n + 2) mod 997) in
      t.(k).(n) <- d + g;
      d + g in
  pop k (37 * k mod 997) mod 97
      
let q12 () =
  let f k = printf "k = %d : %d\n" k (pop_g k) in
  List.iter f [48; 55; 61]

      
type 'b assoc =
  | Empty
  | Node of (tri * 'b) * 'b assoc * 'b assoc

let rec set t x = function
  | Empty -> Node ((t, x), Empty, Empty)
  | Node ((t', y), ga, dr) as s ->
    let res = compare t t' in
    if res = 0 then s
    else if res < 0 then set t x ga
    else set t x dr

let rec get t = function
  | Empty -> None
  | Node ((t', y), ga, dr) ->
    let res = compare t t' in
    if res = 0 then Some y
    else if res = -1 then get t ga
    else get t dr

let sig_dec k =
  let t_gen = Array.make_matrix (k + 1) 997 None in
  let t_v = Array.make_matrix (k + 1) 997 None in 
  let sigs = Hashtbl.create 1000 in
  let decs = ref Empty in
  let xprimes = ref Empty in
  let arbre_v k n =
      match t_v.(k).(n) with
      | None -> let res = tri_of_int (v k n) in t_v.(k).(n) <- Some res; res
      | Some x -> x in                                  
  let rec gen k n =
    match t_gen.(k).(n) with
    | None ->
      let res = 
        if k = 0 && u n mod 7 = 0 then Z
        else if k = 0 then U
        else
          let k' = max 0 (k - 1 - u n mod 2) in
          let g = gen k' ((n + 1) mod 997) in
          let p = arbre_v k' n in
          let d = gen k' ((n + 2) mod 997) in
          if d = Z then g
          else N (g, p, d) in
      t_gen.(k).(n) <- Some res;
      res
    | Some res -> res in
  let rec sign t =
    try Hashtbl.find sigs t
    with
    | Not_found ->
      match t with
      | Z -> 0
      | U -> u 10 mod 97
      | N (g, p, d) ->
        let sg = sign g in
        let sd = sign d in
        let m = if impair p then u 20 else u 30 in
        let res = (sg + m * sd) mod 97 in
        Hashtbl.add sigs t res;
        res in
  let rec dec t =
    match get t !decs with
    | Some t' -> t'
    | None ->
      let res = 
        match t with
        | Z -> failwith "dec Z"
        | U -> Z
        | N (Z, p, U) -> x' p 
        | N (Z, p, d) -> N (x' p, p, dec d)
        | N (g, p, d) -> N (dec g, p, d) in
      decs := set t res !decs;
      res
  and x' p =
    match get p !xprimes with
    | Some q -> q
    | None ->
      match p with
      | Z -> U
      | p ->
        let q = dec p in
        let r = x' q in
        let res = N (r, q, r) in
        xprimes := set p res !xprimes;
        res  in
  let n = (19 * k) mod 997 in
  let t = gen k n in
  sign (dec t)

