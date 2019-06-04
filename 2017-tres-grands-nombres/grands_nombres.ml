
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
    | N (g, _, _) -> impair g
    
let rec signature = function
    | Z -> 0
    | U -> u 10 mod 97
    | N (g, p, d) when impair p -> 
        (signature g + (u 20) * (signature d)) mod 97
    | N (g, _, d) -> 
        (signature g + (u 30) * (signature d)) mod 97
        
let loglog n = 
    let p = ref 0 in
    while 1 lsl !p < 62 && 1 lsl (1 lsl !p) <= n do
        incr p
    done;
    !p - 1
    
let rec tri_of_int n = 
    if n = 0 then Z
    else if n = 1 then U
    else
        let p = loglog n in
        let xp = 1 lsl (1 lsl p) in
        let g = tri_of_int (n land (xp - 1)) in
        let mid = tri_of_int p in
        let d = tri_of_int (n lsr (1 lsl p)) in
        N (g, mid, d)
        
let q3 () = 
    let f (k, n) = 
        let t = tri_of_int (v k n) in
        printf "(%d, %d) : %d\n" k n (signature t) in
    List.iter f [(1, 10); (2, 20); (32, 30); (61, 40)];
    print_newline ()
        

let rec h n = 
    if n = 0 then U
    else 
        let t = h (n - 1) in
        N (t, t, t)

let rec signature_h n = 
    if n = 0 then (u 10) mod 97
    else 
        let s = signature_h (n - 1) in
        (s + (u 20) * s) mod 97
  
let q4 () = 
    let f k = 
        let n = v k (7 * k) in
        printf "k = %d : %d\n" k (signature_h n) in
    List.iter f [0; 2; 4; 8];
    print_newline ()

(*
let cree_tab_gen kmax = 
    let nmax = 996 in
    let t = Array.make_matrix (kmax + 1) (nmax + 1) Z in
    for n = 0 to nmax do
        if u n mod 7 <> 0 then t.(0).(n) <- U
    done;
    for k = 1 to kmax do
        for n = 0 to nmax do
            let k' = max 0 (k - 1 - (u n mod 2)) in
            let g = t.(k').((n + 1) mod 997) in
            let p = v k' n in
            let d = t.(k').((n + 2) mod 997) in
            if d = Z then t.(k).(n) <- g
            else t.(k).(n) <- N (g, tri_of_int p, d)
        done
    done;
    t

let tab_gen = cree_tab_gen 14

let gen k n = tab_gen.(k).(n)
*)


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
        printf "(%d, %d) : %d" k n (signature t);
        print_newline () in
    List.iter f [(6, 35); (8, 45); (10, 55); (12, 65); (14, 75)];
    print_newline ()

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
        let s = signature (dec t) in
        printf "k = %d : %d\n" k s in
    List.iter f [6; 16; 26];
    print_newline ()

let rec int_of_tri = function
    | Z -> 0
    | U -> 1
    | N (g, p, d) -> 
        int_of_tri g
        + (int_of_tri d * 1 lsl (1 lsl int_of_tri p))      
        
let test_dec nmax = 
    let test n = (int_of_tri (dec (tri_of_int n)) = n - 1) in
    for n = 1 to nmax do
        assert (test n)
    done;
    printf "OK jusqu'à n = %d\n" nmax;
    print_newline ()

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
        let t = inc (gen k (17 * k mod 997)) in
        printf "k = %d -> %d\n" k (signature t) in
    List.iter f [6; 7; 16];
    print_newline ()

let test_inc nmax = 
    let test n = (int_of_tri (inc (tri_of_int n)) = n + 1) in
    for n = 0 to nmax do
        assert (test n)
    done;
    printf "OK jusqu'à n = %d\n" nmax;
    print_newline ()
    
let rec compare t t' = 
    match t, t' with
    | Z, Z | U, U -> 0
    | _, Z -> 1
    | Z, _ -> -1
    | _, U -> 1    
    | U, _ -> -1
    | N (g, p, d), N (g', p', d') ->
        let x = compare p p' in
        if x <> 0 then x
        else
            let y = compare d d' in
            if y <> 0 then y 
            else compare g g'
 
 let q8 () =
    let f k =
        let t = gen k (29 * k mod 997) in
        let t' = gen k (31 * k mod 997) in
        printf "k = %d : %d\n" k (compare t t') in
    List.iter f [6; 8; 16];
    print_newline ()

let teste_compare nmax = 
    let tri = tri_of_int in
    for i = 0 to nmax do
        assert (compare (tri i) (tri i) = 0);
        for j = i + 1 to nmax do
            assert (compare (tri i) (tri j) = -1);
            assert (compare (tri j) (tri i) = 1)
        done
    done;
    printf "OK jusqu'à %d\n" nmax;
    print_newline ()
    
let rec (++) t t' = 
    match t, t' with
    | Z, x | x, Z -> x
    | U, x | x, U -> inc x
    | N (g, p, d), N (g', p', d') ->
        if compare p p' = 0 then norm (g ++ g', p, d ++ d')
        else if compare p p' = 1 then norm (g ++ t', p, d)
        else norm (g' ++ t, p', d')
and norm = function
    | (N (gg, gp, gd), p, d) as t ->
        let x = compare gp p in
        if x = -1 then normd t
        else if x = 0 then normd (gg, p, gd ++ d)
        else norm (norm (gg, p, d), gp, gd)
    | g, p, d -> normd (g, p, d)
and normd = function
    | (g, p, N (dg, dp, dd)) ->
        let x = compare dp p in
        if x = -1 then N (g, p, N (dg, dp, dd))
        else if x = 0 then N (normd (g, p, dg), inc p, dd)
        else norm (normd (g, p, dg), dp, normd (Z, p, dd))
    | (g, p, Z) -> g
    | (g, p, U) -> N (g, p, U)
    
let q9 () =
    let f k =
        let t = gen k (41 * k mod 997) in
        let t' = gen k (43 * k mod 997) in
        let x = signature (t ++ t') in
        printf "k = %d : %d\n" k x in
    List.iter f [6; 12; 16];
    print_newline ()

let teste_add nmax = 
    let teste x y = (tri_of_int x ++ tri_of_int y = tri_of_int (x + y)) in
    for x = 1 to nmax do
        for y = 1 to nmax do
            assert (teste x y)
        done
    done;
    printf "OK jusqu'à %d" nmax;
    print_newline ()

let rec ( ** ) t t' = 
    match t, t' with
    | Z, _ | _, Z -> Z
    | U, x | x, U -> x
    | N (g, p, d), N (g', p', d') ->
        let x = compare p p' in
        if x < 0 then
            let g'' = t ** g' in
            let d'' = norm (g ** d', p, d ** d') in
            norm (g'', p', d'')
        else if x = 0 then
            let g'' = norm (g ** g', p, g ** d' ++ g' ** d) in
            let d'' = d ** d' in
            norm (g'', inc p, d'')
        else t' ** t
        
let q10 () =
    let f k =
        let t = gen k (41 * k mod 997) in
        let t' = gen k (43 * k mod 997) in
        let x = signature (t ** t') in
        printf "k = %d : %d\n" k x in
    List.iter f [5; 8; 10];
    print_newline ()
      

let teste_mul nmax = 
    let teste x y = (tri_of_int x ** tri_of_int y = tri_of_int (x * y)) in
    for x = 1 to nmax do
        for y = 1 to nmax do
            assert (teste x y)
        done
    done;
    printf "OK jusqu'à %d" nmax;
    print_newline ()

let rec nb_noeuds = function
    | Z | U -> 0
    | N (g, p, d) -> 1 + nb_noeuds g + nb_noeuds p + nb_noeuds d

type abr = 
    | Vide
    | Noeud of tri * abr * abr
    
(* Renvoie le nouvel arbre, et un booléen indiquant s'il y a eu modification *)    
let rec insere t = function
    | Vide -> (Noeud (t, Vide, Vide), true)
    | Noeud (t', g, d) ->
        let x = compare t t' in
        if x = 0 then (Noeud (t', g, d), false)
        else if x < 0 then 
            let g', b = insere t g in 
            (Noeud (t', g', d), b)
        else 
            let d', b = insere t d in
            (Noeud (t', g, d'), b)
        
let rec cardinal = function
    | Vide -> 0
    | Noeud (_, g, d) -> 1 + cardinal g + cardinal d
    
let nb_parties t = 
    let rec aux foret ensemble = 
        match foret with
        | [] -> ensemble
        | Z :: xs | U :: xs -> aux xs ensemble
        | (N (g, p, d) as t) :: xs -> 
            let ensemble', b = insere t ensemble in
            if b then aux (g :: p :: d :: xs) ensemble'
            else aux xs ensemble' in
    cardinal (aux [t] Vide)
    
let q11 () = 
    let f k = 
        let t = gen k (23 * k mod 997) in
        printf "k = %d -> (s = %d, t = %d)" k (nb_parties t) (nb_noeuds t);
        print_newline () in
    List.iter f [8; 16; 24; 32];
    print_newline ()
    
let nb_parties_hash t = 
    let h = Hashtbl.create 1000 in
    let rec traite = function
        | Z | U -> ()
        | N (g, p, d) as t ->
            if not (Hashtbl.mem h t) then begin
                Hashtbl.add h t ();
                traite g;
                traite p;
                traite d
            end in
    traite t;
    Hashtbl.length h
    
let q11_hash () = 
    let f k = 
        let t = gen k (23 * k mod 997) in
        printf "k = %d -> (s = %d, t = %d)" k (nb_parties_hash t) (nb_noeuds t);
        print_newline () in
    List.iter f [8; 16; 24; 32];
    print_newline ()
    

module H = Hashtbl

let taille = 1_000_000

type id = Id of int
type tri_hash_consed = 
    | Zh 
    | Uh 
    | Th of id * id * id
    
let id (Id i) = i


let tab_hash = H.create taille   

let tab_noeuds = 
    let t = Array.make taille Zh in
    t.(1) <- Uh;
    H.add tab_hash Zh (Id 0);
    H.add tab_hash Uh (Id 1);
    t

let id_zero = Id 0
let id_un = Id 1
let invalide = Id (-1)

let next = ref 2
    
let construit g p d = 
    try 
        H.find tab_hash (Th (g, p, d)) 
    with
        Not_found -> 
            if !next >= taille then failwith 
                "Échec de la construction : tableau trop petit.";
            tab_noeuds.(!next) <- Th (g, p, d);
            H.add tab_hash (Th (g, p, d)) (Id !next);
            incr next;
            Id (!next - 1)
    
let get_noeud (Id i) = 
    assert (i >= 2 || i < !next);
    tab_noeuds.(i)

let tab_gen = 
    let kmax = 61 in
    let nmax = 996 in
    let t = Array.make_matrix (kmax + 1) (nmax + 1) invalide in
    for n = 0 to nmax do
        if u n mod 7 <> 0 then t.(0).(n) <- id_un
        else t.(0).(n) <- id_zero
    done;
    t

let rec tri_cons_of_int (n : int) : id = 
    if n = 0 then id_zero
    else if n = 1 then id_un
    else 
        let p = loglog n in
        let xp = 1 lsl (1 lsl p) in
        let g = tri_cons_of_int (n land (xp - 1)) in
        let m = tri_cons_of_int p in
        let d = tri_cons_of_int (n lsr (1 lsl p)) in
        construit g m d

let rec gen_m k n : id = 
    if tab_gen.(k).(n) = invalide then begin
        let k' = max 0 (k - 1 - u n mod 2) in
        let g = gen_m k' ((n + 1) mod 997) in
        let p = tri_cons_of_int (v k' n) in
        let d = gen_m k' ((n + 2) mod 997) in
        let res = 
            if d = id_zero then g
            else construit g p d in
        tab_gen.(k).(n) <- res
    end;
    tab_gen.(k).(n)
    
let tab_pop = Array.make taille (-1)

let rec pop (t : id) : int = 
    if tab_pop.(id t) = -1 then begin
        let res = match get_noeud t with
            | Zh -> 0
            | Uh -> 1
            | Th (g, p, d) -> pop g + pop d in
        tab_pop.(id t) <- res
    end;
    tab_pop.(id t)
        
let q12 () = 
    let f k = 
        let t = gen_m k (37 * k mod 997) in
        printf "k = %d -> %d\n" k (pop t mod 97) in
    List.iter f [48; 55; 61];
    print_newline ()
            
let tab_signature = Array.make taille (-1)

let rec impair (t : id) : bool = 
    match get_noeud t with
    | Zh -> false
    | Uh -> true
    | Th (g, p, d) -> impair g

let rec signature_m t = 
    if tab_signature.(id t) = -1 then begin
        let res = 
            match get_noeud t with
            | Zh -> 0
            | Uh -> u 10 mod 97
            | Th (g, p, d) -> 
                if impair p then (signature_m g + u 20 * signature_m d) mod 97
                else (signature_m g + u 30 * signature_m d) mod 97 in
        tab_signature.(id t) <- res
    end;
    tab_signature.(id t)

let tab_dec = Array.make taille invalide          
let tab_x' = Array.make taille invalide

let rec dec_m t = 
    if tab_dec.(id t) = invalide then begin
        let res = match get_noeud t with
            | Zh -> failwith "dec 0"
            | Uh -> id_zero
            | Th (g, p, d) -> 
                if g <> id_zero then construit (dec_m g) p d
                else if d = id_un then x' p
                else construit (x' p) p (dec_m d) in
        tab_dec.(id t) <- res
    end;
    tab_dec.(id t)
and x' p = 
    if tab_x'.(id p) = invalide then begin
        let res = 
            if p = id_zero then id_un
            else 
                let q = dec_m p in
                let q' = x' q in
                construit q' q q' in
        tab_x'.(id p) <- res
    end;
    tab_x'.(id p)

let q13 () = 
    let f k = 
        let t = gen_m k (19 * k mod 997) in
        let s = signature_m (dec_m t) in
        printf "k = %d -> %d\n" k s in
    List.iter f [48; 55; 61];
    print_newline ()

let rec neg p = function
    | Z -> Z
    | U -> dec (N (Z, p, U))
    | N (Z, p', d') when p' = dec p -> N (Z, p', neg p' d')
    | N (g', p', d') when p' = dec p -> N (neg p' g', p', dec (neg p' d'))
    | N (g', p', d') as t -> N (Z, dec p, U) ++ neg p (N (Z, dec p, U) ++ t)

let rec mod_xp p = function
    | Z -> Z
    | U -> U
    | N (g, p', d) as t ->
        if compare p p' = 0 then g
        else if compare p p' = 1 then t
        else mod_xp p g
        
let (--) t t' = 
    match t, t' with 
    | _, Z -> t
    | Z, _ -> failwith "-- : t < t'"
    | _, U -> dec t
    | U, _ -> failwith "-- : t < t'"
    | N (g, p, d), _ ->
        let t'' = neg (inc p) t' in
        mod_xp (inc p) (t ++ t'')
        
let test_moins n p = 
    int_of_tri (tri_of_int n -- tri_of_int p)
    
let q14_naif k = 
    let t = gen (k + 2) (41 * k mod 997) in
    let t' = gen k (43 * k mod 997) in
    signature (t -- t')

let rec compare_m t t' = 
    if t = t' then 0
    else match get_noeud t, get_noeud t' with
    | Zh, _ -> -1
    | _, Zh -> 1
    | Uh, _ -> -1
    | _, Uh -> 1
    | Th (g, p, d), Th (g', p', d') ->
        let x = compare_m p p' in 
        if x < 0 then -1
        else if x > 0 then 1
        else let y = compare_m d d' in
            if y < 0 then -1
            else if y > 0 then 1
            else compare_m g g'
  
let tab_inc = Array.make taille invalide
let rec inc_m t = 
    if tab_inc.(id t) = invalide then begin
        let res = match get_noeud t with
            | Zh -> id_un
            | Uh -> construit id_zero id_zero id_un
            | Th (g, p, d) ->
                let g' = inc_m g in
                if g' <> construit id_zero p id_un then 
                    construit g' p d
                else
                    let d' = inc_m d in
                    if d' <> construit id_zero p id_un then
                        construit id_zero p d'
                    else
                        construit id_zero (inc_m p) id_un in
        tab_inc.(id t) <- res
    end;
    tab_inc.(id t)
                      
let tab_plus = Hashtbl.create taille                  
let rec (+++) t t' = 
    try 
        Hashtbl.find tab_plus (t, t')
    with
    | Not_found ->
        let res = match get_noeud t, get_noeud t' with
        | Zh, _  -> t'
        | _, Zh -> t
        | Uh, _ -> inc_m t'
        | _, Uh -> inc_m t
        | Th (g, p, d), Th (g', p', d') ->
            if p = p' then norm_m (g +++ g', p, d +++ d')
            else if compare_m p p' = 1 then norm_m (g +++ t', p, d)
            else norm_m (g' +++ t, p', d') in
        Hashtbl.add tab_plus (t, t') res;
        res
and norm_m (g, p, d) =
    match get_noeud g with
    | Th (gg, gp, gd) ->
        let x = compare_m gp p in
        if x = -1 then normd_m (g, p, d)
        else if x = 0 then normd_m (gg, p, gd +++ d)
        else norm_m (norm_m (gg, p, d), gp, gd)
    | _ -> normd_m (g, p, d)
and normd_m (g, p, d) = 
    match get_noeud d with
    | Th (dg, dp, dd) ->
        let x = compare_m dp p in
        if x = -1 then construit g p (construit dg dp dd)
        else if x = 0 then construit (normd_m (g, p, dg)) (inc_m p) dd
        else norm_m (normd_m (g, p, dg), dp, normd_m (id_zero, p, dd))
    | Zh -> g
    | Uh -> construit g p id_un               

let tab_neg = Hashtbl.create taille

let rec neg_m p t' = 
    try 
        Hashtbl.find tab_neg (p, t')
    with
    | Not_found ->
        let res = match get_noeud t' with
            | Zh -> id_zero
            | Uh -> dec_m (construit id_zero p id_un)
            | Th (g', p', d') when p' = dec_m p -> 
                if g' = id_zero then construit id_zero p' (neg_m p' d')
                else construit (neg_m p' g') p' (dec_m (neg_m p' d'))
            | _ -> 
                let x = construit id_zero (dec_m p) id_un in
                x +++ neg_m p (x +++ t') in
        Hashtbl.add tab_neg (p, t') res;
        res


let rec mod_xp_m p t = 
    match get_noeud t with
    | Zh -> id_zero
    | Uh -> id_un
    | Th (g', p', d') ->
        if p = p' then g'
        else if compare_m p p' < 0 then mod_xp_m p g'
        else t
    
let ( --- ) t t' = 
    match get_noeud t, get_noeud t' with
    | _, Zh -> t
    | Zh, _ -> failwith "-- : t < t'"
    | _, Uh -> dec_m t
    | Uh, _ -> failwith "-- : t < t'"
    | Th (g, p, d), _ -> 
        let t'' = neg_m (inc_m p) t' in
        mod_xp_m (inc_m p) (t +++ t'')
        
let rec int_of_tri_cons t = 
    match get_noeud t with
    | Zh -> 0
    | Uh -> 1
    | Th (g, p, d) ->
        let xg = int_of_tri_cons g in
        let xp = int_of_tri_cons p in
        let xd = int_of_tri_cons d in
        xg + (1 lsl (1 lsl xp)) * xd

let teste_plus_m a b =
    let t = tri_cons_of_int a in
    let t' = tri_cons_of_int b in
    int_of_tri_cons (t +++ t')

let teste_moins_m a b =
    let t = tri_cons_of_int a in
    let t' = tri_cons_of_int b in
    int_of_tri_cons (t --- t')
    
    
let q14 () = 
    let f k = 
        let t = gen_m (k + 2) ((41 * k) mod 997) in
        let t' = gen_m k ((43 * k) mod 997) in
        let s = signature_m (t --- t') in
        printf "Pour k = %d : %d\n" k s in
    List.iter f [2; 6; 8];
    print_newline ()
    
let () =
  let questions = [| q1; q2; q3; q4; q5; q6; q7; q8; q9;
                     q10; q11; q12; q13; q14 |] in
  Array.iteri
    (fun i f -> printf "Question %d\n" i; f (); print_newline ())
    questions

