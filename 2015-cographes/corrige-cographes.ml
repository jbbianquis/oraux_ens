
open Printf

let u0_test = 42
let u0_perso = 69                

let m = 1_048_573
         
let tab_u u0 =
  let t = Array.make 10_000_000 u0 in
  for i = 1 to Array.length t - 1 do
    t.(i) <- (1022 * t.(i - 1)) mod m
  done;
  t

let t_test = tab_u u0_test
let t_perso = tab_u u0_perso                   

let test = ref true
                    
let u i = if !test then t_test.(i) else t_perso.(i)

let affiche_u0 () = printf "u_0 = %d\n" (u 0)  

let q1 () =
  affiche_u0 ();
  List.iter (fun n -> printf "u_%d = %d\n" n (u n))
            [10; 500; 10_000];
  print_newline ()

type coarbre = 
    | F
    | N of bool * coarbre * coarbre
    
let rec t n k = 
    if n = 1 then F
    else
        let i = 1 + u k mod (n - 1) in
        let ga = t i (k + 2) in
        let dr = t (n - i) (k + 2 * i) in
        let b = (u (k + 1) mod 2 = 1) in
        N (b, ga, dr)
        
let rec hauteur = function
    | F -> 0
    | N (_, ga, dr) -> 1 + max (hauteur ga) (hauteur dr)
    
let q2 () = 
    affiche_u0 ();
    printf "Question 2\n";
    List.iter 
        (fun (n, k) -> printf "hauteur(T_(%i, %i)) = %i\n" n k (hauteur (t n k)))
        [(10, 12); (500, 345); (5_000, 6_789)];
    print_newline ()

let rec nb_feuilles = function
    | F -> 1
    | N (_, g, d) -> nb_feuilles g + nb_feuilles d

let rec aretes = function
    | F -> 0
    | N (false, g, d) -> aretes g + aretes d
    | N (true, g, d) -> aretes g + aretes d + nb_feuilles g * nb_feuilles d
    
let rec d_max = function
    | F -> 0
    | N (false, g, d) -> max (d_max g) (d_max d)
    | N (true, g, d) -> max (d_max g + nb_feuilles d) (d_max d + nb_feuilles g)
    
let q3 () =
    affiche_u0 ();
    List.iter
        (fun (n, k) ->
            let g = t n k in
            printf "G(%d, %d) : aretes %d, degre max %d\n" 
                n k (aretes g) (d_max g)
        )
        [(10, 98); (500, 765); (2000, 4321)];
    print_newline ()

let rec omega = function
    | F -> 1
    | N (false, g, d) -> max (omega g) (omega d)
    | N (true, g, d) -> omega g + omega d
    
let q4 () =
    affiche_u0 ();
    List.iter 
        (fun (n, k) -> printf "omega(G(%d, %d)) = %d\n" n k (omega (t n k)))
        [(100, 314); (1000, 159); (10_000, 265)];
    print_newline ()
    
let omega_moyen n kmax =
    let rec aux k s = 
        if k > kmax then s 
        else aux (k + 1) (s + omega (t n k)) in
    float (aux 1 0) /. float kmax
    
let q5 () =
    affiche_u0 ();
    List.iter
        (fun n -> printf "moyenne n = %d : %.2f\n" n (omega_moyen n 1000))
        [100; 1_000; 10_000];
    print_newline ()

type naire = 
    | Fn
    | Nn of bool * naire list

let remonte b = function
    | Fn -> [Fn] 
    | Nn (b', fils) -> 
        if b' = b then fils 
        else [Nn (b', fils)]

let rec canonique = function
    | F -> Fn
    | N (b, g, d) -> Nn (b, remonte b (canonique g) @ remonte b (canonique d))

let somme = List.fold_left (+) 0

let rec nb_noeuds = function
    | Fn -> 1
    | Nn (_, fils) -> 1 + somme (List.map nb_noeuds fils)
    
let q6 () =
    affiche_u0 ();
    List.iter
        (fun (n, k) -> 
            let g = t n k in 
            printf "T'(%d, %d) : %d noeuds\n" n k (nb_noeuds (canonique g)))
        [(100, 271); (1000, 828); (10_000, 182)];
    print_newline ()
        

(* compare est la fonction de comparaison polymorphe prédéfinie 
    en Caml. *)
let rec tri = function
    | Fn -> Fn
    | Nn(b, fils) -> 
        let f = List.map tri fils in
        Nn(b, List.sort compare f)
        
let rec equiv t t' = (tri t = tri t')
    
let premier_equiv n =
    let cible = tri (canonique (t n 0)) in
    let rec aux k =
        let a = canonique (t n k) in
        if cible = tri a then k
        else aux (k + 1) in
    aux 1

let q7 () =
    affiche_u0 ();
    List.iter
        (fun n -> printf "pour G(%d, 0) : G(%d, %d)\n" n n (premier_equiv n))
        [8; 12; 15];
    print_newline ()

let nb_classes_equiv n kmax = 
    let rec ajoute x = function
        | [] -> [x]
        | y :: ys -> if (x = y) then y :: ys else y :: ajoute x ys in
    let rec classes k c = 
        if k > kmax then c
        else
            let x = tri (canonique (t n k)) in
            classes (k + 1) (ajoute x c) in
    List.length (classes 1 [])
    
let q8 () =
    affiche_u0 ();
    List.iter
        (fun n -> printf "nb classes pour (%d, k) : %d\n" 
            n (nb_classes_equiv n 10_000))
        [10; 15; 20];
    print_newline ()

let gprime n k =
    let g = Array.make_matrix n n false in
    for i = 0 to n - 1 do
        for j = 0 to n - 1 do
            if i <> j && u (min i j + 1 + u (k + max i j + 1)) mod 2 = 1 then
                g.(i).(j) <- true
        done
    done;
    g
  
let connexe g =
    let n = Array.length g in
    let vus = Array.make n false in
    let rec explore i =
        if not vus.(i) then begin
            vus.(i) <- true;
            for j = 0 to n - 1 do
                if g.(i).(j) then explore j
            done
        end in
    explore 0;
    Array.fold_left (&&) true vus 
  
let nb_non_connexes n kmax =
    let i = ref 0 in
    for k = 1 to kmax do
        if not (connexe (gprime n k)) then incr i
    done;
    !i

let q9 () =
    affiche_u0 ();
    List.iter
        (fun (n, kmax) -> printf "nb non connexes pour n = %d, k <= %d : %d\n" 
            n kmax (nb_non_connexes n kmax))
        [(4, 10_000); (6, 10_000); (8, 100_000); (10, 100_000)];
    print_newline ()
        

let gbar g =
  let n = Array.length g in
  Array.init n (fun i -> Array.init n (fun j -> i <> j && not g.(i).(j)))

(* La méthode choisie pour extraire les composantes connexes n'est sans 
   doute pas la meilleure, mais elle fait l'affaire. *)

(* Prend un graphe et une liste de numéros de sommets et renvoie
   le sous-graphe induit par ces sommets. *)             
let sous_graphe g sommets = 
    let t = Array.of_list sommets in
    let n = Array.length t in
    let g' = Array.make_matrix n n false in
    for i = 0 to n - 1 do
        for j = 0 to n - 1 do
            g'.(i).(j) <- g.(t.(i)).(t.(j))
        done
    done;
    g'
    

(* Renvoie la liste des composantes connexes (liste de listes). *)    
let composantes g =
    let n = Array.length g in
    let vus = Array.make n false in
    let rec ajoute i composante =
    if not vus.(i) then
        begin
            vus.(i) <- true;
            composante := i :: !composante;
            for j = 0 to n - 1 do
                if g.(i).(j) then ajoute j composante
            done
        end in
    let composantes = ref [] in
    for i = 0 to n - 1 do
        if not vus.(i) then begin
            let c = ref [] in
            ajoute i c;
            composantes := !c :: !composantes
        end
    done;
    !composantes

(* Renvoie les composantes connexes sous forme d'une liste de graphes. *)   
let graphes_composantes g =
  List.map (sous_graphe g) (composantes g)
   
let rec est_cographe g =
  if Array.length g = 1 then true
  else if not (connexe g) then
    let compos = composantes g in
    let sous_graphes =
      List.map (fun sommets -> sous_graphe g sommets) compos in
    List.fold_left (&&) true (List.map est_cographe sous_graphes)
  else
    let gb = gbar g in
    if connexe gb then false
    else est_cographe gb

let nb_cographes n kmax =
  let i = ref 0 in
  for k = 1 to kmax do
    if est_cographe (gprime n k) then incr i
  done;
  !i

let q10 () =
  affiche_u0 ();
  List.iter (fun (n, kmax) -> printf "Nb de cographes n = %d, k <= %d : %d\n"
                                     n kmax (nb_cographes n kmax))
            [(4, 10_000); (6, 10_000); (8, 100_000); (10, 100_000)];
  print_newline ()

let max3 a b c = max a (max b c)

let rec raccords_et_taille = function
    | F -> (1, 1)
    | N (b, g, d) ->
        let mg, ng = raccords_et_taille g in
        let md, nd = raccords_et_taille d in
        if b then 
            (max3 0 (mg - nd) (md - ng), ng + nd)
        else
            (max 1 mg + max 1 md, ng + nd)
            
let hamiltonien t = 
    let (raccords, _) = raccords_et_taille t in
    raccords = 0
    
let nb_hamiltoniens n kmax = 
    let nb = ref 0 in
    for k = 1 to kmax do
        if hamiltonien (t n k) then incr nb
    done;
    !nb
    
let q11 () = 
    affiche_u0 ();
    List.iter 
        (fun n -> printf "Hamiltoniens pour n = %d : %d\n"
            n (nb_hamiltoniens n 10_000))
        [10; 100; 1_000; 10_000];
    print_newline ()

let questions = [| q1; q2; q3; q4; q5; q6; q7; q8; q9; q10; q11 |]

let () =
  Array.iteri
    (fun i f -> printf "Question %d\n" i; f (); print_newline ())
    questions
