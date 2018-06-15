open Printf
let () = Printexc.record_backtrace true
       
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

(****************************)
(* Génération des co-arbres *)
(****************************)

(* Question 1 *)
                                               
let q1 () =
  affiche_u0 ();
  List.iter (fun n -> printf "u_%d = %d\n" n (u n))
            [10; 500; 10_000]

(* Question 2 *)
            
type coarbre = F | N of bool * coarbre list
        
let rec t n k =
  if n = 1 then F
  else
    let i = 1 + u k mod (n - 1) in
    let ga = (t i (k + 2)) in
    let dr = (t (n - i) (k + 2*i)) in
    N((u (k + 1) mod 2 = 1), [ga; dr])

    
let max_liste = List.fold_left max min_int
let somme_liste = List.fold_left (+) 0
    
let rec hauteur = function
  | F -> 0
  | N(_, fils) -> 1 + max_liste (List.map hauteur fils)

let q2 () =
  affiche_u0 ();
  List.iter 
    (fun (n, k) -> Printf.printf "hauteur(T_(%i, %i)) = %i\n"
                                 n k (hauteur (t n k)))
    [(10, 12); (500, 345); (5000, 6789)]
    
(** Pour l'oral **)

(* 
  Une induction structurelle immédiate montre que T_(n, k) a n feuilles, et 
  donc 2n - 1 noeuds (c'est un arbre binaire).
*)

                                
(* Cographe associé *)

(* On peut calculer explicitement le cographe, mais ce n'est pas nécessaire
  (c'est même sans doute contre-productif). *)                


let rec card = function
  | F -> 1
  | N(_, fils) -> 1 + somme_liste (List.map card fils)

let rec nb_feuilles = function
  | F -> 1
  | N(_, fils) -> somme_liste (List.map nb_feuilles fils)

(* On pourrait largement améliorer la complexité mais c'est inutile pour traiter
   les exemples demandés. *)
                              
let rec aretes = function
  | F -> 0
  | N(b, fils) ->
     let anciennes = somme_liste (List.map aretes fils) in
     let nb_f = List.map nb_feuilles fils in
     let nouvelles =
       if b then
         let rec f = function
           | [] -> 0
           | x :: xs -> f xs + x * somme_liste xs in
         f nb_f
       else 0 in
     anciennes + nouvelles
  
let rec degre_max = function
  | F -> 0
  | N(false, fils) -> max_liste (List.map degre_max fils)
  | N(true, fils) ->
     let nb_f = List.map nb_feuilles fils in
     let anciens = List.map degre_max fils in
     let s = somme_liste (List.map nb_feuilles fils) in
     let nouveaux =
       List.map2 (fun fe de -> de + s - fe) nb_f anciens in
     max_liste nouveaux

let q3 () =
  affiche_u0 ();
  List.iter
    (fun (n, k) ->
      let g = t n k in
      printf "G(%d, %d) : aretes %d, degre max %d\n"
             n k (aretes g) (degre_max g))
    [(10, 98); (500, 765); (2000, 4321)]

(** Pour l'oral **)

(* On peut obtenir le nombre d'arêtes et le degré max sans calculer val(t), on 
   vient de le faire !
   Pour la complexité, en se limitant au cas des arbres binaires :
    - pour aretes, on a en notant n le nombre de noeuds
      f(n + 1) = f(i) + f(n - i) + Cn avec 1 <= i <= n - 1 (le Cn vient du 
      calcul de nb_feuilles et pourrait être évité).
      On reconnaît la récurrence associée au tri rapide, O(n^2) dans le pire 
      des cas.
    - pour degre_max : idem
   On pourrait le faire en temps linéaire.
 *)

(*********************************)
(* Algorithmes sur les cographes *)
(*********************************)
    
(* Cliques *)

(* Aucune difficulté ici, si l'on travaille bien sur les arbres. *)    
     
let rec omega = function
  | F -> 1
  | N(false, fils) -> max_liste (List.map omega fils)
  | N(true, fils) -> somme_liste (List.map omega fils)

let q4 () =
  affiche_u0 ();
  List.iter (fun (n, k) -> printf "omega(G(%d, %d)) = %d\n" n k (omega (t n k)))
            [(100, 314); (1000, 159); (10_000, 265)]
                               
                                 
let rec (<|>) a b =
  if a >= b then [] else a :: (a + 1 <|> b)
                   
let rec om_moyen n kmax =
  let s = somme_liste (List.map (fun k -> omega (t n k)) (1 <|> (kmax + 1))) in
  let foi = float_of_int in
  foi s /. foi kmax

let q5 () =
  affiche_u0 ();
  List.iter
    (fun n -> printf "moyenne n = %d : %.2f\n" n (om_moyen n 1000))
    [100; 1_000; 10_000]

(** Pour l'oral **)

(* omega fait un simple parcours de l'arbre, complexité linéaire.
   Pour faire la moyenne, on appelle omega sur kmax arbres de taille n,
   donc O(kmax * n). *)

(***********************************************************************)
(*  La plupart des candidats se sont arrêtés ici (12 sur 40 ont fait   *)
(*  la question 6, mais certains ont sans doute sauté la question 6    *)
(*  et réussi d'autres questions plus loin).                           *)
(*  On peut raisonnablement penser que traiter les questions de        *)
(*  programmation 1 à 5 avec ensuite une prestation convenable à       *)
(*  l'oral permettait d'obtenir une note autour de 10.                 *)
(***********************************************************************)
               
(* Forme canonique *)

(* Question 6 *)
    
(* Question très discriminante... *)
    
let rec remonte b = function
  | [] -> []
  | F :: xs -> F :: remonte b xs
  | N(b', fils) :: xs -> let u = remonte b xs in
                         if b = b' then fils @ u
                         else  N(b', fils) :: u
  
let rec canonique = function
  | F -> F
  | N(_, [x]) -> x
  | N(b, fils) -> N(b, remonte b (List.map canonique fils))

let q6 () =
  affiche_u0 ();
  List.iter
    (fun (n, k) -> printf "T'(%d, %d) : %d noeuds\n"
                          n k (card (canonique (t n k))))
    [(100, 271); (1000, 828); (10_000, 182)]

(* Question 7 *)

(** Pour l'oral (et pour comprendre le code **)

(* Une possibilité : 
   - une feuille est < à un N(_, _)
   - un N(false, _) est < à un N(true, _)
   - si |fils| < |fils'|, alors N(b, fils) < N(b, fils')
   - sinon (cas N(b, fils) / N(b', fils') avec b = b' et |fils| = |fils'|),
     on compare fils et fils' par ordre lexicographique (induit par l'ordre
     que l'on est en train de définir).
   L'ordre est bien défini (cela revient à dire que la fonction cmp termine
   et c'est clairement le cas).
   Noter que la séparation du cas |fils| < |fils'| est juste une optimisation
   qui n'est pas nécessaire (et qui ne sert même strictement à rien dans
   le cas des arbres binaires...).
 *)    

(* On pourrait faire plus efficace que ce qui suit (autant pour cmp que pour
   premier_equiv et nb_classes_equiv a priori), mais cela suffit pour traiter
   l'énoncé. La question 8 est quand même loin d'être instantanée ! *)
    
let rec lexi u v cmp =
  match u, v with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: xs, y :: ys when cmp x y < 0 -> -1
  | x :: xs, y :: ys when cmp x y > 0 -> 1
  | x :: xs, y :: ys -> lexi xs ys cmp
                
let rec cmp t t' =
  match t, t' with
  | F, F -> 0
  | F, _ -> -1
  | _, F -> 1
  | N(false, _), N(true, _) -> -1
  | N(true, _), N(false, _) -> 1
  | N(_, fils), N(_, fils') ->
     let n, n' = List.length fils, List.length fils' in
     if n < n' then -1
     else if n > n' then 1
     else 
       let tri = List.sort cmp in
       let f = tri fils in
       let f' = tri fils' in
       lexi f f' cmp
    
let rec equiv t t' =
  cmp t t' = 0               

let premier_equiv n =
  let cible = canonique (t n 0) in
  let rec aux k =
    if equiv cible (canonique (t n k)) then k
    else aux (k + 1) in
  aux 1

let q7 () =
  affiche_u0 ();
  List.iter
    (fun n -> printf "pour G(%d, 0) : G(%d, %d)\n" n n (premier_equiv n))
    [8; 12; 15]

(* Question 8 *)
    
let nb_classes_equiv n kmax =
  let rec ajoute x = function
    | [] -> [x]
    | y :: ys -> if equiv x y then y :: ys else y :: ajoute x ys in
  let rec classes k =
    if k > kmax then []
    else
      let c = classes (k + 1) in
      ajoute (canonique (t n k)) c in
  List.length (classes 1)

let q8 () =
  affiche_u0 ();
  List.iter
    (fun n -> printf "nb classes pour (%d, k) : %d\n"
                     n (nb_classes_equiv n 10_000))
    [10; 15; 20]
              
(* Reconnaissance des cographes *)

(* On symétrise le graphe, ce sera plus simple. *)
    
let gprime n k =
  let g = Array.make_matrix n n false in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if i <> j && u (min i j + 1 + u (k + max i j + 1)) mod 2 = 1 then
        g.(i).(j) <- true
    done
  done;
  g

(* Question 9 *)

(* C'est une question de cours, il faut absolument la traiter même si on n'a
   pas réussi les précédentes ! *)
  
let connexe g =
  let n = Array.length g in
  let vus = Array.make n false in
  let rec update i =
    if not vus.(i) then begin
        vus.(i) <- true;
        for j = 0 to n - 1 do
          if g.(i).(j) then update j
        done
      end in
  update 0;
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
    [(4, 10_000); (6, 10_000); (8, 100_000); (10, 100_000)]


(** Pour l'oral **)

(* 
  Un cographe dont la racine est étiquetée 0 est une union disjointe de 
  cographes plus petits (et n'est donc pas connexe).
  Un cographe dont la racine est étiquetée 1 est le complémentaire d'un
  cographe dont la racine est étiquetée 0 (obtenu en complémentant les 
  fils).

  Un algorithme possible est donc :
  - un graphe réduit à un sommet est un cographe ;
  - un graphe non connexe est un cographe ssi chacune de ses composantes
    connexes l'est ;
  - un graphe connexe est un cographe ssi son complémentaire n'est pas
    connexe et est un cographe.
*)
    
let gbar g =
  let n = Array.length g in
  Array.init n (fun i -> Array.init n (fun j -> i <> j && not g.(i).(j)))

(* La méthode choisie pour extraire les composantes connexes n'est sans 
   doute pas la meilleure, mais elle fait l'affaire. *)

(* Prend un graphe et une liste de numéros de sommets et renvoie
   le sous-graphe induit par ces sommets. *)             
let sous_graphe g sommets =
  let n = Array.length g in
  let n' = List.length sommets in
  let g' = Array.make_matrix n' n' false in
  let numeros = Array.make n (-1) in
  let rec numerote i = function
    | [] -> ()
    | x :: xs -> numeros.(x) <- i; numerote (i + 1) xs in
  numerote 0 sommets;
  let rec connexions = function
    | [] -> ()
    | x :: xs ->
       for j = 0 to n - 1 do
         if g.(x).(j) && numeros.(j) <> -1 then
           g'.(numeros.(x)).(numeros.(j)) <- true
       done;
       connexions xs in
  connexions sommets;
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
  List.map (fun sommets -> sous_graphe g sommets) (composantes g)
   
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
                 

(* Pour illustrer la construction du coarbre associé à un cographe, non 
   nécessaire pour la question 10. *)                      
exception Echec
                     
let rec coarbre g =
  if Array.length g = 1 then F
  else if not (connexe g) then
    let compos = graphes_composantes g in
    N (true, List.map coarbre compos)
  else
    let gb = gbar g in
    if connexe gb then raise Echec
    else
      let compos_gb = graphes_composantes gb in
      let compos = List.map gbar compos_gb in
      N (false, List.map coarbre compos)
    
        
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
            [(4, 10_000); (6, 10_000); (8, 100_000); (10, 100_000)]


(*******************************)
(* Bon, arrivé ici on a déjà   *)
(* largement 20, après c'est   *)
(* pour le plaisir...          *)
(*******************************)

(** Pour l'oral 8 **)

(* Je ne sais pas trop ce qu'on est censé conclure. Peut-être simplement
   que les cographes sont un sous-ensemble strict des graphes ?
   Pour le plus petit graphe qui n'est pas un cographe, il faut chercher
   le plus petit G tel que G et Gbar soient connexes. 
   La réponse est P4, le graphe chemin à 4 sommets : a - b - c - d.
*)

(** Pour l'oral 9 **)

(*
  Considérons le plus petit ancêtre commun aux 4 sommets de H. 
  - Si c'est un noeud 0, alors ses enfants correspondent aux composantes
    connexes de G : tous les sommets de H sont donc dans le même fils,
    absurde.
  - Si c'est un noeud 1, alors ses enfants correspondent aux composantes
    connexes de Gbar : de même, c'est absurde.

  Inversement, considérons un graphe qui n'est pas un cographe. Si l'on 
  essaie d'appliquer l'algorithme de construction de coarbre vu plus haut,
  on va donc échouer à un moment, c'est-à-dire tomber sur un graphe induit
  de G (notons le H) tel que H soit connexe et Hbar soit connexe.
  Considérons H' un sous-graphe induit minimal de H ayant la même propriété
  (autrement dit, H' et H'bar sont connexes mais ce n'est plus vrai si
  l'on enlève l'un des sommets de H').
  H' a au moins 4 sommets d'après la question précédente. 
  ... Je ne suis pas sûr de comment conclure ...
*) 

let rec nb_et_taille = function
  | F -> (1, 1)
  | N (false, u) ->
     List.fold_left
       (fun (acc_x, acc_y) (x, y) -> (max x 1 + acc_x, y + acc_y))
       (0, 0)
       (List.map nb_et_taille u)
  | N (true, u) ->
     let v = List.map nb_et_taille u in
     let taille_totale = somme_liste (List.map snd v) in
     let f (n, t) = n + t - taille_totale in
     (max_liste (List.map f v), taille_totale)
       
let compte_hami n kmax =
  let i = ref 0 in
  for k = 1 to kmax do
    let arbre = t n k in
    match arbre with
    | N (true, _) -> let (n, _) = nb_et_taille arbre in
                     if n <= 0 then incr i
    | _ -> ()
  done;
  !i
    
let q11 () =
  affiche_u0 ();
  List.iter (fun n -> printf "Hamiltoniens pour n = %d : %d\n"
                             n (compte_hami n 10_000))
            [10; 100; 1000; 10000]

(** Pour l'oral 10 **)

(* La complexité est clairement linéaire en la taille du graphe (c'est juste un
   parcours de l'arbre).
   Pour comment ça marche, je vous laisse réfléchir (c'est plus simple si l'on
   se limite aux arbres binaires comme le permettait l'énoncé).
*)           

let affiche_tout () =
  Array.iteri (fun i f -> printf "Question %d\n" i; f (); print_newline ())
              [|q1; q2; q3; q4; q5; q6; q7; q8; q9; q10; q11|]
