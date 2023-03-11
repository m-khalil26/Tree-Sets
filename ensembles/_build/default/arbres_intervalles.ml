(*  Makhloufi Khalil, TP3 *)

open Intervalles

(*-----*)
(*-----*)
(* -------------------------------------------------signature----------------------------------------------------- *)
(*-----*)
(*-----*)

module type arbresIntervalles = sig
  type element
  type ab
  type inter

  val est_dans_arbre_intervalle : element -> ab -> bool
  val ajout : inter -> ab -> ab
  val retrait : inter -> ab -> ab
  val valide_arbre_inter : unit -> unit
end

(*-----*)
(*-----*)
(* --------------------------------------------foncteur arbre binaire-------------------------------------------- *)
(*-----*)
(*-----*)

module MakeArbresIntervalles (O : TypeOrdonne) :
  arbresIntervalles with type element = O.t = struct
  module Intervalle = MakeIntervalles (O)

  type element = O.t
  type couleur = Rouge | Noir | DoubleNoir
  type ab = Vide | VideNoir | Noeud of (Intervalle.inter * couleur * ab * ab)
  type inter = Intervalle.inter

  exception Arbre_vide

  (* est_dans_arbre_interalle:
     verifie si un un element est dans l'arbre
  *)
  let est_dans_arbre_intervalle va tr =
    let rec aux va tr =
      match tr with
      | Vide | VideNoir -> false
      | Noeud (Intervalle.Inter (x, _, y, _), _, _, _)
        when Intervalle.est_dans_intervalle x va
             && Intervalle.est_dans_intervalle y va ->
          true
      | Noeud (v, _, ag, _) when Intervalle.comp va v == -1 -> aux va ag
      | Noeud (_, _, _, ad) -> aux va ad
    in
    aux (Option.get (Intervalle.inter va true va true)) tr

  (*--*)
  (*--*)
  (*-------------------------------fonctions outil pour insertion et suppression--------------------------------*)
  (*--*)
  (*--*)

  (* colorer_racineNoire :
     definis la couleur de la racine à Noir
  *)
  let colorer_racineNoire tr =
    match tr with
    | Vide -> Vide
    | Noeud (v, _, ag, ad) -> Noeud (v, Noir, ag, ad)
    | _ -> failwith "erreur"

  (*racineRouge:
    renvoie true si la racine d'un arbre donné en entrée  est Rouge false sinon
  *)
  let racineRouge tr =
    match tr with Noeud (_, Rouge, _, _) -> true | _ -> false

  (*a_un_fils_rouge:
    renvoie true si l'arbre donné en entrée a un fils Rouge
  *)
  let a_un_fils_rouge = function
    | Noeud (_, _, ag, ad) -> racineRouge ag || racineRouge ad
    | _ -> false

  (*rotationDroite:
    effectue une rotation droite sur l'arbre
  *)
  let rotationDroite tr =
    match tr with
    | Noeud (v, c, Noeud (vg, cg, agg, adg), ad) ->
        Noeud (vg, cg, agg, Noeud (v, c, adg, ad))
    | _ -> failwith " l'arbre ne supporte pas la rotation droite"

  (*rotationGauche:
     effectue une rotation gauche sur l'arbre
  *)
  let rotationGauche tr =
    match tr with
    | Noeud (v, c, ag, Noeud (vd, cd, agd, add)) ->
        Noeud (vd, cd, Noeud (v, c, ag, agd), add)
    | _ -> failwith " l'arbre ne supporte pas la rotation gauche"

  (*equilbrer :
    equilibre l'arbre donné en entrée
  *)
  let rec equilibrer = function
    | Noeud (g, Noir, ag, ad)
      when racineRouge ag && racineRouge ad
           && (a_un_fils_rouge ag || a_un_fils_rouge ad) ->
        Noeud (g, Rouge, colorer_racineNoire ag, colorer_racineNoire ad)
    | Noeud (g, Noir, Noeud (p, Rouge, agp, adp), ad) when racineRouge agp ->
        colorer_racineNoire
          (rotationDroite (Noeud (g, Rouge, Noeud (p, Rouge, agp, adp), ad)))
    | Noeud (g, Noir, Noeud (p, Rouge, agp, adp), ad) when racineRouge adp ->
        equilibrer
          (Noeud (g, Noir, rotationGauche (Noeud (p, Rouge, agp, adp)), ad))
    | Noeud (g, Noir, ag, Noeud (p, Rouge, agp, adp)) when racineRouge agp ->
        equilibrer
          (Noeud (g, Noir, ag, rotationDroite (Noeud (p, Rouge, agp, adp))))
    | Noeud (g, Noir, ag, Noeud (p, Rouge, agp, adp)) when racineRouge adp ->
        rotationGauche (Noeud (g, Rouge, ag, Noeud (p, Noir, agp, adp)))
    | a -> a

  (*inserer:
    insere une valeur dans un arbre donnés en entrée
  *)
  let inserer tr va =
    let rec aux tr va =
      match (tr, va) with
      | Noeud (v, _, _, _), va when Intervalle.comp v va = 0 -> tr
      | Vide, va -> Noeud (va, Rouge, Vide, Vide)
      | Noeud (v, c, ag, ad), va when Intervalle.comp v va = -1 ->
          equilibrer (Noeud (v, c, ag, aux ad va))
      | Noeud (v, c, ag, ad), va -> equilibrer (Noeud (v, c, aux ag va, ad))
      | _ -> failwith "erreur"
    in
    colorer_racineNoire (aux tr va)

  (*inserer_liste:
    inserer toute les valeurs d'une liste dans un arbre donnés en entée
  *)
  let inserer_liste tr l =
    let rec aux l acc =
      match l with [] -> acc | t :: q -> aux q (inserer acc t)
    in
    aux l tr

  (*supprimer_max:
    renvoie le max d'un arbre donné en entré
  *)
  let rec supprimer_max = function
    | Noeud (r, Rouge, Vide, Vide) -> (r, Vide)
    | Noeud (r, Noir, Noeud (r', Rouge, Vide, Vide), Vide) ->
        (r, Noeud (r', Noir, Vide, Vide))
    | Noeud (r, Noir, Vide, Vide) -> (r, VideNoir)
    | Noeud (r, c, ag, ad) ->
        let m, ad' = supprimer_max ad in
        (m, Noeud (r, c, ag, ad'))
    | _ -> failwith "erreur supprimermax"

  (*supprimer_racine
    renvoie l'arbre donné en entrée privé de sa racine
  *)
  let supprimer_racine = function
    | Noeud (_, Rouge, Vide, Vide) -> Vide
    | Noeud (_, Noir, Vide, Noeud (r', Rouge, Vide, Vide)) ->
        Noeud (r', Noir, Vide, Vide)
    | Noeud (_, Noir, Vide, Vide) -> VideNoir
    | Noeud (_, c, ag, ad) ->
        let m, ag' = supprimer_max ag in
        Noeud (m, c, ag', ad)
    | _ -> failwith "erreur supprimer racine"

  let estProblematique tr =
    match tr with Noeud (_, DoubleNoir, _, _) | VideNoir -> true | _ -> false

  (* noirSansFilsRouge:
     renvoie true si l'abre donné en entrée n'a pas d'enfant Rouge
  *)
  let noirSansFilsRouge tr =
    match tr with
    | Noeud
        (_, Noir, (Noeud (_, Noir, _, _) | Vide), (Noeud (_, Noir, _, _) | Vide))
      ->
        true
    | _ -> false

  (*diminuerCouleur :
    si le noeud est Noir ou Rouge change la couleur en Rouge
    si le noid est DoubleNoir change la couleur en Noir
    sinon renvoie Vide
  *)
  let diminuerCouleur tr =
    match tr with
    | Noeud (r, Noir, ag, ad) | Noeud (r, Rouge, ag, ad) ->
        Noeud (r, Rouge, ag, ad)
    | Noeud (r, DoubleNoir, ag, ad) -> Noeud (r, Noir, ag, ad)
    | VideNoir | Vide -> Vide

  (*augmenterCouleur:
     si c =  Noir ou DoubleNoir  renvoie DoubleNoir
    sinon renvoie Noir
  *)
  let augmenterCouleur c =
    match c with Noir | DoubleNoir -> DoubleNoir | Rouge -> Noir

  let eq_supp = function
    | Noeud (p, c, x, f)
      when (estProblematique x && noirSansFilsRouge f)
           || (estProblematique f && noirSansFilsRouge x) ->
        Noeud (p, augmenterCouleur c, diminuerCouleur x, diminuerCouleur f)
    | Noeud (p, c, x, Noeud (f, Noir, a3, Noeud (d, Rouge, a4, a5)))
      when estProblematique x ->
        Noeud
          (f, c, Noeud (p, Noir, diminuerCouleur x, a3), Noeud (d, Noir, a4, a5))
    | Noeud (p, c, x, Noeud (f, Noir, Noeud (g, Rouge, a3, a4), a5))
      when estProblematique x ->
        Noeud (p, c, x, Noeud (g, Noir, a3, Noeud (f, Rouge, a4, a5)))
    | Noeud (p, Noir, x, Noeud (f, Rouge, a3, a4)) when estProblematique x ->
        Noeud (f, Noir, Noeud (p, Rouge, x, a3), a4)
    | Noeud (p, c, Noeud (f, Noir, Noeud (g, Rouge, a4, a5), a3), x)
      when estProblematique x ->
        Noeud
          (f, c, Noeud (g, Noir, a4, a5), Noeud (p, Noir, a3, diminuerCouleur x))
    | Noeud (p, c, Noeud (f, _, a1, Noeud (d, Rouge, a2, a3)), x)
      when estProblematique x ->
        Noeud (p, c, Noeud (d, Noir, Noeud (f, Rouge, a1, a2), a3), x)
    | Noeud (p, Noir, Noeud (f, Rouge, a3, a4), x) when estProblematique x ->
        Noeud (f, Noir, a3, Noeud (p, Rouge, a4, x))
    | a -> a

  let stabiliser = function
    | Noeud (r, DoubleNoir, ag, ad) -> Noeud (r, Noir, ag, ad)
    | VideNoir -> Vide
    | a -> a

  (*supprimer :
    supprime d'un arbre une valeur donnée en entrée
  *)
  let supprimer inter tr =
    let rec aux = function
      | Vide -> Vide
      | Noeud (r, c, ag, ad) when Intervalle.comp inter r = -1 ->
          eq_supp (Noeud (r, c, aux ag, ad))
      | Noeud (r, c, ag, ad) when Intervalle.comp inter r = 1 ->
          eq_supp (Noeud (r, c, ag, aux ad))
      | tr -> supprimer_racine tr
    in
    stabiliser (aux tr)

  (* liste_non_disjoints:
     renvoie la liste d'intervalles de l'arbre non disjoints de l'intervalle
     donnés en entrée
  *)
  let liste_non_disjoints tr inter =
    let rec aux tr acc =
      match tr with
      | Vide | VideNoir -> acc
      | Noeud (v, _, ag, ad) when not (Intervalle.sont_disjoints v inter) ->
          aux ag (v :: acc) @ aux ad acc
      | Noeud (_, _, ag, ad) -> aux ag acc @ aux ad acc
    in
    aux tr []

  (*suppression_liste:
    supprime d'un arbre toutes les valeurs d'une liste donnée en entrée
  *)
  let suppression_liste tr l =
    let rec aux tr l =
      match l with [] -> tr | t :: q -> aux (supprimer t tr) q
    in
    aux tr l

  (*union_inter_liste :
    calcule l'union d'un intervalle avec tout les intervalles d'une liste
  *)
  let union_inter_liste inter l =
    let rec aux l acc =
      match l with
      | [] -> acc
      | t :: q when Either.find_left (Intervalle.union acc t) = None ->
          aux q (Option.get (Either.find_right (Intervalle.union acc t)))
      | _ -> failwith "n'est pas censé venir ici"
    in
    aux l inter

  (*difference_inter_liste :
    calcule la difference entre  tout les intervalles d'une liste et un intervalle donné en entrée
  *)
  let difference_inter_liste inter l =
    let rec aux l acc =
      match l with
      | [] -> acc
      | t :: q
        when Either.find_left (Intervalle.difference t inter) = None
             && Option.get (Either.find_right (Intervalle.difference t inter))
                = Intervalle.Vide ->
          aux q acc
      | t :: q when Either.find_left (Intervalle.difference t inter) = None ->
          aux q
            (Option.get (Either.find_right (Intervalle.difference t inter))
            :: acc)
      | t :: q ->
          let aux' =
            match
              Option.get (Either.find_left (Intervalle.difference t inter))
            with
            | int1, int2 -> [ int1; int2 ]
          in
          aux q aux' @ acc
    in
    aux l []

  (*racine :
    renvoie la racine d'un arbre donné en entrée
  *)
  let racine tr =
    match tr with
    | Vide | VideNoir -> raise Arbre_vide
    | Noeud (v, _, _, _) -> v

  (*--*)
  (*--*)
  (*----------------------fonctions d'ajouts et de suppression -------------------------*)
  (*--*)
  (*--*)

  (* ajout:
     ajoute un intervalle dans un arbre tout deux donnés en entée
  *)
  let ajout inter tr =
    let l_nonD = liste_non_disjoints tr inter in
    let tr_supp = suppression_liste tr l_nonD
    and union = union_inter_liste inter l_nonD in
    inserer tr_supp union

  (*retrait:
    supprime un intervalle d'un arbre tout deux donnés en entrée
  *)
  let retrait inter tr =
    let l_nonD = liste_non_disjoints tr inter in
    let tr_supp = suppression_liste tr l_nonD
    and difference = difference_inter_liste inter l_nonD in
    inserer_liste tr_supp difference

  (*--*)
  (*--*)
  (*---------------------fonctions outils pour verification -----------------------------*)
  (*--*)
  (*--*)

  (* inter_disjoint_arbre:
     verifie si un intervalle est disjoints de tout les intervalles d'un arbre
  *)
  let inter_disjoint_arbre inter tr =
    if liste_non_disjoints tr inter = [] then true else false

  (*inter_arbre_disjoints :
    verifie si tout les intervalles d'un arbre sont disjoints deux à deux
  *)

  let inter_arbre_disjoints tr =
    let rec aux tr acc =
      match tr with
      | Vide | VideNoir -> true
      | tr when not (inter_disjoint_arbre acc tr) -> false
      | _ -> aux (retrait (racine tr) tr) (racine tr)
    in
    aux (supprimer_racine tr) (racine tr)

  (*construction_valide:
    renvoie un intervalle bien construit
  *)
  let construction_valide x x_b y y_b =
    if x <= y then Option.get (Intervalle.inter x x_b y y_b)
    else Option.get (Intervalle.inter y y_b x x_b)

  (*random_inter_liste:
    renvoie une liste d'intervalles tirés aléatoirement
  *)
  let random_inter_liste () =
    let rec aux l compt =
      match compt with
      | 0 -> l
      | _ ->
          aux
            (construction_valide (O.random O.seed) (Random.bool ())
               (O.random O.seed) (Random.bool ())
            :: l)
            (compt - 1)
    in
    aux [] (Random.int 30)

  (* random_liste :
     renvoie une liste d'elements aléatoires
  *)
  let random_liste () =
    let rec aux l compt =
      match compt with 0 -> l | _ -> aux (O.random O.seed :: l) (compt - 1)
    in
    aux [] (Random.int 100)

  (*elem_est_dans_arbre:
    verifie si un élèment est présent dans un arbre
  *)
  let elem_est_dans_arbre tr e =
    let rec aux tr =
      match tr with
      | Vide | VideNoir -> false
      | Noeud (v, _, _, _) when Intervalle.est_dans_intervalle e v -> true
      | Noeud (Intervalle.Inter (x, _, _, _), _, ag, _) when O.comp e x = -1 ->
          aux ag
      | Noeud (_, _, _, ad) -> aux ad
    in
    aux tr

  (*verif_final:
    vérifie si chaque valeur de l est dans a’ si et seulement si elle est dans a mais pas dans i
  *)
  let verif_final a' a l i =
    let rec aux l =
      match l with
      | [] -> true
      | t :: q
        when (elem_est_dans_arbre a' t && elem_est_dans_arbre a t)
             || Intervalle.est_dans_intervalle t i
             || (not (elem_est_dans_arbre a t))
                && not (Intervalle.est_dans_intervalle t i) ->
          aux q
      | _ -> false
    in
    aux l

  (*to_string_inter:
    transforme un intervalle en string
  *)

  let to_string_inter inter =
    match inter with
    | Intervalle.Inter (x, x_b, y, y_b) ->
        O.to_string x ^ "," ^ Bool.to_string x_b ^ "," ^ O.to_string y ^ ","
        ^ Bool.to_string y_b
    | Intervalle.Vide -> "Vide"

  (*string_of_list:
    transforme une liste d'intervalles en string
  *)
  let string_of_list l =
    let rec aux l acc =
      match l with [] -> acc | t :: q -> aux q (acc ^ to_string_inter t ^ "\n")
    in
    aux l ""

  (*string_of_tree :
    transforme un arbre d'intervalles en string
  *)
  let string_of_tree tr =
    let rec aux tr acc =
      match tr with
      | Vide | VideNoir -> acc
      | Noeud (v, _, _, _) -> aux (retrait v tr) (acc ^ to_string_inter v ^ "\n")
    in
    aux tr ""

  (*--*)
  (*--*)
  (*---------------------------------fonction de verification--------- -------------------------*)
  (*--*)
  (*--*)

  let valide_arbre_inter () =
    let l = random_inter_liste () in
    let rec inserer' a l =
      match l with [] -> a | t :: q -> inserer' (ajout t a) q
    in
    let a = inserer' Vide l in
    let disjoints_2a2 = inter_arbre_disjoints a in
    let i' =
      construction_valide (O.random O.seed) (Random.bool ()) (O.random O.seed)
        (Random.bool ())
    in
    let a' = retrait i' a in
    let l_elem = random_liste () in
    let vf = verif_final a' a l_elem i' in
    Printf.printf
      "l =\n\
       %s\n\
       intervalles de a =\n\
       %s\n\
       les intervalles de a sont ils tous deux à deux disjoints ?  %b\n\
       i' = %s\n\
       a'=\n\
       %s\n\
       chaque valeur de l’ est dans a’ si et seulement si elle est dans a, \
       mais pas dans i’ : %b "
      (string_of_list l) (string_of_tree a) disjoints_2a2 (to_string_inter i')
      (string_of_tree a') vf
end
