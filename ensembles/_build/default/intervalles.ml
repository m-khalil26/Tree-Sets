(* Makhloufi Khalil, TP3 *)

module type TypeOrdonne = sig
  type t

  val comp : t -> t -> int
  val add_one : t -> t
  val to_string : t -> string
  val seed : t
  val random : t -> t
end

module EntierOrdreNaturel : TypeOrdonne with type t = int = struct
  type t = int

  let comp = compare
  let add_one t = t + 1
  let to_string t = Int.to_string t
  let seed = 100
  let random t = Random.int t
end

module Character : TypeOrdonne with type t = char = struct
  type t = char

  let add_one t = Char.chr (Char.code t + 1)
  let comp = compare
  let to_string t = Char.escaped t
  let seed = 'z'
  let random t = Char.chr (EntierOrdreNaturel.random (int_of_char t))
end

(*------------------------------signature du module -----------------------------*)

module type intervalles = sig
  type element
  type inter = Vide | Inter of element * bool * element * bool

  val inter : element -> bool -> element -> bool -> inter option
  val comp : inter -> inter -> int
  val est_dans_intervalle : element -> inter -> bool
  val sont_disjoints : inter -> inter -> bool
  val union : inter -> inter -> (inter * inter, inter) Either.t
  val difference : inter -> inter -> (inter * inter, inter) Either.t
  val est_valide_inter : unit -> unit
end

(*-----------------------------foncteur du module----------------------------- *)

module MakeIntervalles (O : TypeOrdonne) : intervalles with type element = O.t =
struct
  type element = O.t
  type inter = Vide | Inter of element * bool * element * bool

  let ( $=$ ) x y = O.comp x y = 0
  let ( $>$ ) x y = O.comp x y > 0
  let ( $<$ ) x y = O.comp x y < 0

  (* inter :
      renvoie un intervalle construit à partir des valeurs données
  *)
  let inter x x_b y y_b =
    if x $>$ y then None else Some (Inter (x, x_b, y, y_b))

  (* est_dans_intervalle:
     verifie si une valeur est dans un dans un intervalle donnés
  *)
  let est_dans_intervalle v inter =
    match inter with
    | Vide -> false
    | Inter (x, _, y, _) when v $>$ x && v $<$ y -> true
    | Inter (x, x_b, y, y_b) when (v $=$ x && x_b) || (v $=$ y && y_b) -> true
    | _ -> false

  (* comp :
     compare deux intervalles i1 et i2,
     renvoie 0 si i1=i2
             1 si i1>i2
            -1 si i1<i2
  *)
  let comp int1 int2 =
    match (int1, int2) with
    | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b')
      when x $<$ x'
           || (x $=$ x' && x_b' < x_b)
           || (x $=$ x' && x_b = x_b' && y $<$ y')
           || (x $=$ x' && x_b = x_b' && y $=$ y' && y_b < y_b') ->
        -1
    | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b')
      when x = x' && x_b = x_b' && y = y' && y_b = y_b' ->
        0
    | _ -> 1

  (* sont_disjoints:
     vérifie si deux intervalles sont disjoints
  *)

  let sont_disjoints int1 int2 =
    match (int1, int2) with
    | Inter (_, _, y, y_b), Inter (x', x_b', _, _)
      when y $<$ x'
           || y $=$ x'
              && (y_b < x_b' || y_b > x_b' || (y_b = false && x_b' = false)) ->
        true
    | Inter (x, x_b, _, _), Inter (_, _, y', y_b')
      when x $>$ y'
           || x $=$ y'
              && (x_b < y_b' || x_b > y_b' || (x_b = false && y_b' = false)) ->
        true
    | _ -> false

  (* est_inclus_dans i1 i2 :
     vérifie si un intervalle i2 est inclus dans un intervalle i1
  *)
  (*
  let est_inclus_dans int1 int2 =
    match (int1, int2) with
    | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b')
      when (est_dans_intervalle x' int1 && est_dans_intervalle y' int1)
           || est_dans_intervalle x' int1
              && y = y'
              && ((y_b != y_b' && y_b = true) || (y_b = y_b' && y_b = false))
           || est_dans_intervalle y' int1
              && x = x'
              && ((x_b != x_b' && x_b = true) || (x_b = x_b' && x_b = false))
           || y = y'
              && ((y_b != y_b' && y_b = true) || (y_b = y_b' && y_b = false))
              && x = x'
              && ((x_b != x_b' && x_b = true) || (x_b = x_b' && x_b = false)) ->
        true
    | _ -> false*)

  let est_inclus_dans int1 int2 =
    match int2 with
    | Inter (x, _, y, _)
      when est_dans_intervalle x int1 && est_dans_intervalle y int1 ->
        true
    | _ -> false

  (* union:
     calcule l'union de deux intervalles
  *)
  let union int1 int2 =
    if est_inclus_dans int1 int2 then Either.right int1
    else if est_inclus_dans int2 int1 then Either.right int2
    else
      match (int1, int2) with
      | int1, Vide -> Either.right int1
      | Vide, int2 -> Either.right int2
      | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b')
        when est_dans_intervalle x' int1
             || (not (est_dans_intervalle x' int1))
                && x' = O.add_one y
                && x_b' = y_b && y_b = true ->
          Either.right (Inter (x, x_b, y', y_b'))
      | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b')
        when est_dans_intervalle x int2
             || (not (est_dans_intervalle x int2))
                && x = O.add_one y'
                && x_b = y_b' && y_b' = true ->
          Either.right (Inter (x', x_b', y, y_b))
      | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b')
        when (y $=$ x' && y_b != x_b') || (y $=$ x' && y_b = x_b' && x_b' = true)
        ->
          Either.right (Inter (x, x_b, y', y_b'))
      | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b')
        when (y' $=$ x && y_b' != x_b) || (y' $=$ x && y_b' = x_b && x_b = true)
        ->
          Either.right (Inter (x', x_b', y, y_b))
      | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b')
        when sont_disjoints int1 int2 && x' >= y ->
          Either.left (Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b'))
      | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b') ->
          Either.left (Inter (x', x_b', y', y_b'), Inter (x, x_b, y, y_b))

  (* difference:
     calcule la difference d'un intervalle i1 et i2
  *)
  let difference int1 int2 =
    if sont_disjoints int1 int2 then Either.right int1
    else if est_inclus_dans int2 int1 then Either.right Vide
    else
      match (int1, int2) with
      | int1, Vide -> Either.right int1
      | Vide, int2 -> Either.right int2
      | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b')
        when est_inclus_dans int1 int1 && x = x' && x_b = x_b' && x_b = false ->
          Either.right (Inter (y', y_b', y, y_b))
      | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b')
        when (y $>$ x' || y $=$ x') && est_inclus_dans int1 int2 && x_b' && y_b'
        ->
          Either.left (Inter (x, x_b, x', false), Inter (y', false, y, y_b))
      | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b')
        when (y $>$ x' || y $=$ x')
             && est_inclus_dans int1 int2 && (not x_b') && not y_b' ->
          Either.left (Inter (x, x_b, x', true), Inter (y', true, y, y_b))
      | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b')
        when (y $>$ x' || y $=$ x')
             && est_inclus_dans int1 int2 && x_b' && not y_b' ->
          Either.left (Inter (x, x_b, x', false), Inter (y', true, y, y_b))
      | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b')
        when (y $>$ x' || y $=$ x')
             && est_inclus_dans int1 int2 && (not x_b') && y_b' ->
          Either.left (Inter (x, x_b, x', true), Inter (y', false, y, y_b))
      | Inter (x, _, y, y_b), Inter (x', x_b', _, _)
        when (y $>$ x' || y $=$ x') && (x $>$ x' || x $=$ x') && not x_b' ->
          Either.right (Inter (x', true, x', y_b))
      | Inter (x, _, y, y_b), Inter (x', x_b', _, _)
        when (y $>$ x' || y $=$ x') && (x' $>$ x || x' $=$ x) && not x_b' ->
          Either.right (Inter (x, true, x', y_b))
      | Inter (x, _, y, y_b), Inter (x', x_b', y', y_b')
        when (y $>$ x' || y $=$ x') && (x $>$ x' || x' $=$ x) && x_b' ->
          Either.right (Inter (y', y_b', y, y_b))
      | Inter (x, x_b, y, _), Inter (x', x_b', _, _)
        when (y $>$ x' || y $=$ x') && (x' $>$ x || x' $=$ x) && x_b' ->
          Either.right (Inter (x, x_b, x', false))
      | _ -> failwith ""

  (*------------------------------- fonctions outils pour verification ------------------------*)

  (* to_string_inter :
     renvoie un string representant  l'intervalle donné
  *)
  let to_string_inter inter =
    match inter with
    | Inter (x, x_b, y, y_b) ->
        O.to_string x ^ "," ^ Bool.to_string x_b ^ "," ^ O.to_string y ^ ","
        ^ Bool.to_string y_b
    | Vide -> "Vide"

  let to_string_either inter =
    if Either.find_left inter = None then
      let inter = Option.get (Either.find_right inter) in
      match inter with
      | Inter (x, x_b, y, y_b) ->
          O.to_string x ^ "," ^ Bool.to_string x_b ^ "," ^ O.to_string y ^ ","
          ^ Bool.to_string y_b
      | Vide -> "Vide"
    else
      let inter = Option.get (Either.find_left inter) in
      match inter with
      | Inter (x, x_b, y, y_b), Inter (x', x_b', y', y_b') ->
          O.to_string x ^ "," ^ Bool.to_string x_b ^ "," ^ O.to_string y ^ ","
          ^ Bool.to_string y_b ^ " union " ^ O.to_string x' ^ ","
          ^ Bool.to_string x_b' ^ "," ^ O.to_string y' ^ ","
          ^ Bool.to_string y_b'
      | _ -> "Vide" (*----------------- encore quelque cas ------------------*)

  (* est_inclus_dans_verif i3 i1 i2 :
     vérifie que toutes les valeurs de i1 et de i2 sont dans i3
  *)
  let est_inclus_dans_verif i3 i1 i2 =
    if Either.find_left i3 = None then
      let i = Option.get (Either.find_right i3) in
      est_inclus_dans i i1 && est_inclus_dans i i2
    else
      let i = Option.get (Either.find_left i3) in
      match i with
      | inter, inter' ->
          (est_inclus_dans inter i1 || est_inclus_dans inter' i1)
          && (est_inclus_dans inter i2 || est_inclus_dans inter' i2)

  (*difference_verification i4 i1 i2:
    vérifie que toutes les valeurs de i1 sont exclusivement soit dans i2, soit dans i4
  *)
  let difference_verification i4 i1 i2 =
    if Either.find_left i4 = None then
      let i = Option.get (Either.find_right i4) in
      est_inclus_dans i i1 || est_inclus_dans i2 i1
    else
      let i = Option.get (Either.find_left i4) in
      match (i, i1) with
      | (i, i'), Inter (x, _, y, _) ->
          est_inclus_dans i i1 || est_inclus_dans i' i1
          || (est_dans_intervalle x i && est_dans_intervalle y i')
      | _ -> failwith ""

  (* construction_valide :
     renvoie un intervalle valide
  *)
  let construction_valide x x_b y y_b =
    if x <= y then Option.get (inter x x_b y y_b)
    else Option.get (inter y y_b x x_b)

  (*--------------------------------fonction de verification -----------------------------*)

  let est_valide_inter () =
    let i1 =
      construction_valide (O.random O.seed) (Random.bool ()) (O.random O.seed)
        (Random.bool ())
    and i2 =
      construction_valide (O.random O.seed) (Random.bool ()) (O.random O.seed)
        (Random.bool ())
    in
    let i3 = union i1 i2 and i4 = difference i1 i2 in
    let union_correct = est_inclus_dans_verif i3 i1 i2
    and difference_correct = difference_verification i4 i1 i2 in
    Printf.printf
      "i1 = %s\n\
       i2 = %s\n\
       i3 = %s\n\
       i4 = %s\n\
       i1 et i2 sont dans i3 = %s\n\
       i1 est exclusivement dans i4 ou  dans i2 : %s\n"
      (to_string_inter i1) (to_string_inter i2) (to_string_either i3)
      (to_string_either i4)
      (Bool.to_string union_correct)
      (Bool.to_string difference_correct)
end
(*module M = MakeIntervalles( EntierOrdreNaturel )::
          M.est_valide_inter();;
*)

module M = MakeIntervalles (Character);;

M.est_valide_inter ()
