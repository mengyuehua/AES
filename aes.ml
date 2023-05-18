
(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _::l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  match n with
  | O -> (match l with
          | [] -> default
          | x::_ -> x)
  | S m -> (match l with
            | [] -> default
            | _::t -> nth m t default)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x::l' -> app (rev l') (x::[])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t -> (f a)::(map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b::t -> fold_left f t (f a0 b)

(** val bool_to_nat : bool -> nat **)

let bool_to_nat = function
| true -> S O
| false -> O

(** val sftl : nat -> nat **)

let rec sftl = function
| O -> S O
| S n0 -> let m = sftl n0 in mul (S (S O)) m

(** val div2 : nat -> nat **)

let rec div2 = function
| O -> O
| S n0 -> (match n0 with
           | O -> O
           | S n1 -> S (div2 n1))

(** val rem2 : nat -> bool **)

let rec rem2 = function
| O -> false
| S n0 -> (match n0 with
           | O -> true
           | S i -> rem2 i)

(** val natlist2nat : bool list -> nat **)

let rec natlist2nat = function
| [] -> O
| hd::tl -> add (mul (bool_to_nat hd) (sftl (length tl))) (natlist2nat tl)

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
  | O -> m
  | S n' -> (match m with
             | O -> n
             | S m' -> add (S O) (max n' m'))

(** val less_than : nat -> nat -> bool **)

let rec less_than a b =
  match a with
  | O -> true
  | S a' -> (match b with
             | O -> false
             | S b' -> less_than a' b')

(** val less : nat -> nat -> bool **)

let less a b =
  negb (less_than b a)

(** val nateq : nat -> nat -> bool **)

let nateq a b =
  if less_than a b then less_than b a else false

(** val is_zero : nat -> bool **)

let is_zero = function
| O -> true
| S _ -> false

(** val div' : nat -> nat -> nat -> nat -> nat **)

let rec div' c m n r =
  match c with
  | O -> r
  | S c' -> if less_than m O then r else div' c' (sub m n) n (add r (S O))

(** val div : nat -> nat -> nat **)

let div m n =
  div' m m n O

(** val mod' : nat -> nat -> nat -> nat **)

let rec mod' c m n =
  match c with
  | O -> m
  | S c' -> if less m n then m else mod' c' (sub m n) n

(** val mod0 : nat -> nat -> nat **)

let mod0 m n =
  mod' m m n

(** val nat_to_bool : nat -> bool **)

let nat_to_bool = function
| O -> false
| S _ -> true

(** val back_cons : 'a1 list -> 'a1 -> 'a1 list **)

let back_cons xs a =
  app xs (a::[])

(** val list_combine : 'a1 list -> 'a1 list list -> 'a1 list list **)

let rec list_combine l1 l2 =
  match l1 with
  | [] -> l2
  | a::l1' ->
    (match l2 with
     | [] -> l2
     | b::l2' -> (a::b)::(list_combine l1' l2'))

(** val mk_list : 'a1 -> 'a1 list **)

let mk_list a =
  a::[]

(** val mk_natlist' : nat -> nat list -> nat list **)

let rec mk_natlist' n r =
  match n with
  | O -> O::r
  | S n' -> mk_natlist' n' (n::r)

(** val mk_natlist : nat -> nat list **)

let mk_natlist n =
  mk_natlist' n []

(** val map2 : ('a1 -> 'a2 -> 'a1) -> 'a1 list -> 'a2 list -> 'a1 list **)

let rec map2 f l1 l2 =
  match l1 with
  | [] -> []
  | h1::tl1 ->
    (match l2 with
     | [] -> []
     | h2::tl2 -> (f h1 h2)::(map2 f tl1 tl2))

(** val alltrue : bool list -> bool **)

let rec alltrue = function
| [] -> true
| b::tl -> if b then alltrue tl else false

(** val ite : ('a1 -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1 -> 'a1 **)

let rec ite f a i init =
  match i with
  | O -> init
  | S i' -> ite f a i' (f a init)

type z2 = bool

type poly = z2 list

type vec = poly list

type matrix = poly list list

(** val z2_add : z2 -> z2 -> z2 **)

let z2_add =
  xorb

(** val rij_add : poly -> poly -> poly **)

let rij_add p q =
  map2 z2_add p q

(** val vec_add : vec -> vec -> vec **)

let vec_add p q =
  map2 rij_add p q

(** val matrix_add : matrix -> matrix -> matrix **)

let matrix_add p q =
  map2 vec_add p q

(** val reqb : poly -> poly -> poly **)

let reqb a b =
  map2 eqb a b

(** val req : poly -> poly -> bool **)

let req a b =
  alltrue (reqb a b)

(** val false_list : nat -> poly **)

let rec false_list = function
| O -> []
| S n' -> false::(false_list n')

(** val fix_shift_left : bool list -> bool list **)

let fix_shift_left = function
| [] -> []
| _::tl -> app tl (false::[])

(** val fix_shift_right : bool list -> bool list **)

let fix_shift_right l =
  rev (fix_shift_left (rev l))

(** val nat2poly' : nat -> nat -> poly -> poly **)

let rec nat2poly' n i p =
  match n with
  | O -> p
  | S n' ->
    (match i with
     | O -> p
     | S _ -> let q = div2 i in let r = rem2 i in nat2poly' n' q (r::p))

(** val nat2poly : nat -> poly **)

let nat2poly i =
  nat2poly' i i []

(** val nat2polyi : nat -> nat -> poly **)

let nat2polyi n i =
  let p = nat2poly n in let l = length p in app (false_list (sub i l)) p

(** val nat2poly8 : nat -> poly **)

let nat2poly8 n =
  nat2polyi n (S (S (S (S (S (S (S (S O))))))))

(** val poly2nat : bool list -> nat **)

let poly2nat =
  natlist2nat

(** val n2p : nat -> poly **)

let n2p =
  nat2poly8

(** val p2n : bool list -> nat **)

let p2n =
  poly2nat

type bvec = bool list

(** val ith : nat -> bvec -> bool **)

let rec ith i a =
  match i with
  | O -> (match a with
          | [] -> false
          | hd::_ -> hd)
  | S i' -> (match a with
             | [] -> false
             | _::tl -> ith i' tl)

(** val getbit : nat -> bvec -> bool **)

let getbit i a =
  ith i (rev a)

(** val transpose : 'a1 list list -> 'a1 list list **)

let rec transpose = function
| [] -> []
| a::l' ->
  (match l' with
   | [] -> map mk_list a
   | _::_ -> list_combine a (transpose l'))

(** val drop : nat -> 'a1 list -> 'a1 list **)

let rec drop n l =
  match n with
  | O -> l
  | S n' -> (match l with
             | [] -> l
             | _::tl -> drop n' tl)

(** val tail : 'a1 list -> 'a1 list **)

let tail l =
  drop (S O) l

(** val take : nat -> 'a1 list -> 'a1 list **)

let rec take n l =
  match n with
  | O -> []
  | S n' -> (match l with
             | [] -> []
             | hd::tl -> hd::(take n' tl))

(** val range : nat -> nat -> 'a1 list -> 'a1 list **)

let range i j l =
  take (add (sub j i) (S O)) (drop i l)

(** val rotate_left : 'a1 list -> 'a1 list **)

let rotate_left = function
| [] -> []
| hd::tl -> app tl (hd::[])

(** val rotate_lefti : 'a1 list -> nat -> 'a1 list **)

let rec rotate_lefti l = function
| O -> l
| S i' -> rotate_lefti (rotate_left l) i'

(** val rotate_right : 'a1 list -> 'a1 list **)

let rotate_right l =
  rev (rotate_left (rev l))

(** val rotate_righti : 'a1 list -> nat -> 'a1 list **)

let rotate_righti l i =
  rev (rotate_lefti (rev l) i)

(** val lth : nat -> 'a1 list list -> 'a1 list **)

let lth n l =
  nth n l []

(** val width : 'a1 list -> nat **)

let width =
  length

(** val rij_0 : poly **)

let rij_0 =
  false::(false::(false::(false::(false::(false::(false::(false::[])))))))

(** val rij_1 : poly **)

let rij_1 =
  false::(false::(false::(false::(false::(false::(false::(true::[])))))))

(** val rij_irreducible : bool list **)

let rij_irreducible =
  false::(false::(false::(true::(true::(false::(true::(true::[])))))))

(** val rij_m' : nat -> poly -> poly -> poly -> poly **)

let rec rij_m' n a b r =
  match n with
  | O -> r
  | S n' ->
    let b0 = getbit O b in
    let r' = if b0 then rij_add r a else r in
    let an = getbit (S (S (S (S (S (S (S O))))))) a in
    let a' = fix_shift_left a in
    let a'' = if an then rij_add a' rij_irreducible else a' in
    let b' = fix_shift_right b in rij_m' n' a'' b' r'

(** val rij_mul : poly -> poly -> poly **)

let rij_mul a b =
  rij_m' (S (S (S (S (S (S (S (S O)))))))) a b rij_0

(** val gtimes : poly -> poly -> poly **)

let gtimes =
  rij_mul

(** val decompose' :
    'a1 list -> nat -> 'a1 list -> ('a1 list, 'a1 list) prod **)

let rec decompose' xs m r =
  match m with
  | O -> Pair ((rev r), xs)
  | S m' ->
    (match xs with
     | [] -> Pair ((rev r), xs)
     | hd::tl -> decompose' tl m' (hd::r))

(** val decompose : 'a1 list -> nat -> ('a1 list, 'a1 list) prod **)

let decompose xs m =
  decompose' xs m []

(** val split' : 'a1 list -> nat -> nat -> 'a1 list list -> 'a1 list list **)

let rec split' xs n m r =
  match n with
  | O -> r
  | S n' ->
    let Pair (r1, r2) = decompose xs m in split' r2 n' m (back_cons r r1)

(** val split : 'a1 list -> nat -> 'a1 list list **)

let split xs n =
  let l = length xs in let m = div l n in split' xs n m []

(** val join : 'a1 list list -> 'a1 list **)

let rec join = function
| [] -> []
| hd::tl -> app hd (join tl)

(** val gpower : poly -> nat -> poly **)

let gpower x i =
  ite gtimes x i rij_1

(** val inverse_n : poly -> nat -> poly **)

let rec inverse_n x n = match n with
| O -> rij_0
| S n' ->
  let y = n2p n in if req (gtimes x y) rij_1 then y else inverse_n x n'

(** val inverse : poly -> poly **)

let inverse x =
  inverse_n x (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val gsum : vec -> poly **)

let gsum xs =
  fold_left rij_add xs rij_0

(** val dot : vec -> vec -> poly **)

let dot xs ys =
  gsum (map2 gtimes xs ys)

(** val mmult : matrix -> matrix -> matrix **)

let mmult xss yss =
  let yss' = transpose yss in
  let mkrow = fun xs -> let dot_xs = fun ys -> dot ys xs in map dot_xs yss' in
  map mkrow xss

(** val parity : poly -> bool **)

let parity xs =
  fold_left xorb xs false

(** val dotBit : poly -> poly -> bool **)

let dotBit a b =
  parity (map2 (fun b1 b2 -> if b1 then b2 else false) a b)

(** val mmultBit : vec -> vec -> vec **)

let mmultBit xss yss =
  let yss' = transpose yss in
  let mkrow = fun xs -> let dot_xs = fun ys -> dotBit ys xs in map dot_xs yss'
  in
  map mkrow xss

(** val rij_8f : bool list **)

let rij_8f =
  map nat_to_bool ((S O)::(O::(O::(O::((S O)::((S O)::((S O)::((S
    O)::[]))))))))

(** val rij_65 : bool list **)

let rij_65 =
  map nat_to_bool (O::(O::((S O)::(O::(O::((S O)::(O::((S O)::[]))))))))

(** val affMat' : nat -> poly -> vec -> vec **)

let rec affMat' n a r =
  match n with
  | O -> r
  | S n' -> let a' = rotate_right a in affMat' n' a' (a::r)

(** val affMat : vec **)

let affMat =
  rev (affMat' (S (S (S (S (S (S (S (S O)))))))) rij_8f [])

(** val inv_affMat : vec **)

let inv_affMat =
  rev (affMat' (S (S (S (S (S (S (S (S O)))))))) rij_65 [])

(** val rij_63 : poly **)

let rij_63 =
  n2p
    (add
      (mul (S (S (S (S (S (S O)))))) (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S O))))))))))))))))) (S (S (S O))))

(** val rij_05 : poly **)

let rij_05 =
  n2p (S (S (S (S (S O)))))

(** val rev_rij_63 : z2 list **)

let rev_rij_63 =
  rev rij_63

(** val rev_rij_05 : z2 list **)

let rev_rij_05 =
  rev rij_05

(** val affine : poly -> poly **)

let affine xs =
  rev
    (rij_add
      (join (mmultBit affMat (split xs (S (S (S (S (S (S (S (S O)))))))))))
      rev_rij_63)

(** val inv_affine : poly -> poly **)

let inv_affine xs =
  rev
    (rij_add
      (join
        (mmultBit inv_affMat (split xs (S (S (S (S (S (S (S (S O)))))))))))
      rev_rij_05)

(** val sbox : vec **)

let sbox =
  map (fun x -> affine (rev (inverse x)))
    (map n2p
      (mk_natlist (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val inv_sbox : vec **)

let inv_sbox =
  map (fun x -> inverse (inv_affine (rev x)))
    (map n2p
      (mk_natlist (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val nb : nat **)

let nb =
  S (S (S (S O)))

(** val nk : nat **)

let nk =
  S (S (S (S O)))

(** val nr : nat **)

let nr =
  add (max nb nk) (S (S (S (S (S (S O))))))

(** val rcon : nat -> poly list **)

let rcon i =
  (gpower (n2p (S (S O))) (sub i (S O)))::(rij_0::(rij_0::(rij_0::[])))

(** val sbox_ith : nat -> poly **)

let sbox_ith i =
  nth i sbox rij_0

(** val sbox_sel : poly -> poly **)

let sbox_sel p =
  sbox_ith (p2n p)

(** val subByte : poly list -> poly list **)

let subByte block =
  map sbox_sel block

(** val inv_sbox_ith : nat -> poly **)

let inv_sbox_ith i =
  nth i inv_sbox rij_0

(** val inv_sbox_sel : poly -> poly **)

let inv_sbox_sel p =
  inv_sbox_ith (p2n p)

(** val stripe : vec -> matrix **)

let stripe block =
  transpose (split block (S (S (S (S O)))))

(** val unstripe : matrix -> vec **)

let unstripe state =
  join (transpose state)

(** val nextWord : poly -> vec -> vec -> vec **)

let nextWord i old prev =
  let n = p2n i in
  let prev' =
    if is_zero (mod0 n nk)
    then vec_add (subByte (rotate_left prev)) (rcon (div n nk))
    else if if less (S (S (S (S (S (S O)))))) nk
            then nateq (mod0 n nk) (S (S (S (S O))))
            else false
         then subByte prev
         else prev
  in
  vec_add old prev'

(** val kEw : nat -> nat -> matrix -> matrix -> matrix **)

let rec kEw k total w wa =
  match k with
  | O -> wa
  | S k' ->
    (match w with
     | [] -> wa
     | hd::l ->
       (match drop (sub nk (S O)) (hd::l) with
        | [] -> wa
        | hd'::_ ->
          let n = sub total k in
          let i = add nk n in
          let next = nextWord (n2p i) hd hd' in
          let w' = back_cons (tail w) next in
          let wa' = back_cons wa next in kEw k' total w' wa'))

(** val keyExpansion : vec -> matrix **)

let keyExpansion key =
  let keyCols = split key (S (S (S (S O)))) in
  let total = add (sub (sub (mul (add nr (S O)) nb) (S O)) nk) (S O) in
  kEw total total keyCols keyCols

(** val keyExpansion_split : vec -> matrix list **)

let keyExpansion_split key =
  let w = keyExpansion key in split w (add nr (S O))

(** val keyExpansion_split_matrix : matrix list -> matrix list **)

let rec keyExpansion_split_matrix = function
| [] -> []
| k::ks -> (stripe (join k))::(keyExpansion_split_matrix ks)

(** val keySchedule : vec -> ((matrix, matrix list) prod, matrix) prod **)

let keySchedule key =
  let w = keyExpansion_split key in
  let rKeys = keyExpansion_split_matrix w in
  Pair ((Pair ((lth O rKeys), (range (S O) (sub nr (S O)) rKeys))),
  (lth nr rKeys))

(** val mk_cols' : nat -> vec -> matrix -> matrix **)

let rec mk_cols' n coeff r =
  match n with
  | O -> rev r
  | S n' -> mk_cols' n' (rotate_right coeff) (coeff::r)

(** val mk_cols : vec -> matrix **)

let mk_cols coeff =
  mk_cols' (width coeff) coeff []

(** val polyMat : vec -> matrix **)

let polyMat coeff =
  transpose (mk_cols coeff)

(** val wiki_mat_start : poly list **)

let wiki_mat_start =
  map n2p ((S (S O))::((S (S (S O)))::((S O)::((S O)::[]))))

(** val wiki_invmat_start : poly list **)

let wiki_invmat_start =
  map n2p ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))::((S (S
    (S (S (S (S (S (S (S (S (S O)))))))))))::((S (S (S (S (S (S (S (S (S (S
    (S (S (S O)))))))))))))::((S (S (S (S (S (S (S (S (S O)))))))))::[]))))

(** val mat_start : poly list **)

let mat_start =
  wiki_mat_start

(** val invmat_start : poly list **)

let invmat_start =
  wiki_invmat_start

(** val cx : matrix **)

let cx =
  transpose (polyMat mat_start)

(** val icx : matrix **)

let icx =
  transpose (polyMat invmat_start)

(** val multCol : matrix -> vec -> vec **)

let multCol cx0 col =
  join (mmult cx0 (split col (S (S (S (S O))))))

(** val mixColumn : matrix -> matrix **)

let mixColumn state =
  transpose (map (fun col -> multCol cx col) (transpose state))

(** val invMixColumn : matrix -> matrix **)

let invMixColumn state =
  transpose (map (fun col -> multCol icx col) (transpose state))

(** val rol : poly list -> nat -> poly list **)

let rol =
  rotate_lefti

(** val ror : poly list -> nat -> poly list **)

let ror =
  rotate_righti

(** val shiftRow : matrix -> matrix **)

let shiftRow state =
  map2 rol state (O::((S O)::((S (S O))::((S (S (S O)))::[]))))

(** val invShiftRow : matrix -> matrix **)

let invShiftRow state =
  map2 ror state (O::((S O)::((S (S O))::((S (S (S O)))::[]))))

(** val byteSub : matrix -> matrix **)

let byteSub state =
  map (fun row -> map sbox_sel row) state

(** val invByteSub : matrix -> matrix **)

let invByteSub state =
  map (fun row -> map inv_sbox_sel row) state

(** val round : matrix -> matrix -> matrix **)

let round state roundKey =
  let state1 = byteSub state in
  let state2 = shiftRow state1 in
  let state3 = mixColumn state2 in matrix_add state3 roundKey

(** val finalRound : matrix -> matrix -> matrix **)

let finalRound state roundKey =
  let state1 = byteSub state in
  let state2 = shiftRow state1 in matrix_add state2 roundKey

(** val mk_rnds : matrix -> matrix list -> matrix **)

let rec mk_rnds state = function
| [] -> state
| key::tl -> mk_rnds (round state key) tl

(** val rounds :
    matrix -> ((matrix, matrix list) prod, matrix) prod -> matrix **)

let rounds state = function
| Pair (p, finalKey) ->
  let Pair (initialKey, rndKeys) = p in
  let istate = matrix_add state initialKey in
  let last_rnd = mk_rnds istate rndKeys in finalRound last_rnd finalKey

(** val inv_Round : matrix -> matrix -> matrix **)

let inv_Round state roundKey =
  let state1 = invShiftRow state in
  let state2 = invByteSub state1 in
  let state3 = matrix_add state2 roundKey in invMixColumn state3

(** val invFinalRound : matrix -> matrix -> matrix **)

let invFinalRound state roundKey =
  let state1 = invShiftRow state in
  let state2 = invByteSub state1 in matrix_add state2 roundKey

(** val mk_inv_rnds : matrix -> matrix list -> matrix **)

let rec mk_inv_rnds state = function
| [] -> state
| key::tl -> mk_inv_rnds (inv_Round state key) tl

(** val inv_rounds :
    matrix -> ((matrix, matrix list) prod, matrix) prod -> matrix **)

let inv_rounds state = function
| Pair (p, finalKey) ->
  let Pair (initialKey, rndKeys) = p in
  let istate = matrix_add state finalKey in
  let last_rnd = mk_inv_rnds istate (rev rndKeys) in
  invFinalRound last_rnd initialKey

(** val encrypt : vec -> vec -> vec **)

let encrypt key pt =
  let state = stripe pt in
  let keys = keySchedule key in unstripe (rounds state keys)

(** val decrypt : vec -> vec -> vec **)

let decrypt key pt =
  let state = stripe pt in
  let keys = keySchedule key in unstripe (inv_rounds state keys)

(** val aes_main : vec -> vec -> vec **)

let aes_main key pt =
  decrypt key (encrypt key pt)
