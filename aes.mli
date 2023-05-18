
val xorb : bool -> bool -> bool

val negb : bool -> bool

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

val eqb : bool -> bool -> bool

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val bool_to_nat : bool -> nat

val sftl : nat -> nat

val div2 : nat -> nat

val rem2 : nat -> bool

val natlist2nat : bool list -> nat

val max : nat -> nat -> nat

val less_than : nat -> nat -> bool

val less : nat -> nat -> bool

val nateq : nat -> nat -> bool

val is_zero : nat -> bool

val div' : nat -> nat -> nat -> nat -> nat

val div : nat -> nat -> nat

val mod' : nat -> nat -> nat -> nat

val mod0 : nat -> nat -> nat

val nat_to_bool : nat -> bool

val back_cons : 'a1 list -> 'a1 -> 'a1 list

val list_combine : 'a1 list -> 'a1 list list -> 'a1 list list

val mk_list : 'a1 -> 'a1 list

val mk_natlist' : nat -> nat list -> nat list

val mk_natlist : nat -> nat list

val map2 : ('a1 -> 'a2 -> 'a1) -> 'a1 list -> 'a2 list -> 'a1 list

val alltrue : bool list -> bool

val ite : ('a1 -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1 -> 'a1

type z2 = bool

type poly = z2 list

type vec = poly list

type matrix = poly list list

val z2_add : z2 -> z2 -> z2

val rij_add : poly -> poly -> poly

val vec_add : vec -> vec -> vec

val matrix_add : matrix -> matrix -> matrix

val reqb : poly -> poly -> poly

val req : poly -> poly -> bool

val false_list : nat -> poly

val fix_shift_left : bool list -> bool list

val fix_shift_right : bool list -> bool list

val nat2poly' : nat -> nat -> poly -> poly

val nat2poly : nat -> poly

val nat2polyi : nat -> nat -> poly

val nat2poly8 : nat -> poly

val poly2nat : bool list -> nat

val n2p : nat -> poly

val p2n : bool list -> nat

type bvec = bool list

val ith : nat -> bvec -> bool

val getbit : nat -> bvec -> bool

val transpose : 'a1 list list -> 'a1 list list

val drop : nat -> 'a1 list -> 'a1 list

val tail : 'a1 list -> 'a1 list

val take : nat -> 'a1 list -> 'a1 list

val range : nat -> nat -> 'a1 list -> 'a1 list

val rotate_left : 'a1 list -> 'a1 list

val rotate_lefti : 'a1 list -> nat -> 'a1 list

val rotate_right : 'a1 list -> 'a1 list

val rotate_righti : 'a1 list -> nat -> 'a1 list

val lth : nat -> 'a1 list list -> 'a1 list

val width : 'a1 list -> nat

val rij_0 : poly

val rij_1 : poly

val rij_irreducible : bool list

val rij_m' : nat -> poly -> poly -> poly -> poly

val rij_mul : poly -> poly -> poly

val gtimes : poly -> poly -> poly

val decompose' : 'a1 list -> nat -> 'a1 list -> ('a1 list, 'a1 list) prod

val decompose : 'a1 list -> nat -> ('a1 list, 'a1 list) prod

val split' : 'a1 list -> nat -> nat -> 'a1 list list -> 'a1 list list

val split : 'a1 list -> nat -> 'a1 list list

val join : 'a1 list list -> 'a1 list

val gpower : poly -> nat -> poly

val inverse_n : poly -> nat -> poly

val inverse : poly -> poly

val gsum : vec -> poly

val dot : vec -> vec -> poly

val mmult : matrix -> matrix -> matrix

val parity : poly -> bool

val dotBit : poly -> poly -> bool

val mmultBit : vec -> vec -> vec

val rij_8f : bool list

val rij_65 : bool list

val affMat' : nat -> poly -> vec -> vec

val affMat : vec

val inv_affMat : vec

val rij_63 : poly

val rij_05 : poly

val rev_rij_63 : z2 list

val rev_rij_05 : z2 list

val affine : poly -> poly

val inv_affine : poly -> poly

val sbox : vec

val inv_sbox : vec

val nb : nat

val nk : nat

val nr : nat

val rcon : nat -> poly list

val sbox_ith : nat -> poly

val sbox_sel : poly -> poly

val subByte : poly list -> poly list

val inv_sbox_ith : nat -> poly

val inv_sbox_sel : poly -> poly

val stripe : vec -> matrix

val unstripe : matrix -> vec

val nextWord : poly -> vec -> vec -> vec

val kEw : nat -> nat -> matrix -> matrix -> matrix

val keyExpansion : vec -> matrix

val keyExpansion_split : vec -> matrix list

val keyExpansion_split_matrix : matrix list -> matrix list

val keySchedule : vec -> ((matrix, matrix list) prod, matrix) prod

val mk_cols' : nat -> vec -> matrix -> matrix

val mk_cols : vec -> matrix

val polyMat : vec -> matrix

val wiki_mat_start : poly list

val wiki_invmat_start : poly list

val mat_start : poly list

val invmat_start : poly list

val cx : matrix

val icx : matrix

val multCol : matrix -> vec -> vec

val mixColumn : matrix -> matrix

val invMixColumn : matrix -> matrix

val rol : poly list -> nat -> poly list

val ror : poly list -> nat -> poly list

val shiftRow : matrix -> matrix

val invShiftRow : matrix -> matrix

val byteSub : matrix -> matrix

val invByteSub : matrix -> matrix

val round : matrix -> matrix -> matrix

val finalRound : matrix -> matrix -> matrix

val mk_rnds : matrix -> matrix list -> matrix

val rounds : matrix -> ((matrix, matrix list) prod, matrix) prod -> matrix

val inv_Round : matrix -> matrix -> matrix

val invFinalRound : matrix -> matrix -> matrix

val mk_inv_rnds : matrix -> matrix list -> matrix

val inv_rounds : matrix -> ((matrix, matrix list) prod, matrix) prod -> matrix

val encrypt : vec -> vec -> vec

val decrypt : vec -> vec -> vec

val aes_main : vec -> vec -> vec
