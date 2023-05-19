val xorb : bool -> bool -> bool
val negb : bool -> bool
type nat = O | S of nat
type 'a option = Some of 'a | None
type ('a, 'b) prod = Pair of 'a * 'b
val fst : ('a, 'b) prod -> 'a
val snd : ('a, 'b) prod -> 'b
val length : 'a list -> nat
val app : 'a list -> 'a list -> 'a list
type sumbool = Left | Right
val add : nat -> nat -> nat
val mul : nat -> nat -> nat
val sub : nat -> nat -> nat
val pow : nat -> nat -> nat
val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod
val div : nat -> nat -> nat
val modulo : nat -> nat -> nat
val eqb : bool -> bool -> bool
val nth : nat -> 'a list -> 'a -> 'a
val rev : 'a list -> 'a list
val map : ('a -> 'b) -> 'a list -> 'b list
val fold_left : ('a -> 'b -> 'a) -> 'b list -> 'a -> 'a
val append : 'a list -> 'a list -> 'a list
val length0 : 'a list -> nat
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
val div0 : nat -> nat -> nat
val mod' : nat -> nat -> nat -> nat
val mod0 : nat -> nat -> nat
val nat_to_bool : nat -> bool
val back_cons : 'a list -> 'a -> 'a list
val list_combine : 'a list -> 'a list list -> 'a list list
val mk_list : 'a -> 'a list
val mk_natlist' : nat -> nat list -> nat list
val mk_natlist : nat -> nat list
val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
val alltrue : bool list -> bool
val ite : ('a -> 'b -> 'b) -> 'a -> nat -> 'b -> 'b
type z2 = bool
type poly = z2 list
type vec = poly list
type matrix = poly list list
val z2_add : bool -> bool -> bool
val rij_add : bool list -> bool list -> bool list
val vec_add : bool list list -> bool list list -> bool list list
val matrix_add :
  bool list list list -> bool list list list -> bool list list list
val reqb : bool list -> bool list -> bool list
val req : bool list -> bool list -> bool
val false_list : nat -> bool list
val fix_shift_left : bool list -> bool list
val fix_shift_right : bool list -> bool list
val nat2poly' : nat -> nat -> bool list -> bool list
val nat2poly : nat -> bool list
val nat2polyi : nat -> nat -> bool list
val nat2poly8 : nat -> bool list
val poly2nat : bool list -> nat
val n2p : nat -> bool list
val p2n : bool list -> nat
type bvec = bool list
val ith : nat -> bool list -> bool
val getbit : nat -> bool list -> bool
val transpose : 'a list list -> 'a list list
val drop : nat -> 'a list -> 'a list
val tail : 'a list -> 'a list
val take : nat -> 'a list -> 'a list
val range : nat -> nat -> 'a list -> 'a list
val rotate_left : 'a list -> 'a list
val rotate_lefti : 'a list -> nat -> 'a list
val rotate_right : 'a list -> 'a list
val rotate_righti : 'a list -> nat -> 'a list
val lth : nat -> 'a list list -> 'a list
val width : 'a list -> nat
val rij_0 : bool list
val rij_1 : bool list
val rij_irreducible : bool list
val rij_m' : nat -> bool list -> bool list -> bool list -> bool list
val rij_mul : bool list -> bool list -> bool list
val gtimes : bool list -> bool list -> bool list
val decompose' : 'a list -> nat -> 'a list -> ('a list, 'a list) prod
val decompose : 'a list -> nat -> ('a list, 'a list) prod
val split' : 'a list -> nat -> nat -> 'a list list -> 'a list list
val split : 'a list -> nat -> 'a list list
val join : 'a list list -> 'a list
val gpower : bool list -> nat -> bool list
val inverse_n : bool list -> nat -> bool list
val inverse : bool list -> bool list
val gsum : bool list list -> bool list
val dot : bool list list -> bool list list -> bool list
val mmult : bool list list list -> bool list list list -> bool list list list
val parity : bool list -> bool
val dotBit : bool list -> bool list -> bool
val mmultBit : bool list list -> bool list list -> bool list list
val rij_8f : bool list
val rij_65 : bool list
val affMat' : nat -> 'a list -> 'a list list -> 'a list list
val affMat : bool list list
val inv_affMat : bool list list
val rij_63 : bool list
val rij_05 : bool list
val rev_rij_63 : bool list
val rev_rij_05 : bool list
val affine : bool list -> bool list
val inv_affine : bool list -> bool list
val sbox : bool list list
val inv_sbox : bool list list
val nb : nat
val nk : nat
val nr : nat
val rcon : nat -> bool list list
val sbox_ith : nat -> bool list
val sbox_sel : bool list -> bool list
val subByte : bool list list -> bool list list
val inv_sbox_ith : nat -> bool list
val inv_sbox_sel : bool list -> bool list
val stripe : 'a list -> 'a list list
val unstripe : 'a list list -> 'a list
val nextWord :
  bool list -> bool list list -> bool list list -> bool list list
val kEw :
  nat ->
  nat -> bool list list list -> bool list list list -> bool list list list
val keyExpansion : bool list list -> bool list list list
val keyExpansion_split : bool list list -> bool list list list list
val keyExpansion_split_matrix : 'a list list list -> 'a list list list
val keySchedule :
  bool list list ->
  ((bool list list list, bool list list list list) prod, bool list list list)
  prod
val mk_cols' : nat -> 'a list -> 'a list list -> 'a list list
val mk_cols : 'a list -> 'a list list
val polyMat : 'a list -> 'a list list
val wiki_mat_start : bool list list
val wiki_invmat_start : bool list list
val mat_start : bool list list
val invmat_start : bool list list
val cx : bool list list list
val icx : bool list list list
val multCol : bool list list list -> bool list list -> bool list list
val mixColumn : bool list list list -> bool list list list
val invMixColumn : bool list list list -> bool list list list
val rol : 'a list -> nat -> 'a list
val ror : 'a list -> nat -> 'a list
val shiftRow : 'a list list -> 'a list list
val invShiftRow : 'a list list -> 'a list list
val byteSub : bool list list list -> bool list list list
val invByteSub : bool list list list -> bool list list list
val round : bool list list list -> bool list list list -> bool list list list
val finalRound :
  bool list list list -> bool list list list -> bool list list list
val mk_rnds :
  bool list list list -> bool list list list list -> bool list list list
val rounds :
  bool list list list ->
  ((bool list list list, bool list list list list) prod, bool list list list)
  prod -> bool list list list
val inv_Round :
  bool list list list -> bool list list list -> bool list list list
val invFinalRound :
  bool list list list -> bool list list list -> bool list list list
val mk_inv_rnds :
  bool list list list -> bool list list list list -> bool list list list
val inv_rounds :
  bool list list list ->
  ((bool list list list, bool list list list list) prod, bool list list list)
  prod -> bool list list list
val encrypt : bool list list -> bool list list -> bool list list
val decrypt : bool list list -> bool list list -> bool list list
val aes_main : bool list list -> bool list list -> bool list list
val nat_to_hex_digit : nat -> char list
val nat_to_hex_aux : nat -> nat -> char list
val nat_to_hex : nat -> char list
val bin8_to_hex : bool list -> char list
val binlist_to_hexlist : bool list list -> char list list
type hex =
    H0
  | H1
  | H2
  | H3
  | H4
  | H5
  | H6
  | H7
  | H8
  | H9
  | Ha
  | Hb
  | Hc
  | Hd
  | He
  | Hf
val hex_to_nat : hex -> nat
val ( = ) : 'a -> 'a -> sumbool
val hex_char_to_hex : char -> hex option
val hex_string_to_nat : char list -> nat option
val hex2nat : char list -> nat
val hexlist_to_bin8list : char list list -> bool list list
val plaintext : char list list
val key : char list list
val encrypt_test : char list list -> char list list -> char list list
val decrypt_test : char list list -> char list list -> char list list
val encrypt_decrypt_test : char list list -> char list list -> char list list
val read_and_process_file : string -> char list list list
