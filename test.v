Require Import List.
Require Import Arith.
Require Import String.
Require Import Nat.
Require Import lib.
Require Import aes.
Require Import HexString.
Require Import Ascii String.
Require Import BinNums.
Import BinNatDef.
Import BinIntDef.
Import BinPosDef.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.


Section binlist_hexlist.
(* nat -> hexadecimal *)
Definition nat_to_hex_digit (n : nat) : string :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | 10 => "a" | 11 => "b" | 12 => "c" | 13 => "d"
  | 14 => "e" | 15 => "f"
  | _ => "?"
  end.

Fixpoint nat_to_hex_aux (n acc : nat) : string :=
  match n, acc with
  | 0, 0 => ""
  | _, 0 => nat_to_hex_digit (n mod 16)
  | _, S acc' => nat_to_hex_aux (n / 16) acc' ++ nat_to_hex_digit (n mod 16)
  end.

Definition nat_to_hex (n : nat) : string :=
  nat_to_hex_aux n 2.

Definition bin8_to_hex (b : list bool) : string :=
  nat_to_hex (p2n b).

Fixpoint binlist_to_hexlist (bin_list : list (list bool)) : list string :=
  match bin_list with
  | [] => []
  | b :: bs => bin8_to_hex b :: binlist_to_hexlist bs
  end.


(* test *)
Definition example_bin_list : list (list bool) :=
  [ true  :: false :: true  :: false :: true  :: false :: true  :: false :: nil ;
    false :: true  :: false :: true  :: false :: true  :: false :: true  :: nil ].
Compute (binlist_to_hexlist example_bin_list). (* ["AA"; "55"] *)

End binlist_hexlist.





Section hexlist_binlist.
Inductive hex : Type :=
| H0 : hex | H1 : hex | H2 : hex | H3 : hex | H4 : hex
| H5 : hex | H6 : hex | H7 : hex | H8 : hex | H9 : hex
| Ha : hex | Hb : hex | Hc : hex | Hd : hex | He : hex
| Hf : hex.

Fixpoint hex_to_nat (h: hex) : nat :=
  match h with
  | H0 => 0 | H1 => 1 | H2 => 2 | H3 => 3 | H4 => 4 | H5 => 5
  | H6 => 6 | H7 => 7 | H8 => 8 | H9 => 9 | Ha => 10
  | Hb => 11 | Hc => 12 | Hd => 13 | He => 14 | Hf => 15
  end.

Definition hex_char_to_hex (ch :  Ascii.ascii) : option hex
  := (if ascii_dec ch "0" then Some H0
      else if ascii_dec ch "1" then Some H1
      else if ascii_dec ch "2" then Some H2
      else if ascii_dec ch "3" then Some H3
      else if ascii_dec ch "4" then Some H4
      else if ascii_dec ch "5" then Some H5
      else if ascii_dec ch "6" then Some H6
      else if ascii_dec ch "7" then Some H7
      else if ascii_dec ch "8" then Some H8
      else if ascii_dec ch "9" then Some H9
      else if ascii_dec ch "a" then Some Ha
      else if ascii_dec ch "b" then Some Hb
      else if ascii_dec ch "c" then Some Hc
      else if ascii_dec ch "d" then Some Hd
      else if ascii_dec ch "e" then Some He
      else if ascii_dec ch "f" then Some Hf
      else None).

Fixpoint hex_string_to_nat (s: string) : option nat :=
  match s with
  | EmptyString => Some 0
  | String c cs =>
    match hex_char_to_hex c with
    | Some hc =>
      match hex_string_to_nat cs with
      | Some n => Some (hex_to_nat hc * (16^(length cs)) + n)
      | None => None
      end
    | None => None
  end
end.

Definition hex2nat (s:string) : nat :=
  match (hex_string_to_nat s) with
  | None => 0
  | Some a => a
  end.

Fixpoint hexlist_to_bin8list (s : list string) : list (list bool) :=
  match s with
  | [] => []
  | sh :: st => n2p (hex2nat sh) :: hexlist_to_bin8list st
  end.

End hexlist_binlist.



(* case comes from fips-197 Appendix B *)
Definition key :=
  ["2b"; "7e"; "15"; "16"; "28"; "ae"; "d2"; "a6"; "ab"; "f7"; "15"; "88"; "09"; "cf"; "4f"; "3c"].
Definition plaintext :=
  ["32"; "43"; "f6"; "a8"; "88"; "5a"; "30"; "8d"; "31"; "31"; "98"; "a2"; "e0"; "37"; "07"; "34"].


(* function test *)
(* ——————————————————————————————————————————————————————————————————————————————————————————————————————————————————*)
Definition liststring_to_Matrix (a : list string) : Matrix :=
   stripe (hexlist_to_bin8list a).
Definition Matrix_to_liststring (a : Matrix) : list string :=
   binlist_to_hexlist (unstripe a).

(* 1. AddRoundKey *)
Definition addRoundKey_test (plaintext key : list string) : list string := 
  let plaintext' := liststring_to_Matrix plaintext in
  let key' := liststring_to_Matrix key in
     Matrix_to_liststring (matrix_add plaintext' key').
Compute addRoundKey_test plaintext key.
(* ["19"; "3d"; "e3"; "be"; "a0"; "f4"; "e2"; "2b"; "9a"; "c6"; "8d"; "2a"; "e9"; "f8"; "48"; "08"] *)

(* 2. SubBytes *)
Definition subBytes_test (a : list string) : list string := 
  let a' := liststring_to_Matrix a in
    Matrix_to_liststring (byteSub a').
Compute subBytes_test 
  ["19"; "3d"; "e3"; "be"; "a0"; "f4"; "e2"; "2b"; "9a"; "c6"; "8d"; "2a"; "e9"; "f8"; "48"; "08"].
(* ["d4"; "27"; "11"; "ae"; "e0"; "bf"; "98"; "f1"; "b8"; "b4"; "5d"; "e5"; "1e"; "41"; "52"; "30"] *)

(*3. ShiftRows *)
Definition shiftRows_test (a : list string) : list string := 
  let a' := liststring_to_Matrix a in
    Matrix_to_liststring (shiftRow a').
Compute shiftRows_test 
  ["d4"; "27"; "11"; "ae"; "e0"; "bf"; "98"; "f1"; "b8"; "b4"; "5d"; "e5"; "1e"; "41"; "52"; "30"].
(* ["d4"; "bf"; "5d"; "30"; "e0"; "b4"; "52"; "ae"; "b8"; "41"; "11"; "f1"; "1e"; "27"; "98"; "e5"] *)

(* 4. MixColumns *)
Definition mixColumns_test (a : list string) : list string := 
  let a' := liststring_to_Matrix a in
    Matrix_to_liststring (mixColumn a').
Compute mixColumns_test
  ["d4"; "bf"; "5d"; "30"; "e0"; "b4"; "52"; "ae"; "b8"; "41"; "11"; "f1"; "1e"; "27"; "98"; "e5"].
(* ["04"; "66"; "81"; "e5"; "e0"; "cb"; "19"; "9a"; "48"; "f8"; "d3"; "7a"; "28"; "06"; "26"; "4c"] *)

(* 5. keyExpansion *)
Definition keyExpansion_test (key : list string) (n : nat) : list string :=
  let key_Vec := hexlist_to_bin8list key in
  let keys := keyExpansion_split key_Vec in
  let keys_arrange := keyExpansion_split_matrix keys in
    Matrix_to_liststring (prim.lth n keys_arrange).
Compute keyExpansion_test key 0.
Compute keyExpansion_test key 1.
(* ["2b"; "7e"; "15"; "16"; "28"; "ae"; "d2"; "a6"; "ab"; "f7"; "15"; "88"; "09"; "cf"; "4f"; "3c"]
   ["a0"; "fa"; "fe"; "17"; "88"; "54"; "2c"; "b1"; "23"; "a3"; "39"; "39"; "2a"; "6c"; "76"; "05"]  *)

(* 6. encrypt *)
Definition encrypt_test (key plaintext : list string) : list string :=
  let key' := hexlist_to_bin8list key in
  let plaintext' := hexlist_to_bin8list plaintext in
    binlist_to_hexlist (encrypt key' plaintext').
Compute encrypt_test key plaintext.
(* ["39"; "25"; "84"; "1d"; "02"; "dc"; "09"; "fb"; "dc"; "11"; "85"; "97"; "19"; "6a"; "0b"; "32"] *)

(* 7. decrypt *)
Definition decrypt_test (key ciphertext : list string) : list string :=
  let key' := hexlist_to_bin8list key in
  let ciphertext' := hexlist_to_bin8list ciphertext in
    binlist_to_hexlist (decrypt key' ciphertext').
Definition ciphertext :=
  ["39"; "25"; "84"; "1d"; "02"; "dc"; "09"; "fb"; "dc"; "11"; "85"; "97"; "19"; "6a"; "0b"; "32"].
Compute decrypt_test key ciphertext.
(* ["32"; "43"; "f6"; "a8"; "88"; "5a"; "30"; "8d"; "31"; "31"; "98"; "a2"; "e0"; "37"; "07"; "34"] *)

(* 8. encrypt and decrypt *)
Definition encrypt_decrypt_test (key plaintext : list string) : list string :=
  let key' := hexlist_to_bin8list key in
  let plaintext' := hexlist_to_bin8list plaintext in
    binlist_to_hexlist (aes_main key' plaintext').
Compute encrypt_decrypt_test key plaintext.
(* ["32"; "43"; "f6"; "a8"; "88"; "5a"; "30"; "8d"; "31"; "31"; "98"; "a2"; "e0"; "37"; "07"; "34"] *)

(*——————————————————————————————————————————————————————————————————————————————————————————————————————————————————*)


Require Import Extraction.
Extraction Language OCaml.
Require Import ExtrOcamlString.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Recursive Extraction key plaintext binlist_to_hexlist encrypt_test decrypt_test encrypt_decrypt_test AddRoundKey_test SubBytes_test ShiftRows_test MixColumns_test keyExpansion_test.
Extraction "test.ml" key plaintext binlist_to_hexlist encrypt_test decrypt_test encrypt_decrypt_test AddRoundKey_test SubBytes_test ShiftRows_test MixColumns_test keyExpansion_test.






