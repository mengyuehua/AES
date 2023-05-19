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

(* to matrix *)
Definition plaintext' := stripe (hexlist_to_bin8list plaintext).
Definition key' := stripe (hexlist_to_bin8list key).

(* AddRoundKet, correct *)
Definition matrix_add_1 := matrix_add plaintext' key'.
Compute (binlist_to_hexlist (prim.join matrix_add_1)).
(* SubBytes, correct *)
Definition byteSub_1 :=byteSub matrix_add_1.
Compute (binlist_to_hexlist (prim.join byteSub_1)).
(* ShiftRows, correct*)
Definition shiftRow_1 :=shiftRow byteSub_1.
Compute (binlist_to_hexlist (prim.join shiftRow_1)).
(* MixColumns, correct *)
Definition mixColumn_1 :=mixColumn shiftRow_1.
Compute (binlist_to_hexlist (prim.join mixColumn_1)).


(* keyExpension, correct *)
Definition keys := keyExpansion_split (hexlist_to_bin8list key).
Definition keys_matrix := keyExpansion_split_matrix keys.
(* key0, correct *)
Definition key0 := prim.lth 0 keys_matrix.
Compute binlist_to_hexlist (prim.join key0).
(* key1, correct *)
Definition key1 := prim.lth 1 keys_matrix.
Compute binlist_to_hexlist (prim.join key1).
(* key2, correct *)
Definition key2 := prim.lth 2 keys_matrix.
Compute binlist_to_hexlist (prim.join key2).


(* encrypt, correct *)
Definition encrypt_test (key plaintext : list string) : list string :=
  binlist_to_hexlist (encrypt (hexlist_to_bin8list key) (hexlist_to_bin8list plaintext)).
Compute encrypt_test key plaintext.

(* decrypt, correct *)
Definition decrypt_test (key ciphertext : list string) : list string :=
  binlist_to_hexlist (decrypt (hexlist_to_bin8list key) (hexlist_to_bin8list ciphertext)).

(* encrypt and decrypt, correct *)
Definition encrypt_decrypt_test (key plaintext : list string) : list string :=
  binlist_to_hexlist (aes_main (hexlist_to_bin8list key) (hexlist_to_bin8list plaintext)).
Compute encrypt_decrypt_test key plaintext.


Require Import Extraction.
Extraction Language OCaml.
Require Import ExtrOcamlString.
(* Require Import ExtrOcamlNativeString. *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Recursive Extraction key plaintext binlist_to_hexlist encrypt_test decrypt_test encrypt_decrypt_test.
Extraction "test.ml" key plaintext binlist_to_hexlist encrypt_test decrypt_test encrypt_decrypt_test.






