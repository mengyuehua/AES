(* Galois Field 2^8. *)
Require Import Bool.
Require Import List.
Require Import natbool.
Require Import lib.
Require Import prim.


(* implementation according to Cryptol functions *)
Section Crytol.

(* x^i *)
Definition gpower (x:Poly) (i:nat) := ite Poly gtimes x i rij_1.

(* return j such that i+j is the index of the first true element. *)
Fixpoint find1 (xs:Poly) (i:nat) {struct xs} : nat :=
  match xs with
    | nil => 0
    | hd::tl => if hd then i else find1 tl (i+1)
  end.

(* return (n2p y) such that x * (n2p y) = 1 where y in [0..n].   *)
Fixpoint inverse_n (x:Poly) (n:nat) {struct n} : Poly :=
  match n with
  | 0 => rij_0
  | S n' => let y := n2p n in
            if req (gtimes x y) rij_1 then y else inverse_n x n'
  end.

(* return (n2p y) such that x * (n2p y) = 1 where y in [0..255].  *)
Definition inverse (x:Poly) : Poly := inverse_n x 255.
Definition gsum (xs:Vec) : Poly := fold_left rij_add xs rij_0.

Arguments map2 [A B].

Definition dot (xs: Vec) (ys: Vec) : Poly :=
  gsum (map2 gtimes xs ys).

(* matrix multplication of xss and yss.  *)
Definition mmult (xss: Matrix) (yss: Matrix) : Matrix :=
  let yss' := transpose Poly yss in
  let mkrow (xs:Vec) := 
    let dot_xs ys := dot ys xs in map dot_xs yss'
  in map mkrow xss.

(* return true if there is an odd number of true elements. *)
Definition parity (xs: Poly) : bool :=
  fold_left xorb xs false.

(* dot operation over bit. *)
Definition dotBit (a:Poly) (b:Poly) : bool :=
  parity (map2 andb a b).   

(* matrix of bits. *)
Definition mmultBit (xss:Vec) (yss:Vec) : Vec :=
  let yss' := transpose bool yss in
  let mkrow (xs:Poly) :=
    let dot_xs ys := dotBit ys xs in map dot_xs yss'
  in map mkrow xss.

End Crytol.


