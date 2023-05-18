Require Import Bool.
Require Import List.
Require Import lib.
Require Import prim.
Require Import tacdef.

Compute n2p 0.
Lemma rij_mul_assoc0 : forall (a b : Poly),
  length a = 8 -> length b = 8 ->
  rij_mul a (rij_mul b (false :: false :: false :: false :: false :: false :: false :: false :: nil)) 
  = rij_mul (rij_mul a b) (false :: false :: false :: false :: false :: false :: false :: false :: nil).
Proof.
  intros. replace (false :: false :: false :: false :: false :: false :: false :: false :: nil) with rij_0.
  assert (forall a : Poly, length a = 8 -> rij_mul a rij_0 = rij_0). { auto. }
  apply H1; assumption. auto.
Qed.


