Require Import Bool.
Require Import List.
Require Import lib.   
Require Import prim.
Require Import tacdef.

Compute n2p 246.
Lemma rij_mul_add_distr246 : forall a b : Poly,
  length a = 8 -> length b = 8 -> 
  rij_mul (rij_add a b) (true :: true :: true :: true :: false :: true :: true :: false :: nil) 
  = rij_add (rij_mul a (true :: true :: true :: true :: false :: true :: true :: false :: nil)) 
    (rij_mul b (true :: true :: true :: true :: false :: true :: true :: false :: nil)).
Proof.
  length8_split.
  case a1; case a2; case a3; case a4; case a5; case a6; case a7; case a8.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
Qed.

