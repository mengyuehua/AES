Require Import Bool.
Require Import List.
Require Import lib.
Require Import prim.
Require Import tacdef.

Compute n2p 116.
Lemma rij_m'_comm8_116 : forall x y,
  length x = 8 -> length y = 8 ->
    rij_m' 8 x y (false :: true :: true :: true :: false :: true :: false :: false :: nil)
    = rij_m' 8 y x (false :: true :: true :: true :: false :: true :: false :: false :: nil).
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
