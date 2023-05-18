(* properties about gsum and gtimes. gsum is defined in galois.v. *) 
Require Import natbool. (* nat_to_bool *)
Require Import Bool.
Require Import List.
Require Import lib.
Require Import prim.
Require Import galois.
Require Import aes.
Require Export map2.
Require Import rijadd.
Require Import rij_mul_add_distr.rij_mul_add_distr.
Require Import rij_m_comm8.rij_m_comm8.


Lemma gsum_non_nil : forall (a : Poly) (x : list Poly),
  length a = 8 -> is_veclen8 x -> gsum (a :: x) = rij_add a (gsum x).
Proof.
  intros. induction x.
  - unfold gsum. rewrite fold_left_cons. simpl. rewrite rij_add_comm. auto.
  - unfold gsum. rewrite fold_left_cons. rewrite rij_add_rij_0_left8.
    -- simpl. rewrite rij_add_rij_0_left8.
      + rewrite fold_rij_add; try (auto; simpl in H0; destruct H0; assumption).
      + simpl in H0. destruct H0. assumption.
    -- assumption.
Qed.


Lemma gsum_nil: gsum nil = rij_0.
Proof. auto. Qed.


Lemma gtimes_comm : forall x y, 
  length x = 8 -> length y = 8 -> gtimes x y = gtimes y x.
Proof.
  intros. unfold gtimes. unfold rij_mul. rewrite rij_m'_comm8; auto.
Qed.

(* 1 and 0 in Galois field. *)
Definition one  := n2p 1.
Definition zero := n2p 0.

(* enumerate and compute all 256 cases to calculate multiply by 0. *)
Lemma gtimes_left_zero : forall (a1 a2 a3 a4 a5 a6 a7 a8 : bool),
  let a := a1::a2::a3::a4::a5::a6::a7::a8::nil in
    gtimes zero a = zero.
Proof.
  intros. unfold gtimes. unfold rij_mul. unfold zero.
  replace (n2p 0) with rij_0.
  - rewrite rij_m_rij0. auto.
  - unfold n2p. compute. auto.
Qed.


(* enumerate and compute all 256 cases. *)
Lemma gtimes_left_unit : forall (a1 a2 a3 a4 a5 a6 a7 a8 : bool),
  let a := a1::a2::a3::a4::a5::a6::a7::a8::nil in
    gtimes one a = a.
Proof.
  intros. unfold a. 
  case a1; case a2; case a3; case a4;
  case a5; case a6; case a7; case a8;
  compute; trivial.
Qed.


(* gtimes left unit lemma for Poly with length 8, a variant of previous lemma. *)
Lemma gtimes_left_unit8 : forall a : Poly,
  (* one is left unit for multiplication in Galois field. *)
  length a = 8 -> gtimes one a = a.
Proof.
  intros. apply length8 in H.
  destruct H as [a1 H1].
  destruct H1 as [a2 H2].
  destruct H2 as [a3 H3].
  destruct H3 as [a4 H4].
  destruct H4 as [a5 H5].
  destruct H5 as [a6 H6].
  destruct H6 as [a7 H7].
  destruct H7 as [a8 H8].
  rewrite H8.
  apply gtimes_left_unit.
Qed.


(* gtimes left zeri lemma for Poly with length 8, a variant of previous lemma. *)
Lemma gtimes_left_zero8 : forall a : Poly,
  length a = 8 -> gtimes zero a = zero.
Proof.
  intros. apply length8 in H.
  destruct H as [a1 H1].
  destruct H1 as [a2 H2].
  destruct H2 as [a3 H3].
  destruct H3 as [a4 H4].
  destruct H4 as [a5 H5].
  destruct H5 as [a6 H6].
  destruct H6 as [a7 H7].
  destruct H7 as [a8 H8].
  rewrite H8.
  apply gtimes_left_zero.
Qed.


(* gsum [0;a1;..;an] = gsum [a1;a2;a3;...;an]. *)
Lemma gsum_zero1 : forall (a : Vec),
    gsum (zero :: a) = gsum a.
Proof.
  intros. induction a; trivial.
Qed.


(* gsum [0;a1;..;an] = gsum [a1;a2;a3;...;an]. *)
Lemma gsum_zero2 : forall (a0 : Poly) (a : Vec),
    length a0 = 8 -> is_veclen8 a ->
    gsum (a0 :: zero :: a) = gsum (a0::a).
Proof.
  intros. rewrite gsum_non_nil.
  - rewrite gsum_zero1. rewrite <- gsum_non_nil. trivial.
    -- assumption.
    -- assumption.
  - assumption.
  - simpl. split; trivial.
Qed.


Lemma gsum_single : forall (a : Poly),
  length a = 8 -> gsum (a :: nil) = a.
Proof.
   intro. case a.
  - intros. discriminate.
  - intros. rewrite gsum_non_nil.
    -- rewrite gsum_nil. rewrite rij_add_rij_0_right8.
      + auto.
      + assumption.
    -- assumption.
    -- simpl. auto.
Qed.


Lemma gtimes_nil : forall a : Poly, gtimes a nil = rij_0.
Proof. intro. auto. Qed.
Lemma gtimes_rij_0_right : forall a, gtimes a rij_0 = rij_0.
Proof. intro. auto. Qed.

(* proved in multassoc.v *)
Lemma rij_mul_len : forall  a b : Poly,
    length a = 8 -> length b = 8 -> length (rij_mul a b) = 8.
Proof. Admitted.


(* (x1+a0+x2+x3) * a = x1*a + a0*a + x2*a + x3*a      *)
Lemma fold_rij_mul : forall (a : Poly) (x : list Poly),
  length a = 8 -> is_veclen8 x ->  
  forall (a0 : Poly), length a0 = 8 ->
    rij_mul (fold_left rij_add x a0) a =
     fold_left rij_add (map (fun y : Poly => rij_mul y a) x) (rij_mul a0 a).
Proof.
  intros a x H1 H2. induction x.
  auto. intros. simpl. simpl in H2. destruct H2.
  rewrite <- rij_mul_add_distr; try assumption.
  set (d:=rij_add a1 a0). apply IHx. assumption. unfold d.
  rewrite rij_add_len8;auto.
Qed.


Lemma gtimes_gsum : forall (x : Vec) (a : Poly),
  length a = 8 -> is_veclen8 x ->
    gtimes (gsum x) a = gsum (map (fun y => gtimes y a) x).
Proof.
  intros. induction x. simpl.
  rewrite gsum_nil. rewrite gtimes_comm;auto.
  unfold gtimes,gsum.
  simpl (fold_left rij_add (a0 :: x) rij_0).
  simpl (map (fun y : Poly => rij_mul y a) (a0 :: x)).
  rewrite rij_add_rij_0_left8.
  - simpl (fold_left rij_add (rij_mul a0 a :: map (fun y : Poly => rij_mul y a) x) rij_0).
    rewrite rij_add_rij_0_left8. 
    + simpl in H0. rewrite fold_rij_mul; easy.
    + rewrite rij_mul_len;auto. simpl in H0. easy.
  - simpl in H0. easy.
Qed.

























