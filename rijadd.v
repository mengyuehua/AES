(* properties about rij_add. *)

Require Import natbool. (* nat_to_bool *)
Require Import Bool.
Require Import List. 
Require Import lib.    (* Matrix    *)
Require Import prim.
Require Import galois. (* mmult     *)
Require Import map2.   (* listABInd *)
Require Import metaind.

Section Length8.

(* prove theorem of form "length l = 8 -> " 
   from a theorem of form "l=a1::..::a8::nil". *)
Lemma length8 : forall (l : list bool), 
  length l = 8 -> 
   exists a1, exists a2, exists a3, exists a4,
   exists a5, exists a6, exists a7, exists a8, 
   l = a1::a2::a3::a4::a5::a6::a7::a8::nil.
Proof.
  intro l. case l.
  - discriminate.
  - intros b l0. case l0. discriminate.
    intros b0 l1. case l1. discriminate.
    intros b1 l2. case l2. discriminate.
    intros b2 l3. case l3. discriminate.
    intros b3 l4. case l4. discriminate.
    intros b4 l5. case l5. discriminate.
    intros b5 l6. case l6. discriminate.
    intros b6 l7. case l7. intros.
    exists b; exists b0; exists b1; exists b2;
    exists b3; exists b4; exists b5; exists b6.
    auto. intros b7 l8. simpl. intro H. simplify_eq H.
Qed.

(* predicate for checking if all elements in Vec are of length 8. *)
Fixpoint is_veclen8 (v : Vec) : Prop :=
  match v with
  | nil   => True
  | a::tl => (length a = 8) /\ (is_veclen8 tl)
  end.

Lemma first_len8 : forall (a : Poly) (v : Vec),
  is_veclen8 (a::v) -> length a = 8.
Proof. intros a v. simpl. intros. destruct H. assumption. Qed.

Lemma rest_len8 : forall (a : Poly) (v : Vec),
  is_veclen8 (a::v) -> is_veclen8 v.
Proof. intros a v. simpl. intros. destruct H. assumption. Qed.
End Length8. 




(* define a tactic to prove a lemma with 
   length a=8 condition to a=a1..a8 condition. *)
Ltac ltac_length8 tac H :=
  apply length8 in H; (* forward reasoning *)
  (* get a = a1::a2::a3::a4::a5::a6::a7::a8 and rewrite it in goal. *)
  destruct H as [a1 H1]; (* open exist formula *)
  destruct H1 as [a2 H2];
  destruct H2 as [a3 H3];
  destruct H3 as [a4 H4];
  destruct H4 as [a5 H5];
  destruct H5 as [a6 H6];
  destruct H6 as [a7 H7];
  destruct H7 as [a8 H8];
  rewrite H8;  
  apply tac.

Ltac length8_split :=
  intros a b Ha Hb;
  apply length8 in Ha; apply length8 in Hb;
  destruct Ha as [a1 H1]; 
  destruct H1 as [a2 H2];
  destruct H2 as [a3 H3];
  destruct H3 as [a4 H4];
  destruct H4 as [a5 H5];
  destruct H5 as [a6 H6];
  destruct H6 as [a7 H7];
  destruct H7 as [a8 H8];
  destruct Hb as [b1 H1];
  destruct H1 as [b2 H2];
  destruct H2 as [b3 H3];
  destruct H3 as [b4 H4];
  destruct H4 as [b5 H5];
  destruct H5 as [b6 H6];
  destruct H6 as [b7 H7];
  destruct H7 as [b8 H9];
  rewrite H8; rewrite H9.

Lemma then_else_same : forall (A:Set) (e:bool) (x:A),
  (if e then x else x) = x.
Proof. intros. induction e; auto. Qed.
Lemma if_then_else : forall (e:bool),
  (if e then true else false) = e.
Proof. intros. induction e; auto. Qed.
Lemma z2_add_false : forall (a : Z2), Z2_add a false = a.
Proof. intros. unfold Z2_add. induction a; auto. Qed.
Lemma fold_left_cons : 
   forall (A B : Set) (a:B) (a0:A) (x: list B) (f:A->B->A),
   fold_left f (a::x) a0 = fold_left f x (f a0 a).
Proof. auto. Qed.

Lemma rij_add_rij_0_right :  forall a1 a2 a3 a4 a5 a6 a7 a8, 
  let a := a1::a2::a3::a4::a5::a6::a7::a8::nil in
    rij_add a rij_0 = a.
Proof.
  intros. unfold rij_add. unfold Z2_add. simpl.
  repeat rewrite z2_add_false. unfold a. trivial.
Qed.

Lemma rij_add_rij_0_right8 :  forall a : Poly,
    length a = 8 -> rij_add a rij_0 = a.
Proof.
  intros. ltac_length8 rij_add_rij_0_right H.
Qed.

Lemma rij_add_rij_0_left :  forall a1 a2 a3 a4 a5 a6 a7 a8, 
  let a := a1::a2::a3::a4::a5::a6::a7::a8::nil in
  rij_add rij_0 a = a.
Proof. 
  intros. unfold rij_add. unfold a. simpl. 
  repeat rewrite if_then_else. trivial.
Qed.

Lemma rij_add_rij_0_left8 :  forall a : Poly,
    length a = 8 -> rij_add rij_0 a = a.
Proof. intros; ltac_length8 rij_add_rij_0_left H. Qed.

Lemma rij_add2_rij_0 :  rij_add rij_0 rij_0 = rij_0.
Proof. auto. Qed.

Lemma rij_m_rij0 : forall (n:nat) (y:Poly),
   rij_m' n rij_0 y rij_0 = rij_0.
Proof.
  induction n. auto. intro. simpl.
  replace (false::false::false::false::false::false::false::false::nil) with rij_0.
  rewrite then_else_same. apply IHn. auto.
Qed.

Arguments listABInd [A B].

Lemma rij_add_comm : forall x y, rij_add x y = rij_add y x.
Proof.
  intros. unfold rij_add.
  apply (listABInd (fun x y => map2 Z2_add x y = map2 Z2_add y x));
  try(intros; apply map2_comm; unfold Z2_add; apply xorb_comm).
Qed.

Lemma rij_add_nil_left : forall a, length a = 8 -> rij_add nil a = nil.
Proof. intros. auto. Qed.
Lemma rij_add_nil_right : forall a, length a = 8 -> rij_add a nil = nil.
Proof. intros. rewrite rij_add_comm. apply rij_add_nil_left. assumption. Qed. 

Lemma rij_m'_S : forall (n:nat) a b r,
  rij_m' (S n) a b r =
     let b0 := getbit 0 b in
     let r' := if b0 then rij_add r a else r in
     let an := getbit 7 a in
     let a' := fix_shift_left a in
     let a'':= if an then rij_add a' rij_irreducible else a' in
     let b' := fix_shift_right b in
       rij_m' n a'' b' r'.
Proof. auto. Qed.

Lemma Z2_add_assoc : forall x y z, 
   Z2_add (Z2_add x y) z = Z2_add x (Z2_add y z).
Proof. intros. unfold Z2_add. apply xorb_assoc_reverse. Qed.

Lemma rij_add_assoc : forall x y z, 
   rij_add (rij_add x y) z = rij_add x (rij_add y z).
Proof.
  intros. unfold rij_add.
  apply (listABCInd Z2 Z2 Z2 (fun x y z => map2 Z2_add (map2 Z2_add x y) z = map2 Z2_add x (map2 Z2_add y z))). auto.
  intros. rewrite map2_right_nil. rewrite map2_left_nil. rewrite map2_right_nil. auto.
  intros. rewrite map2_right_nil. rewrite map2_right_nil. rewrite map2_right_nil. auto.
  intros. simpl. rewrite Z2_add_assoc. f_equal. assumption.
Qed.

Lemma rij_add_len8 : forall (a b : Poly),
   length a = 8 -> length b = 8 -> length (rij_add a b) = 8.
Proof.
  intros. unfold rij_add. rewrite <- H. apply map2_len.
  rewrite H. rewrite H0. auto.
Qed.

(* x1+(a+a0)+x2+x3 = a+(x1+a0+x2+x3) *)
Lemma fold_rij_add : forall (a : Poly) (x : list Poly),
  length a = 8 -> is_veclen8 x -> 
  forall (a0 : Poly), length a0 = 8 ->
    fold_left rij_add x (rij_add a a0) = rij_add a (fold_left rij_add x a0).
Proof.
  intros a x H1 H2. induction x.
  auto. intros. simpl. rewrite rij_add_assoc. apply IHx.
  apply H2. apply rij_add_len8. assumption. apply H2.
Qed.




