Require Import natbool.
Require Import Bool.
Require Import List.
Require Import lib.

Arguments map2 [A B].

(* preparation for theorems on map2 *)
Section EqListAB.
Variable A B C : Set.

Implicit Types la : list A.
Implicit Types lb : list B.
Implicit Types lc : list C.

Definition len_eq la lb := length la = length lb.

Variable P : list A -> list B -> Prop.
Variable Q : list A -> list B -> list C -> Prop.

Implicit Types a : A.
Implicit Types b : B.
Implicit Types c : C.

Theorem listABInd : 
  (forall lb, P nil lb) ->
  (forall la, P la nil) ->
  (forall a b la lb, P la lb -> P (a::la) (b::lb)) ->
  (forall la lb, P la lb).
Proof.
  intros P0 Pn.     (* keep one assumption in goal *) 
  induction la.
  - assumption.
  - induction lb.   (* induction within the base case of la *)
    -- auto. 
    -- induction lb.
      + auto.
      + auto.
Qed.

Theorem listABCInd : 
   (forall lb lc, Q nil lb lc) -> 
   (forall la lc, Q la nil lc) ->
   (forall la lb, Q la lb nil) ->
   (forall a b c la lb lc, Q la lb lc-> Q (a::la) (b::lb) (c::lc))
   -> (forall la lb lc, Q la lb lc).
Proof.
  intros P0 Pn.
  induction la.
  - auto.
  - induction lb.
    -- auto.
    -- induction lc; auto.
Qed.
 
(* two equal length lists induction scheme *)
Theorem eqListABInd :
  P nil nil ->
  (forall a b la lb, P la lb -> P (a::la) (b::lb)) ->
  (forall la lb, len_eq la lb -> P la lb).
Proof.
  intros P0 Pn. induction la.
  - intros. induction lb.
    -- assumption.
    -- unfold len_eq in H. simpl in H. discriminate H.
  - intros. induction lb.
    -- unfold len_eq in H. simpl in H. discriminate H.
    -- apply Pn. apply IHla. unfold len_eq in H. simpl in H. 
       unfold len_eq. auto.
Qed.

End EqListAB.





Section natInduction.
Theorem natABInd : forall (P : nat -> nat -> Prop), 
  (forall (n : nat), P 0 n) ->
  (forall (n : nat), P n 0) ->
  (forall (n m : nat), (P n m -> P (S n) (S m))) -> 
  (forall n m, P n m).
Proof.
  intros P0 P1 P2. induction n.
  - induction m; auto.
  - induction m; auto.
Qed.
End natInduction.





Section Map2.
Variable A : Set.

Lemma map2_comm :
  forall (f:A->A->A) (x y : list A)
  (h : forall (a b : A), (f a b) = (f b a)),
  map2 f x y = map2 f y x.
Proof.
  intros.
  apply (listABInd A A (fun x y => map2 f x y = map2 f y x)).
  - induction lb; auto.
  - induction la; auto.
  - intros. simpl. rewrite h. rewrite H. auto.
Qed.

(* map2 commutativity based on equal size lists. *)
Lemma map2_eq_comm : 
  forall (f:A->A->A) (x y : list A)
   (h : forall (a b : A), (f a b) = (f b a)),
    len_eq A A x y -> map2 f x y = map2 f y x.
Proof.
  intros.
  apply (eqListABInd A A (fun x y => map2 f x y = map2 f y x)).
  - trivial.
  - intros. simpl. rewrite h. rewrite H0. auto.
  - trivial.
Qed.

Lemma map2_right_nil : forall (A:Set) (x: list A) (f : A->A->A),
   map2 f x nil = nil.
Proof. intros. induction x; auto. Qed.

Lemma map2_left_nil : forall (A:Set) (x: list A) (f : A->A->A),
   map2 f nil x = nil.
Proof. intros. induction x; auto. Qed.

Lemma map2_cons :  forall (A:Set) (a b : A) (x y : list A) (f : A->A->A),
   map2 f (a::x) (b::y) = (f a b)::(map2 f x y).
Proof. intros. auto. Qed.

Lemma S_eq : forall (x y : nat), (S x) = (S y) -> x = y.
Proof. 
  intros x y. apply (natABInd (fun x y => ((S x) = (S y) -> x = y))); auto.
Qed.

Lemma map2_len : forall (x y : list A) (f : A->A->A),
  length x = length y -> length (map2 f x y) = length x.
Proof.
  intros.
  apply (eqListABInd A A (fun x y => length x = length y -> 
                          length (map2 f x y) = length x)); auto.
  intros. simpl. f_equal. apply H0. simpl in H1. auto.
Qed.

End Map2.


