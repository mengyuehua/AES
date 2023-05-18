Require Import List.
Require Import ArithRing.
Require Import Arith.
Require Import Bool.
Require Import Lia.
Require Import tacdef.
Require Import Min.
Require Import Plus.
Require Import metaind.

Implicit Type m n : nat.
Implicit Type a b c : bool.

(* simple nat related staffs. *)
Section NatSimple.
Definition bool_to_nat b :=
  match b with
  | true => 1
  | false => 0
  end.
Coercion bool_to_nat : bool >-> nat.
Lemma less_eq_S : forall n, 0<n -> exists m, n=S m.
Proof.
  intro. case n. intro H. absurdLe H.
  intros. exists n0. reflexivity.
Qed.
Lemma one_S : forall n, n+1 = S n.
Proof. intros. ring. Qed.
Lemma eq_min : forall (n:nat), min n n = n.
Proof. intros. apply min_l. trivial. Qed.
Lemma times2 : forall (n:nat), 2*(S n) = S(S(2*n)).
Proof. intros. rewrite <- one_S. ring. Qed.
Lemma S_le_double : forall n, 0 < n -> S n <= 2 * n.
Proof. intros. lia. Qed.
Lemma plus_S : forall (m n : nat), m + S n = S (m + n).
Proof. intros. lia. Qed.
Lemma plus_SS : forall (m n : nat), S m + n = S (m + n).
Proof. intros. lia. Qed.
End NatSimple.



Section OneShiftLeft.
(* return 2^n = 1 shift left n. *)
Fixpoint sftl n : nat :=
  match n with
  | 0 => 1
  | S n => let m := sftl n in 2*m
  end.
Lemma sftl_red : forall n, sftl (S n) = 2 * (sftl n).
Proof. intros. simpl. ring. Qed.
Lemma sftl_nzero : forall n, 0 < sftl n.
Proof. intros. induction n; simpl; autoLe. Qed.
Lemma sftl_S : forall n, exists m, sftl n = S m.
Proof. intro. apply less_eq_S. apply sftl_nzero. Qed.
Lemma n_le_sftl_n : forall n,  n < sftl n.
Proof. induction n. auto. rewrite sftl_red. lia. Qed.
End OneShiftLeft.



(* definition of div2, rem2, lg1 and their properties *)
Section Div2Rem2.
Fixpoint div2 (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Fixpoint rem2 (n : nat) : bool :=
  match n with
  | 0 => false
  | 1 => true
  | S(S i) => rem2 i
  end.

Lemma div2_red : forall n, div2 (S (S n)) = S (div2 n).
Proof. auto. Qed.
Lemma rem2_S : forall n, rem2 (S (S n)) = rem2 n.
Proof. auto. Qed.
Lemma rem2_2 : forall n, rem2 (2*n) = false.
Proof. 
  intros. induction n. simpl. reflexivity.
  rewrite times2. rewrite rem2_S. assumption.
Qed.
Lemma sftl_rem2 : forall n, 0<n -> rem2 (sftl n) = false.
Proof.
  intro. case n.
  intros. absurd (0<0); auto with arith.
  intros. rewrite sftl_red. rewrite rem2_2. reflexivity.
Qed.

(* return 1 if n>1 else 0, representing carry of full adder over nat *)
Definition lg1 n : bool :=
  match n with
  | 0 => false
  | 1 => false
  | _ => true
  end.

Lemma lg1_S : forall n, lg1 (S (S n)) = true.
Proof. auto. Qed.

Definition ci := lg1.     (* carry part of number n *)
Definition si := rem2.    (* sum part of number n *)

Lemma div2_rem2_ok : forall n, (div2 n) * 2 + (rem2 n) = n.
Proof.
  induction n using nat_ind2;try auto.
  rewrite div2_red. rewrite rem2_S. simpl. rewrite IHn. reflexivity.
Qed.

(* main lemma: 2 * carry_part_of n + sum_part_of_n = n *)
Lemma lg1_rem2_3bools : forall a b c, let n := a + b + c in 
  2 * lg1 n + rem2 n = n.
Proof. intros. caseBool (a,b,c). Qed.

Lemma div2_one : forall (n:nat), 
  0<n -> div2 (S(2*n)) = div2 (2*n).
Proof.
  apply lg0_imply. induction n.
  simpl. trivial. rewrite times2. rewrite div2_red. 
  rewrite div2_red. rewrite IHn. reflexivity.
Qed. 

Lemma div2_ok : forall n, div2 (2*n) = n.
Proof. 
  intros. induction n. auto.
  rewrite times2. rewrite div2_red. rewrite IHn. trivial.
Qed.

Lemma div2_le : forall (n:nat), div2 n <= n.
Proof. 
  intros. induction n using nat_ind2; auto.
  simpl. apply le_n_S. apply le_S. assumption.
Qed.

Lemma div2_lt : forall (n:nat), 0<n -> div2 n < n.
Proof.
  intro. induction n using nat_ind2; auto.
  intros. rewrite div2_red. autoLe. apply (le_lt_trans (div2 n) n (S n)).
  apply div2_le. auto.
Qed.
End Div2Rem2.



Section Log2.
Fixpoint log2_aux (m n : nat) {struct m} : nat :=
  match n,m with
  | 1,_ => 0
  | S n', S m' => S (log2_aux m' (div2 n))
  | _,_ => 0
  end.

Lemma log2_aux0 : forall m, log2_aux m 0 = 0.
Proof. induction m; auto. Qed.
Lemma log2_aux1 : forall m, log2_aux m 1 = 0.
Proof. induction m; auto. Qed.
Lemma log2_aux_S : forall (m n: nat),
  1<n -> log2_aux (S m) n = S (log2_aux m (div2 n)).
Proof.
  intros m n. case n. intros. lia. intro n0. case n0.
  intros. lia. intros. simpl. lia.
Qed.

(* log2 (2*n) = 1 + (log2 n) *)
Lemma log2_aux_red : forall (m n:nat),
  log2_aux (S m) (2 * (S n)) = S (log2_aux m (S n)).
Proof.
  induction n. auto. simpl. 
  replace (n+S(S(n+0))) with (S(S(2*n))).
  rewrite div2_red. rewrite div2_ok. reflexivity. ring.
Qed.

Lemma log2_aux_red1 : forall (m n:nat),
  0<n -> log2_aux (S m) (2 * n) = S(log2_aux m n).
Proof.
  intros m n. case n. intro. lia.
  intros. apply log2_aux_red.
Qed.

Lemma log2_aux_plus_one : forall (m n:nat),
  0<n -> log2_aux (S m) (S (2 * n)) = S(log2_aux m n).
Proof.
  intros. rewrite log2_aux_S.
  f_equal. rewrite div2_one. rewrite div2_ok.
  reflexivity. assumption. lia.
Qed.

(* log2 (2^n) = n *)
Lemma log2_aux_sftl : forall (n m:nat),
  n<m -> log2_aux m (sftl n) = n.
Proof.
  induction n.
  - intros. simpl. apply log2_aux1.
  - intro m. rewrite sftl_red. case m.
    + intros. lia.
    + intros. rewrite log2_aux_red1. 
      ++ f_equal. apply IHn. rmS H.
      ++ apply sftl_nzero.
Qed.

Lemma log2_aux_eq_times2 : forall (n m : nat),
  n<=m ->
  (forall k, log2_aux (n+k) n = log2_aux n n) ->
  log2_aux (S m) (S (2*n)) = log2_aux (S (2*n)) (S (2*n)).
Proof.
  intros n m. case n. auto.
  intros. rewrite log2_aux_plus_one. rewrite log2_aux_plus_one.
  f_equal. replace (2 * S n0) with (S n0 + S n0).
  rewrite (H0 (S n0)). rewrite <- (H0 (m - S n0)). f_equal. lia.
  lia. lia. lia.
Qed.

Lemma log2_aux_inv : forall (n m: nat),
   log2_aux (n+m) n = log2_aux n n.
Proof.
  apply (natGenInd div2 (fun n => forall m, log2_aux (n + m) n = log2_aux n n)).
  intros. apply div2_lt. assumption.
  intros. case m; auto.
  intros. generalize dependent H. case m.
  case n. intros. lia. intros. auto.
  intros. rewrite <- (div2_rem2_ok n). case (rem2 n).
  simpl bool_to_nat. replace (div2 n * 2 + 1) with (S (2 * div2 n)).
  rewrite <- plus_n_Sm. apply log2_aux_eq_times2. lia. apply H0.
  lia. BasicArith. rewrite mult_comm. generalize H. generalize H0. case n.
  intro. lia. intro n1. case n1. intros. auto.
  intros. rewrite <- plus_n_Sm. apply sym_eq. locRewrite div2_red div2.
  locRewrite times2 div2. rewrite log2_aux_red1. rewrite log2_aux_red1.
  f_equal. replace (2 * div2 (S (S n2)) + n0) with (div2 (S (S n2)) + (div2 (S (S n2)) + n0)).
  rewrite (H1 (div2 (S (S n2)) + n0)). rewrite <- (H1 (div2 n2)). f_equal. simpl div2. ring.
  ring. simpl. lia. simpl. lia.
Qed.

Definition log2 n : nat := log2_aux n n.

(* log2 (2^n) = n *)
Lemma log2_ok : forall n, log2 (sftl n) = n.
Proof.
  intro. unfold log2. apply log2_aux_sftl. apply n_le_sftl_n.
Qed.

Lemma log2_red : forall (n:nat),
  0<n -> log2 (2 * n) = S (log2 n).
Proof.
  unfold log2. intros. generalize dependent H. case n.
  lia. intros. locRewrite times2 mult. rewrite log2_aux_red.
  f_equal. replace (S (2 * n0)) with (S n0 + n0).
  apply log2_aux_inv. lia.
Qed.
End Log2.



(* Conversion from binary list to natural number. *)
Section Binary2Nat.
(* convert a 0-1 list to natural number *)
(* binary number bn..b1 is represented as [bn;..;b1] *)
Fixpoint natlist2nat (nlist:(list bool)) : nat :=
  match nlist with
  | nil => 0
  | hd :: tl => hd * (sftl (length tl)) + natlist2nat(tl)
  end.

(* binary number bn..b1 is represented as [b1;..bn] *)
Fixpoint rev_natlist2nat (nlist:(list bool)) : nat :=
  match nlist with
  | nil => 0
  | hd::tl => hd + 2 * rev_natlist2nat(tl)
  end.

Lemma natlist2nat_red : forall (a:bool) (l:(list bool)),
  natlist2nat (a::l) = 
  a * (sftl (length l)) + (natlist2nat l).
Proof. auto. Qed.

Lemma rev_natlist2nat_red : forall (a:bool) (l:(list bool)),
  rev_natlist2nat (a::l) = a + 2 * rev_natlist2nat(l).
Proof. simpl rev_natlist2nat. trivial. Qed.

Notation "x :+ y" := (x ++ y :: nil) (at level 30, right associativity)  : list_scope.

Lemma natlist2nat_redr : forall  (l:(list bool)) (a:bool),
  natlist2nat (l :+ a) = a + 2 * (natlist2nat l).
Proof.
  induction l. intro. simpl. ring.
  intro. simpl app. simpl natlist2nat. rewrite app_length.
  simpl length. rewrite IHl. rewrite one_S. rewrite sftl_red. ring.
Qed.

Lemma rev_natlist2nat_redr : forall  (l:(list bool)) (a:bool),
  rev_natlist2nat (l :+ a) = 
  a * (sftl (length l)) +  (rev_natlist2nat l).
Proof.
  induction l. intro. simpl. ring.
  intro. simpl. BasicArith. rewrite IHl. ring.
Qed.

Lemma natlist2nat_rev : forall (l:(list bool)),
  natlist2nat (rev l) =  (rev_natlist2nat l).
Proof.
  induction l. auto.
  simpl. rewrite natlist2nat_redr. rewrite IHl. ring.
Qed.

(* return the sum,carry of n=a+b+c *)
Definition nat_full_adder (n:nat) : bool * bool := (si n, ci n).
Definition nat_full_adder_ok := lg1_rem2_3bools.
End Binary2Nat.

Hint Rewrite sftl_red natlist2nat_red  rev_natlist2nat_red : base_red.
Hint Rewrite natlist2nat_redr rev_natlist2nat_redr : base_redr.
Notation "`` x" := (natlist2nat x) (at level 30, right associativity)  : list_scope.
Notation "` x"  := (rev_natlist2nat x) (at level 30, right associativity)  : list_scope.







