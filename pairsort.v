Require Import List.
Require Import Heap.  (* for sorting. *)
Require Import Lia. (* proofs for inequality. *)
Require Import Compare_dec.


Section PairSort.
(* pair list elements with their index. *)
Fixpoint pair_idx_ele' (l:list nat) (i:nat) {struct l} : list (nat*nat) :=
  match l with
  | nil => nil
  | hd::tl => (i,hd)::(pair_idx_ele' tl (i+1))
  end.

(* pair list elements with their index  *)
Definition pair_idx_ele (l:list nat) : list (nat*nat) :=
  pair_idx_ele' l 0.

(* to interprete * as product operator rather than multiplication.  *)
Definition nat_pair : Set := (nat*nat)%type.

(* nat_pair_le : relation nat_pair. *)
Definition nat_pair_le (a b : nat_pair) : Prop :=
  match a,b with
    (a1,a2),(b1,b2) => a2 <= b2
  end.

Definition nat_pair_lt (a b : nat_pair) : Prop :=
  match a,b with
    (a1,a2),(b1,b2) => a2 < b2
  end.

Definition nat_pair_eq (a b : nat_pair) : Prop :=
  match a,b with
    (a1,a2),(b1,b2) => a2=b2
  end.

Implicit Types m n : nat_pair.
(* proof is the program: if n<= m then left else right. *)
Definition natpair_le_lt_dec n m : 
  {nat_pair_le n m} + {nat_pair_lt m n}. 
Proof.
  case n; case m. intros. unfold nat_pair_le.
  unfold nat_pair_lt. apply le_lt_dec. 
Qed.

Fixpoint pair_insert (n:nat_pair) (l:list nat_pair) {struct l} : list nat_pair :=
  match l with
  | nil => cons n nil
  | cons m k => match natpair_le_lt_dec n m with
                | left _ => cons n (cons m k)
                | right _ => cons m (pair_insert n k)
                end
  end.

(* sort with ascending order. *)
Fixpoint natpair_sort (l : list nat_pair) : list nat_pair :=
  match l with
  | nil => nil
  | cons m k => pair_insert m (natpair_sort k)
  end.
End PairSort.



Section PairSortTest.

Definition l := 0::3::2::1::4::nil.
Definition l2 := pair_idx_ele l.
Definition l3 := natpair_sort l2.
Definition natfst := fst (A:=nat) (B:=nat).

(* inversed sbox by natural numbers. *)
Definition l4 : list nat := 
  map natfst (natpair_sort (pair_idx_ele l)).
End PairSortTest.


