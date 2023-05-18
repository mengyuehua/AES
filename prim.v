Require Import Bool.
Require Import List.
Require Import natbool.
Require Import lib.
Require Import Lia.

Section SimplePrimitive.
(* return the ith bit from right, the rightest index is 0. *)
(* equivalent to a @ i. *)
Definition getbit (i:nat) (a:bvec) : bool := ith i (rev a).
(* return true if there is an odd number of true elements. *)
Definition pairty (xs:Poly) : bool := fold_left xorb xs false.
End SimplePrimitive.



Section ListPrimitive.
Variable A : Set.
Fixpoint transpose (l : list (list A)) : list (list A) :=
  match l with
  | nil => nil
  | a::nil => map (mk_list A) a
  | a::l' => list_combine A a (transpose l')
  end.

(* remove first n elements from list. *)
Fixpoint drop (n:nat) (l: list A) {struct n} : list A :=
  match n,l with
    | S n', hd::tl => drop n' tl
    | _,_ => l
  end.

Definition tail (l : list A) := drop 1 l.

(* take first n elements in the list *)
Fixpoint take (n:nat) (l:list A) {struct n} : list A :=
  match n,l with
  | S n', hd::tl => hd::(take n' tl)
  | _,_ => nil
  end.

(* collect elements from i to j inclusive.  *)
Definition range (i j : nat) (l : list A) : list A :=
  take (j-i+1) (drop i l).

(* list rotation to left <<< 1 *)
Definition rotate_left (l : list A) : list A :=
  match l with
  | nil => nil
  | hd::tl => app tl (hd::nil)
  end.

(* list rotation to left for i times = <<< i.  *)
Fixpoint rotate_lefti (l:list A) (i:nat) {struct i} : list A :=
  match i with
  | 0 => l
  | S i' => rotate_lefti (rotate_left l) i'
  end.

(* list rotation to right >>> *)
Definition rotate_right (l:list A) : list A :=
  rev (rotate_left (rev l)).
Definition rotate_righti (l:list A) (i:nat) : list A :=
  rev (rotate_lefti (rev l) i).

(* select nth element from left = l @ n. default value is nil. *)
Definition lth (n:nat) (l:list (list A)) : list A := nth n l nil.
(* Cryptol width function is the length function. *)
Definition width := length.


Lemma rotate_left_one : forall a (l:list A),
  rotate_left (a::l) = l ++ a::nil.
Proof. intros. auto. Qed. 
Lemma rotate_right_one : forall a l,
  rotate_right (l ++ a::nil) = a::l.
Proof. 
  intros. unfold rotate_right. rewrite rev_unit. rewrite rotate_left_one.
  rewrite rev_unit. rewrite rev_involutive. auto.
Qed.

Lemma rotate_right_left : forall l : list A, 
  rotate_right (rotate_left l) = l.
Proof.
  intro. induction l. auto. 
  rewrite rotate_left_one. rewrite rotate_right_one. auto. 
Qed.

Variable d : A.
Lemma rotate_left_right : forall (l : list A),
  rotate_left (rotate_right l) = l.
Proof.
  intro. 
  assert (forall (l:list A) (d:A), l<>nil -> l = (removelast l) ++ (last l d)::nil).
  { apply app_removelast_last. } 
  induction l. auto.
  set (l':=a::l).
  replace l' with (removelast l' ++ last l' d :: nil).
  set (l'':=removelast l'). set (b:=last l' d).
  rewrite rotate_right_one. rewrite rotate_left_one. auto.
  symmetry. apply app_removelast_last. unfold l'. easy.
Qed.
End ListPrimitive.



Arguments drop [A].
Arguments take [A].
Arguments range [A].

Section PolyMul.
(** GF(2^8) constants. *)
Definition rij_0 : Poly := false::false::false::false::false::false::false::false::nil.
(* 0x1 rightest bit = 1. *)
Definition rij_1 : Poly := false::false::false::false::false::false::false::true::nil.
(* 0x80 leftest bit = 1. *)
Definition rij_8 : Poly := true::false::false::false::false::false::false::false::nil.
(* x^4 + x^3 + x + 1 = 00011011 = 0x1b = 27 *)
Definition rij_irreducible := false::false::false::true::true::false::true::true::nil.

Fixpoint rij_m' (n:nat)  (a:Poly) (b:Poly) (r:Poly) {struct n} : Poly :=
 match n with
   | 0 => r
   | S n' =>
     let b0 := getbit 0 b in
     let r' := if b0 then rij_add r a else r in 
     let an := getbit 7 a in
     let a' := fix_shift_left a in
     let a'':= if an then rij_add a' rij_irreducible else a' in
     let b' := fix_shift_right b in
       rij_m' n' a'' b' r'
 end.

Definition rij_mul (a b : Poly) := rij_m' 8 a b rij_0.
Definition gtimes := rij_mul.
End PolyMul.



Section Split.
Variable A : Set.

Fixpoint decompose' (xs: list A) (m:nat) (r: list A)
  {struct m} : (list A) * (list A) :=
  match m,xs with
    | S m', hd::tl => decompose' tl m' (hd::r)
    | _,_ => pair (rev r) xs 
  end.

Definition decompose (xs: list A) (m:nat) : (list A)*(list A) :=
  decompose' xs m nil.

Fixpoint split' (xs: list A) (n m : nat) (r: list (list A)) {struct n} : list (list A) :=
  match n with
  | 0 => r
  | S n' => let (r1,r2) := decompose xs m in  
	            split' r2 n' m  (back_cons (list A) r r1)
  end.

Definition split (xs: list A) (n:nat) : list (list A) :=
  let l := length xs in
  let m := div l n in
      split' xs n m nil.

Variables a1 a2 a3 a4:A.

Fixpoint join (xs: list (list A)) : list A :=
  match xs with
    | nil => nil
    | hd::tl => app hd (join tl)
  end.
End Split.



