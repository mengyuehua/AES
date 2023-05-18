(* Library Functions *)
Require Import Bool.
Require Import List.
Require Import natbool.  (* for rem2 *)
Require Import tacdef. 


Section NatFun.
Fixpoint max (n m : nat) {struct n} :=
  match n,m with
  | 0 , _ => m
  | _ , 0 => n
  | S n', S m' => 1 + (max n' m')
  end.

(* less than predicate returns a bool. <= *)
Fixpoint less_than (a b : nat) {struct a} : bool :=
  match a,b with
  | 0 , _ => true
  | S _ , 0 => false
  | S a', S b' => less_than a' b'
  end.

Definition less (a b : nat) : bool :=
  negb (less_than b a).

(* a<=b /\ b<=a -> a=b *)
Definition nateq (a b :nat) : bool :=
  andb (less_than a b) (less_than b a).

Definition is_zero (n:nat) : bool :=
  match n with
  | 0 => true
  | _ => false
  end.

(* supporting function for div  *)
Fixpoint div' (c m n r : nat) {struct c} : nat :=
  match c with
  | 0 => r
  | S c' => if less_than m 0 then r 
            else div' c' (m-n) n (r+1)
  end.

(*  division, assume m is multiples of n. *)
Definition div (m n : nat) : nat := div' m m n 0.

Fixpoint mod' (c m n : nat) {struct c} : nat :=
  match c with
  | 0 => m
  | S c' => if less m n then m
            else mod' c' (m-n) n
  end.

Definition mod (m n : nat) : nat := mod' m m n.

Definition nat_to_bool (n:nat) : bool :=
  match n with
  | 0 => false
  | _ => true
  end.

End NatFun.





Section ListFun.
Variables A B : Set.

(* cons at the end. *)
Definition back_cons (xs : list A) (a : A) : list A :=
  app xs (a :: nil).

(* [a;b;c] [[d];[e];[f]] => [[a;d];[b;e];[c;f]] *)
Fixpoint list_combine (l1 : list A) (l2 : list (list A)) {struct l1} :=
  match l1,l2 with
  | a::l1', b::l2' => (a::b)::(list_combine l1' l2')
  | _,_ => l2
  end.

(* a => [a] *)
Definition mk_list (a : A) : list A := a::nil.

(* make a constant list of length n *)
Fixpoint mk_const (n:nat) (a:A) : list A :=
  match n with
  | 0 => nil
  | S n' => a::(mk_const n' a)
  end.

(* support function for mk_natlist *)
Fixpoint mk_natlist' (n:nat) (r:list nat) {struct n} : list nat :=
  match n with
  | 0 => 0::r
  | S n' => mk_natlist' n' (n::r)
  end.

(* generate a nat list [0..n]. *)
Definition mk_natlist (n:nat) : list nat := mk_natlist' n nil.

(* A,B may be different: e.g. A is a matrix and B is a Vec. *)
Fixpoint map2 (f: A->B->A) (l1: list A) (l2: list B) {struct l1} : list A :=
  match l1,l2 with
  | h1::tl1,h2::tl2 => (f h1 h2)::(map2 f tl1 tl2)
  | _,_ => nil
  end.

(* return true if all elements of a list is true. *)
Fixpoint alltrue (l : list bool) : bool :=
  match l with
  | nil => true
  | true::tl => alltrue tl
  | false::tl => false
  end.
End ListFun.



(* higher order functionals *)
Section Ite.
Variable A : Set.

(* repeat r <- f(a,r) for i times, initially r=init. *)
Fixpoint ite (f:A->A->A) (a:A) (i:nat) (init:A) : A :=
  match i with
  | 0 => init
  | S i' => ite f a i' (f a init)
  end.
End Ite.




Section PolyBasic.
Definition Z2 := bool.
Definition Poly := list Z2.
Definition Vec    := list Poly.
Definition Matrix := list (list Poly).
(* Z2 operations *)
Definition Z2_add (a:Z2) (b:Z2) : Z2 := xorb a b.
Definition Z2_sub := Z2_add.
Definition Z2_mul := andb.

(* polynomial operations.  *)
Arguments map2 [A B].

Definition rij_add (p q : Poly) : Poly := map2 Z2_add p q.
Definition vec_add (p q : Vec) : Vec := map2 rij_add p q.
Definition matrix_add (p q : Matrix) : Matrix := map2 vec_add p q.
Definition rand (a:Poly) (b:Poly) : Poly := map2 andb a b.
Definition rxor (a:Poly) (b:Poly) : Poly := map2 xorb a b.
Definition reqb (a:Poly) (b:Poly) : Poly := map2 eqb a b.
Definition req (a b : Poly) : bool := alltrue (reqb a b) .
End PolyBasic.





Section ShiftFun.
(* generate a false list of length m. *)
Fixpoint false_list (n:nat) : Poly :=
  match n with
  | 0 => nil
  | S n' => false :: (false_list n')
  end.

(* shift a one bit to the left, discarding the high bit, 
   and making the low bit have a value of zero. *)
Definition fix_shift_left (l : list bool) : list bool :=
  match l with
  | nil => nil
  | _ :: tl => app tl (false :: nil)
  end.

(* shift the input one bit to the right, discarding the low bit,
   and making the high (leftmost) bit have a value of zero. *)
Definition fix_shift_right (l : list bool) : list bool :=
  rev (fix_shift_left (rev l)).

(* shift one bit to the left : n -> n+1  *)
Definition shift_left (l : list bool) : list bool := 
  app l (false :: nil).

(* shift the input one bit to the right: n->n-1 *)
Definition shift_right (l : list bool) : list bool :=
  rev (tail (rev l)).
End ShiftFun.




(* conversions between nat and poly. *)
Section NatPoly.
(* convert nat i to bool list p *)
Fixpoint nat2poly' (n i : nat) (p : Poly) {struct n} : Poly :=
  match n with
  | 0 => p
  | S n' => match i with
            | 0 => p
            | _ => let q := div2 i in
                      let r := rem2 i in
                          nat2poly' n' q (r::p)
            end
  end.

Definition nat2poly (i:nat) : Poly := nat2poly' i i nil.

(* convert a nat n to a bool list of length i. *)
Definition nat2polyi (n i : nat) : Poly :=
  let p := nat2poly n in
    let l := length p in
      app (false_list (i-l)) p.

Definition nat2poly8 (n:nat) : Poly := nat2polyi n 8.
(* convert a bool list to nat. *)
Definition poly2nat := natlist2nat.   

(* conversion between a bool vector of length 8 to natural. *)
Definition n2p := nat2poly8.
Definition p2n := poly2nat.
(* conversion between a bool vector with leading 1 to natural. *)
Definition n2b := nat2poly.
Definition b2n := poly2nat.

Definition eval1 f a   := p2n (f (n2p a)).
Definition eval2 f a b := p2n (f (n2p a) (n2p b)).
Definition evali f a (i:nat) := p2n (f (n2p a) i).
(* convert bool vector to natural number. *)
Definition vector_p2n (v:Vec)    := map p2n v.
Definition matrix_p2n (m:Matrix) := map vector_p2n m.
Definition vector_n2p (v:list nat) : Vec := map n2p v.
Definition matrix_n2p m := map vector_n2p m.
(* convert bool vector to 1-0 vector. *)
Definition poly_b2b (p:Poly) : list nat := map bool_to_nat p.
Definition vector_b2b (v:Vec) : list (list nat) := map poly_b2b v.
End NatPoly.




(* structure and primitive functions of bvec. *)
Section BitVec.
(* type of boolean vector. currently, bvec is same as poly. *)
Definition bvec := list bool.
(* get the value of the ith element from left, return false if length a < i.  *)
Fixpoint ith (i:nat) (a:bvec) {struct i} : bool :=
  match i,a with
    | 0,hd::tl => hd
    | S i', _::tl => ith i' tl
    | _,_ => false
  end.
End BitVec.


(* mat_unit_nat : list (list nat) *)
Definition mat_unit_nat := 
  (1::0::0::0::nil)::
  (0::1::0::0::nil)::
  (0::0::1::0::nil)::
  (0::0::0::1::nil)::nil.

(* matrix_n2p : list (list nat) -> list Vec *)
Definition mat_unit := matrix_n2p mat_unit_nat.

