Require Import natbool. (* nat_to_bool *)
Require Import Bool.
Require Import List.
Require Import lib.    (* Matrix *)
Require Import prim.
Require Import galois. (* mmult *)
Require Import aes.
Require Import matrix4.
Require Import rijadd.
Require Import gsumgtimes.

Lemma dot_left_unit1 :
  forall  a1 a2 a3 a4 : Poly,
     let c := one::zero::zero::zero::nil in
     let a := a1::a2::a3::a4::nil in
        length a1 = 8 -> length a2 = 8 ->
        length a3 = 8 -> length a4 = 8 ->
        dot c a = a1.
Proof.
  intros. unfold dot. unfold c. unfold a. simpl.
  rewrite gtimes_left_unit8; try assumption.
  rewrite gtimes_left_zero8; try assumption.
  rewrite gtimes_left_zero8; try assumption.
  rewrite gtimes_left_zero8; try assumption.
  rewrite gsum_zero2. rewrite gsum_zero2. 
  rewrite gsum_zero2. apply gsum_single. 
  assumption. assumption.
  unfold is_veclen8. auto. assumption.
  unfold is_veclen8. split. auto. auto.
  assumption. unfold is_veclen8. split. auto. split. auto. auto.
Qed.

(* multiply with first unit raw (0,1,0,0) * (a1,a2,a3,a4) = a2. *)
Lemma dot_left_unit2 :  
  forall  a1 a2 a3 a4 : Poly,    
     let c := zero::one::zero::zero::nil in
     let a := a1::a2::a3::a4::nil in
        length a1 = 8 -> length a2 = 8 ->
        length a3 = 8 -> length a4 = 8 ->
        dot c a = a2.
Proof.
  intros. unfold dot. unfold c. unfold a. simpl.
  rewrite gtimes_left_zero8;try easy. rewrite gtimes_left_unit8;try easy.
  rewrite gtimes_left_zero8;try easy. rewrite gtimes_left_zero8;try easy.
  rewrite gsum_zero1. rewrite gsum_zero2;try easy. 
  rewrite gsum_zero2;try easy. rewrite gsum_single;try easy.
Qed.

(* multiply with first unit raw (0,0,1,0) * (a1,a2,a3,a4) = a3. *)
Lemma dot_left_unit3 :  
  forall  a1 a2 a3 a4 : Poly,    
     let c := zero::zero::one::zero::nil in
     let a := a1::a2::a3::a4::nil in
        length a1 = 8 -> length a2 = 8 ->
        length a3 = 8 -> length a4 = 8 ->
        dot c a = a3.
Proof.
  intros. unfold dot. unfold c. unfold a. simpl.
  rewrite gtimes_left_zero8;try easy.
  rewrite gtimes_left_unit8;try easy.
  rewrite gtimes_left_zero8;try easy.
  rewrite gtimes_left_zero8;try easy.
  repeat rewrite gsum_zero1. rewrite gsum_zero2;try easy. 
  rewrite gsum_single; auto.
Qed.


(* multiply with 4th unit raw (0,0,0,1) * (a1,a2,a3,a4) = a4. *)
Lemma dot_left_unit4 :  
  forall  a1 a2 a3 a4 : Poly,    
     let c := zero::zero::zero::one::nil in
     let a := a1::a2::a3::a4::nil in
        length a1 = 8 -> length a2 = 8 ->
        length a3 = 8 -> length a4 = 8 ->
        dot c a = a4.
Proof.
  intros. unfold dot. unfold c. unfold a. simpl.
  rewrite gtimes_left_zero8;try easy.
  rewrite gtimes_left_unit8;try easy.
  rewrite gtimes_left_zero8;try easy.
  rewrite gtimes_left_zero8;try easy.
  repeat rewrite gsum_zero1.
  rewrite gsum_single;auto.
Qed.

Lemma dot_left_unit1n :  
  forall  a1 a2 a3 a4 : Poly,    
     let c := (n2p 1)::(n2p 0)::(n2p 0)::(n2p 0)::nil in
     let a := a1::a2::a3::a4::nil in
        length a1 = 8 -> length a2 = 8 ->
        length a3 = 8 -> length a4 = 8 ->
        dot c a = a1.
Proof. unfold n2p. apply dot_left_unit1. Qed.

Lemma dot_left_unit2n :  
  forall  a1 a2 a3 a4 : Poly,    
     let c := (n2p 0)::(n2p 1)::(n2p 0)::(n2p 0)::nil in
     let a := a1::a2::a3::a4::nil in
        length a1 = 8 -> length a2 = 8 ->
        length a3 = 8 -> length a4 = 8 ->
        dot c a = a2.
Proof. unfold n2p. apply dot_left_unit2. Qed.

Lemma dot_left_unit3n :  
  forall  a1 a2 a3 a4 : Poly,    
     let c := (n2p 0)::(n2p 0)::(n2p 1)::(n2p 0)::nil in
     let a := a1::a2::a3::a4::nil in
        length a1 = 8 -> length a2 = 8 ->
        length a3 = 8 -> length a4 = 8 ->
        dot c a = a3.
Proof. unfold n2p. apply dot_left_unit3. Qed.

Lemma dot_left_unit4n :  
  forall  a1 a2 a3 a4 : Poly,    
     let c := (n2p 0)::(n2p 0)::(n2p 0)::(n2p 1)::nil in
     let a := a1::a2::a3::a4::nil in
        length a1 = 8 -> length a2 = 8 ->
        length a3 = 8 -> length a4 = 8 ->
        dot c a = a4.
Proof. unfold n2p. apply dot_left_unit4. Qed.

Lemma dot_right_unit1n :  
  forall  a1 a2 a3 a4 : Poly,    
     let c := (n2p 1)::(n2p 0)::(n2p 0)::(n2p 0)::nil in
     let a := a1::a2::a3::a4::nil in
        length a1 = 8 -> length a2 = 8 ->
        length a3 = 8 -> length a4 = 8 ->
        dot a c = a1.
Proof.
  intros. unfold a,c.
  rewrite dot_comm. apply dot_left_unit1n; assumption.
  simpl;easy. simpl;easy.
Qed.

Lemma dot_right_unit2n :  
  forall  a1 a2 a3 a4 : Poly,    
     let c := (n2p 0)::(n2p 1)::(n2p 0)::(n2p 0)::nil in
     let a := a1::a2::a3::a4::nil in
        length a1 = 8 -> length a2 = 8 ->
        length a3 = 8 -> length a4 = 8 ->
        dot a c = a2.
Proof.
  intros. unfold a,c.
  rewrite dot_comm. apply dot_left_unit2n; assumption.
  simpl;easy. simpl;easy.
Qed.

Lemma dot_right_unit3n :  
  forall  a1 a2 a3 a4 : Poly,    
     let c := (n2p 0)::(n2p 0)::(n2p 1)::(n2p 0)::nil in
     let a := a1::a2::a3::a4::nil in
        length a1 = 8 -> length a2 = 8 ->
        length a3 = 8 -> length a4 = 8 ->
        dot a c = a3.
Proof.
  intros. unfold a,c.
  rewrite dot_comm. apply dot_left_unit3n; assumption.
  simpl;easy. simpl;easy.
Qed.

Lemma dot_right_unit4n :  
  forall  a1 a2 a3 a4 : Poly,    
     let c := (n2p 0)::(n2p 0)::(n2p 0)::(n2p 1)::nil in
     let a := a1::a2::a3::a4::nil in
        length a1 = 8 -> length a2 = 8 ->
        length a3 = 8 -> length a4 = 8 ->
        dot a c = a4.
Proof.
  intros. unfold a,c.
  rewrite dot_comm. apply dot_left_unit4n; assumption.
  simpl;easy. simpl;easy.
Qed.

Lemma mmult_left_unit :
  forall  a11 a12 a13 a14
          a21 a22 a23 a24
          a31 a32 a33 a34
          a41 a42 a43 a44 : Poly,
	  let a1 := a11::a12::a13::a14::nil in
	  let a2 := a21::a22::a23::a24::nil in
	  let a3 := a31::a32::a33::a34::nil in
	  let a4 := a41::a42::a43::a44::nil in
          let ma := a1::a2::a3::a4::nil in
        length a11 = 8 -> length a12 = 8 ->
        length a13 = 8 -> length a14 = 8 ->
        length a21 = 8 -> length a22 = 8 ->
        length a23 = 8 -> length a24 = 8 ->
        length a31 = 8 -> length a32 = 8 ->
        length a33 = 8 -> length a34 = 8 ->
        length a41 = 8 -> length a42 = 8 ->
        length a43 = 8 -> length a44 = 8 ->
           mmult mat_unit ma = ma.
Proof.
  intros. unfold mmult. unfold mat_unit. simpl. unfold mk_list. 
  repeat rewrite dot_right_unit1n;(try assumption).
  repeat rewrite dot_right_unit2n;(try assumption).
  repeat rewrite dot_right_unit3n;(try assumption).
  repeat rewrite dot_right_unit4n;(try assumption).
  trivial.
Qed.
