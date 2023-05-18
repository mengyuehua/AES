Require Import natbool. 
Require Import Bool.
Require Import List.
Require Import lib.
Require Import prim.
Require Import galois.
Require Import aes.
Require Import matrix4.
Require Import multunit.
Require Import rijadd.
Require Import gsumgtimes.
Require Import rij_mul_add_distr.rij_mul_add_distr.
Require Import rij_mul_assoc.rij_mul_assoc.
Require Import rij_m_comm8.rij_m_comm8.

Lemma first_len8 : forall (a : Poly) (v : Vec),
  is_veclen8 (a::v) -> length a = 8.
Proof.
  intro a. induction v.
  simpl. intros [H1 H2]. assumption.
  simpl. intros [K1 K2]. assumption.
Qed.

Lemma rest_len8 : forall (a : Poly) (v : Vec),
  is_veclen8 (a::v) -> is_veclen8 v.
Proof.
  intros a v. simpl. intros [K1 K2]; trivial.
Qed.

Lemma Z2_add_assoc : forall x y z, 
   Z2_add (Z2_add x y) z = Z2_add x (Z2_add y z).
Proof.
  intros; unfold Z2_add. rewrite xorb_assoc. trivial.
Qed.

Lemma rij_add_assoc : forall x y z, 
   rij_add (rij_add x y) z = rij_add x (rij_add y z).
Proof.
  intros. unfold rij_add.
  apply (listABCInd Z2 Z2 Z2 (fun x y z  => 
      map2 Z2_add (map2 Z2_add x y) z = map2 Z2_add x (map2 Z2_add y z))).
  simpl. trivial. intros. rewrite map2_right_nil. rewrite map2_left_nil.
  rewrite map2_right_nil. trivial. intros. rewrite map2_right_nil.
  rewrite map2_right_nil. rewrite map2_right_nil. trivial.
  intros. simpl. rewrite Z2_add_assoc. f_equal. assumption.
Qed.

Lemma rij_add_len8 : forall (a b : Poly),
   length a = 8 -> length b = 8 -> length (rij_add a b) = 8.
Proof.
  intros. unfold rij_add. rewrite <- H. apply map2_len. 
  rewrite H; rewrite H0; reflexivity.
Qed.


Lemma fold_rij_add : forall (a : Poly) (x : list Poly),
  length a = 8 -> is_veclen8 x -> 
  forall (a0 : Poly), length a0 = 8 ->
    fold_left rij_add x (rij_add a a0) = rij_add a (fold_left rij_add x a0).
Proof.
  intros a x H1 H2. induction x.
  intros;simpl;trivial. intros;simpl.
  rewrite rij_add_assoc. apply IHx.
  apply (rest_len8 a0); assumption.
  apply rij_add_len8. assumption.
  apply (first_len8 a0 x); assumption.
Qed.


Lemma gsum_non_nil : forall (a : Poly) (x : list Poly),
  length a = 8 -> is_veclen8 x -> gsum (a :: x) = rij_add a (gsum x).
Proof.
  intros. unfold gsum at 1. simpl.
  rewrite rij_add_rij_0_left8.
  induction x. simpl. rewrite gsum_nil. rewrite rij_add_rij_0_right8. auto. assumption.
  simpl. unfold gsum. simpl. rewrite rij_add_rij_0_left8.
  apply fold_rij_add. assumption. destruct H0. assumption. destruct H0. assumption.
  destruct H0. assumption. assumption.
Qed.

Lemma dot4 : forall (a1 a2 a3 a4 b1 b2 b3 b4 : Poly),
   dot (a1::a2::a3::a4::nil) (b1::b2::b3::b4::nil) =
   gsum ((gtimes a1 b1)::(gtimes a2 b2)::(gtimes a3 b3)::(gtimes a4 b4)::nil).
Proof.
  intros. unfold dot; simpl. trivial.
Qed.


Lemma rij_mul_comm : forall a b : Poly,
  length a = 8 -> length b = 8 -> rij_mul a b = rij_mul b a.
Proof.
  intros. unfold rij_mul. apply rij_m'_comm8; trivial.
Qed.

Lemma rij_mul_len : forall  a b : Poly,
    length a = 8 -> length b = 8 -> length (rij_mul a b) = 8.
Proof.
  length8_split.
  case a1. case a2. case a3. case a4. case a5. case a6. case a7. case a8.
  case b1. case b2. case b3. case b4. case b5. case b6. case b7. case b8.
  auto. auto. case b8; try (repeat auto).
  case b7; case b8; try (repeat auto).
  case b6; case b7; case b8; try (repeat auto).
  case b5; case b6; case b7; case b8; try (repeat auto).
  case b4; case b5; case b6; case b7; case b8; try (repeat auto).
  case b3; case b4; case b5; case b6; case b7; case b8; try (repeat auto).
  case b2; case b3; case b4; case b5; case b6; case b7; case b8; try (repeat auto).
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; try (repeat auto).
  case a8; case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; try (repeat auto).
  case a7; case a8; case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; try (repeat auto).
  case a6; case a7; case a8; case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; try (repeat auto).
  case a5; case a6; case a7; case a8; case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; try (repeat auto).
  case a4; case a5; case a6; case a7; case a8; case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; try (repeat auto).
  case a3; case a4; case a5; case a6; case a7; case a8; case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; try (repeat auto).
  case a2; case a3; case a4; case a5; case a6; case a7; case a8; case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; try (repeat auto).
Qed.


Lemma rij_mul_len2 : forall a b c d : Poly,
    length (rij_mul a b) = 8 -> length (rij_mul c d) = 8 ->
    length (rij_add (rij_mul a b) (rij_mul c d)) = 8.
Proof.
  intros.
  set (x := rij_mul a b).
  set (y := rij_mul c d).
  assert (length x = 8). { unfold x. assumption. }
  assert (length y = 8). { unfold y. assumption. }
  apply rij_add_len8; assumption.
Qed.


Lemma rij_mul_len3 : forall a b c d e f: Poly,
    length (rij_mul a b) = 8 -> 
    length (rij_mul c d) = 8 ->
    length (rij_mul e f) = 8 -> 
    length (rij_add (rij_mul a b) (rij_add (rij_mul c d) (rij_mul e f))) = 8.
Proof.
  intros.
  set (x := rij_mul a b).
  set (y := rij_mul c d).
  set (z := rij_mul e f).
  assert (length x = 8). { unfold x. assumption. }
  assert (length y = 8). { unfold y. assumption. }
  assert (length z = 8). { unfold y. assumption. }
  apply rij_add_len8. assumption.
  apply rij_add_len8; assumption.
Qed.


Lemma rij_mul_len4 : forall a1 a2 a3 a4 b1 b2 b3 b4 : Poly,
    length (rij_mul b1 a1) = 8 -> length (rij_mul b2 a2) = 8 -> length (rij_mul b3 a3) = 8 -> length (rij_mul b4 a4) = 8 ->
    length (rij_add (rij_mul b1 a1) (rij_add (rij_mul b2 a2) (rij_add (rij_mul b3 a3) (rij_mul b4 a4)))) = 8.
Proof.
  intros.
  set (x := rij_mul b4 a4).
  set (y := rij_mul b3 a3).
  set (z := rij_mul b2 a2).
  set (w := rij_mul b1 a1). 
  assert (length x = 8). { unfold x. assumption. }
  assert (length y = 8). { unfold y. assumption. }
  assert (length z = 8). { unfold x. assumption. }
  assert (length w = 8). { unfold y. assumption. }
  apply rij_add_len8. assumption.
  apply rij_add_len8. assumption.
  apply rij_add_len8. assumption.
  assumption.
Qed.

(*  (c1b1 + c2b2 + c3b3 + c4b4) * a = c1b1a + c2b2a+ c3b3a + c4b4a    *)
Lemma rij_mul_add_right : forall a b1 b2 b3 b4 c1 c2 c3 c4: Poly,
  length a = 8 ->
  length b1 = 8 -> length b2 = 8 -> length b3 = 8 -> length b4 = 8 -> 
  length c1 = 8 -> length c2 = 8 -> length c3 = 8 -> length c4 = 8 -> 
  rij_mul (rij_add (rij_mul c1 b1) (rij_add (rij_mul c2 b2) (rij_add (rij_mul c3 b3) (rij_mul c4 b4)))) a = 
  rij_add (rij_add (rij_add (rij_mul (rij_mul c1 b1) a) (rij_mul (rij_mul c2 b2) a)) (rij_mul (rij_mul c3 b3) a)) (rij_mul (rij_mul c4 b4) a).
Proof.
  intros. repeat (rewrite rij_mul_add_distr); 
  repeat (rewrite rij_add_assoc);
  try (rewrite rij_mul_len); try (trivial).
  rewrite rij_mul_len2; try (rewrite rij_mul_len); try (trivial).
  rewrite rij_mul_len3; try (rewrite rij_mul_len); try (trivial).
Qed.


(* a * (c1b1 + c2b2 + c3b3 + c4b4) = ac1b1 + ac2b2 + ac3b3 + ac4b4 *)
Lemma rij_mul_add_left : forall a b1 b2 b3 b4 c1 c2 c3 c4: Poly,
  length a = 8 ->
  length b1 = 8 -> length b2 = 8 -> length b3 = 8 -> length b4 = 8 -> 
  length c1 = 8 -> length c2 = 8 -> length c3 = 8 -> length c4 = 8 -> 
  rij_mul a (rij_add (rij_mul c1 b1) (rij_add (rij_mul c2 b2) (rij_add (rij_mul c3 b3) (rij_mul c4 b4))))  = 
  rij_add (rij_add (rij_add (rij_mul a (rij_mul c1 b1) ) (rij_mul a (rij_mul c2 b2) )) (rij_mul a (rij_mul c3 b3) )) (rij_mul a (rij_mul c4 b4) ).
Proof.
  intros. rewrite rij_mul_comm.
  - rewrite rij_mul_add_right; trivial. f_equal.
    rewrite rij_mul_comm; try (rewrite rij_mul_len); try (trivial). f_equal.
    rewrite rij_mul_comm; try (rewrite rij_mul_len); try (trivial). f_equal.
    rewrite rij_mul_comm; try (rewrite rij_mul_len); try (trivial).
    rewrite rij_mul_comm; try (rewrite rij_mul_len); try (trivial).
    rewrite rij_mul_comm; try (rewrite rij_mul_len); try (trivial).
  - assumption.
  - rewrite rij_mul_len4; try (rewrite rij_mul_len); try (trivial).
Qed.


Lemma rij_mul_rij_0_left : forall a, rij_mul rij_0 a = rij_0.
Proof. intro. induction a. auto. unfold rij_mul. rewrite rij_m_rij0. auto. Qed.

Lemma rij_mul_nil : rij_mul nil nil = rij_0.
Proof. auto. Qed.
Lemma rij_mul_nil_right : forall a, rij_mul a nil = rij_0.
Proof. intro. induction a. auto. compute. auto. Qed.


(* vector x * matrix y * vector z. *)
Lemma mmult_vec_assoc : 
  forall ( a1 a2 a3 a4 
           b11 b12 b13 b14 
           b21 b22 b23 b24
           b31 b32 b33 b34
           b41 b42 b43 b44
           c1  c2  c3  c4 : Poly),
    let x0 := (a1::a2::a3::a4::nil) in
          let x  := (a1::a2::a3::a4::nil)::nil in
	  let b1 := b11::b12::b13::b14::nil in
	  let b2 := b21::b22::b23::b24::nil in
	  let b3 := b31::b32::b33::b34::nil in
	  let b4 := b41::b42::b43::b44::nil in
          let y  := b1::b2::b3::b4::nil in
          let z  := (c1::nil)::(c2::nil)::(c3::nil)::(c4::nil)::nil in
  is_veclen8 x0
  -> is_veclen8 b1 -> is_veclen8 b2 -> is_veclen8 b3 -> is_veclen8 b4
  -> length c1 = 8 -> length c2 = 8 -> length c3 = 8 -> length c4 = 8
  -> mmult x (mmult y z) = (mmult (mmult x y) z).
Proof.
  intros. unfold mmult. unfold x; unfold y; unfold z.
  simpl. unfold mk_list.
  unfold b1; unfold b2; unfold b3; unfold b4. 
  f_equal.
  repeat (rewrite dot4). 
  (* small goal *)
  simpl in H. simpl in H0. simpl in H1. simpl in H2. simpl in H3.
  repeat (rewrite gsum_non_nil);
  unfold gtimes; try (apply rij_mul_len); try (unfold is_veclen8);
  repeat (try (split); try (apply rij_mul_len));
  try (rewrite gsum_nil); try (rewrite rij_add_rij_0_right8);
  try (apply rij_mul_len4); try (apply rij_mul_len); try (easy).
  (* main goal *)
  repeat (rewrite rij_add_rij_0_right8); 
  try (rewrite rij_mul_add_left); try (apply rij_mul_len); try (easy).
  repeat (rewrite rij_mul_add_right); try (easy).
  repeat (rewrite rij_mul_add_left); try (easy).
  repeat (rewrite rij_mul_assoc); try (easy).
  - f_equal. repeat (rewrite <- rij_add_assoc). f_equal.
    set (d1:=rij_mul (rij_mul c1 b11) a1);  set (d2:=rij_mul (rij_mul c2 b12) a1);
    set (d3:=rij_mul (rij_mul c3 b13) a1);  set (d4:=rij_mul (rij_mul c4 b14) a1);
    set (d5:=rij_mul (rij_mul c1 b21) a2);  set (d6:=rij_mul (rij_mul c2 b22) a2);
    set (d7:=rij_mul (rij_mul c3 b23) a2);  set (d8:=rij_mul (rij_mul c4 b24) a2);
    set (d9:=rij_mul (rij_mul c1 b31) a3);  set (d10:=rij_mul (rij_mul c2 b32) a3);
    set (d11:=rij_mul (rij_mul c3 b33) a3); set (d12:=rij_mul (rij_mul c4 b34) a3);
    set (d13:=rij_mul (rij_mul c1 b41) a4); set (d14:=rij_mul (rij_mul c2 b42) a4);
    set (d15:=rij_mul (rij_mul c3 b43) a4).
    (* d12 *)
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    repeat (rewrite <- rij_add_assoc).
    f_equal.
    (* d8 *)
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    f_equal.
    (* d4 *)
    repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    f_equal.
    (* d15 *)
    repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    repeat (rewrite <- rij_add_assoc). 
    f_equal.
    (* d11 *)
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    repeat (rewrite <- rij_add_assoc).
    f_equal.
    (* d7 *)
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    repeat (rewrite <- rij_add_assoc).
    f_equal.
    (* d3 *)
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    repeat (rewrite <- rij_add_assoc).
    f_equal.
    (* d14 *)
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    rewrite rij_add_comm. rewrite <- rij_add_assoc.
    repeat (rewrite <- rij_add_assoc).
    f_equal.
    (* remaining *)
    repeat (rewrite rij_add_comm; rewrite <- rij_add_assoc;
            repeat (rewrite <- rij_add_assoc);
            f_equal).
  - repeat (apply rij_add_len8); repeat (apply rij_mul_len); try easy.
  - apply rij_mul_len4; try (apply rij_mul_len); try (easy).
Qed.



Lemma mmult_assoc : 
  forall  (a11 a12 a13 a14 b11 b12 b13 b14 c11 c12 c13 c14
           a21 a22 a23 a24 b21 b22 b23 b24 c21 c22 c23 c24
           a31 a32 a33 a34 b31 b32 b33 b34 c31 c32 c33 c34
           a41 a42 a43 a44 b41 b42 b43 b44 c41 c42 c43 c44 : Poly),
	  let a1 := a11::a12::a13::a14::nil in
	  let a2 := a21::a22::a23::a24::nil in
	  let a3 := a31::a32::a33::a34::nil in
	  let a4 := a41::a42::a43::a44::nil in
          let x  := a1::a2::a3::a4::nil in
	  let b1 := b11::b12::b13::b14::nil in
	  let b2 := b21::b22::b23::b24::nil in
	  let b3 := b31::b32::b33::b34::nil in
	  let b4 := b41::b42::b43::b44::nil in
          let y  := b1::b2::b3::b4::nil in
	  let c1 := c11::c12::c13::c14::nil in
	  let c2 := c21::c22::c23::c24::nil in
	  let c3 := c31::c32::c33::c34::nil in
	  let c4 := c41::c42::c43::c44::nil in
          let z  := c1::c2::c3::c4::nil in
  is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 ->
  is_veclen8 b1 -> is_veclen8 b2 -> is_veclen8 b3 -> is_veclen8 b4 ->
  is_veclen8 c1 -> is_veclen8 c2 -> is_veclen8 c3 -> is_veclen8 c4 ->
  mmult x (mmult y z) = (mmult (mmult x y) z).
Proof.
intros. unfold z. unfold c1,c2,c3,c4.
replace (((c11 :: c12 :: c13 :: c14 :: nil)
      :: (c21 :: c22 :: c23 :: c24 :: nil)
         :: (c31 :: c32 :: c33 :: c34 :: nil)
            :: (c41 :: c42 :: c43 :: c44 :: nil) :: nil)) 
    with (split (c11::c12::c13::c14::
                 c21::c22::c23::c24::
                 c31::c32::c33::c34::
                 c41::c42::c43::c44::nil) 4).
- set (c:=c11 :: c12 :: c13 :: c14 :: c21 :: c22 :: c23 :: c24 :: c31 :: c32 :: c33 :: c34 :: c41 :: c42 :: c43 :: c44 :: nil).
unfold x,y. unfold a1,a2,a3,a4,b1,b2,b3,b4.
Abort.

























