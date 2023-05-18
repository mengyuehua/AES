Require Import natbool.
Require Import Bool.
Require Import List.
Require Import lib.
Require Import prim.
Require Import galois.
Require Import aes.
Require Import matrix4.
Require Import multunit.
Require Import multassoc.
Require Import rijadd.
Require Import rij_mul_assoc.rij_mul_assoc.


Lemma cx_icx :  mmult cx icx =  mat_unit.
Proof. auto. Qed.
Lemma icx_cx :  mmult icx cx =  mat_unit.
Proof. auto. Qed.
 

(* (a*b)*c = (a*c)*b *)
Lemma rij_mul_assoc' : forall a b c : Poly,
  length a = 8 -> length b = 8 -> length c = 8 ->
  rij_mul (rij_mul a b) c = rij_mul (rij_mul a c) b.
Proof. 
  intros. rewrite rij_mul_comm;try auto. rewrite rij_mul_assoc;auto.
  assert (rij_mul c a = rij_mul a c). { rewrite rij_mul_comm;auto. }
  rewrite H2. auto. rewrite rij_mul_len;auto.
Qed.


(* mmult icx (mmult cx (split (a1 :: a2 :: a3 :: a4 :: nil) 4)) *)
Lemma mmult_assoc : 
  forall x11 x12 x13 x14 y11 y12 y13 y14
         x21 x22 x23 x24 y21 y22 y23 y24
         x31 x32 x33 x34 y31 y32 y33 y34
         x41 x42 x43 x44 y41 y42 y43 y44
         z1 z2 z3 z4 : Poly,
  let x1 := x11::x12::x13::x14::nil in
  let x2 := x21::x22::x23::x24::nil in
  let x3 := x31::x32::x33::x34::nil in
  let x4 := x41::x42::x43::x44::nil in
       let x := x1::x2::x3::x4::nil in
  let y1 := y11::y12::y13::y14::nil in
  let y2 := y21::y22::y23::y24::nil in
  let y3 := y31::y32::y33::y34::nil in
  let y4 := y41::y42::y43::y44::nil in
       let y := y1::y2::y3::y4::nil in
       let z:= z1::z2::z3::z4::nil in
  length z1=8 -> length z2=8 -> length z3=8 -> length z4 =8 ->
  is_veclen8 x1 -> is_veclen8 x2 -> is_veclen8 x3 -> is_veclen8 x4 ->
  is_veclen8 y1 -> is_veclen8 y2 -> is_veclen8 y3 -> is_veclen8 y4 ->
  mmult x (mmult y (split z 4)) = (mmult (mmult x y) (split z 4)).
Proof.
  intros. simpl in H3,H4,H5,H6,H7,H8,H9,H10;
  destruct H3 as [H11[H12[H13[H14 H15]]]]; destruct H4 as [H16[H17[H18[H19 H20]]]];
  destruct H5 as [H21[H22[H23[H24 H25]]]]; destruct H6 as [H26[H27[H28[H29 H30]]]];
  destruct H7 as [H31[H32[H33[H34 H35]]]]; destruct H8 as [H36[H37[H38[H39 H40]]]];
  destruct H9 as [H41[H42[H43[H44 H45]]]]; destruct H10 as [H46[H47[H48[H49 H50]]]].
  assert (mmult y (split z 4) = split (dot y1 z::dot y2 z::dot y3 z::dot y4 z::nil) 4).
  apply mmult_ma_cv;simpl;easy. rewrite H3. rewrite split4. 
  simpl. unfold mk_list. unfold x1,x2,x3,x4. repeat (rewrite dot4).
  repeat (rewrite gsum_non_nil); try (unfold gtimes);
  try (unfold is_veclen8); repeat (try split); try (apply rij_mul_len); try auto;
  try repeat(apply rij_add_len8); try apply rij_mul_len; try auto.
  rewrite gsumgtimes.gsum_nil. repeat(rewrite rij_add_rij_0_right8);try (apply rij_mul_len); auto;
  try repeat(apply rij_add_len8); try (apply rij_mul_len); auto.
  unfold y1,y2,y3,y4,dot,gtimes,gsum. simpl fold_left.
  repeat(rewrite rij_add_rij_0_left8); try apply rij_mul_len; auto.
  assert (forall a1 a2 a3 a4 b1 b2 b3 b4 c : Poly,
    length a1 = 8 -> length a2 = 8 -> length a3 = 8 -> length a4 = 8 ->
    length b1 = 8 -> length b2 = 8 -> length b3 = 8 -> length b4 = 8 -> length c = 8 ->
    rij_mul (rij_add (rij_add (rij_add (rij_mul a1 b1) (rij_mul a2 b2)) (rij_mul a3 b3)) (rij_mul a4 b4)) c
  = rij_add (rij_add (rij_add (rij_mul (rij_mul a1 b1) c) (rij_mul (rij_mul a2 b2) c)) (rij_mul (rij_mul a3 b3) c)) (rij_mul (rij_mul a4 b4) c)).
  { intros. rewrite <- rij_mul_add_right; try assumption. repeat (rewrite <- rij_add_assoc). auto. }
  repeat rewrite H4; try assumption.
  assert (forall a1 a2 a3 a4 b1 b2 b3 b4 c : Poly,
    length a1 = 8 -> length a2 = 8 -> length a3 = 8 -> length a4 = 8 ->
    length b1 = 8 -> length b2 = 8 -> length b3 = 8 -> length b4 = 8 -> length c = 8 ->
    rij_mul c (rij_add (rij_mul a1 b1) (rij_add (rij_mul a2 b2) (rij_add (rij_mul a3 b3) (rij_mul a4 b4))))
  = rij_add (rij_add (rij_add (rij_mul (rij_mul a1 b1) c) (rij_mul (rij_mul a2 b2) c)) (rij_mul (rij_mul a3 b3) c)) (rij_mul (rij_mul a4 b4) c)).
  { intros. rewrite rij_mul_add_left; try assumption. repeat (rewrite <- rij_add_assoc). 
    rewrite rij_mul_comm.
    assert (rij_mul c (rij_mul a2 b2) = rij_mul (rij_mul a2 b2) c). 
    { rewrite rij_mul_comm; try auto. rewrite rij_mul_len; auto. }  rewrite H54. clear H54.
    assert (rij_mul c (rij_mul a3 b3) = rij_mul (rij_mul a3 b3) c). 
    { rewrite rij_mul_comm; try auto. rewrite rij_mul_len; auto. }  rewrite H54. clear H54.
    assert (rij_mul c (rij_mul a4 b4) = rij_mul (rij_mul a4 b4) c). 
    { rewrite rij_mul_comm; try auto. rewrite rij_mul_len; auto. }  rewrite H54. clear H54.
    auto. auto. rewrite rij_mul_len; auto. }
  repeat rewrite H5; try assumption. clear H3 H4 H5.
  rewrite rij_mul_assoc';auto;               set (d1:=rij_mul (rij_mul y11 x11) z1);
  rewrite rij_mul_assoc' with (a:=y12);auto; set (d2:=rij_mul (rij_mul y12 x11) z2);
  rewrite rij_mul_assoc' with (a:=y13);auto; set (d3:=rij_mul (rij_mul y13 x11) z3);
  rewrite rij_mul_assoc' with (a:=y14);auto; set (d4:=rij_mul (rij_mul y14 x11) z4);
  rewrite rij_mul_assoc' with (a:=y21);auto; set (d5:=rij_mul (rij_mul y21 x12) z1);
  rewrite rij_mul_assoc' with (a:=y22);auto; set (d6:=rij_mul (rij_mul y22 x12) z2);
  rewrite rij_mul_assoc' with (a:=y23);auto; set (d7:=rij_mul (rij_mul y23 x12) z3);
  rewrite rij_mul_assoc' with (a:=y24);auto; set (d8:=rij_mul (rij_mul y24 x12) z4);
  rewrite rij_mul_assoc' with (a:=y31);auto; set (d9:=rij_mul (rij_mul y31 x13) z1);
  rewrite rij_mul_assoc' with (a:=y32);auto; set (d10:=rij_mul (rij_mul y32 x13) z2);
  rewrite rij_mul_assoc' with (a:=y33);auto; set (d11:=rij_mul (rij_mul y33 x13) z3);
  rewrite rij_mul_assoc' with (a:=y34);auto; set (d12:=rij_mul (rij_mul y34 x13) z4);
  rewrite rij_mul_assoc' with (a:=y41);auto; set (d13:=rij_mul (rij_mul y41 x14) z1);
  rewrite rij_mul_assoc' with (a:=y42);auto; set (d14:=rij_mul (rij_mul y42 x14) z2);
  rewrite rij_mul_assoc' with (a:=y43);auto; set (d15:=rij_mul (rij_mul y43 x14) z3);
  rewrite rij_mul_assoc' with (a:=y44);auto; set (d16:=rij_mul (rij_mul y44 x14) z4);
  rewrite rij_mul_assoc' with (a:=y11);auto; set (d17:=rij_mul (rij_mul y11 x21) z1);
  rewrite rij_mul_assoc' with (a:=y12);auto; set (d18:=rij_mul (rij_mul y12 x21) z2);
  rewrite rij_mul_assoc' with (a:=y13);auto; set (d19:=rij_mul (rij_mul y13 x21) z3);
  rewrite rij_mul_assoc' with (a:=y14);auto; set (d20:=rij_mul (rij_mul y14 x21) z4);
  rewrite rij_mul_assoc' with (a:=y21);auto; set (d21:=rij_mul (rij_mul y21 x22) z1);
  rewrite rij_mul_assoc' with (a:=y22);auto; set (d22:=rij_mul (rij_mul y22 x22) z2);
  rewrite rij_mul_assoc' with (a:=y23);auto; set (d23:=rij_mul (rij_mul y23 x22) z3);
  rewrite rij_mul_assoc' with (a:=y24);auto; set (d24:=rij_mul (rij_mul y24 x22) z4);
  rewrite rij_mul_assoc' with (a:=y31);auto; set (d25:=rij_mul (rij_mul y31 x23) z1);
  rewrite rij_mul_assoc' with (a:=y32);auto; set (d26:=rij_mul (rij_mul y32 x23) z2);
  rewrite rij_mul_assoc' with (a:=y33);auto; set (d27:=rij_mul (rij_mul y33 x23) z3);
  rewrite rij_mul_assoc' with (a:=y34);auto; set (d28:=rij_mul (rij_mul y34 x23) z4);
  rewrite rij_mul_assoc' with (a:=y41);auto; set (d29:=rij_mul (rij_mul y41 x24) z1);
  rewrite rij_mul_assoc' with (a:=y42);auto; set (d30:=rij_mul (rij_mul y42 x24) z2);
  rewrite rij_mul_assoc' with (a:=y43);auto; set (d31:=rij_mul (rij_mul y43 x24) z3);
  rewrite rij_mul_assoc' with (a:=y44);auto; set (d32:=rij_mul (rij_mul y44 x24) z4);
  rewrite rij_mul_assoc' with (a:=y11);auto; set (d33:=rij_mul (rij_mul y11 x31) z1);
  rewrite rij_mul_assoc' with (a:=y12);auto; set (d34:=rij_mul (rij_mul y12 x31) z2);
  rewrite rij_mul_assoc' with (a:=y13);auto; set (d35:=rij_mul (rij_mul y13 x31) z3);
  rewrite rij_mul_assoc' with (a:=y14);auto; set (d36:=rij_mul (rij_mul y14 x31) z4);
  rewrite rij_mul_assoc' with (a:=y21);auto; set (d37:=rij_mul (rij_mul y21 x32) z1);
  rewrite rij_mul_assoc' with (a:=y22);auto; set (d38:=rij_mul (rij_mul y22 x32) z2);
  rewrite rij_mul_assoc' with (a:=y23);auto; set (d39:=rij_mul (rij_mul y23 x32) z3);
  rewrite rij_mul_assoc' with (a:=y24);auto; set (d40:=rij_mul (rij_mul y24 x32) z4);
  rewrite rij_mul_assoc' with (a:=y31);auto; set (d41:=rij_mul (rij_mul y31 x33) z1);
  rewrite rij_mul_assoc' with (a:=y32);auto; set (d42:=rij_mul (rij_mul y32 x33) z2);
  rewrite rij_mul_assoc' with (a:=y33);auto; set (d43:=rij_mul (rij_mul y33 x33) z3);
  rewrite rij_mul_assoc' with (a:=y34);auto; set (d44:=rij_mul (rij_mul y34 x33) z4);
  rewrite rij_mul_assoc' with (a:=y41);auto; set (d45:=rij_mul (rij_mul y41 x34) z1);
  rewrite rij_mul_assoc' with (a:=y42);auto; set (d46:=rij_mul (rij_mul y42 x34) z2);
  rewrite rij_mul_assoc' with (a:=y43);auto; set (d47:=rij_mul (rij_mul y43 x34) z3);
  rewrite rij_mul_assoc' with (a:=y44);auto; set (d48:=rij_mul (rij_mul y44 x34) z4);
  rewrite rij_mul_assoc' with (a:=y11);auto; set (d49:=rij_mul (rij_mul y11 x41) z1);
  rewrite rij_mul_assoc' with (a:=y12);auto; set (d50:=rij_mul (rij_mul y12 x41) z2);
  rewrite rij_mul_assoc' with (a:=y13);auto; set (d51:=rij_mul (rij_mul y13 x41) z3);
  rewrite rij_mul_assoc' with (a:=y14);auto; set (d52:=rij_mul (rij_mul y14 x41) z4);
  rewrite rij_mul_assoc' with (a:=y21);auto; set (d53:=rij_mul (rij_mul y21 x42) z1);
  rewrite rij_mul_assoc' with (a:=y22);auto; set (d54:=rij_mul (rij_mul y22 x42) z2);
  rewrite rij_mul_assoc' with (a:=y23);auto; set (d55:=rij_mul (rij_mul y23 x42) z3);
  rewrite rij_mul_assoc' with (a:=y24);auto; set (d56:=rij_mul (rij_mul y24 x42) z4);
  rewrite rij_mul_assoc' with (a:=y31);auto; set (d57:=rij_mul (rij_mul y31 x43) z1);
  rewrite rij_mul_assoc' with (a:=y32);auto; set (d58:=rij_mul (rij_mul y32 x43) z2);
  rewrite rij_mul_assoc' with (a:=y33);auto; set (d59:=rij_mul (rij_mul y33 x43) z3);
  rewrite rij_mul_assoc' with (a:=y34);auto; set (d60:=rij_mul (rij_mul y34 x43) z4);
  rewrite rij_mul_assoc' with (a:=y41);auto; set (d61:=rij_mul (rij_mul y41 x44) z1);
  rewrite rij_mul_assoc' with (a:=y42);auto; set (d62:=rij_mul (rij_mul y42 x44) z2);
  rewrite rij_mul_assoc' with (a:=y43);auto; set (d63:=rij_mul (rij_mul y43 x44) z3);
  rewrite rij_mul_assoc' with (a:=y44);auto; set (d64:=rij_mul (rij_mul y44 x44) z4).
  clear. f_equal.
  assert (rij_add (rij_add (rij_add (rij_add d1 d2) d3) d4)
   (rij_add (rij_add (rij_add (rij_add d5 d6) d7) d8)
      (rij_add (rij_add (rij_add (rij_add d9 d10) d11) d12) (rij_add (rij_add (rij_add d13 d14) d15) d16)))
  = rij_add (rij_add (rij_add (rij_add d1 d5) d9) d13)
   (rij_add (rij_add (rij_add (rij_add d2 d6) d10) d14)
      (rij_add (rij_add (rij_add (rij_add d3 d7) d11) d15) (rij_add (rij_add (rij_add d4 d8) d12) d16)))).
  { repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal. }
  rewrite H; clear H; f_equal.
  assert (rij_add (rij_add (rij_add (rij_add d17 d18) d19) d20)
   (rij_add (rij_add (rij_add (rij_add d21 d22) d23) d24)
      (rij_add (rij_add (rij_add (rij_add d25 d26) d27) d28)
         (rij_add (rij_add (rij_add d29 d30) d31) d32)))
  = rij_add (rij_add (rij_add (rij_add d17 d21) d25) d29)
   (rij_add (rij_add (rij_add (rij_add d18 d22) d26) d30)
      (rij_add (rij_add (rij_add (rij_add d19 d23) d27) d31)
         (rij_add (rij_add (rij_add d20 d24) d28) d32)))).
  { repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal. }
  rewrite H; clear H; f_equal.
  assert(rij_add (rij_add (rij_add (rij_add d33 d34) d35) d36)
   (rij_add (rij_add (rij_add (rij_add d37 d38) d39) d40)
      (rij_add (rij_add (rij_add (rij_add d41 d42) d43) d44)
         (rij_add (rij_add (rij_add d45 d46) d47) d48)))
  = rij_add (rij_add (rij_add (rij_add d33 d37) d41) d45)
   (rij_add (rij_add (rij_add (rij_add d34 d38) d42) d46)
      (rij_add (rij_add (rij_add (rij_add d35 d39) d43) d47)
         (rij_add (rij_add (rij_add d36 d40) d44) d48)))).
  { repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
    rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal. }
  rewrite H; clear H; f_equal.
  repeat (rewrite <- rij_add_assoc). f_equal. f_equal. f_equal.
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc).
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
  rewrite rij_add_comm. repeat (rewrite <- rij_add_assoc). f_equal.
Qed.


Lemma mmult_unit: forall a1 a2 a3 a4 : Poly,
  let ma := a1::a2::a3::a4::nil in
  length a1 = 8 -> length a2 = 8 -> length a3 = 8 -> length a4 = 8 ->
  mmult mat_unit (split ma 4) = split ma 4.
Proof.
  intros. unfold ma. unfold mat_unit. simpl (matrix_n2p mat_unit_nat).
  rewrite mmult_ma_cv;try easy. repeat (rewrite dot4). rewrite split4.
  unfold gsum,gtimes. rewrite split4.
  replace (n2p 0) with rij_0. repeat (rewrite rij_mul_rij_0_left).
  simpl fold_left. repeat (rewrite rij_add_rij_0_left8); try (apply rij_mul_len; auto).
  repeat (rewrite rij_add_rij_0_right8); try (apply rij_mul_len; auto). repeat f_equal.
  replace (n2p 1) with (false :: false :: false :: false :: false :: false :: false :: true :: nil).
  apply length8 in H; destruct H as [b1 H3]; destruct H3 as [b2 H4]; destruct H4 as [b3 H5];
  destruct H5 as [b4 H6]; destruct H6 as [b5 H7]; destruct H7 as [b6 H8];
  destruct H8 as [b7 H9]; destruct H9 as [b8 H10]; rewrite H10;
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto. auto.
  apply length8 in H0; destruct H0 as [b1 H3]; destruct H3 as [b2 H4]; destruct H4 as [b3 H5];
  destruct H5 as [b4 H6]; destruct H6 as [b5 H7]; destruct H7 as [b6 H8];
  destruct H8 as [b7 H9]; destruct H9 as [b8 H10]; rewrite H10;
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  apply length8 in H1. destruct H1 as [b1 H3]; destruct H3 as [b2 H4]; destruct H4 as [b3 H5];
  destruct H5 as [b4 H6]; destruct H6 as [b5 H7]; destruct H7 as [b6 H8];
  destruct H8 as [b7 H9]; destruct H9 as [b8 H10]; rewrite H10;
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto.
  apply length8 in H2; destruct H2 as [b1 H3]; destruct H3 as [b2 H4]; destruct H4 as [b3 H5];
  destruct H5 as [b4 H6]; destruct H6 as [b5 H7]; destruct H7 as [b6 H8];
  destruct H8 as [b7 H9]; destruct H9 as [b8 H10]; rewrite H10;
  case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; auto. auto.
Qed.

Lemma transpose_ok : 
  forall  a11 a12 a13 a14 
          a21 a22 a23 a24
          a31 a32 a33 a34
          a41 a42 a43 a44 : Poly,
	  let a1 := a11::a12::a13::a14::nil in
	  let a2 := a21::a22::a23::a24::nil in
	  let a3 := a31::a32::a33::a34::nil in
	  let a4 := a41::a42::a43::a44::nil in
          let s := a1::a2::a3::a4::nil in
  transpose (transpose s) = s.
Proof. intros. easy. Qed.

Lemma transpose_len : 
  forall a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44,
    let a1:= a11::a12::a13::a14::nil in 
    let a2:= a21::a22::a23::a24::nil in
    let a3:= a31::a32::a33::a34::nil in
    let a4:= a41::a42::a43::a44::nil in
    let s:= a1::a2::a3::a4::nil in
  length (transpose s) = 4 -> is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 ->
  exists b11 b12 b13 b14 b21 b22 b23 b24 b31 b32 b33 b34 b41 b42 b43 b44 : Poly, 
  transpose s = (b11::b12::b13::b14::nil)::(b21::b22::b23::b24::nil)::
              (b31::b32::b33::b34::nil)::(b41::b42::b43::b44::nil)::nil
  /\ is_veclen8 (b11::b12::b13::b14::nil) /\ is_veclen8 (b21::b22::b23::b24::nil)
  /\ is_veclen8 (b31::b32::b33::b34::nil) /\ is_veclen8 (b41::b42::b43::b44::nil).
Proof. 
intros. simpl in *. unfold mk_list.
exists a11;exists a21;exists a31;exists a41;exists a12;exists a22;exists a32;exists a42;
exists a13;exists a23;exists a33;exists a43;exists a14;exists a24;exists a34;exists a44;easy.
Qed.

Lemma sbox_invSbox : forall (s:Poly),
  length s=8 -> inv_sbox_sel (sbox_sel s) = s.
Proof.
intros. apply length8 in H. do 8 destruct H. rewrite H.
case x; case x0; case x1; case x2; case x3; case x4; case x5; case x6; auto.
Qed.



(* Reversibility of byteSub *)
Lemma byteSub_correct : 
  forall a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44,
  let a1:= a11::a12::a13::a14::nil in 
  let a2:= a21::a22::a23::a24::nil in
  let a3:= a31::a32::a33::a34::nil in
  let a4:= a41::a42::a43::a44::nil in
  let s:= a1::a2::a3::a4::nil in
  is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 ->
  invByteSub (byteSub s) = s.
Proof.
  intros. unfold byteSub, invByteSub. unfold s. unfold a1,a2,a3,a4.
  simpl in *. repeat rewrite sbox_invSbox;easy.
Qed. 

(* Reversibility of shifwRow *)
Lemma shiftRow_correct : forall a : Matrix,
  length a = 4 -> invShiftRow (shiftRow a) = a.
Proof.
intros. induction a as [|a0 a1]. auto. unfold shiftRow,invShiftRow. simpl.
f_equal. unfold ror. unfold rotate_righti. unfold rotate_lefti.
rewrite rev_involutive. auto. 
induction a1 as [|a1 a2]. auto. simpl. f_equal. unfold ror.
assert (forall l : list Poly, rotate_righti Poly l 1 = rotate_right l). auto.
rewrite H0. rewrite rotate_right_left. auto.
induction a2 as [|a2 a3]. auto. simpl. f_equal. unfold ror.
assert (forall l:list Poly, rotate_righti Poly l 2 = rotate_right (rotate_right l)).
intro. unfold rotate_righti,rotate_right. unfold rotate_lefti. rewrite rev_involutive. auto.
rewrite H0. repeat rewrite rotate_right_left. auto.
induction a3 as [|a3 a4]. auto. simpl. f_equal.
assert (forall l:list Poly, rotate_righti Poly l 3 = rotate_right (rotate_right (rotate_right l))).
intro. unfold rotate_righti,rotate_right. repeat rewrite rev_involutive. auto.
rewrite H0. repeat rewrite rotate_right_left. auto.
inversion H. apply simple.length_nil in H1. rewrite H1. auto.
Qed.



(* Reversibility of mixColumn *)
Lemma mixColumn_correct :
  forall a11 a12 a13 a14 
         a21 a22 a23 a24
         a31 a32 a33 a34
         a41 a42 a43 a44,
  let a1:= a11::a12::a13::a14::nil in 
  let a2:= a21::a22::a23::a24::nil in
  let a3:= a31::a32::a33::a34::nil in
  let a4:= a41::a42::a43::a44::nil in
  let s:= a1::a2::a3::a4::nil in
  is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 ->
	   invMixColumn (mixColumn s) = s.
Proof.
intros. simpl in H,H0,H1,H2. unfold mixColumn, invMixColumn.
assert (transpose (transpose (map (fun col : Vec => multCol cx col) (transpose s)))=map (fun col : Vec => multCol cx col) (transpose s)).
{ assert (length(transpose s)=4). auto. apply transpose_len in H3;try easy. }
rewrite H3;clear H3.
assert(map (fun col : Vec => multCol icx col) (map (fun col : Vec => multCol cx col) (transpose s))=transpose s).
{ assert (length(transpose s)=4). auto. apply transpose_len in H3;try easy. do 17 destruct H3.
  unfold s. unfold a1,a2,a3,a4. rewrite H3;clear H3. simpl. unfold multCol.
  replace(split (join (mmult cx (split (x :: x0 :: x1 :: x2 :: nil) 4))) 4)with(mmult cx (split (x :: x0 :: x1 :: x2 :: nil) 4));
  replace(split (join (mmult cx (split (x3 :: x4 :: x5 :: x6 :: nil) 4))) 4)with(mmult cx (split (x3 :: x4 :: x5 :: x6 :: nil) 4));
  replace(split (join (mmult cx (split (x7 :: x8 :: x9 :: x10 :: nil) 4))) 4)with(mmult cx (split (x7 :: x8 :: x9 :: x10 :: nil) 4));
  replace(split (join (mmult cx (split (x11 :: x12 :: x13 :: x14 :: nil) 4))) 4)with(mmult cx (split (x11 :: x12 :: x13 :: x14 :: nil) 4));try easy.
  assert(forall y1 y2 y3 y4:Poly, length y1=8 -> length y2=8 -> length y3=8-> length y4=8 -> mmult icx (mmult cx (split (y1 :: y2 :: y3 :: y4 :: nil) 4))=mmult (mmult icx cx) (split (y1 :: y2 :: y3 :: y4 :: nil) 4)).
  { intros. unfold cx; simpl (transpose (polyMat mat_start)); unfold mk_list; unfold icx; simpl (transpose (polyMat invmat_start)); unfold mk_list.
    rewrite mmult_assoc;try easy. } 
  destruct H4 as [H5 [H6 [H7 H8]]]. simpl in H5,H6,H7,H8.
  repeat rewrite H3;try easy; repeat rewrite icx_cx; repeat rewrite mmult_unit;try easy. }
rewrite H3;clear H3. unfold s. unfold a1,a2,a3,a4. rewrite transpose_ok. auto.
Qed.


(* Reversibility of AddRoundKey *)
Lemma matrix_add_correct :
  forall a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44
         b11 b12 b13 b14 b21 b22 b23 b24 b31 b32 b33 b34 b41 b42 b43 b44 : Poly,
  let a1:=a11::a12::a13::a14::nil in
  let a2:=a21::a22::a23::a24::nil in
  let a3:=a31::a32::a33::a34::nil in
  let a4:=a41::a42::a43::a44::nil in
    let a:= a1::a2::a3::a4::nil in
  let b1:=b11::b12::b13::b14::nil in
  let b2:=b21::b22::b23::b24::nil in
  let b3:=b31::b32::b33::b34::nil in
  let b4:=b41::b42::b43::b44::nil in
    let b:= b1::b2::b3::b4::nil in
    is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 ->
    is_veclen8 b1 -> is_veclen8 b2 -> is_veclen8 b3 -> is_veclen8 b4 ->
   matrix_add (matrix_add a b) b = a.
Proof.
intros. unfold matrix_add,a,b. unfold a1,a2,a3,a4,b1,b2,b3,b4. simpl.
unfold vec_add. simpl in *. unfold rij_add.
assert (forall x y:Poly, length x = 8 -> length y = 8 -> map2 Z2_add (map2 Z2_add x y) y = x).
{ intros. apply length8 in H7,H8. do 8 destruct H7;do 8 destruct H8. rewrite H7;rewrite H8.
  case x0. case x1. case x2. case x3. case x4. case x5. case x6. case x7.
  case x8. case x9. case x10. case x11. case x12. case x13. case x14. case x15.
  auto. auto. case x15; try (repeat auto).
  case x14; case x15; try (repeat auto).
  case x13; case x14; case x15; try (repeat auto).
  case x12; case x13; case x14; case x15; try (repeat auto).
  case x11; case x12; case x13; case x14; case x15; try (repeat auto).
  case x10; case x11; case x12; case x13; case x14; case x15; try (repeat auto).
  case x9; case x10; case x11; case x12; case x13; case x14; case x15; try (repeat auto).
  case x8; case x9; case x10; case x11; case x12; case x13; case x14; case x15; try (repeat auto).
  case x7; case x8; case x9; case x10; case x11; case x12; case x13; case x14; case x15; try (repeat auto).
  case x6; case x7; case x8; case x9; case x10; case x11; case x12; case x13; case x14; case x15; try (repeat auto).
  case x5; case x6; case x7; case x8; case x9; case x10; case x11; case x12; case x13; case x14; case x15; try (repeat auto).
  case x4; case x5; case x6; case x7; case x8; case x9; case x10; case x11; case x12; case x13; case x14; case x15; try (repeat auto).
  case x3; case x4; case x5; case x6; case x7; case x8; case x9; case x10; case x11; case x12; case x13; case x14; case x15; try (repeat auto).
  case x2; case x3; case x4; case x5; case x6; case x7; case x8; case x9; case x10; case x11; case x12; case x13; case x14; case x15; try (repeat auto).
  case x1; case x2; case x3; case x4; case x5; case x6; case x7; case x8; case x9; case x10; case x11; case x12; case x13; case x14; case x15; try (repeat auto). }
repeat rewrite H7;easy.
Qed.


Lemma sbox_sel_len8 : forall a:Poly, length a = 8 -> length (sbox_sel a) = 8.
Proof.
intros. apply length8 in H. do 8 destruct H. rewrite H;clear H.
case x;case x0;case x1;case x2;case x3;case x4;case x5;case x6; auto.
Qed.


Lemma byteSub_len : 
    forall a11 a12 a13 a14 a21 a22 a23 a24
           a31 a32 a33 a34 a41 a42 a43 a44 : Poly,
    let a1:=a11::a12::a13::a14::nil in
    let a2:=a21::a22::a23::a24::nil in
    let a3:=a31::a32::a33::a34::nil in
    let a4:=a41::a42::a43::a44::nil in
      let a:= a1::a2::a3::a4::nil in
  length (byteSub a) = 4 -> is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 ->
  exists b11 b12 b13 b14 b21 b22 b23 b24 b31 b32 b33 b34 b41 b42 b43 b44 : Poly, 
  byteSub a = (b11::b12::b13::b14::nil)::(b21::b22::b23::b24::nil)::
              (b31::b32::b33::b34::nil)::(b41::b42::b43::b44::nil)::nil
  /\ is_veclen8 (b11::b12::b13::b14::nil) /\ is_veclen8 (b21::b22::b23::b24::nil)
  /\ is_veclen8 (b31::b32::b33::b34::nil) /\ is_veclen8 (b41::b42::b43::b44::nil).
Proof.
intros. unfold byteSub. simpl in *.
exists (sbox_sel a11); exists (sbox_sel a12); exists (sbox_sel a13); exists (sbox_sel a14);
exists (sbox_sel a21); exists (sbox_sel a22); exists (sbox_sel a23); exists (sbox_sel a24);
exists (sbox_sel a31); exists (sbox_sel a32); exists (sbox_sel a33); exists (sbox_sel a34);
exists (sbox_sel a41); exists (sbox_sel a42); exists (sbox_sel a43); exists (sbox_sel a44);
try repeat split; apply sbox_sel_len8; easy. 
Qed.



Lemma shiftRow_len :
    forall a11 a12 a13 a14 a21 a22 a23 a24
           a31 a32 a33 a34 a41 a42 a43 a44 : Poly,
    let a1:=a11::a12::a13::a14::nil in
    let a2:=a21::a22::a23::a24::nil in
    let a3:=a31::a32::a33::a34::nil in
    let a4:=a41::a42::a43::a44::nil in
      let a:= a1::a2::a3::a4::nil in
    length (shiftRow a) = 4 -> is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 ->
    exists b11 b12 b13 b14 b21 b22 b23 b24 b31 b32 b33 b34 b41 b42 b43 b44 : Poly, 
     shiftRow a = (b11::b12::b13::b14::nil)::(b21::b22::b23::b24::nil)::
                  (b31::b32::b33::b34::nil)::(b41::b42::b43::b44::nil)::nil
    /\ is_veclen8 (b11::b12::b13::b14::nil) /\ is_veclen8 (b21::b22::b23::b24::nil)
    /\ is_veclen8 (b31::b32::b33::b34::nil) /\ is_veclen8 (b41::b42::b43::b44::nil).
Proof.
intros. unfold shiftRow. unfold a. simpl. unfold a1. simpl in *.
exists a11; exists a12; exists a13; exists a14;
exists a22; exists a23; exists a24; exists a21;
exists a33; exists a34; exists a31; exists a32;
exists a44; exists a41; exists a42; exists a43;
try repeat split;easy. 
Qed.


Lemma mixColumn_len : 
  forall a11 a12 a13 a14 a21 a22 a23 a24
         a31 a32 a33 a34 a41 a42 a43 a44 : Poly,
  let a1:=a11::a12::a13::a14::nil in
  let a2:=a21::a22::a23::a24::nil in
  let a3:=a31::a32::a33::a34::nil in
  let a4:=a41::a42::a43::a44::nil in
    let a:= a1::a2::a3::a4::nil in
    length (mixColumn a) = 4 -> is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 ->
    exists b11 b12 b13 b14 b21 b22 b23 b24 b31 b32 b33 b34 b41 b42 b43 b44 : Poly, 
     mixColumn a = (b11::b12::b13::b14::nil)::(b21::b22::b23::b24::nil)::
                   (b31::b32::b33::b34::nil)::(b41::b42::b43::b44::nil)::nil
    /\ is_veclen8 (b11::b12::b13::b14::nil) /\ is_veclen8 (b21::b22::b23::b24::nil)
    /\ is_veclen8 (b31::b32::b33::b34::nil) /\ is_veclen8 (b41::b42::b43::b44::nil).
Proof.
intros. unfold mixColumn. simpl in *. unfold mk_list. 
exists (dot (a11 :: a21 :: a31 :: a41 :: nil) (n2p 2 :: n2p 3 :: n2p 1 :: n2p 1 :: nil));
exists (dot (a12 :: a22 :: a32 :: a42 :: nil) (n2p 2 :: n2p 3 :: n2p 1 :: n2p 1 :: nil));
exists (dot (a13 :: a23 :: a33 :: a43 :: nil) (n2p 2 :: n2p 3 :: n2p 1 :: n2p 1 :: nil));
exists (dot (a14 :: a24 :: a34 :: a44 :: nil) (n2p 2 :: n2p 3 :: n2p 1 :: n2p 1 :: nil));
exists (dot (a11 :: a21 :: a31 :: a41 :: nil) (n2p 1 :: n2p 2 :: n2p 3 :: n2p 1 :: nil));
exists (dot (a12 :: a22 :: a32 :: a42 :: nil) (n2p 1 :: n2p 2 :: n2p 3 :: n2p 1 :: nil));
exists (dot (a13 :: a23 :: a33 :: a43 :: nil) (n2p 1 :: n2p 2 :: n2p 3 :: n2p 1 :: nil));
exists (dot (a14 :: a24 :: a34 :: a44 :: nil) (n2p 1 :: n2p 2 :: n2p 3 :: n2p 1 :: nil));
exists (dot (a11 :: a21 :: a31 :: a41 :: nil) (n2p 1 :: n2p 1 :: n2p 2 :: n2p 3 :: nil));
exists (dot (a12 :: a22 :: a32 :: a42 :: nil) (n2p 1 :: n2p 1 :: n2p 2 :: n2p 3 :: nil));
exists (dot (a13 :: a23 :: a33 :: a43 :: nil) (n2p 1 :: n2p 1 :: n2p 2 :: n2p 3 :: nil));
exists (dot (a14 :: a24 :: a34 :: a44 :: nil) (n2p 1 :: n2p 1 :: n2p 2 :: n2p 3 :: nil));
exists (dot (a11 :: a21 :: a31 :: a41 :: nil) (n2p 3 :: n2p 1 :: n2p 1 :: n2p 2 :: nil));
exists (dot (a12 :: a22 :: a32 :: a42 :: nil) (n2p 3 :: n2p 1 :: n2p 1 :: n2p 2 :: nil));
exists (dot (a13 :: a23 :: a33 :: a43 :: nil) (n2p 3 :: n2p 1 :: n2p 1 :: n2p 2 :: nil));
exists (dot (a14 :: a24 :: a34 :: a44 :: nil) (n2p 3 :: n2p 1 :: n2p 1 :: n2p 2 :: nil)).
try repeat split; rewrite dot4; try replace gtimes with rij_mul; try unfold gsum;
simpl; try rewrite rij_add_rij_0_left8; try repeat rewrite rij_add_len8; try easy;
rewrite rij_mul_len;easy.
Qed.

Lemma matrix_add_len : 
  forall a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44
         b11 b12 b13 b14 b21 b22 b23 b24 b31 b32 b33 b34 b41 b42 b43 b44 : Poly,
  let a1:=a11::a12::a13::a14::nil in
  let a2:=a21::a22::a23::a24::nil in
  let a3:=a31::a32::a33::a34::nil in
  let a4:=a41::a42::a43::a44::nil in
    let a:= a1::a2::a3::a4::nil in
  let b1:=b11::b12::b13::b14::nil in
  let b2:=b21::b22::b23::b24::nil in
  let b3:=b31::b32::b33::b34::nil in
  let b4:=b41::b42::b43::b44::nil in
    let b:= b1::b2::b3::b4::nil in
    length (matrix_add a b) = 4 -> 
    is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 ->
    is_veclen8 b1 -> is_veclen8 b2 -> is_veclen8 b3 -> is_veclen8 b4 ->
    exists c11 c12 c13 c14 c21 c22 c23 c24 c31 c32 c33 c34 c41 c42 c43 c44 : Poly, 
     matrix_add a b = (c11::c12::c13::c14::nil)::(c21::c22::c23::c24::nil)::
                      (c31::c32::c33::c34::nil)::(c41::c42::c43::c44::nil)::nil
    /\ is_veclen8 (c11::c12::c13::c14::nil) /\ is_veclen8 (c21::c22::c23::c24::nil)
    /\ is_veclen8 (c31::c32::c33::c34::nil) /\ is_veclen8 (c41::c42::c43::c44::nil).
Proof.
intros. unfold matrix_add,a,b. unfold a1,a2,a3,a4,b1,b2,b3,b4. unfold vec_add. simpl in *.
exists (rij_add a11 b11); exists(rij_add a12 b12);exists (rij_add a13 b13);exists (rij_add a14 b14);
exists (rij_add a21 b21);exists (rij_add a22 b22);exists (rij_add a23 b23);exists (rij_add a24 b24);
exists (rij_add a31 b31);exists (rij_add a32 b32);exists (rij_add a33 b33);exists (rij_add a34 b34);
exists (rij_add a41 b41);exists (rij_add a42 b42);exists (rij_add a43 b43);exists (rij_add a44 b44);
try repeat split; try rewrite rij_add_len8; easy.
Qed.


Lemma round_len : 
 forall a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 
        b11 b12 b13 b14 b21 b22 b23 b24 b31 b32 b33 b34 b41 b42 b43 b44 : Poly, 
  let a1:=a11::a12::a13::a14::nil in
  let a2:=a21::a22::a23::a24::nil in
  let a3:=a31::a32::a33::a34::nil in
  let a4:=a41::a42::a43::a44::nil in
  let b1:=b11::b12::b13::b14::nil in
  let b2:=b21::b22::b23::b24::nil in
  let b3:=b31::b32::b33::b34::nil in
  let b4:=b41::b42::b43::b44::nil in
    let a:=a1::a2::a3::a4::nil in
    let b:=b1::b2::b3::b4::nil in
    length (round a b) = 4 -> 
    is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 ->
    is_veclen8 b1 -> is_veclen8 b2 -> is_veclen8 b3 -> is_veclen8 b4 ->
    exists c11 c12 c13 c14 c21 c22 c23 c24 c31 c32 c33 c34 c41 c42 c43 c44 : Poly, 
     round a b = (c11::c12::c13::c14::nil)::(c21::c22::c23::c24::nil)::
                 (c31::c32::c33::c34::nil)::(c41::c42::c43::c44::nil)::nil
    /\ is_veclen8 (c11::c12::c13::c14::nil) /\ is_veclen8 (c21::c22::c23::c24::nil)
    /\ is_veclen8 (c31::c32::c33::c34::nil) /\ is_veclen8 (c41::c42::c43::c44::nil).
Proof.
intros. unfold round. assert (length (byteSub a) = 4). auto. apply byteSub_len in H8;try easy.
simpl. unfold shiftRow. simpl. unfold mixColumn. simpl. unfold mk_list. unfold b. 
unfold b1,b2,b3,b4. unfold matrix_add. simpl. unfold vec_add. simpl in *.
exists (rij_add (dot (sbox_sel a11 :: sbox_sel a22 :: sbox_sel a33 :: sbox_sel a44 :: nil) (n2p 2 :: n2p 3 :: n2p 1 :: n2p 1 :: nil)) b11);
exists (rij_add (dot (sbox_sel a12 :: sbox_sel a23 :: sbox_sel a34 :: sbox_sel a41 :: nil) (n2p 2 :: n2p 3 :: n2p 1 :: n2p 1 :: nil)) b12);
exists (rij_add (dot (sbox_sel a13 :: sbox_sel a24 :: sbox_sel a31 :: sbox_sel a42 :: nil) (n2p 2 :: n2p 3 :: n2p 1 :: n2p 1 :: nil)) b13);
exists (rij_add (dot (sbox_sel a14 :: sbox_sel a21 :: sbox_sel a32 :: sbox_sel a43 :: nil) (n2p 2 :: n2p 3 :: n2p 1 :: n2p 1 :: nil)) b14);
exists (rij_add (dot (sbox_sel a11 :: sbox_sel a22 :: sbox_sel a33 :: sbox_sel a44 :: nil) (n2p 1 :: n2p 2 :: n2p 3 :: n2p 1 :: nil)) b21);
exists (rij_add (dot (sbox_sel a12 :: sbox_sel a23 :: sbox_sel a34 :: sbox_sel a41 :: nil) (n2p 1 :: n2p 2 :: n2p 3 :: n2p 1 :: nil)) b22);
exists (rij_add (dot (sbox_sel a13 :: sbox_sel a24 :: sbox_sel a31 :: sbox_sel a42 :: nil) (n2p 1 :: n2p 2 :: n2p 3 :: n2p 1 :: nil)) b23);
exists (rij_add (dot (sbox_sel a14 :: sbox_sel a21 :: sbox_sel a32 :: sbox_sel a43 :: nil) (n2p 1 :: n2p 2 :: n2p 3 :: n2p 1 :: nil)) b24);
exists (rij_add (dot (sbox_sel a11 :: sbox_sel a22 :: sbox_sel a33 :: sbox_sel a44 :: nil) (n2p 1 :: n2p 1 :: n2p 2 :: n2p 3 :: nil)) b31);
exists (rij_add (dot (sbox_sel a12 :: sbox_sel a23 :: sbox_sel a34 :: sbox_sel a41 :: nil) (n2p 1 :: n2p 1 :: n2p 2 :: n2p 3 :: nil)) b32);
exists (rij_add (dot (sbox_sel a13 :: sbox_sel a24 :: sbox_sel a31 :: sbox_sel a42 :: nil) (n2p 1 :: n2p 1 :: n2p 2 :: n2p 3 :: nil)) b33);
exists (rij_add (dot (sbox_sel a14 :: sbox_sel a21 :: sbox_sel a32 :: sbox_sel a43 :: nil) (n2p 1 :: n2p 1 :: n2p 2 :: n2p 3 :: nil)) b34);
exists (rij_add (dot (sbox_sel a11 :: sbox_sel a22 :: sbox_sel a33 :: sbox_sel a44 :: nil) (n2p 3 :: n2p 1 :: n2p 1 :: n2p 2 :: nil)) b41);
exists (rij_add (dot (sbox_sel a12 :: sbox_sel a23 :: sbox_sel a34 :: sbox_sel a41 :: nil) (n2p 3 :: n2p 1 :: n2p 1 :: n2p 2 :: nil)) b42);
exists (rij_add (dot (sbox_sel a13 :: sbox_sel a24 :: sbox_sel a31 :: sbox_sel a42 :: nil) (n2p 3 :: n2p 1 :: n2p 1 :: n2p 2 :: nil)) b43);
exists (rij_add (dot (sbox_sel a14 :: sbox_sel a21 :: sbox_sel a32 :: sbox_sel a43 :: nil) (n2p 3 :: n2p 1 :: n2p 1 :: n2p 2 :: nil)) b44);
try repeat split; auto; try rewrite rij_add_len8; auto; try rewrite dot4; 
try replace gtimes with rij_mul;try unfold gsum;simpl; try rewrite rij_add_rij_0_left8;
try repeat rewrite rij_add_len8; auto; try rewrite rij_mul_len;auto; try apply sbox_sel_len8;try easy.
Qed.



Lemma mk_rnds_len:
  forall a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44
         k111 k112 k113 k114 k121 k122 k123 k124 k131 k132 k133 k134 k141 k142 k143 k144 
         k211 k212 k213 k214 k221 k222 k223 k224 k231 k232 k233 k234 k241 k242 k243 k244
         k311 k312 k313 k314 k321 k322 k323 k324 k331 k332 k333 k334 k341 k342 k343 k344
         k411 k412 k413 k414 k421 k422 k423 k424 k431 k432 k433 k434 k441 k442 k443 k444
         k511 k512 k513 k514 k521 k522 k523 k524 k531 k532 k533 k534 k541 k542 k543 k544
         k611 k612 k613 k614 k621 k622 k623 k624 k631 k632 k633 k634 k641 k642 k643 k644 
         k711 k712 k713 k714 k721 k722 k723 k724 k731 k732 k733 k734 k741 k742 k743 k744
         k811 k812 k813 k814 k821 k822 k823 k824 k831 k832 k833 k834 k841 k842 k843 k844
         k911 k912 k913 k914 k921 k922 k923 k924 k931 k932 k933 k934 k941 k942 k943 k944 : Poly,
    let a1:=a11::a12::a13::a14::nil in         let a2:=a21::a22::a23::a24::nil in
    let a3:=a31::a32::a33::a34::nil in         let a4:=a41::a42::a43::a44::nil in
      let a:=a1::a2::a3::a4::nil in
    let k11:=k111::k112::k113::k114::nil in    let k12:=k121::k122::k123::k124::nil in
    let k13:=k131::k132::k133::k134::nil in    let k14:=k141::k142::k143::k144::nil in
    let k21:=k211::k212::k213::k214::nil in    let k22:=k221::k222::k223::k224::nil in
    let k23:=k231::k232::k233::k234::nil in    let k24:=k241::k242::k243::k244::nil in
    let k31:=k311::k312::k313::k314::nil in    let k32:=k321::k322::k323::k324::nil in
    let k33:=k331::k332::k333::k334::nil in    let k34:=k341::k342::k343::k344::nil in
    let k41:=k411::k412::k413::k414::nil in    let k42:=k421::k422::k423::k424::nil in
    let k43:=k431::k432::k433::k434::nil in    let k44:=k441::k442::k443::k444::nil in
    let k51:=k511::k512::k513::k514::nil in    let k52:=k521::k522::k523::k524::nil in
    let k53:=k531::k532::k533::k534::nil in    let k54:=k541::k542::k543::k544::nil in
    let k61:=k611::k612::k613::k614::nil in    let k62:=k621::k622::k623::k624::nil in
    let k63:=k631::k632::k633::k634::nil in    let k64:=k641::k642::k643::k644::nil in
    let k71:=k711::k712::k713::k714::nil in    let k72:=k721::k722::k723::k724::nil in
    let k73:=k731::k732::k733::k734::nil in    let k74:=k741::k742::k743::k744::nil in
    let k81:=k811::k812::k813::k814::nil in    let k82:=k821::k822::k823::k824::nil in
    let k83:=k831::k832::k833::k834::nil in    let k84:=k841::k842::k843::k844::nil in
    let k91:=k911::k912::k913::k914::nil in    let k92:=k921::k922::k923::k924::nil in
    let k93:=k931::k932::k933::k934::nil in    let k94:=k941::k942::k943::k944::nil in
      let k1:=k11::k12::k13::k14::nil in    let k2:=k21::k22::k23::k24::nil in
      let k3:=k31::k32::k33::k34::nil in    let k4:=k41::k42::k43::k44::nil in
      let k5:=k51::k52::k53::k54::nil in    let k6:=k61::k62::k63::k64::nil in
      let k7:=k71::k72::k73::k74::nil in    let k8:=k81::k82::k83::k84::nil in
      let k9:=k91::k92::k93::k94::nil in
      let rndkeys:=k1::k2::k3::k4::k5::k6::k7::k8::k9::nil in
   is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 ->
   is_veclen8 k11 -> is_veclen8 k12 -> is_veclen8 k13 -> is_veclen8 k14 -> is_veclen8 k21 -> is_veclen8 k22 -> is_veclen8 k23 -> is_veclen8 k24 ->
   is_veclen8 k31 -> is_veclen8 k32 -> is_veclen8 k33 -> is_veclen8 k34 -> is_veclen8 k41 -> is_veclen8 k42 -> is_veclen8 k43 -> is_veclen8 k44 ->
   is_veclen8 k51 -> is_veclen8 k52 -> is_veclen8 k53 -> is_veclen8 k54 -> is_veclen8 k61 -> is_veclen8 k62 -> is_veclen8 k63 -> is_veclen8 k64 ->
   is_veclen8 k71 -> is_veclen8 k72 -> is_veclen8 k73 -> is_veclen8 k74 -> is_veclen8 k81 -> is_veclen8 k82 -> is_veclen8 k83 -> is_veclen8 k84 ->
   is_veclen8 k91 -> is_veclen8 k92 -> is_veclen8 k93 -> is_veclen8 k94 ->
   length (mk_rnds a rndkeys) = 4 ->
   exists c11 c12 c13 c14 c21 c22 c23 c24 c31 c32 c33 c34 c41 c42 c43 c44 : Poly, 
   mk_rnds a rndkeys = (c11::c12::c13::c14::nil)::(c21::c22::c23::c24::nil)::
                 (c31::c32::c33::c34::nil)::(c41::c42::c43::c44::nil)::nil
    /\ is_veclen8 (c11::c12::c13::c14::nil) /\ is_veclen8 (c21::c22::c23::c24::nil)
    /\ is_veclen8 (c31::c32::c33::c34::nil) /\ is_veclen8 (c41::c42::c43::c44::nil).
Proof.
intros. unfold rndkeys. unfold mk_rnds.
simpl in H,H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15,H16,H17,H18,H19,H20,
         H21,H22,H23,H24,H25,H26,H27,H28,H29,H30,H31,H32,H33,H34,H35,H36,H37,H38.
assert (length (round a k1) = 4). auto. apply round_len in H40; auto.
do 17 destruct H40. unfold a,k1. unfold a1,a2,a3,a4.
replace (round((a11 :: a12 :: a13 :: a14 :: nil) :: (a21 :: a22 :: a23 :: a24 :: nil):: (a31 :: a32 :: a33 :: a34 :: nil) :: (a41 :: a42 :: a43 :: a44 :: nil) :: nil)(k11 :: k12 :: k13 :: k14 :: nil)) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
clear H40. set (d:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
assert (length (round d k2) = 4). auto. apply round_len in H40; destruct H41 as [H42 [H43 [H44 H45]]];auto; clear H42 H43 H44 H45.
do 17 destruct H40. unfold d,k2;clear d.
replace (round((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)(k21 :: k22 :: k23 :: k24 :: nil)) with ((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil) :: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
clear H40. set (d:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
assert (length (round d k3) = 4). auto. apply round_len in H40; destruct H41 as [H42 [H43 [H44 H45]]];auto; clear H42 H43 H44 H45.
do 17 destruct H40. unfold d,k3;clear d.
replace (round((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)(k31 :: k32 :: k33 :: k34 :: nil)) with ((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
clear H40. set (d:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
assert (length (round d k4) =4). auto. apply round_len in H40; destruct H41 as [H42 [H43 [H44 H45]]];auto; clear H42 H43 H44 H45.
do 17 destruct H40. unfold d,k4;clear d.
replace (round((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)(k41 :: k42 :: k43 :: k44 :: nil))with ((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil) :: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
clear H40. set (d:=((x47 :: x48 :: x49 :: x50 :: nil) :: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
assert (length (round d k5) = 4). auto. apply round_len in H40; destruct H41 as [H42 [H43 [H44 H45]]];auto; clear H42 H43 H44 H45.
do 17 destruct H40. unfold d,k5;clear d.
replace (round((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)(k51 :: k52 :: k53 :: k54 :: nil))with ((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
clear H40. set (d:=((x63 :: x64 :: x65 :: x66 :: nil) :: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
assert (length (round d k6) = 4). auto. apply round_len in H40; destruct H41 as [H42 [H43 [H44 H45]]];auto; clear H42 H43 H44 H45.
do 17 destruct H40. unfold d,k6;clear d.
replace (round ((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)(k61 :: k62 :: k63 :: k64 :: nil))with ((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil) :: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil).
clear H40. set (d:=((x79 :: x80 :: x81 :: x82 :: nil) :: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
assert (length (round d k7) = 4). auto. apply round_len in H40; destruct H41 as [H42 [H43 [H44 H45]]];auto; clear H42 H43 H44 H45.
do 17 destruct H40. unfold d,k7;clear d.
replace ((round((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil) (k71 :: k72 :: k73 :: k74 :: nil)))with ((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil).
clear H40. set (d:=((x95 :: x96 :: x97 :: x98 :: nil) :: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil)).
assert (length (round d k8) = 4). auto. apply round_len in H40; destruct H41 as [H42 [H43 [H44 H45]]];auto; clear H42 H43 H44 H45.
do 17 destruct H40. unfold d,k8;clear d.
replace ((round((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil)(k81 :: k82 :: k83 :: k84 :: nil)))with ((x111 :: x112 :: x113 :: x114 :: nil):: (x115 :: x116 :: x117 :: x118 :: nil):: (x119 :: x120 :: x121 :: x122 :: nil) :: (x123 :: x124 :: x125 :: x126 :: nil) :: nil).
clear H40. set (d:=((x111 :: x112 :: x113 :: x114 :: nil) :: (x115 :: x116 :: x117 :: x118 :: nil):: (x119 :: x120 :: x121 :: x122 :: nil) :: (x123 :: x124 :: x125 :: x126 :: nil) :: nil) ).
assert (length (round d k9) = 4). auto. apply round_len in H40; destruct H41 as [H42 [H43 [H44 H45]]];auto; clear H42 H43 H44 H45.
Qed.





(* final *)
Definition A := Poly.
Variables  a11 a12 a13 a14 a31 a32 a33 a34 a21 a22 a23 a24 a41 a42 a43 a44
           k011 k012 k013 k014 k021 k022 k023 k024 k031 k032 k033 k034 k041 k042 k043 k044
           k111 k112 k113 k114 k121 k122 k123 k124 k131 k132 k133 k134 k141 k142 k143 k144
           k211 k212 k213 k214 k221 k222 k223 k224 k231 k232 k233 k234 k241 k242 k243 k244
           k311 k312 k313 k314 k321 k322 k323 k324 k331 k332 k333 k334 k341 k342 k343 k344
           k411 k412 k413 k414 k421 k422 k423 k424 k431 k432 k433 k434 k441 k442 k443 k444
           k511 k512 k513 k514 k521 k522 k523 k524 k531 k532 k533 k534 k541 k542 k543 k544
           k611 k612 k613 k614 k621 k622 k623 k624 k631 k632 k633 k634 k641 k642 k643 k644
           k711 k712 k713 k714 k721 k722 k723 k724 k731 k732 k733 k734 k741 k742 k743 k744
           k811 k812 k813 k814 k821 k822 k823 k824 k831 k832 k833 k834 k841 k842 k843 k844
           k911 k912 k913 k914 k921 k922 k923 k924 k931 k932 k933 k934 k941 k942 k943 k944
           k1011 k1012 k1013 k1014 k1021 k1022 k1023 k1024 
           k1031 k1032 k1033 k1034 k1041 k1042 k1043 k1044 : A.
Definition a1:=a11::a12::a13::a14::nil.
Definition a2:=a21::a22::a23::a24::nil.
Definition a3:=a31::a32::a33::a34::nil.
Definition a4:=a41::a42::a43::a44::nil.         Definition state:=a1::a2::a3::a4::nil.
Definition k01:=k011::k012::k013::k014::nil.
Definition k02:=k021::k022::k023::k024::nil.
Definition k03:=k031::k032::k033::k034::nil.
Definition k04:=k041::k042::k043::k044::nil.    Definition key0:=k01::k02::k03::k04::nil.
Definition k11:=k111::k112::k113::k114::nil.
Definition k12:=k121::k122::k123::k124::nil.
Definition k13:=k131::k132::k133::k134::nil.
Definition k14:=k141::k142::k143::k144::nil.    Definition key1:=k11::k12::k13::k14::nil.
Definition k21:=k211::k212::k213::k214::nil.
Definition k22:=k221::k222::k223::k224::nil.
Definition k23:=k231::k232::k233::k234::nil.
Definition k24:=k241::k242::k243::k244::nil.    Definition key2:=k21::k22::k23::k24::nil.
Definition k31:=k311::k312::k313::k314::nil.
Definition k32:=k321::k322::k323::k324::nil.
Definition k33:=k331::k332::k333::k334::nil.
Definition k34:=k341::k342::k343::k344::nil.    Definition key3:=k31::k32::k33::k34::nil.  
Definition k41:=k411::k412::k413::k414::nil.
Definition k42:=k421::k422::k423::k424::nil.
Definition k43:=k431::k432::k433::k434::nil.
Definition k44:=k441::k442::k443::k444::nil.    Definition key4:=k41::k42::k43::k44::nil.
Definition k51:=k511::k512::k513::k514::nil.
Definition k52:=k521::k522::k523::k524::nil.
Definition k53:=k531::k532::k533::k534::nil.
Definition k54:=k541::k542::k543::k544::nil.    Definition key5:=k51::k52::k53::k54::nil.
Definition k61:=k611::k612::k613::k614::nil.
Definition k62:=k621::k622::k623::k624::nil.
Definition k63:=k631::k632::k633::k634::nil.
Definition k64:=k641::k642::k643::k644::nil.    Definition key6:=k61::k62::k63::k64::nil.
Definition k71:=k711::k712::k713::k714::nil.
Definition k72:=k721::k722::k723::k724::nil.
Definition k73:=k731::k732::k733::k734::nil.
Definition k74:=k741::k742::k743::k744::nil.    Definition key7:=k71::k72::k73::k74::nil.
Definition k81:=k811::k812::k813::k814::nil.
Definition k82:=k821::k822::k823::k824::nil.
Definition k83:=k831::k832::k833::k834::nil.
Definition k84:=k841::k842::k843::k844::nil.    Definition key8:=k81::k82::k83::k84::nil.
Definition k91:=k911::k912::k913::k914::nil.
Definition k92:=k921::k922::k923::k924::nil.
Definition k93:=k931::k932::k933::k934::nil.
Definition k94:=k941::k942::k943::k944::nil.       Definition key9:=k91::k92::k93::k94::nil.  
Definition k101:=k1011::k1012::k1013::k1014::nil.
Definition k102:=k1021::k1022::k1023::k1024::nil.
Definition k103:=k1031::k1032::k1033::k1034::nil.
Definition k104:=k1041::k1042::k1043::k1044::nil.  Definition key10:=k101::k102::k103::k104::nil.
Definition initialKey:=key0.
Definition rndKeys:=key1::key2::key3::key4::key5::key6::key7::key8::key9::nil.
Definition finalKey:=key10.



Theorem aes_correct :
    is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 ->
    is_veclen8 k01 -> is_veclen8 k02 -> is_veclen8 k03 -> is_veclen8 k04 ->
    is_veclen8 k11 -> is_veclen8 k12 -> is_veclen8 k13 -> is_veclen8 k14 ->
    is_veclen8 k21 -> is_veclen8 k22 -> is_veclen8 k23 -> is_veclen8 k24 ->
    is_veclen8 k31 -> is_veclen8 k32 -> is_veclen8 k33 -> is_veclen8 k34 ->
    is_veclen8 k41 -> is_veclen8 k42 -> is_veclen8 k43 -> is_veclen8 k44 ->
    is_veclen8 k51 -> is_veclen8 k52 -> is_veclen8 k53 -> is_veclen8 k54 ->
    is_veclen8 k61 -> is_veclen8 k62 -> is_veclen8 k63 -> is_veclen8 k64 ->
    is_veclen8 k71 -> is_veclen8 k72 -> is_veclen8 k73 -> is_veclen8 k74 ->
    is_veclen8 k81 -> is_veclen8 k82 -> is_veclen8 k83 -> is_veclen8 k84 ->
    is_veclen8 k91 -> is_veclen8 k92 -> is_veclen8 k93 -> is_veclen8 k94 ->
    is_veclen8 k101 -> is_veclen8 k102 -> is_veclen8 k103 -> is_veclen8 k104 ->
    inv_rounds (rounds state (initialKey,rndKeys,finalKey)) (initialKey,rndKeys,finalKey) = state.
Proof.
intros. unfold rounds. unfold inv_rounds.
simpl in H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15,H16,H17,H18,H19,H20,
         H21,H22,H23,H24,H25,H26,H27,H28,H29,H30,H31,H32,H33,H34,H35,H36,H37,H38,H39,H40,
         H41,H42,H43,H44,H45,H46.
(* 1.加密finalRound中的秘钥加和解密最初的秘钥加 *) (* 要把matrix_add的两个参数表示成4*4的矩阵才行 *)
unfold finalRound.
assert (matrix_add (matrix_add (shiftRow (byteSub (mk_rnds (matrix_add state initialKey) rndKeys))) finalKey) finalKey
       = shiftRow (byteSub (mk_rnds (matrix_add state initialKey) rndKeys))).
{ assert (length (matrix_add state initialKey) = 4). auto. apply matrix_add_len in H47;try easy.
  do 17 destruct H47. unfold state,initialKey. unfold a1,a2,a3,a4,key0. unfold k01,k02,k03,k04.
  replace (matrix_add((a11 :: a12 :: a13 :: a14 :: nil) :: (a21 :: a22 :: a23 :: a24 :: nil) :: (a31 :: a32 :: a33 :: a34 :: nil) :: (a41 :: a42 :: a43 :: a44 :: nil) :: nil)((k011 :: k012 :: k013 :: k014 :: nil):: (k021 :: k022 :: k023 :: k024 :: nil) :: (k031 :: k032 :: k033 :: k034 :: nil) :: (k041 :: k042 :: k043 :: k044 :: nil) :: nil))with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. destruct H48 as [H50 [H51 [H52 H53]]].
  set (d:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length (mk_rnds d rndKeys) = 4). auto. apply mk_rnds_len in H47;auto;clear H50 H51 H52 H53. do 17 destruct H47.
  replace (mk_rnds d rndKeys) with ((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 d. set (d:=((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil):: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length(byteSub d)=4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  replace (byteSub d) with ((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 d. set (d:=((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil):: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length(shiftRow d) = 4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
  replace (shiftRow d) with ((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil) :: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  unfold finalKey. unfold key10. unfold k101,k102,k103,k104. rewrite matrix_add_correct;try easy. }
  rewrite H47;clear H47.
(* 2.行移位和逆行移位，一个在finalRound里面(已经展开)，另一个在解密的九轮循环里(mk_inv_rnds) *)
unfold mk_inv_rnds. set (d:=(shiftRow (byteSub (mk_rnds (matrix_add state initialKey) rndKeys)))).
simpl ((fix mk_inv_rnds (state0 : Matrix) (rndKeys0 : list Matrix) {struct rndKeys0} : Matrix := match rndKeys0 with | nil => state0 | key :: tl => mk_inv_rnds (inv_Round state0 key) tl end) d (rev rndKeys)). (* 解密的十轮循环会全部展开 *)
assert (inv_Round d key9 = invMixColumn (matrix_add (invByteSub (invShiftRow  (shiftRow (byteSub (mk_rnds (matrix_add state initialKey) rndKeys))))) key9)). easy.
set (d1:=byteSub (mk_rnds (matrix_add state initialKey) rndKeys)) in H47.
rewrite shiftRow_correct in H47. rewrite H47;clear H47 d.
(* 3. 字节代换和逆字节代换*)
unfold d1. assert (invByteSub (byteSub (mk_rnds (matrix_add state initialKey) rndKeys))=mk_rnds (matrix_add state initialKey) rndKeys).
{ assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy.
  do 17 destruct H47. replace (matrix_add state initialKey) with ( (x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47 d1. set (d1:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length(mk_rnds d1 rndKeys)=4). auto. destruct H48 as [H50 [H51 [H52 H53]]]. apply mk_rnds_len in H47;auto. clear H50 H51 H52 H53.
  do 17 destruct H47. replace (mk_rnds d1 rndKeys) with ( (x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil) :: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47. rewrite byteSub_correct;try easy. } 
rewrite H47;clear H47 d1.
(* 4. 秘钥加和秘钥加 *)
unfold mk_rnds. set (d1:=matrix_add state initialKey).
simpl ((fix mk_rnds (state0 : Matrix) (rndKeys0 : list Matrix) {struct rndKeys0} : Matrix := match rndKeys0 with | nil => state0 | key :: tl => mk_rnds (round state0 key) tl end) d1 rndKeys).
unfold d1;clear d1. set (d:=round (round (round (round (round (round (round (round (matrix_add state initialKey) key1) key2) key3) key4) key5) key6) key7) key8).
assert (matrix_add (round d key9) key9 = matrix_add (matrix_add (mixColumn (shiftRow (byteSub d))) key9) key9). easy.
rewrite H47; clear H47.
assert (matrix_add (matrix_add (mixColumn (shiftRow (byteSub d))) key9) key9 = mixColumn (shiftRow (byteSub d)) ).
{ unfold d. assert (length (matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;auto.
  do 17 destruct H47. replace (matrix_add state initialKey) with ((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  set (d1:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  (* 目标：把matrix_add后面的部分化简成4*4的矩阵 *)
  assert(length(round d1 key1)=4). auto. apply round_len in H49;try easy. do 17 destruct H49.
  replace (round d1 key1) with ((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil) :: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H49 H48 d1. set (d1:=((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil) :: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length (round d1 key2)=4). auto. apply round_len in H48;try easy. do 17 destruct H48.
  replace (round d1 key2) with ((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H48 H50 d1. set (d1:=((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length(round d1 key3)=4). auto. apply round_len in H48;try easy. do 17 destruct H48.
  replace (round d1 key3) with ( (x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil) :: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H48 H47 H49 d1. set (d1:=((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length(round d1 key4)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key4) with ((x63 :: x64 :: x65 :: x66 :: nil) :: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47 H50 d1. set (d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length(round d1 key5)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key5) with ((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert (length (round d1 key6)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key6) with ((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil).
  clear H47 H49 d1. set (d1:=((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil)).
  assert (length(round d1 key7)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key7) with ( (x111 :: x112 :: x113 :: x114 :: nil):: (x115 :: x116 :: x117 :: x118 :: nil):: (x119 :: x120 :: x121 :: x122 :: nil) :: (x123 :: x124 :: x125 :: x126 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x111 :: x112 :: x113 :: x114 :: nil):: (x115 :: x116 :: x117 :: x118 :: nil):: (x119 :: x120 :: x121 :: x122 :: nil) :: (x123 :: x124 :: x125 :: x126 :: nil) :: nil)).
  assert (length(round d1 key8)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key8) with ((x127 :: x128 :: x129 :: x130 :: nil):: (x131 :: x132 :: x133 :: x134 :: nil) :: (x135 :: x136 :: x137 :: x138 :: nil) :: (x139 :: x140 :: x141 :: x142 :: nil) :: nil).
  clear H47 H49 d1. set (d1:=((x127 :: x128 :: x129 :: x130 :: nil):: (x131 :: x132 :: x133 :: x134 :: nil) :: (x135 :: x136 :: x137 :: x138 :: nil) :: (x139 :: x140 :: x141 :: x142 :: nil) :: nil)).
  assert (length(byteSub d1)=4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear d1 H47. set (d1:=((x143 :: x144 :: x145 :: x146 :: nil):: (x147 :: x148 :: x149 :: x150 :: nil) :: (x151 :: x152 :: x153 :: x154 :: nil) :: (x155 :: x156 :: x157 :: x158 :: nil) :: nil)).
  assert (length(shiftRow d1)=4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
  unfold d1;rewrite H47;clear H47 d1. set (d1:=((x159 :: x160 :: x161 :: x162 :: nil):: (x163 :: x164 :: x165 :: x166 :: nil) :: (x167 :: x168 :: x169 :: x170 :: nil) :: (x171 :: x172 :: x173 :: x174 :: nil) :: nil)).
  assert (length(mixColumn d1)=4). auto. apply mixColumn_len in H47;try easy. do 17 destruct H47.
  unfold d1;rewrite H47;clear H47 d1 H49 H48 H50.
  unfold key9. unfold k91,k92,k93,k94. rewrite matrix_add_correct;try easy. }
rewrite H47;clear H47.
(* 5. 列混合和逆列混合 *) (* 把mixColumn后面的化简成4×4的矩阵 *)
assert (invMixColumn (mixColumn (shiftRow (byteSub d))) = shiftRow (byteSub d)).
{   assert (exists c11 c12 c13 c14 c21 c22 c23 c24 c31 c32 c33 c34 c41 c42 c43 c44,
    d=(c11::c12::c13::c14::nil)::(c21::c22::c23::c24::nil)::(c31::c32::c33::c34::nil)::(c41::c42::c43::c44::nil)::nil 
    /\ is_veclen8 (c11::c12::c13::c14::nil) /\ is_veclen8 (c21::c22::c23::c24::nil) /\ is_veclen8 (c31::c32::c33::c34::nil) /\ is_veclen8 (c41::c42::c43::c44::nil)) .
    (* 加了长度的条件 *)
{ unfold d. assert (length (matrix_add state initialKey) =4). auto. apply matrix_add_len in H47; try easy. 
  do 16 destruct H47. unfold state,initialKey. unfold a1,a2,a3,a4,key0. unfold k01,k02,k03,k04. destruct H47.
  replace ( matrix_add ((a11 :: a12 :: a13 :: a14 :: nil) :: (a21 :: a22 :: a23 :: a24 :: nil) :: (a31 :: a32 :: a33 :: a34 :: nil) :: (a41 :: a42 :: a43 :: a44 :: nil) :: nil) ((k011 :: k012 :: k013 :: k014 :: nil) :: (k021 :: k022 :: k023 :: k024 :: nil) :: (k031 :: k032 :: k033 :: k034 :: nil) :: (k041 :: k042 :: k043 :: k044 :: nil) :: nil))  with ((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil):: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length ((round d1 key1)) = 4). auto. apply round_len in H47;try easy.
  do 16 destruct H47. unfold d1,key1;clear d1. unfold k11,k12,k13,k14. destruct H47.
  replace (round((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil) ((k111 :: k112 :: k113 :: k114 :: nil) :: (k121 :: k122 :: k123 :: k124 :: nil) :: (k131 :: k132 :: k133 :: k134 :: nil) :: (k141 :: k142 :: k143 :: k144 :: nil) :: nil)) with ((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil) :: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47. set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil) :: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length (round d1 key2) =4). auto. apply round_len in H47;try easy.
  do 16 destruct H47. unfold d1,key2;clear d1. unfold k21,k22,k23,k24. destruct H47.
  replace ((round ((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil) :: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil) ((k211 :: k212 :: k213 :: k214 :: nil) :: (k221 :: k222 :: k223 :: k224 :: nil) :: (k231 :: k232 :: k233 :: k234 :: nil) :: (k241 :: k242 :: k243 :: k244 :: nil) :: nil))) with ((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47. set (d1:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length (round d1 key3) = 4). auto. apply round_len in H47;try easy.
  do 16 destruct H47. unfold d1,key3;clear d1. unfold k31,k32,k33,k34. destruct H47.
  replace (round ((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil) ((k311 :: k312 :: k313 :: k314 :: nil) :: (k321 :: k322 :: k323 :: k324 :: nil) :: (k331 :: k332 :: k333 :: k334 :: nil) :: (k341 :: k342 :: k343 :: k344 :: nil) :: nil)) with ((x47 :: x48 :: x49 :: x50 :: nil) :: (x51 :: x52 :: x53 :: x54 :: nil) :: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47. set (d1:=((x47 :: x48 :: x49 :: x50 :: nil) :: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length (round d1 key4) = 4). auto. apply round_len in H47;try easy. do 16 destruct H47.
  unfold d1,key4;clear d1. unfold k41,k42,k43,k44. destruct H47.
  replace (round ((x47 :: x48 :: x49 :: x50 :: nil) :: (x51 :: x52 :: x53 :: x54 :: nil) :: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil) ((k411 :: k412 :: k413 :: k414 :: nil) :: (k421 :: k422 :: k423 :: k424 :: nil) :: (k431 :: k432 :: k433 :: k434 :: nil) :: (k441 :: k442 :: k443 :: k444 :: nil) :: nil)) with ((x63 :: x64 :: x65 :: x66 :: nil) :: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47. set (d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length (round d1 key5) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key5;clear d1. unfold k51,k52,k53,k54.
  replace (round ((x63 :: x64 :: x65 :: x66 :: nil) :: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil) ((k511 :: k512 :: k513 :: k514 :: nil) :: (k521 :: k522 :: k523 :: k524 :: nil) :: (k531 :: k532 :: k533 :: k534 :: nil) :: (k541 :: k542 :: k543 :: k544 :: nil) :: nil)) with ((x79 :: x80 :: x81 :: x82 :: nil) :: (x83 :: x84 :: x85 :: x86 :: nil) :: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil).
  clear H47. set (d1:=((x79 :: x80 :: x81 :: x82 :: nil) :: (x83 :: x84 :: x85 :: x86 :: nil) :: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert (length (round d1 key6) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key6;clear d1. unfold k61,k62,k63,k64.
  replace (round ((x79 :: x80 :: x81 :: x82 :: nil) :: (x83 :: x84 :: x85 :: x86 :: nil) :: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil) ((k611 :: k612 :: k613 :: k614 :: nil) :: (k621 :: k622 :: k623 :: k624 :: nil) :: (k631 :: k632 :: k633 :: k634 :: nil) :: (k641 :: k642 :: k643 :: k644 :: nil) :: nil)) with ((x95 :: x96 :: x97 :: x98 :: nil) :: (x99 :: x100 :: x101 :: x102 :: nil) :: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil).
  clear H47. set (d1:=((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil)).
  assert (length (round d1 key7) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key7;clear d1. unfold k71,k72,k73,k74.
  replace (round ((x95 :: x96 :: x97 :: x98 :: nil) :: (x99 :: x100 :: x101 :: x102 :: nil) :: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil) ((k711 :: k712 :: k713 :: k714 :: nil) :: (k721 :: k722 :: k723 :: k724 :: nil) :: (k731 :: k732 :: k733 :: k734 :: nil) :: (k741 :: k742 :: k743 :: k744 :: nil) :: nil)) with ((x111 :: x112 :: x113 :: x114 :: nil) :: (x115 :: x116 :: x117 :: x118 :: nil) :: (x119 :: x120 :: x121 :: x122 :: nil) :: (x123 :: x124 :: x125 :: x126 :: nil) :: nil).
  clear H47. set (d1:=((x111 :: x112 :: x113 :: x114 :: nil) :: (x115 :: x116 :: x117 :: x118 :: nil) :: (x119 :: x120 :: x121 :: x122 :: nil) :: (x123 :: x124 :: x125 :: x126 :: nil) :: nil)).
  assert (length (round d1 key8) = 4). auto. apply round_len in H47;try easy. }
do 17 destruct H47. rewrite H47;clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
assert (length (byteSub d1) = 4). auto. apply byteSub_len in H47;try easy.
unfold d1;clear d1. do 17 destruct H47. rewrite H47;clear H47.
set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil) :: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
assert (length (shiftRow d1) = 4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
unfold d1;clear d1. rewrite H47;clear H47. rewrite mixColumn_correct;try easy. }
rewrite H47;clear H47.
(* 6. 加密解密9轮循环中的行移位 *)
unfold d; clear d.
set (d:=byteSub (round (round (round (round (round (round (round (round (matrix_add state initialKey) key1) key2) key3) key4) key5) key6) key7) key8)).
assert (inv_Round (shiftRow d) key8 = invMixColumn (matrix_add (invByteSub (invShiftRow (shiftRow d))) key8)). easy.
rewrite H47;clear H47. rewrite shiftRow_correct;try easy. unfold d;clear d.
(* 7. 字节代换和逆字节代换 *)
set (d1:=round(round(round(round (round (round (round (matrix_add state initialKey) key1) key2) key3) key4) key5) key6) key7).
assert (invByteSub (byteSub (round d1 key8)) = round d1 key8).
{ unfold d1. assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy.
  do 17 destruct H47. replace (matrix_add state initialKey) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d2:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length(round d2 key1)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d2 key1) with ((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil) :: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 H48 d2. set (d2:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length(round d2 key2)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d2 key2) with ((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 H49 d2. set (d2:=((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length (round d2 key3) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d2 key3) with ((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil) :: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47 H48 d2. set (d2:=((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil) :: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length(round d2 key4)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d2 key4) with ((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47 H49 d2. set (d2:=((x63 :: x64 :: x65 :: x66 :: nil) :: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length(round d2 key5)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d2 key5) with ((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil) :: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil).
  clear H47 H48 d2. set (d2:=((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil) :: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert (length(round d2 key6)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d2 key6) with ((x95 :: x96 :: x97 :: x98 :: nil) :: (x99 :: x100 :: x101 :: x102 :: nil) :: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil).
  clear H47 H49 d2. set (d2:=((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil) :: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil)).
  assert (length(round d2 key7)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d2 key7) with ((x111 :: x112 :: x113 :: x114 :: nil):: (x115 :: x116 :: x117 :: x118 :: nil) :: (x119 :: x120 :: x121 :: x122 :: nil) :: (x123 :: x124 :: x125 :: x126 :: nil) :: nil).
  clear H47 H48 d2. set (d2:=((x111 :: x112 :: x113 :: x114 :: nil):: (x115 :: x116 :: x117 :: x118 :: nil) :: (x119 :: x120 :: x121 :: x122 :: nil) :: (x123 :: x124 :: x125 :: x126 :: nil) :: nil)).
  assert (length(round d2 key8)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d2 key8) with((x127 :: x128 :: x129 :: x130 :: nil):: (x131 :: x132 :: x133 :: x134 :: nil) :: (x135 :: x136 :: x137 :: x138 :: nil) :: (x139 :: x140 :: x141 :: x142 :: nil) :: nil).
  clear H47 H49 d2. rewrite byteSub_correct;easy. }
rewrite H47;clear H47.
(* 8. 秘钥加和秘钥加 *)
unfold d1;clear d1. set (d:=round (round (round (round (round (round (round (matrix_add state initialKey) key1) key2) key3) key4) key5) key6) key7).
assert (round d key8 = matrix_add (mixColumn (shiftRow (byteSub d))) key8). easy.
rewrite H47;clear H47.
assert (matrix_add (matrix_add (mixColumn (shiftRow (byteSub d))) key8) key8 = mixColumn (shiftRow (byteSub d))).
{ unfold d. assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy.
  do 17 destruct H47. replace (matrix_add state initialKey) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length(round d1 key1)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key1) with ((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil) :: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length(round d1 key2)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key2) with ((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 H49 d1. set (d1:=((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length (round d1 key3) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key3) with ((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil) :: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil) :: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length(round d1 key4)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key4) with ((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47 H49 d1. set (d1:=((x63 :: x64 :: x65 :: x66 :: nil) :: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length(round d1 key5)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key5) with ((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil) :: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil) :: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert (length(round d1 key6)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key6) with ((x95 :: x96 :: x97 :: x98 :: nil) :: (x99 :: x100 :: x101 :: x102 :: nil) :: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil).
  clear H47 H49 d1. set (d1:=((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil) :: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil)).
  assert (length(round d1 key7)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key7) with ((x111 :: x112 :: x113 :: x114 :: nil):: (x115 :: x116 :: x117 :: x118 :: nil) :: (x119 :: x120 :: x121 :: x122 :: nil) :: (x123 :: x124 :: x125 :: x126 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x111 :: x112 :: x113 :: x114 :: nil):: (x115 :: x116 :: x117 :: x118 :: nil) :: (x119 :: x120 :: x121 :: x122 :: nil) :: (x123 :: x124 :: x125 :: x126 :: nil) :: nil)).
  assert (length(byteSub d1)=4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear d1 H49. set (d1:=((x127 :: x128 :: x129 :: x130 :: nil):: (x131 :: x132 :: x133 :: x134 :: nil) :: (x135 :: x136 :: x137 :: x138 :: nil) :: (x139 :: x140 :: x141 :: x142 :: nil) :: nil)).
  assert (length(shiftRow d1)=4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H48 d1. set(d1:=((x143 :: x144 :: x145 :: x146 :: nil):: (x147 :: x148 :: x149 :: x150 :: nil) :: (x151 :: x152 :: x153 :: x154 :: nil) :: (x155 :: x156 :: x157 :: x158 :: nil) :: nil)).
  assert (length(mixColumn d1)=4). auto. apply mixColumn_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. 
  unfold key8. unfold k81,k82,k83,k84. rewrite matrix_add_correct;try easy. }
  rewrite H47;clear H47.
(* 9. 列混合和逆列混合 *)
assert (invMixColumn (mixColumn (shiftRow (byteSub d))) = shiftRow (byteSub d)).
{ assert (exists c11 c12 c13 c14 c21 c22 c23 c24 c31 c32 c33 c34 c41 c42 c43 c44,
        d=(c11::c12::c13::c14::nil)::(c21::c22::c23::c24::nil)::(c31::c32::c33::c34::nil)::(c41::c42::c43::c44::nil)::nil
        /\ is_veclen8 (c11::c12::c13::c14::nil) /\ is_veclen8 (c21::c22::c23::c24::nil) /\ is_veclen8 (c31::c32::c33::c34::nil) /\ is_veclen8 (c41::c42::c43::c44::nil)).
{ unfold d. assert (length (matrix_add state initialKey) =4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  unfold state,initialKey. unfold a1,a2,a3,a4,key0. unfold k01,k02,k03,k04.
  replace (matrix_add ((a11 :: a12 :: a13 :: a14 :: nil) :: (a21 :: a22 :: a23 :: a24 :: nil) :: (a31 :: a32 :: a33 :: a34 :: nil) :: (a41 :: a42 :: a43 :: a44 :: nil) :: nil)((k011 :: k012 :: k013 :: k014 :: nil) :: (k021 :: k022 :: k023 :: k024 :: nil):: (k031 :: k032 :: k033 :: k034 :: nil) :: (k041 :: k042 :: k043 :: k044 :: nil) :: nil))with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length ((round d1 key1)) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key1;clear d1. unfold k11,k12,k13,k14.
  replace (round((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)((k111 :: k112 :: k113 :: k114 :: nil) :: (k121 :: k122 :: k123 :: k124 :: nil):: (k131 :: k132 :: k133 :: k134 :: nil) :: (k141 :: k142 :: k143 :: k144 :: nil) :: nil)) with ((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47. set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length (round d1 key2) =4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key2;clear d1. unfold k21,k22,k23,k24.
  replace (round((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)((k211 :: k212 :: k213 :: k214 :: nil):: (k221 :: k222 :: k223 :: k224 :: nil):: (k231 :: k232 :: k233 :: k234 :: nil) :: (k241 :: k242 :: k243 :: k244 :: nil) :: nil)) with ((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47. set (d1:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length (round d1 key3) = 4). auto. apply round_len in H47;try easy; do 17 destruct H47.
  unfold d1,key3;clear d1. unfold k31,k32,k33,k34.
  replace (round((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)((k311 :: k312 :: k313 :: k314 :: nil):: (k321 :: k322 :: k323 :: k324 :: nil):: (k331 :: k332 :: k333 :: k334 :: nil) :: (k341 :: k342 :: k343 :: k344 :: nil) :: nil))with ((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47. set (d1:=((x47 :: x48 :: x49 :: x50 :: nil) :: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length (round d1 key4) = 4). auto. apply round_len in H47;try easy; do 17 destruct H47.
  unfold d1,key4;clear d1. unfold k41,k42,k43,k44.
  replace (round((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)((k411 :: k412 :: k413 :: k414 :: nil):: (k421 :: k422 :: k423 :: k424 :: nil):: (k431 :: k432 :: k433 :: k434 :: nil) :: (k441 :: k442 :: k443 :: k444 :: nil) :: nil)) with ((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil). 
  clear H47. set (d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length (round d1 key5) = 4). auto. apply round_len in H47;try easy; do 17 destruct H47.
  unfold d1,key5;clear d1. unfold k51,k52,k53,k54.
  replace (round((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)((k511 :: k512 :: k513 :: k514 :: nil):: (k521 :: k522 :: k523 :: k524 :: nil):: (k531 :: k532 :: k533 :: k534 :: nil) :: (k541 :: k542 :: k543 :: k544 :: nil) :: nil)) with ((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil).
  clear H47. set (d1:=((x79 :: x80 :: x81 :: x82 :: nil) :: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert (length (round d1 key6) = 4). auto. apply round_len in H47;try easy; do 17 destruct H47.
  unfold d1,key6;clear d1. unfold k61,k62,k63,k64.
  replace (round((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)((k611 :: k612 :: k613 :: k614 :: nil):: (k621 :: k622 :: k623 :: k624 :: nil):: (k631 :: k632 :: k633 :: k634 :: nil) :: (k641 :: k642 :: k643 :: k644 :: nil) :: nil))with ((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil).
  clear H47. set (d1:=((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil)).
  assert (length (round d1 key7) = 4). auto. apply round_len in H47;try easy; do 17 destruct H47. }
do 17 destruct H47. rewrite H47;clear H47.
set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
assert (length (byteSub d1) = 4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
unfold d1;clear d1. rewrite H47;clear H47.
set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
assert (length (shiftRow d1) = 4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
unfold d1;clear d1. rewrite H47;clear H47. rewrite mixColumn_correct;try easy. }
rewrite H47;clear H47.
(* 10. 行移位和逆行移位 *)
assert (inv_Round (shiftRow (byteSub d)) key7 = invMixColumn (matrix_add (invByteSub (invShiftRow (shiftRow (byteSub d)))) key7)).
easy. rewrite H47;clear H47. rewrite shiftRow_correct;try easy.
(* 11. 字节代换和逆字节代换 *)
assert (invByteSub (byteSub d) = d).
{ unfold d. assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace (matrix_add state initialKey) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set(d1:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length(round d1 key1)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key1) with ((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length(round d1 key2)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key2) with ((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 H49 d1. set (d1:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)) .
  assert (length(round d1 key3)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key3) with ((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length(round d1 key4)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key4) with ((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47 H49 d1. set (d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length(round d1 key5)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key5) with ((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil) :: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert (length(round d1 key6)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key6) with ((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil).
  clear H47 H49 d1. set(d1:=((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil)).
  assert (length(round d1 key7)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key7)with((x111 :: x112 :: x113 :: x114 :: nil):: (x115 :: x116 :: x117 :: x118 :: nil):: (x119 :: x120 :: x121 :: x122 :: nil) :: (x123 :: x124 :: x125 :: x126 :: nil) :: nil).
  clear H47 H48 d1. rewrite byteSub_correct;try easy. }
rewrite H47;clear H47.
(* 12. 秘钥加和秘钥加 *)
unfold d;clear d. set (d:=round (round (round (round (round (round (matrix_add state initialKey) key1) key2) key3) key4) key5) key6).
assert (round d key7 =  matrix_add (mixColumn (shiftRow (byteSub d))) key7). easy.
rewrite H47;clear H47. 
assert (matrix_add (matrix_add (mixColumn (shiftRow (byteSub d))) key7) key7 = mixColumn (shiftRow (byteSub d))).
{ unfold d. assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace (matrix_add state initialKey) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set(d1:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length(round d1 key1)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key1) with ((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length(round d1 key2)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key2) with ((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 H49 d1. set (d1:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)) .
  assert (length(round d1 key3)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key3) with ((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length(round d1 key4)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key4) with ((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47 H49 d1. set (d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length(round d1 key5)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key5) with ((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil) :: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert (length(round d1 key6)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key6) with ((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil).
  clear H47 H49 d1. set(d1:=((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil)).
  assert (length(byteSub d1)=4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H48 d1. set (d1:=((x111 :: x112 :: x113 :: x114 :: nil):: (x115 :: x116 :: x117 :: x118 :: nil):: (x119 :: x120 :: x121 :: x122 :: nil) :: (x123 :: x124 :: x125 :: x126 :: nil) :: nil)).
  assert (length(shiftRow d1)=4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47; clear H49 d1. set (d1:=((x127 :: x128 :: x129 :: x130 :: nil) :: (x131 :: x132 :: x133 :: x134 :: nil) :: (x135 :: x136 :: x137 :: x138 :: nil) :: (x139 :: x140 :: x141 :: x142 :: nil) :: nil)).
  assert (length(mixColumn d1)=4). auto. apply mixColumn_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H48 d1. unfold key7. unfold k71,k72,k73,k74. 
  rewrite matrix_add_correct;try easy. }
rewrite H47;clear H47.
(* 13. 列混合 *)
assert (invMixColumn (mixColumn (shiftRow (byteSub d))) = shiftRow (byteSub d)).
{ assert (exists c11 c12 c13 c14 c21 c22 c23 c24 c31 c32 c33 c34 c41 c42 c43 c44,
        d=(c11::c12::c13::c14::nil)::(c21::c22::c23::c24::nil)::(c31::c32::c33::c34::nil)::(c41::c42::c43::c44::nil)::nil
        /\ is_veclen8 (c11::c12::c13::c14::nil) /\ is_veclen8 (c21::c22::c23::c24::nil) /\ is_veclen8 (c31::c32::c33::c34::nil) /\ is_veclen8 (c41::c42::c43::c44::nil)).
{ unfold d. assert (length (matrix_add state initialKey) =4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  unfold state,initialKey. unfold a1,a2,a3,a4,key0. unfold k01,k02,k03,k04.
  replace (matrix_add((a11 :: a12 :: a13 :: a14 :: nil):: (a21 :: a22 :: a23 :: a24 :: nil):: (a31 :: a32 :: a33 :: a34 :: nil) :: (a41 :: a42 :: a43 :: a44 :: nil) :: nil)((k011 :: k012 :: k013 :: k014 :: nil):: (k021 :: k022 :: k023 :: k024 :: nil) :: (k031 :: k032 :: k033 :: k034 :: nil) :: (k041 :: k042 :: k043 :: k044 :: nil) :: nil)) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length ((round d1 key1)) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key1;clear d1. unfold k11,k12,k13,k14.
  replace (round((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)((k111 :: k112 :: k113 :: k114 :: nil):: (k121 :: k122 :: k123 :: k124 :: nil):: (k131 :: k132 :: k133 :: k134 :: nil) :: (k141 :: k142 :: k143 :: k144 :: nil) :: nil)) with ((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47. set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length (round d1 key2) =4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key2;clear d1. unfold k21,k22,k23,k24.
  replace (round((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)((k211 :: k212 :: k213 :: k214 :: nil):: (k221 :: k222 :: k223 :: k224 :: nil):: (k231 :: k232 :: k233 :: k234 :: nil) :: (k241 :: k242 :: k243 :: k244 :: nil) :: nil)) with ((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47. set (d1:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length (round d1 key3) = 4). auto. apply round_len in H47;try easy; do 17 destruct H47.
  unfold d1,key3;clear d1. unfold k31,k32,k33,k34.
  replace ((round((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)((k311 :: k312 :: k313 :: k314 :: nil):: (k321 :: k322 :: k323 :: k324 :: nil):: (k331 :: k332 :: k333 :: k334 :: nil) :: (k341 :: k342 :: k343 :: k344 :: nil) :: nil))) with ((x47 :: x48 :: x49 :: x50 :: nil) :: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47. set (d1:=((x47 :: x48 :: x49 :: x50 :: nil) :: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length (round d1 key4) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key4;clear d1. unfold k41,k42,k43,k44.
  replace (round((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)((k411 :: k412 :: k413 :: k414 :: nil):: (k421 :: k422 :: k423 :: k424 :: nil):: (k431 :: k432 :: k433 :: k434 :: nil) :: (k441 :: k442 :: k443 :: k444 :: nil) :: nil)) with ((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil). 
  clear H47. set (d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length (round d1 key5) = 4). auto. apply round_len in H47;try easy; do 17 destruct H47.
  unfold d1,key5;clear d1. unfold k51,k52,k53,k54.
  replace (round((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)((k511 :: k512 :: k513 :: k514 :: nil):: (k521 :: k522 :: k523 :: k524 :: nil):: (k531 :: k532 :: k533 :: k534 :: nil) :: (k541 :: k542 :: k543 :: k544 :: nil) :: nil)) with ((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil).
  clear H47. set (d1:=((x79 :: x80 :: x81 :: x82 :: nil) :: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert (length (round d1 key6) = 4). auto. apply round_len in H47;try easy. }
do 17 destruct H47. rewrite H47;clear H47.
set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
assert (length (byteSub d1) = 4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
unfold d1;clear d1. rewrite H47;clear H47.
set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
assert (length (shiftRow d1) = 4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
unfold d1;clear d1. rewrite H47;clear H47. rewrite mixColumn_correct;try easy. }
rewrite H47;clear H47.
(* 14. 行移位 *)
unfold d;clear d.
set (d:=byteSub (round (round (round (round (round (round (matrix_add state initialKey) key1) key2) key3) key4) key5) key6)).
assert (inv_Round (shiftRow d) key6 = invMixColumn (matrix_add (invByteSub (invShiftRow (shiftRow d))) key6)).
easy. rewrite H47;clear H47. rewrite shiftRow_correct;try easy.
(* 15. 字节代换 *)
unfold d; clear d. set (d:=round(round(round(round (round (round (matrix_add state initialKey) key1) key2) key3)key4) key5) key6).
assert (invByteSub (byteSub d)=d).
{ unfold d;clear d. assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace (matrix_add state initialKey) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length(round d1 key1)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key1) with ((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil) :: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length(round d1 key2)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key2) with ((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 H49 d1. set(d1:=((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length(round d1 key3)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key3) with ((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length(round d1 key4)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key4) with ((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47 H49 d1. set (d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length(round d1 key5)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key5)with( (x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert (length(round d1 key6)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key6)with((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil).
  clear H47 H49 d1. rewrite byteSub_correct;try easy. }
rewrite H47;clear H47. unfold d;clear d.
(* 16. 秘钥加 *)
set (d:=round (round (round (round (round (matrix_add state initialKey) key1) key2) key3) key4) key5).
assert (round d key6 = matrix_add (mixColumn (shiftRow (byteSub d))) key6). easy. rewrite H47;clear H47. unfold d.
assert (matrix_add(matrix_add(mixColumn(shiftRow (byteSub(round(round (round (round (round (matrix_add state initialKey) key1) key2) key3)key4) key5)))) key6) key6 = mixColumn(shiftRow(byteSub(round(round (round (round (round (matrix_add state initialKey) key1) key2) key3)key4) key5)))).
{ assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace (matrix_add state initialKey) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length(round d1 key1)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key1) with ((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil) :: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length(round d1 key2)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key2) with ((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 H49 d1. set(d1:=((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length(round d1 key3)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key3) with ((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length(round d1 key4)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key4) with ((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47 H49 d1. set (d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length(round d1 key5)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key5)with( (x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil).
  clear H47 H48 d1. set (d1:=((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil) :: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert (length(byteSub d1)=4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1;rewrite H47;clear H47. clear H49 d1. set(d1:=((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil)).
  assert (length(shiftRow d1)=4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H48 d1. set(d1:=((x111 :: x112 :: x113 :: x114 :: nil):: (x115 :: x116 :: x117 :: x118 :: nil):: (x119 :: x120 :: x121 :: x122 :: nil) :: (x123 :: x124 :: x125 :: x126 :: nil) :: nil)).
  assert(length(mixColumn d1)=4). auto. apply mixColumn_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H49 d1. unfold key6. unfold k61,k62,k63,k64.
  rewrite matrix_add_correct;try easy. }
rewrite H47;clear H47.
(* 17. 列混合 *)
assert (invMixColumn (mixColumn (shiftRow (byteSub d))) = shiftRow (byteSub d)).
{ assert (exists c11 c12 c13 c14 c21 c22 c23 c24 c31 c32 c33 c34 c41 c42 c43 c44,
        d=(c11::c12::c13::c14::nil)::(c21::c22::c23::c24::nil)::(c31::c32::c33::c34::nil)::(c41::c42::c43::c44::nil)::nil
        /\ is_veclen8 (c11::c12::c13::c14::nil) /\ is_veclen8 (c21::c22::c23::c24::nil) /\ is_veclen8 (c31::c32::c33::c34::nil) /\ is_veclen8 (c41::c42::c43::c44::nil) ).
{ unfold d. assert (length (matrix_add state initialKey) =4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  unfold state,initialKey. unfold a1,a2,a3,a4,key0. unfold k01,k02,k03,k04.
  replace (matrix_add((a11 :: a12 :: a13 :: a14 :: nil):: (a21 :: a22 :: a23 :: a24 :: nil):: (a31 :: a32 :: a33 :: a34 :: nil) :: (a41 :: a42 :: a43 :: a44 :: nil) :: nil)((k011 :: k012 :: k013 :: k014 :: nil):: (k021 :: k022 :: k023 :: k024 :: nil):: (k031 :: k032 :: k033 :: k034 :: nil) :: (k041 :: k042 :: k043 :: k044 :: nil) :: nil)) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length ((round d1 key1)) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key1;clear d1. unfold k11,k12,k13,k14.
  replace (round((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)((k111 :: k112 :: k113 :: k114 :: nil):: (k121 :: k122 :: k123 :: k124 :: nil):: (k131 :: k132 :: k133 :: k134 :: nil) :: (k141 :: k142 :: k143 :: k144 :: nil) :: nil)) with ((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47. set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length (round d1 key2) =4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key2;clear d1. unfold k21,k22,k23,k24.
  replace ((round((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)((k211 :: k212 :: k213 :: k214 :: nil):: (k221 :: k222 :: k223 :: k224 :: nil):: (k231 :: k232 :: k233 :: k234 :: nil) :: (k241 :: k242 :: k243 :: k244 :: nil) :: nil))) with ((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47. set (d1:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length (round d1 key3) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key3;clear d1. unfold k31,k32,k33,k34.
  replace ((round((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)((k311 :: k312 :: k313 :: k314 :: nil) :: (k321 :: k322 :: k323 :: k324 :: nil):: (k331 :: k332 :: k333 :: k334 :: nil) :: (k341 :: k342 :: k343 :: k344 :: nil) :: nil))) with ((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47. set (d1:=((x47 :: x48 :: x49 :: x50 :: nil) :: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length (round d1 key4) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key4;clear d1. unfold k41,k42,k43,k44. 
  replace ((round((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)((k411 :: k412 :: k413 :: k414 :: nil) :: (k421 :: k422 :: k423 :: k424 :: nil):: (k431 :: k432 :: k433 :: k434 :: nil) :: (k441 :: k442 :: k443 :: k444 :: nil) :: nil))) with ((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47. set (d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length (round d1 key5) = 4). auto. apply round_len in H47;try easy. }
do 17 destruct H47. rewrite H47;clear H47.
set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
assert (length (byteSub d1) = 4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
unfold d1;clear d1. rewrite H47;clear H47.
set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
assert (length (shiftRow d1) = 4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
unfold d1;clear d1. rewrite H47;clear H47. rewrite mixColumn_correct;try easy. }
unfold d in H47. rewrite H47;clear H47.
(* 18. 行移位 *)
fold d. set (d1:=inv_Round (shiftRow (byteSub d)) key5). unfold inv_Round in d1. 
unfold d1;clear d1. rewrite shiftRow_correct;try easy.
(* 19. 字节代换 *)
assert (invByteSub (byteSub d)=d).
{ unfold d;clear d. assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace(matrix_add state initialKey)with((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert(length(round d1 key1)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key1)with((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length(round d1 key2)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key2)with((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 H49 d1. set(d1:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length(round d1 key3)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key3) with((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil) :: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length(round d1 key4)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key4) with((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47 H49 d1. set(d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length(round d1 key5)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key5)with( (x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil).
  clear H47 H48 d1. rewrite byteSub_correct;try easy. }
rewrite H47;clear H47.
(* 20. 秘钥加 *)
unfold d;clear d.  
set (d:=round (round (round (round (matrix_add state initialKey) key1) key2) key3) key4).
assert (round d key5 = matrix_add (mixColumn (shiftRow (byteSub d))) key5). easy.
rewrite H47;clear H47. unfold d. 
assert (matrix_add (matrix_add (mixColumn (shiftRow (byteSub (round (round (round (round (matrix_add state initialKey) key1) key2) key3) key4)))) key5) key5=mixColumn (shiftRow (byteSub (round (round (round (round (matrix_add state initialKey) key1) key2) key3) key4)))).
{ assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace(matrix_add state initialKey)with((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert(length(round d1 key1)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key1)with((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length(round d1 key2)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key2)with((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 H49 d1. set(d1:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length(round d1 key3)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key3) with((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil) :: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length(round d1 key4)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace (round d1 key4) with((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47 H49 d1. set(d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert(length(byteSub d1)=4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H48 d1. set (d1:=((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert (length(shiftRow d1)= 4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H49 d1. set (d1:=((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil) :: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil)).
  assert (length(mixColumn d1)=4). auto. apply mixColumn_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. unfold key5. unfold k51,k52,k53,k54.
  rewrite matrix_add_correct;try easy. }
rewrite H47;clear H47.
(* 21. 列混合 *)
fold d. assert (invMixColumn (mixColumn (shiftRow (byteSub d))) = shiftRow (byteSub d)).
{ assert (exists c11 c12 c13 c14 c21 c22 c23 c24 c31 c32 c33 c34 c41 c42 c43 c44,
        d=(c11::c12::c13::c14::nil)::(c21::c22::c23::c24::nil)::(c31::c32::c33::c34::nil)::(c41::c42::c43::c44::nil)::nil
        /\ is_veclen8 (c11::c12::c13::c14::nil) /\ is_veclen8 (c21::c22::c23::c24::nil) /\ is_veclen8 (c31::c32::c33::c34::nil) /\ is_veclen8 (c41::c42::c43::c44::nil)).
{ unfold d. assert (length (matrix_add state initialKey) =4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  unfold state,initialKey. unfold a1,a2,a3,a4,key0. unfold k01,k02,k03,k04.
  replace (matrix_add((a11 :: a12 :: a13 :: a14 :: nil):: (a21 :: a22 :: a23 :: a24 :: nil):: (a31 :: a32 :: a33 :: a34 :: nil) :: (a41 :: a42 :: a43 :: a44 :: nil) :: nil)((k011 :: k012 :: k013 :: k014 :: nil):: (k021 :: k022 :: k023 :: k024 :: nil):: (k031 :: k032 :: k033 :: k034 :: nil):: (k041 :: k042 :: k043 :: k044 :: nil) :: nil)) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length ((round d1 key1)) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key1;clear d1. unfold k11,k12,k13,k14.
  replace (round ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)((k111 :: k112 :: k113 :: k114 :: nil):: (k121 :: k122 :: k123 :: k124 :: nil):: (k131 :: k132 :: k133 :: k134 :: nil) :: (k141 :: k142 :: k143 :: k144 :: nil) :: nil)) with ((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47. set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil) :: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length (round d1 key2) =4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key2;clear d1. unfold k21,k22,k23,k24.
  replace (round((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil) ((k211 :: k212 :: k213 :: k214 :: nil):: (k221 :: k222 :: k223 :: k224 :: nil):: (k231 :: k232 :: k233 :: k234 :: nil) :: (k241 :: k242 :: k243 :: k244 :: nil) :: nil))with ((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47. set (d1:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length (round d1 key3) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key3;clear d1. unfold k31,k32,k33,k34.
  replace (round((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)((k311 :: k312 :: k313 :: k314 :: nil):: (k321 :: k322 :: k323 :: k324 :: nil):: (k331 :: k332 :: k333 :: k334 :: nil) :: (k341 :: k342 :: k343 :: k344 :: nil) :: nil)) with ((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47. set (d1:=((x47 :: x48 :: x49 :: x50 :: nil) :: (x51 :: x52 :: x53 :: x54 :: nil) :: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length (round d1 key4) = 4). auto. apply round_len in H47;try easy. }
do 17 destruct H47. rewrite H47;clear H47.
set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
assert (length (byteSub d1) = 4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
unfold d1;clear d1. rewrite H47;clear H47.
set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
assert (length (shiftRow d1) = 4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
unfold d1;clear d1. rewrite H47;clear H47. rewrite mixColumn_correct;try easy. }
rewrite H47;clear H47.
(* 22. 行移位 *)
unfold inv_Round. rewrite shiftRow_correct;try easy.
(* 23. 字节代换 *)
assert (invByteSub (byteSub d)=d).
{ unfold d;clear d. assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace (matrix_add state initialKey) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length(round d1 key1)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key1)with((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length(round d1 key2)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key2)with((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 H49 d1. set(d1:=((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length(round d1 key3)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key3)with((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length(round d1 key4)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key4)with((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47 H49 d1. rewrite byteSub_correct;try easy. }
rewrite H47;clear H47.
(* 24. 秘钥加 *)
unfold d;clear d.
set (d:=round (round (round (matrix_add state initialKey) key1) key2) key3).
set (d1:=round d key4). unfold round in d1. unfold d1;clear d1.
unfold d. assert(matrix_add (matrix_add (mixColumn (shiftRow (byteSub (round (round (round (matrix_add state initialKey) key1) key2) key3)))) key4) key4=mixColumn (shiftRow (byteSub (round (round (round (matrix_add state initialKey) key1) key2) key3)))).
{ assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace (matrix_add state initialKey) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length(round d1 key1)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key1)with((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length(round d1 key2)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key2)with((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 H49 d1. set(d1:=((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length(round d1 key3)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key3)with((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert(length(byteSub d1)=4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H49 d1. set (d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert(length(shiftRow d1)=4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H48 d1. set (d1:=((x79 :: x80 :: x81 :: x82 :: nil):: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert (length(mixColumn d1)=4). auto. apply mixColumn_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H49 d1. unfold key4. unfold k41,k42,k43,k44.
  rewrite matrix_add_correct;try easy. }
rewrite H47;clear H47.
(* 25. 列混合 *)
fold d. assert (invMixColumn (mixColumn (shiftRow (byteSub d))) = shiftRow (byteSub d)).
{ assert (exists c11 c12 c13 c14 c21 c22 c23 c24 c31 c32 c33 c34 c41 c42 c43 c44,
        d=(c11::c12::c13::c14::nil)::(c21::c22::c23::c24::nil)::(c31::c32::c33::c34::nil)::(c41::c42::c43::c44::nil)::nil
        /\ is_veclen8 (c11::c12::c13::c14::nil) /\ is_veclen8 (c21::c22::c23::c24::nil) /\ is_veclen8 (c31::c32::c33::c34::nil) /\ is_veclen8 (c41::c42::c43::c44::nil)).
{ unfold d. assert (length (matrix_add state initialKey) =4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  unfold state,initialKey. unfold a1,a2,a3,a4,key0. unfold k01,k02,k03,k04.
  replace (matrix_add((a11 :: a12 :: a13 :: a14 :: nil):: (a21 :: a22 :: a23 :: a24 :: nil):: (a31 :: a32 :: a33 :: a34 :: nil) :: (a41 :: a42 :: a43 :: a44 :: nil) :: nil) ((k011 :: k012 :: k013 :: k014 :: nil):: (k021 :: k022 :: k023 :: k024 :: nil):: (k031 :: k032 :: k033 :: k034 :: nil) :: (k041 :: k042 :: k043 :: k044 :: nil) :: nil)) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length ((round d1 key1)) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key1;clear d1. unfold k11,k12,k13,k14.
  replace (round((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)((k111 :: k112 :: k113 :: k114 :: nil):: (k121 :: k122 :: k123 :: k124 :: nil):: (k131 :: k132 :: k133 :: k134 :: nil) :: (k141 :: k142 :: k143 :: k144 :: nil) :: nil)) with ((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47. set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length (round d1 key2) =4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key2;clear d1. unfold k21,k22,k23,k24.
  replace (round((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)((k211 :: k212 :: k213 :: k214 :: nil):: (k221 :: k222 :: k223 :: k224 :: nil):: (k231 :: k232 :: k233 :: k234 :: nil) :: (k241 :: k242 :: k243 :: k244 :: nil) :: nil)) with ((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47. set (d1:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length (round d1 key3) = 4). auto. apply round_len in H47;try easy. }
do 17 destruct H47. rewrite H47;clear H47.
set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
assert (length (byteSub d1) = 4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
unfold d1;clear d1. rewrite H47;clear H47.
set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
assert (length (shiftRow d1) = 4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
unfold d1;clear d1. rewrite H47;clear H47. rewrite mixColumn_correct;try easy. }
rewrite H47;clear H47.
(* 26. 行移位 *)
rewrite shiftRow_correct;try easy.
(* 27. 字节代换 *)
assert (invByteSub (byteSub d)=d).
{ unfold d;clear d. assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace (matrix_add state initialKey) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set(d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert(length(round d1 key1)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key1)with((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert(length(round d1 key2)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key2)with((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 H49 d1. set(d1:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert(length(round d1 key3)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key3)with((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47 H48 d1. rewrite byteSub_correct;try easy. }
rewrite H47;clear H47.
(* 28. 秘钥加 *)
unfold d;clear d. set (d:=round (round (matrix_add state initialKey) key1) key2).
assert (round d key3 = matrix_add (mixColumn (shiftRow (byteSub d))) key3). easy.
rewrite H47;clear H47. unfold d.
assert(matrix_add(matrix_add(mixColumn(shiftRow (byteSub (round (round (matrix_add state initialKey) key1) key2))))key3) key3=mixColumn(shiftRow (byteSub (round (round (matrix_add state initialKey) key1) key2)))).
{ assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace (matrix_add state initialKey) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set(d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert(length(round d1 key1)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key1)with((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert(length(round d1 key2)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key2)with((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 H49 d1. set(d1:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil) :: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert(length(byteSub d1)=4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H48 d1. set(d1:=((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert(length(shiftRow d1)=4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H49 d1. set(d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert(length(mixColumn d1)=4). auto. apply mixColumn_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. unfold key3. unfold k31,k32,k33,k34.
  rewrite matrix_add_correct;try easy. }
rewrite H47;clear H47.
(* 29. 列混合 *)
fold d. assert (invMixColumn (mixColumn (shiftRow (byteSub d))) = shiftRow (byteSub d)).
{ assert (exists c11 c12 c13 c14 c21 c22 c23 c24 c31 c32 c33 c34 c41 c42 c43 c44,
        d=(c11::c12::c13::c14::nil)::(c21::c22::c23::c24::nil)::(c31::c32::c33::c34::nil)::(c41::c42::c43::c44::nil)::nil
        /\ is_veclen8 (c11::c12::c13::c14::nil) /\ is_veclen8 (c21::c22::c23::c24::nil) /\ is_veclen8 (c31::c32::c33::c34::nil) /\ is_veclen8 (c41::c42::c43::c44::nil) ).
{ unfold d. assert (length (matrix_add state initialKey) =4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  unfold state,initialKey. unfold a1,a2,a3,a4,key0. unfold k01,k02,k03,k04.
  replace (matrix_add((a11 :: a12 :: a13 :: a14 :: nil):: (a21 :: a22 :: a23 :: a24 :: nil):: (a31 :: a32 :: a33 :: a34 :: nil):: (a41 :: a42 :: a43 :: a44 :: nil) :: nil)((k011 :: k012 :: k013 :: k014 :: nil):: (k021 :: k022 :: k023 :: k024 :: nil):: (k031 :: k032 :: k033 :: k034 :: nil):: (k041 :: k042 :: k043 :: k044 :: nil) :: nil))with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil):: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length ((round d1 key1)) = 4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  unfold d1,key1;clear d1. unfold k11,k12,k13,k14.
  replace ((round((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil):: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)((k111 :: k112 :: k113 :: k114 :: nil):: (k121 :: k122 :: k123 :: k124 :: nil):: (k131 :: k132 :: k133 :: k134 :: nil) :: (k141 :: k142 :: k143 :: k144 :: nil) :: nil))) with ((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil):: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47. set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length (round d1 key2) =4). auto. apply round_len in H47;try easy. }
do 17 destruct H47. rewrite H47;clear H47.
set (d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
assert (length (byteSub d1) = 4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
unfold d1;clear d1. rewrite H47;clear H47.
set (d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
assert (length (shiftRow d1) = 4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
unfold d1;clear d1. rewrite H47;clear H47. rewrite mixColumn_correct;try easy. }
rewrite H47;clear H47.
(* 30. 行移位 *)
rewrite shiftRow_correct;try easy.
(* 31. 字节代换 *)
assert (invByteSub (byteSub d)=d).
{ unfold d;clear d. assert(length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace(matrix_add state initialKey)with((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set(d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length(round d1 key1)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key1)with((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length(round d1 key2)=4). auto. apply round_len in H47;try easy. do 17 destruct H47.
  replace(round d1 key2)with((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil).
  clear H47 H49 d1. rewrite byteSub_correct;try easy. }
rewrite H47;clear H47.
(* 32. 剩下的所有 *)
unfold d;clear d. unfold round.
assert(matrix_add(matrix_add(mixColumn (shiftRow (byteSub (matrix_add (mixColumn (shiftRow (byteSub (matrix_add state initialKey)))) key1))))key2) key2=mixColumn (shiftRow (byteSub (matrix_add (mixColumn (shiftRow (byteSub (matrix_add state initialKey)))) key1)))).
{ assert(length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace(matrix_add state initialKey)with((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set(d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert(length(byteSub d1)=4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1; rewrite H47;clear H47. clear H48 d1. set(d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert(length(shiftRow d1)=4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
  unfold d1;rewrite H47;clear H47. clear H49 d1. set(d1:=((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert(length(mixColumn d1)=4). auto. apply mixColumn_len in H47;try easy. do 17 destruct H47.
  unfold d1; rewrite H47;clear H47. clear H48 d1.  set(d1:=((x47 :: x48 :: x49 :: x50 :: nil) :: (x51 :: x52 :: x53 :: x54 :: nil) :: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert(length(matrix_add d1 key1)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace (matrix_add d1 key1) with ((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47 H49 d1. set(d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length(byteSub d1)=4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1;rewrite H47;clear H47. clear H48 d1. set(d1:=((x79 :: x80 :: x81 :: x82 :: nil) :: (x83 :: x84 :: x85 :: x86 :: nil):: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert(length(shiftRow d1)=4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
  unfold d1; rewrite H47;clear H47. clear H49 d1. set(d1:=((x95 :: x96 :: x97 :: x98 :: nil):: (x99 :: x100 :: x101 :: x102 :: nil):: (x103 :: x104 :: x105 :: x106 :: nil) :: (x107 :: x108 :: x109 :: x110 :: nil) :: nil)).
  assert(length(mixColumn d1)=4). auto. apply mixColumn_len in H47;try easy. do 17 destruct H47.
  unfold d1;rewrite H47;clear H47. unfold key2. unfold k21,k22,k23,k24. 
  rewrite matrix_add_correct;try easy. } rewrite H47;clear H47.
assert (invMixColumn (mixColumn (shiftRow (byteSub (matrix_add (mixColumn (shiftRow (byteSub (matrix_add state initialKey)))) key1)))) 
        = shiftRow (byteSub (matrix_add (mixColumn (shiftRow (byteSub (matrix_add state initialKey)))) key1)) ).
{ set (d:=shiftRow (byteSub (matrix_add (mixColumn (shiftRow (byteSub (matrix_add state initialKey)))) key1))).
assert (exists c11 c12 c13 c14 c21 c22 c23 c24 c31 c32 c33 c34 c41 c42 c43 c44,
        d=(c11::c12::c13::c14::nil)::(c21::c22::c23::c24::nil)::(c31::c32::c33::c34::nil)::(c41::c42::c43::c44::nil)::nil
        /\ is_veclen8 (c11::c12::c13::c14::nil) /\ is_veclen8 (c21::c22::c23::c24::nil) /\ is_veclen8 (c31::c32::c33::c34::nil) /\ is_veclen8 (c41::c42::c43::c44::nil)).
{ unfold d. assert (length (matrix_add state initialKey) = 4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  unfold state,initialKey. unfold a1,a2,a3,a4,key0. unfold k01,k02,k03,k04.
  replace (matrix_add((a11 :: a12 :: a13 :: a14 :: nil):: (a21 :: a22 :: a23 :: a24 :: nil):: (a31 :: a32 :: a33 :: a34 :: nil):: (a41 :: a42 :: a43 :: a44 :: nil) :: nil) ((k011 :: k012 :: k013 :: k014 :: nil):: (k021 :: k022 :: k023 :: k024 :: nil):: (k031 :: k032 :: k033 :: k034 :: nil):: (k041 :: k042 :: k043 :: k044 :: nil) :: nil)) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil) :: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length (byteSub d1) = 4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1;clear d1. rewrite H47;clear H47.
  set(d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length (shiftRow d1) = 4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
  unfold d1;clear d1. rewrite H47;clear H47.
  set (d1:=((x31 :: x32 :: x33 :: x34 :: nil) :: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert (length (mixColumn d1) = 4). auto. apply mixColumn_len in H47;try easy. do 17 destruct H47.
  unfold d1;clear d1. rewrite H47;clear H47.
  set (d1:=((x47 :: x48 :: x49 :: x50 :: nil) :: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert (length (matrix_add d1 key1) = 4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  unfold d1,key1;clear d1. unfold k11,k12,k13,k14.
  replace (matrix_add((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)((k111 :: k112 :: k113 :: k114 :: nil) :: (k121 :: k122 :: k123 :: k124 :: nil):: (k131 :: k132 :: k133 :: k134 :: nil):: (k141 :: k142 :: k143 :: k144 :: nil) :: nil)) with ((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47. set(d1:=((x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil) :: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil)).
  assert (length (byteSub d1) = 4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1;clear d1. rewrite H47;clear H47.
  set (d1:=((x79 :: x80 :: x81 :: x82 :: nil) :: (x83 :: x84 :: x85 :: x86 :: nil) :: (x87 :: x88 :: x89 :: x90 :: nil) :: (x91 :: x92 :: x93 :: x94 :: nil) :: nil)).
  assert (length (shiftRow d1) = 4). auto. apply shiftRow_len in H47;try easy. }
do 17 destruct H47. rewrite H47;clear H47. rewrite mixColumn_correct;try easy. }
rewrite H47;clear H47.
rewrite shiftRow_correct;try easy.
assert (invByteSub(byteSub (matrix_add (mixColumn (shiftRow (byteSub (matrix_add state initialKey)))) key1))=matrix_add (mixColumn (shiftRow (byteSub (matrix_add state initialKey)))) key1).
{ assert(length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace(matrix_add state initialKey)with((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set(d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert(length(byteSub d1)=4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H48 d1. set(d1:=((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert(length(shiftRow d1)=4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
  unfold d1;rewrite H47;clear H47. clear H49 d1. set(d1:=((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert(length(mixColumn d1)=4). auto. apply mixColumn_len in H47;try easy. do 17 destruct H47.
  replace(mixColumn d1)with( (x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil).
  clear H47 H48 d1. set(d1:=((x47 :: x48 :: x49 :: x50 :: nil):: (x51 :: x52 :: x53 :: x54 :: nil):: (x55 :: x56 :: x57 :: x58 :: nil) :: (x59 :: x60 :: x61 :: x62 :: nil) :: nil)).
  assert(length(matrix_add d1 key1)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace(matrix_add d1 key1)with( (x63 :: x64 :: x65 :: x66 :: nil):: (x67 :: x68 :: x69 :: x70 :: nil):: (x71 :: x72 :: x73 :: x74 :: nil) :: (x75 :: x76 :: x77 :: x78 :: nil) :: nil).
  clear H47 H49 d1. rewrite byteSub_correct;try easy. }
rewrite H47;clear H47.
assert(matrix_add (matrix_add (mixColumn (shiftRow (byteSub (matrix_add state initialKey)))) key1) key1=mixColumn (shiftRow (byteSub (matrix_add state initialKey)))).
{ assert(length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace(matrix_add state initialKey)with((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set(d1:=((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert(length(byteSub d1)=4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1. rewrite H47;clear H47. clear H48 d1. set(d1:=((x15 :: x16 :: x17 :: x18 :: nil):: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert(length(shiftRow d1)=4). auto. apply shiftRow_len in H47;try easy. do 17 destruct H47.
  unfold d1;rewrite H47;clear H47. clear H49 d1. set(d1:=((x31 :: x32 :: x33 :: x34 :: nil):: (x35 :: x36 :: x37 :: x38 :: nil):: (x39 :: x40 :: x41 :: x42 :: nil) :: (x43 :: x44 :: x45 :: x46 :: nil) :: nil)).
  assert(length(mixColumn d1)=4). auto. apply mixColumn_len in H47;try easy. do 17 destruct H47.
  unfold d1;rewrite H47;clear H47. unfold key1. unfold k11,k12,k13,k14.
  rewrite matrix_add_correct;try easy. } 
rewrite H47;clear H47.
assert (invMixColumn (mixColumn (shiftRow (byteSub (matrix_add state initialKey)))) = shiftRow (byteSub (matrix_add state initialKey))).
{ set (d:=shiftRow (byteSub (matrix_add state initialKey))).
  assert (exists c11 c12 c13 c14 c21 c22 c23 c24 c31 c32 c33 c34 c41 c42 c43 c44,
        d=(c11::c12::c13::c14::nil)::(c21::c22::c23::c24::nil)::(c31::c32::c33::c34::nil)::(c41::c42::c43::c44::nil)::nil
        /\ is_veclen8 (c11::c12::c13::c14::nil) /\ is_veclen8 (c21::c22::c23::c24::nil) /\ is_veclen8 (c31::c32::c33::c34::nil) /\ is_veclen8 (c41::c42::c43::c44::nil)).
{ unfold d. assert (length (matrix_add state initialKey) = 4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  unfold state,initialKey. unfold a1,a2,a3,a4,key0. unfold k01,k02,k03,k04.
  replace ((matrix_add((a11 :: a12 :: a13 :: a14 :: nil):: (a21 :: a22 :: a23 :: a24 :: nil):: (a31 :: a32 :: a33 :: a34 :: nil) :: (a41 :: a42 :: a43 :: a44 :: nil) :: nil)((k011 :: k012 :: k013 :: k014 :: nil):: (k021 :: k022 :: k023 :: k024 :: nil):: (k031 :: k032 :: k033 :: k034 :: nil):: (k041 :: k042 :: k043 :: k044 :: nil) :: nil))) with ((x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. set (d1:=((x :: x0 :: x1 :: x2 :: nil) :: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil)).
  assert (length (byteSub d1) = 4). auto. apply byteSub_len in H47;try easy. do 17 destruct H47.
  unfold d1;clear d1. rewrite H47;clear H47.
  set(d1:=((x15 :: x16 :: x17 :: x18 :: nil) :: (x19 :: x20 :: x21 :: x22 :: nil):: (x23 :: x24 :: x25 :: x26 :: nil) :: (x27 :: x28 :: x29 :: x30 :: nil) :: nil)).
  assert (length (shiftRow d1) = 4). auto. apply shiftRow_len in H47;try easy. }
do 17 destruct H47. rewrite H47;clear H47. rewrite mixColumn_correct;try easy. }
rewrite H47;clear H47. unfold invFinalRound. rewrite shiftRow_correct;try easy. 
assert (invByteSub (byteSub (matrix_add state initialKey))=matrix_add state initialKey).
{ assert (length(matrix_add state initialKey)=4). auto. apply matrix_add_len in H47;try easy. do 17 destruct H47.
  replace(matrix_add state initialKey)with( (x :: x0 :: x1 :: x2 :: nil):: (x3 :: x4 :: x5 :: x6 :: nil):: (x7 :: x8 :: x9 :: x10 :: nil) :: (x11 :: x12 :: x13 :: x14 :: nil) :: nil).
  clear H47. rewrite byteSub_correct;try easy. }
rewrite H47;clear H47. unfold state,initialKey. unfold a1,a2,a3,a4,key0. unfold k01,k02,k03,k04. 
rewrite matrix_add_correct;try easy. auto.
Qed.
















