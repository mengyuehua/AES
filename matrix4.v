Require Import natbool. (* nat_to_bool *)
Require Import Bool.
Require Import List. 
Require Import lib.    (* Matrix *)
Require Import prim.
Require Import galois. (* mmult *)
Require Import aes.
Require Export map2.
Require Import rijadd.
Require Import gsumgtimes.

Lemma dot_comm : 
  forall x1 x2 x3 x4 y1 y2 y3 y4 : Poly,
    let x:=x1::x2::x3::x4::nil in
    let y:=y1::y2::y3::y4::nil in
    is_veclen8 x -> is_veclen8 y -> dot x y = dot y x.
Proof.
  intros. unfold dot. unfold x,y. simpl. f_equal. simpl in H,H0;
  destruct H as [H1[H2[H3[H4 H5]]]]; destruct H0 as [H6[H7[H8[H9 H10]]]].
  repeat (rewrite gtimes_comm;auto;f_equal).
Qed.


Section Matrix4.
Lemma split4 :
  forall b1 b2 b3 b4 : Poly,
  split (b1::b2::b3::b4::nil) 4 =
  (b1::nil)::(b2::nil)::(b3::nil)::(b4::nil)::nil.
Proof. auto. Qed.

Lemma mmult_ma_cv :
  forall  a11 a12 a13 a14 
          a21 a22 a23 a24
          a31 a32 a33 a34
          a41 a42 a43 a44 c1 c2 c3 c4 : Poly,
	  let a1 := a11::a12::a13::a14::nil in
	  let a2 := a21::a22::a23::a24::nil in
	  let a3 := a31::a32::a33::a34::nil in
	  let a4 := a41::a42::a43::a44::nil in
          let ma := a1::a2::a3::a4::nil in
	  let cv := c1::c2::c3::c4::nil in
  is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 -> is_veclen8 cv ->
  mmult ma (split cv 4) =
   split ((dot a1 cv)::(dot a2 cv)::(dot a3 cv)::(dot a4 cv)::nil) 4.
Proof.
  unfold mmult. simpl. unfold mk_list. intros.
  set (cv := c1::c2::c3::c4::nil).
	set (a1 := a11::a12::a13::a14::nil).
  set (a2 := a21::a22::a23::a24::nil).
  set (a3 := a31::a32::a33::a34::nil).
  set (a4 := a41::a42::a43::a44::nil).
  unfold cv,a1.
  rewrite dot_comm;try easy.
  rewrite split4. f_equal.
  unfold a2. rewrite dot_comm;try easy. f_equal.
  unfold a3. rewrite dot_comm;try easy. f_equal.
  unfold a4. rewrite dot_comm;try easy.
Qed.


Definition A := Poly.
Variables a11 a12 a13 a14 
          a21 a22 a23 a24
          a31 a32 a33 a34
          a41 a42 a43 a44 : A.

Definition a1 := a11::a12::a13::a14::nil.
Definition a2 := a21::a22::a23::a24::nil.
Definition a3 := a31::a32::a33::a34::nil.
Definition a4 := a41::a42::a43::a44::nil.

Variables c1 c2 c3 c4 : A.
Definition c := (c1::nil)::(c2::nil)::(c3::nil)::(c4::nil)::nil.
Definition cv := (c1::c2::c3::c4::nil).

(* ma is an arbitrary 4*4 matrix. *)
Definition ma := a1::a2::a3::a4::nil.

Lemma cv_eq : (c1 :: c2 :: c3 :: c4 :: nil) = cv.
Proof. auto. Qed. 

Lemma mmult_cv :
   is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 -> is_veclen8 cv ->
   mmult ma (split cv 4) = 
   split ((dot a1 cv)::(dot a2 cv)::(dot a3 cv)::(dot a4 cv)::nil) 4.
Proof.
  intros.
  unfold mmult. rewrite split4. unfold ma. simpl. unfold mk_list.
  unfold cv. 
  unfold a1; rewrite dot_comm;try easy; f_equal.
  unfold a2; rewrite dot_comm;try easy; f_equal.
  unfold a3; rewrite dot_comm;try easy; f_equal.
  unfold a4; rewrite dot_comm;try easy.
Qed.


(* prove that mmult a 4*4 matrix to a vector yield a vector. *)
Lemma mmult_vec :
  is_veclen8 a1 -> is_veclen8 a2 -> is_veclen8 a3 -> is_veclen8 a4 -> is_veclen8 cv ->
  exists d1, exists d2, exists d3, exists d4, 
     mmult ma c = d1::d2::d3::d4::nil.
Proof.
  unfold c.
  exists ((dot a1 cv)::nil).
  exists ((dot a2 cv)::nil).
  exists ((dot a3 cv)::nil).
  exists ((dot a4 cv)::nil).
  replace (((c1 :: nil) :: (c2 :: nil) :: (c3 :: nil) :: (c4 :: nil) :: nil)) with (split cv 4).
  simpl in H,H0,H1,H2,H3. rewrite mmult_cv;try easy. auto.
Qed.

End Matrix4.





