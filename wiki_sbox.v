Require Import Bool.
Require Import List.
Require Import lib.
Require Import prim.
Require Import galois.
Require Import pairsort.

Section SboxSec.
Definition rij_8f := map nat_to_bool (1::0::0::0::1::1::1::1::nil).
Definition rij_65 := map nat_to_bool (0::0::1::0::0::1::0::1::nil).

Fixpoint affMat' (n:nat) (a:Poly) (r:Vec) : Vec :=
  match n with
  | 0 => r
  | S n' => let a' := rotate_right bool a in
              affMat' n' a' (a::r)
  end.

Definition affMat : Vec := rev (affMat' 8 rij_8f nil).
Definition inv_affMat : Vec := rev (affMat' 8 rij_65 nil).

Arguments split [A].
Arguments join [A].
Arguments rev [A].

Definition rij_63 := n2p (6*16+3).  
Definition rij_05 := n2p 5.
Definition rev_rij_63 := rev rij_63.
Definition rev_rij_05 := rev rij_05.
Definition affine (xs:Poly) : Poly :=
  rev (rij_add (join (mmultBit affMat (split xs 8))) rev_rij_63).
Definition inv_affine (xs:Poly) : Poly :=
  rev (rij_add (join (mmultBit inv_affMat (split xs 8))) rev_rij_05).

Definition sbox : Vec :=
  map (fun x=> affine (rev (inverse x)))
    (map n2p (mk_natlist 255)).
Definition inv_sbox : Vec :=
  map (fun x => (inverse (inv_affine (rev x))))
    (map n2p (mk_natlist 255)).
End SboxSec.

























