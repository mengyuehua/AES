Require Import natbool.
Require Import Bool.
Require Import List.
Require Import lib.
Require Import prim.
Require Import galois.
Require Import wiki_sbox.

Section Para.
Definition Nb := 4.
Definition Nk := 4.
Definition Nr := (max Nb Nk) + 6.
Definition byte := list bool.
Definition byte_vec := list byte.
Implicit Type state : list byte_vec.

(* Key Schedule. *)
Definition Rcon (i : nat) : list Poly :=
  (gpower (n2p 2) (i-1))::rij_0::rij_0::rij_0::nil.
End Para.


(* subByte transformation *)
Section SubByte.
(* select the ith element from sbox *)
Definition sbox_ith (i:nat) := nth i sbox rij_0.
(* Sbox -- select ith element corresponds to the input poly p from sbox. *)
Definition sbox_sel (p:Poly) : Poly := sbox_ith (p2n p).
(* apply sbox to a sequence of bytes. *)
Definition subByte (block : list Poly) := map sbox_sel block.
End SubByte.

(* inversed subByte transformation *)
Section InvSubByte.
Definition inv_sbox_ith (i : nat) := nth i inv_sbox rij_0.
Definition inv_sbox_sel (p:Poly) : Poly := inv_sbox_ith (p2n p).
Definition inv_subByte (block : list Poly) := map inv_sbox_sel block.
End InvSubByte.


Arguments rotate_left [A].
Arguments back_cons [A].
Arguments split [A].
Arguments lth [A].
Arguments transpose [A].
Arguments join [A].
Arguments tail [A].

(* Vec <--> Matrix *)
Definition stripe (block:Vec) : Matrix :=
  transpose (split block 4).
Definition unstripe (state:Matrix) : Vec :=
  join (transpose state).


Section KeySchedule.
(* prev:w[i-1], old:w[i-Nk] *) 
Definition nextWord (i:Poly) (old:Vec) (prev:Vec) : Vec :=
  let n := p2n i in
  let prev' := if is_zero (mod n Nk)
               then vec_add (subByte (rotate_left prev)) (Rcon (div n Nk))
               else if andb (less 6 Nk) (nateq (mod n Nk) 4)
                    then subByte prev
                    else prev
  in vec_add old prev'.

(* Computation of the variable W in keyExpansion *)
Fixpoint kEw (k:nat) (total:nat) (w:Matrix) (wa:Matrix) {struct k} : Matrix :=
  match k,w,drop (Nk-1) w with
  | S k', hd::_, hd'::_ =>
    let n    := total - k in
    let i    := Nk + n in
    let old  := hd in
    let prev := hd' in
    let next := nextWord (n2p i) old prev in
    let w'   := back_cons (tail w) next in
    let wa'  := back_cons wa next in
      kEw k' total w' wa'
  | _,_,_ => wa
  end.

Definition keyExpansion (key:Vec) : Matrix :=
  let keyCols := split key 4 in
  let total := ((Nr+1)*Nb-1) - Nk + 1 in
  let expkey := kEw total total keyCols keyCols in
    expkey.

Definition keyExpansion_split (key:Vec) : list Matrix :=
  let w := keyExpansion key in
    split w (Nr+1).

Fixpoint keyExpansion_split_matrix (keys:list Matrix) : list Matrix :=
  match keys with
  | nil => nil
  | k :: ks => stripe (join k) :: keyExpansion_split_matrix ks
  end.

Definition keySchedule (key:Vec) : Matrix * (list Matrix) * Matrix :=
  let w := keyExpansion_split key in
  let rKeys := keyExpansion_split_matrix w in
    (lth 0 rKeys, range 1 (Nr-1) rKeys, lth Nr rKeys). 

End KeySchedule.


Arguments rotate_right [A].
Arguments width [A].
Arguments map2 [A B].



Section Round.

(* calculate the cols in polyMat, n = length woeff *)
Fixpoint mk_cols' (n:nat) (coeff:Vec) (r:Matrix) : Matrix :=
  match n with
  | 0 => rev r
  | S n' => mk_cols' n' (rotate_right coeff) (coeff::r)
  end.

Definition mk_cols (coeff:Vec) : Matrix :=
  mk_cols' (width coeff) coeff nil.

Definition polyMat (coeff:Vec) : Matrix :=
  transpose (mk_cols coeff).
Definition cryptol_mat_start := map n2p (2::1::1::3::nil).
Definition wiki_mat_start    := map n2p (2::3::1::1::nil).
Definition wiki_invmat_start := map n2p (14::11::13::9::nil).
Definition mat_start := wiki_mat_start.
Definition invmat_start := wiki_invmat_start.
Definition cx : Matrix := transpose (polyMat mat_start).
Definition icx : Matrix := transpose (polyMat invmat_start).


(* col has 4 bytes *)
Definition multCol (cx:Matrix) (col:Vec) : Vec :=
  join (mmult cx (split col 4)).
Definition mixColumn (state:Matrix) : Matrix :=
  transpose (map (fun col => multCol cx col) (transpose state)).
Definition invMixColumn (state:Matrix) : Matrix :=
  transpose (map (fun col => multCol icx col) (transpose state)). 


Arguments rotate_righti [A].
Arguments rotate_lefti [A].

Definition rol (l:list Poly) (i:nat) := rotate_lefti l i.
Definition ror (l:list Poly) (i:nat) := rotate_righti l i.

Definition shiftRow (state:Matrix) : Matrix :=
  map2 rol state (0::1::2::3::nil).
Definition invShiftRow (state:Matrix) : Matrix :=
  map2 ror state (0::1::2::3::nil).

(* [4][Nb][8] -> [4][Nb][8] *)
Definition byteSub (state:Matrix) : Matrix :=
  map
    (fun (row:Vec) => 
      map (fun (x:Poly) => sbox_sel x) row)
    state.
Definition invByteSub (state:Matrix) : Matrix :=
  map
    (fun (row:Vec) =>
      map (fun (x:Poly) => inv_sbox_sel x) row)
    state.


(* AES rounds *)
Definition round (state:Matrix) (roundKey:Matrix) : Matrix :=
  let state1 := byteSub state in
  let state2 := shiftRow state1 in
  let state3 := mixColumn state2 in
  let state4 := matrix_add state3 roundKey in
    state4.

Definition finalRound (state:Matrix) (roundKey:Matrix) : Matrix :=
  let state1 := byteSub state in
  let state2 := shiftRow state1 in
  let state3 := matrix_add state2 roundKey in
    state3.

Fixpoint mk_rnds (state:Matrix) (rndKeys:list Matrix) {struct rndKeys} : Matrix :=
  match rndKeys with
  | nil => state
  | key::tl => mk_rnds (round state key) tl
  end.

Definition rounds (state:Matrix) (keys : Matrix*(list Matrix)*Matrix) : Matrix :=
  match keys with
  (initialKey,rndKeys,finalKey) =>
    let istate := matrix_add state initialKey in
    let last_rnd := mk_rnds istate rndKeys in
    let finalRound := finalRound last_rnd finalKey in
      finalRound
  end.


(* inversed rounds *)
Definition inv_Round (state:Matrix) (roundKey:Matrix) : Matrix :=
  let state1 := invShiftRow state in
  let state2 := invByteSub state1 in
	let state3 := matrix_add state2 roundKey in
  let state4 := invMixColumn state3 in
	    state4.

Definition invFinalRound (state:Matrix) (roundKey:Matrix) : Matrix :=
  let state1 := invShiftRow state in
  let state2 := invByteSub state1 in
	let state3 :=  matrix_add state2 roundKey in
	  state3.

Fixpoint mk_inv_rnds (state:Matrix) (rndKeys:list Matrix) {struct rndKeys} : Matrix :=
  match rndKeys with
  | nil => state
  | key::tl => mk_inv_rnds (inv_Round state key) tl
  end.

Definition inv_rounds (state:Matrix) (keys:Matrix*(list Matrix)*Matrix) : Matrix :=
  match keys with
  (initialKey,rndKeys,finalKey) =>
    let istate := matrix_add state finalKey in
    let last_rnd := mk_inv_rnds istate (rev rndKeys) in
    let invFinalRound := invFinalRound last_rnd initialKey in
      invFinalRound 
  end.

Definition encrypt (key pt:Vec) := 
  let state := stripe pt in
  let keys := keySchedule key in
    unstripe (rounds state keys).
Definition decrypt (key pt:Vec) :=
  let state := stripe pt in
  let keys := keySchedule key in
    unstripe (inv_rounds state keys).

Definition aes_main (key:Vec) (pt:Vec) : Vec :=
    decrypt key (encrypt key pt).

End Round.



Require Import Extraction.
Extraction Language OCaml.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Recursive Extraction aes_main.
Extraction "aes.ml" aes_main.



