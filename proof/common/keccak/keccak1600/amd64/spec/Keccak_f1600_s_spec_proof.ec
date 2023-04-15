(******************************************************************************
   Keccak_f1600_s_spec_proof.ec:

   Correctness proof for the REF1 implementation
******************************************************************************)
require import List Real Int IntDiv CoreMap.


require import Keccak_f1600_Spec_facts.


from JExtract require import Jextracted.


equiv rhotates_spec_eq _x _y:
 M.__rhotates_spec ~ Spec.keccak_rho_offsets:
 i{2}=idx(_x,_y) /\ x{1}=_x /\ y{1}=_y /\ 0<=_x<5 /\ 0<=_y<5 ==> ={res}.
proof.
proc; simplify.
inline*; wp.
while (0 <= t{2} <= 24 /\  #[/-4:]pre /\
       i0{1}=idx(_x,_y) /\
       (t,r,x,y,i){2} = (t,r1,x1,y1,i0){1} /\
       0 <= x{2} < 5 /\ 0 <= y{2} < 5
     ).
 auto => /> &m Ht1 _ Hx1 Hx2 Hy1 Hy2 Ht2 ???? ; split.
  move=> ->; split. smt().
  by rewrite ifT /idx /#. 
 move => /> E; split; first smt().
 smt().
by auto => />.
qed.

hoare rhotates_spec_h _x _y:
  M.__rhotates_spec :
  x = _x /\ y = _y /\ 0<=_x<5 /\ 0<=_y<5 ==> res = rhotates.[idx(_x,_y)].
proof.
conseq (rhotates_spec_eq _x _y) (keccak_rho_offsets_h (idx(_x,_y))).
 by move=> /> &m *; exists (idx(x{m},y{m})) => /> /#.
done.
qed.

lemma rhotates_spec_ll: islossless M.__rhotates_spec.
proof.
islossless; while (true) (24-t).
 by move=> z; auto => /> /#.
by auto => /> /#.
qed.

phoare rhotates_spec_ph _x _y:
  [ M.__rhotates_spec :
  x = _x /\ y = _y /\ 0<=_x<5 /\ 0<=_y<5 ==> res = rhotates.[idx(_x,_y)] ] = 1%r.
proof. by conseq rhotates_spec_ll (rhotates_spec_h _x _y). qed.

