(******************************************************************************
   Keccak_f1600_s_ref1_proof.ec:

   Correctness proof for the REF1 implementation
******************************************************************************)
require import List Real Int IntDiv CoreMap.


require import Keccak_f1600_Spec_facts.
require import Keccak_f1600_s_spec_proof.


from JExtract require import Jextracted.

(** lemmata (move?) *)

lemma ROL_64_by0 (w: W64.t): w `|<<<|` 0 = w.
proof. by apply  W64.all_eq_eq; rewrite /all_eq /=. qed.

lemma ROL_64_val w i:
 (ROL_64 w (W8.of_int i)).`3 = w `|<<<|` (i %% 64).
proof.
rewrite /ROL_64 /shift_mask /=.
rewrite modz_dvd 1:/#.
case: (i %% 64 = 0) => [->|//].
by apply W64.all_eq_eq; rewrite /all_eq.
qed.

hoare rol_u64_h _x _r:
 M.__rol_u64_ref1
 : x = _x /\ i = _r%%64
 ==> res = _x  `|<<<|` _r%%64.
proof.
proc; simplify.
case: (i=0).
 by rcondf 1; auto => /> ->; rewrite ROL_64_by0.
rcondt 1; auto => /> E.
rewrite /ROL_64 /shift_mask /=.
by rewrite !modz_dvd 1..2:/# E.
qed.

lemma rol_u64_ll: islossless M.__rol_u64_ref1
 by islossless.

phoare rol_u64_ph _x _r:
 [ M.__rol_u64_ref1
 : x = _x /\ i = _r%%64 ==> res = _x  `|<<<|` _r%%64 ] = 1%r
by conseq rol_u64_ll (rol_u64_h _x _r).


(* *)

hoare theta_sum_ref1_h _a:
 M.__theta_sum_ref1 :
  a = _a ==> res = keccak_C _a.
proof.
proc.
unroll for 5; unroll for 3.
unroll for 24; unroll for 21; unroll for 18; unroll for 15 => /> .
auto => />.
by rewrite -ext_eq_all /all_eq /keccak_C /idx /invidx /=.
qed.

hoare theta_rol_ref1_h _c:
 M.__theta_rol_ref1 :
  c = _c ==> res = keccak_D _c.
proof.
proc.
unroll for 3; inline*; auto => />.
rewrite -ext_eq_all /all_eq /keccak_D /idx /invidx /=.
by rewrite /ROL_64 /shift_mask /=; smt(W64.xorwC).
qed.

hoare rol_sum_ref1_h _a _y:
 M.__rol_sum_ref1 :
  a = _a /\ d = keccak_D (keccak_C _a) /\ y = _y /\ 0 <= y < 5
  ==> forall x, 0 <= x < 5 => res.[x] = (keccak_pi_op (keccak_rho_op (keccak_theta_op _a))).[idx(x,_y)].
proof.
proc; simplify.
while (#pre /\ 0 <= x <= 5 /\
       forall i, 0 <= i < x =>
        b.[i] =
        _a.[idx (i + 3 * _y, i)] 
        `^` (keccak_D (keccak_C _a)).[idx (i + 3 * _y, i) %% 5]
            `|<<<|` rhotates.[idx (i + 3 * _y, i)]).
 wp; ecall (rol_u64_h b.[x] r).
 wp; ecall (rhotates_spec_h x_ y_).
 auto => /> &m Hy1 Hy2 Hx1 _ IH Hx2; split; first smt().
 move=> Hz1 Hz2; split. 
  by rewrite rhotates_idx_mod64.
 move => _; split; first by smt().
 move => i Hi1 Hi2.
 case: (i = x{m}) => E.
  rewrite E get_setE 1:/# ifT 1:/#.
  rewrite get_setE 1:/# ifT 1:/#.
  rewrite get_setE 1:/# ifT 1:/#.
  by rewrite rhotates_idx_mod64 /idx /= /#.
 by rewrite get_setE 1:/# ifF 1:/# IH 1:/#.
auto => /> Hy1 Hy2; split; first by smt().
move => A k ???; have ->:k=5 by smt().
move => IH x Hx1 Hx2.
rewrite IH 1:/#.
rewrite /keccak_pi_op /keccak_rho_op /keccak_theta_op /=.
pose R:= rhotates.[_] (*obs: lock reduction *).
rewrite initiE 1:/# /= idxK 1..2:/# /=. 
rewrite initiE 1:/# //=.
by rewrite initiE 1:/# //=.
qed.

hoare ANDN_64_h _a _b:
 M.__ANDN_64 :
 a = _a /\ b = _b ==> res = invw _a `&` _b.
proof. by proc; auto. qed.

phoare ANDN_64_ph _a _b:
 [ M.__ANDN_64 :
   a = _a /\ b = _b ==> res = invw _a `&` _b ] = 1%r.
proof. by proc; auto. qed.

hoare set_row_ref1_h _a _e _b _y _c:
 M.__set_row_ref1 :
  e = _e /\ b = _b /\ y = _y /\ s_rc = _c /\ 0 <= y < 5
  /\ (forall x, 0 <= x < 5 =>
      _b.[x] = (keccak_pi_op (keccak_rho_op (keccak_theta_op _a))).[idx(x,_y)])
  /\ (forall k, 0 <= k < 5*_y => e.[k] = (keccak_round_op _c _a).[k])
  ==> forall k, 0 <= k < 5*_y + 5 => res.[k] = (keccak_round_op _c _a).[k].
proof.
proc; simplify.
while (#[/2:7]pre /\ 0 <= x <= 5 /\ 
       forall k, 0 <= k < x+5*_y => e.[k] = (keccak_round_op _c _a).[k]).
 wp; ecall (ANDN_64_h b.[x1] b.[x2]).
 auto => /> &m Hy1 Hy2 Hb Hx1 _ IH Hx2; split.
  move => Ex Ey k ??; have ->: k=0 by smt().
  rewrite get_setE 1:/# ifT 1:/#.
  rewrite /keccak_round_op /keccak_iota_op /keccak_chi_op /=.
  rewrite !Hb // /invidx /idx Ey /=.
  by congr; rewrite W64.xorwC.
 move => E0; split; first smt().
 move=> k Hk1 Hk2.
 case: (k = x{m}+5*_y) => E.
  rewrite /keccak_round_op /keccak_iota_op /keccak_chi_op /=.
  rewrite eq_sym get_setE 1:/# ifF 1:/#.
  rewrite get_setE 1:/# ifT 1:/#.
  rewrite !Hb 1..3:/# /=.
  rewrite initiE 1:/# E /=.
  have ->/=: invidx (x{m} + 5 * _y) = (x{m},_y) by smt().
  rewrite /idx /= !modz_mod; smt(W64.xorwC).
 by rewrite get_setE 1:/# ifF 1:/# -IH /#.
by auto => /> Hy1 Hy2 _ H e k ???; have ->: k=5; smt().
qed.

hoare round_ref1_h _a _c:
 M.__round_ref1 :
  a = _a /\ s_rc = _c ==> res = keccak_round_op _c _a.
proof.
proc; simplify.
while (0 <= y <= 5 /\ #pre /\
       d = keccak_D (keccak_C _a) /\
       forall k, 0 <= k < 5*y => 
        e.[k] = (keccak_round_op _c _a).[k]).
 wp; ecall (set_row_ref1_h a e b y s_rc).
 simplify; ecall (rol_sum_ref1_h a y); simplify.
 auto => /> &m Hy1 _ IH Hy2 b Hb e He; split; smt().
wp; ecall (theta_rol_ref1_h c).
ecall (theta_sum_ref1_h a).
auto => /> &m; split; first smt().
move=> e y ???; have ->: y=5 by smt().
by move=> /= H; apply ext_eq => k Hk; apply H.
qed.

require import List.
import BitEncoding.BitChunking.

abbrev keccak_double_round A i =
 keccak_round_op rc_spec.[2*i+1] (keccak_round_op rc_spec.[2*i] A).

hoare keccakf1600_ref1_h _a:
 M.__keccakf1600_ref1 :
  a = _a ==> res = keccak_f1600_op _a.
proof.
proc.
while (2 <= to_uint c <= 24 /\ 2 %| to_uint c /\
       s_RC = KECCAK1600_RC /\
       keccak_f1600_op _a = foldl keccak_double_round a (range (to_uint c %/ 2) 12)).
 wp; ecall (round_ref1_h e s_rc).
 wp; ecall (round_ref1_h a s_rc).
 auto => /> &m Hc1 _ Hc_2 IH.
 rewrite ultE of_uintK /= => Hc2; split.
  by rewrite to_uintD_small /#.
 rewrite to_uintD_small 1:/#.
 move: IH; rewrite (range_cat (to_uint c{m} %/ 2 + 1)) 1..2:/#.
 by rewrite /rc_spec rangeS foldl_cat /= => -> /#.
wp; ecall (round_ref1_h e s_rc).
wp; ecall (round_ref1_h a s_rc).
auto => />; split.
 by rewrite /keccak_f1600_op /range /rc_spec -iotaredE of_listK.
move => a c; rewrite ultE /= => ????.
have ->/=: to_uint c = 24 by smt().
by rewrite range_geq /=.
qed.



