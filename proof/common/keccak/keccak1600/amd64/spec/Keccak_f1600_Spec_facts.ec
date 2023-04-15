(******************************************************************************
   Keccak_f1600_Spec_facts.ec:

   Basic facts on the specification of Keccak

******************************************************************************)
require import List Int IntDiv CoreMap.

require export Keccak_f1600_Spec.

require import JWordList.

(** State (sec. 3.1)

  We specialise the width of the permutation to [b = 1600], leading to the related
  quantities [w = b / 25 = 64] and [l = log2 (b/25) = 6] (c.f. Table 1).

  The state [A] is organized as a matrix of 5-by-5-by 64 bits. For convenience, and
  since Jasmin does not support directly matrices, we adopt the view of an array of
  25 words of 64 bit.

    A[x,y,z] = st[ x * (5*y)].[z]	, for 0 <= x,y < y, and 0 <= z < 64
*)

op invidx (i: int): int*int = (i %% 5, i %/ 5).

lemma idx_bnd x y:
 0 <= idx(x,y) < 25.
proof. by rewrite /idx /= /#. qed.

lemma invidxK i:
 0 <= i < 25 =>
 idx (invidx i) = i.
proof.
rewrite -(add0z 25) andaE -mem_iota.
by move: i; rewrite -allP -iotaredE /idx /invidx /=.
qed.

lemma idxK x y:
 0 <= x < 5 => 0 <= y < 5 =>
 invidx (idx (x,y)) = (x,y).
proof.
move => Hx; rewrite -(add0z 5) andaE -mem_iota.
move: y; rewrite -allP.
move: Hx; rewrite -(add0z 5) andaE -mem_iota.
by move: x; rewrite -allP -!iotaredE /idx /invidx /=.
qed.


(******************************************************************************
   Functional Specification
******************************************************************************)

op keccak_C (A: state): W64.t Array5.t =
 Array5.init (fun x => A.[x+5*0] `^` A.[x+5*1]
                      `^` A.[x+5*2] `^` A.[x+5*3] `^` A.[x+5*4]).

op keccak_D (C: W64.t Array5.t): W64.t Array5.t =
 Array5.init (fun x => C.[(x-1)%%5]
                       `^` (C.[(x+1)%%5] `|<<<|` 1)).

op keccak_theta_op (A: state ): state =
 Array25.init (fun i => A.[i] `^` (keccak_D (keccak_C A)).[i %% 5]).

op keccak_theta_spec (A A': state ): bool =
  all (fun i => A'.[i] = A.[i] `^` (keccak_D (keccak_C A)).[i %% 5]) (iota_ 0 25).

lemma keccak_thetaP (A A': state):
 A' = keccak_theta_op A
 <=> keccak_theta_spec A A'.
proof.
by rewrite /keccak_theta_spec /keccak_theta_op -iotaredE -ext_eq_all /all_eq.
qed.

hoare keccak_theta_h _A:
 Spec.keccak_theta : a = _A ==> res = keccak_theta_op _A.
proof.
conseq (: _ ==> keccak_theta_spec _A res).
 by move=> /> r /keccak_thetaP.
proc.
swap 2 2.
seq 3: (#pre /\ c = keccak_C _A).
 unroll for 3.
 unroll for 21; unroll for 17; unroll for 13; unroll for 9; unroll for 5; auto => /> .
 by rewrite -ext_eq_all /all_eq /keccak_C /idx /invidx /=.
seq 3: (#pre /\ d = keccak_D c).
 unroll for 3; auto => />.
 by rewrite -ext_eq_all /all_eq /keccak_D /idx /invidx /=; smt(W64.xorwC).
unroll for 2.
unroll for 15; unroll for 12; unroll for 9; unroll for 6; unroll for 3.
wp; skip => &m E @/keccak_theta_spec @/idx /=.
by rewrite -iotaredE /= /#.
qed.

(* precomputed rotation offsets *)
op rhotates: int Array25.t =
 Array25.of_list 0 [  0;  1; 62; 28; 27
                   ; 36; 44;  6; 55; 20
                   ;  3; 10; 43; 25; 39
                   ; 41; 45; 15; 21;  8
                   ; 18;  2; 61; 56; 14 ].


hoare keccak_rho_offsets_h _i:
  Spec.keccak_rho_offsets:
  0 <= i < 25 /\ i = _i ==> res = rhotates.[_i].
proof.
proc.
unroll for 5.
wp; auto => /> H1 H2.
rewrite initiE 1:/#.
have: _i \in iota_ 0 25 by smt(mem_iota).
move: {H1 H2} _i; apply/List.allP.
by rewrite -iotaredE /idx /= .
qed.

lemma rhotates_idx_mod64 _x _y:
 rhotates.[idx(_x,_y)] %% 64 = rhotates.[idx(_x,_y)].
proof.
pose i:= idx(_x,_y).
have: i \in iota_ 0 25.
 by rewrite mem_iota; smt(idx_bnd).
by move: i; rewrite -allP -iotaredE /= initiE /=.
qed.

op keccak_rho_op (A: state): state =
 Array25.init (fun i => A.[i] `|<<<|` rhotates.[i]).

op keccak_rho_spec (A A': state)=
 List.all (fun i => A'.[i] = A.[i] `|<<<|` rhotates.[i]) (iota_ 0 25).

lemma keccak_rhoP (A A': state):
 A' = keccak_rho_op A
 <=> keccak_rho_spec A A'.
proof.
by rewrite /keccak_rho_spec /keccak_rho_op -iotaredE -ext_eq_all /all_eq.
qed.

hoare keccak_rho_h _A:
 Spec.keccak_rho : a = _A ==> res = keccak_rho_op _A.
proof.
conseq (: _ ==> keccak_rho_spec _A res).
 by move=> /> r /keccak_rhoP.
proc.
while (0 <= i <= 25 /\
       forall j, 0 <= j < 25 => 
         a.[j] = if j < i
                 then _A.[j] `|<<<|` rhotates.[j]
                 else _A.[j]).
 wp; ecall (keccak_rho_offsets_h i).
 auto => /> &m Hi1 _ IH Hi2.
 split; first smt().
 move=> j Hj1 Hj2.
 case: (j = i{m}) => E.
  rewrite ifT 1:/# get_setE 1:/# E /=.
  move: (IH i{m} _); first smt().
  by rewrite ifF 1:/# => ->.
 rewrite get_setE 1:/# ifF //=. 
 have ->: (j < i{m} + 1) = (j < i{m}) by smt().
 by apply IH.
auto => />; split; first smt().
move=> A i ???; have ->: i=25 by smt().
move => H; rewrite /keccak_rho_spec allP => x.
rewrite mem_iota /= => Hx.
by rewrite H 1:/# ifT /#.
qed.

op keccak_pi_op (A: state): state =
 Array25.init (fun i => let (x,y) = invidx i in A.[idx(x+3*y, x)]).

op keccak_pi_spec (A A': state) =
 all (fun i => let (x,y) = invidx i in A'.[idx(x,y)] = A.[idx(x+3*y, x)]) (iota_ 0 25).

lemma keccak_piP A A':
 A' = keccak_pi_op A
 <=> keccak_pi_spec A A'.
proof.
by rewrite /keccak_pi_spec /keccak_pi_op /idx /invidx -iotaredE -!ext_eq_all /all_eq /=.
qed.

op keccak_pi_spec' (A B: state) =
 all (fun i => let (x,y) = invidx i in B.[idx(y,2*x+3*y)] = A.[idx(x,y)]) (iota_ 0 25).

lemma keccak_pi_spec_eq A B:
 keccak_pi_spec A B <=> keccak_pi_spec' A B
by rewrite /keccak_pi_spec /keccak_pi_spec' -!iotaredE /invidx /idx /= /#. 

hoare keccak_pi_h _A:
 Spec.keccak_pi : a = _A ==> res = keccak_pi_op _A.
proof.
conseq (: _ ==> keccak_pi_spec' _A res).
 by move=> /> r /keccak_pi_spec_eq /keccak_piP.
proc.
while (0 <= x <= 5 /\
       forall j y, 0 <= j < x => 0 <= y < 5 => 
                   a.[idx(y,2*j+3*y)] = b.[idx(j,y)]).
 wp; while (0 <= y <= 5 /\
            (forall j y, 0 <= j && j < x => 0 <= y && y < 5 => 
                         a.[idx (y, 2 * j + 3 * y)] = b.[idx (j, y)]) /\
            forall k, 0 <= k < y => a.[idx(k,2*x+3*k)] = b.[idx(x,k)]).
  auto => /> &1 Hy1 _ IH HH Hy2; split; first smt().
  split.
   move => j i *.
   rewrite get_setE. smt().
   case: (i=y{1} /\ j=x{1}) => E.
    by rewrite ifT /#.
   smt().
  move=> k Hk1 Hk2.
  rewrite get_setE. 
   by rewrite /idx /#.
  case: (k=y{1}) => E.
   by rewrite E ifT /#.
  by rewrite HH /#.
 auto => /> &m Hx1 Hx2 IH Hx.
 split; first smt().
 move=> A y ???.
 have ->: y=5 by smt().
 move=>IH2A IH2; split; first smt().
 move => /> j y1 *.
 case: (j = x{m}) => E.
  by rewrite E IH2 //= /#.
 by rewrite IH2A //= /#.
auto => /> *. 
split; first smt().
move=> A x ???; have ->: x=5 by smt().
by move => IH; rewrite /keccak_pi_spec' -iotaredE /invidx /= /#.
qed.

op keccak_chi_op (A: state): state =
 Array25.init
  (fun i => let (x,y) = invidx i in
            A.[idx(x,y)] `^` (invw A.[idx(x+1, y)] `&` A.[idx(x+2, y)])).

op keccak_chi_spec (A A': state) =
 forall x y,
  0 <= x < 5 => 0 <= y < 5 =>
    A'.[idx(x,y)]
    = A.[idx(x,y)] `^` (invw A.[idx(x+1, y)] `&` A.[idx(x+2, y)]).

op keccak_chi_spec' (A A': state) =
 all (fun x=> 
       all (fun y=> 
             A'.[idx(x,y)] = A.[idx(x,y)] `^` (invw A.[idx(x+1, y)] `&` A.[idx(x+2, y)]))
           (iota_ 0 5))
     (iota_ 0 5).

lemma keccak_chi_spec_eq A A':
 keccak_chi_spec A A' <=> keccak_chi_spec' A A'.
proof.
rewrite /keccak_chi_spec /keccak_chi_spec'; split.
move=> H; apply/List.allP => x /mem_iota /= Hx.
 by apply/List.allP => y /mem_iota /= Hy; apply H => /#.
move=> /List.allP H x y Hx Hy.
move: (H x _); first smt(mem_iota).
rewrite /= allP => {H} H.
move: (H y _); first smt(mem_iota).
done.
qed.

lemma keccak_chiP A A':
 A' = keccak_chi_op A
 <=> keccak_chi_spec A A'.
proof.
rewrite keccak_chi_spec_eq /keccak_chi_spec' /keccak_chi_op.
by rewrite -ext_eq_all /all_eq /invidx /idx -!iotaredE /= /#.
qed.

hoare keccak_chi_h _A:
 Spec.keccak_chi : a = _A ==> res = keccak_chi_op _A.
proof.
conseq (: a=_A ==> keccak_chi_spec _A res).
 by move=> /> r /keccak_chiP.
proc.
while (#pre /\ 0 <= y <= 5 /\  
       forall i j, 0 <= i < 5 => 0 <= j < y =>
        b.[idx(i,j)]
           = a.[idx(i,j)] `^`
             (invw a.[idx(i+1,j)] `&` a.[idx(i+2,j)])).
 wp; while (#pre /\ 0 <= x <= 5 /\
            forall i, 0 <= i < x =>
             b.[idx(i,y)]
             = a.[idx(i,y)] `^`
               (invw a.[idx(i+1,y)] `&` a.[idx(i+2,y)])).
  auto => /> &m Hy1 _ H1 Hy2 Hx1 _ H2 Hx2; split.
   move => i j Hi1 Hi2 Hj1 Hj2.
   rewrite /= get_setE 1:/# ifF 1:/#.
   by apply H1.
  split; first smt().
  move=> i Hi1 Hi2.
  case: (i = x{m}) => E.
   by rewrite !E get_setE 1:/# ifT 1://.
  rewrite /= get_setE 1:/# ifF 1:/#.
  by rewrite H2 /#.
 auto => /> &m Hy1 _ H Hy2; split; first smt().
 move=> A k ? H1 ??; have ->: k=5 by smt().
 move=> H2; split; first by smt().
 move=> i j Hi1 Hi2 Hj1 Hj2.
 case: (j = y{m}) => E.
  by rewrite !E H2.
 by rewrite H1 /#.
auto => />; split; first by smt().
move=> A j ???; have ->: j=5 by smt().
done.
qed.

op keccak_iota_op c (A: state) =
 A.[0 <- A.[0] `^` c].

op keccak_iota_spec c (A A': state) =
 A' = A.[0 <- A.[0] `^` c].

lemma keccak_iotaP c A A':
 A' = keccak_iota_op c A
 <=> keccak_iota_spec c A A'
by done.

hoare keccak_iota_h _c _A:
 Spec.keccak_iota : a = _A /\ c = _c ==> res = keccak_iota_op _c _A.
proof. by proc; auto => /> *. qed.


op keccak_round_op c (A: state) =
 keccak_iota_op c (keccak_chi_op (keccak_pi_op (keccak_rho_op (keccak_theta_op A)))).

(* obs: dosen't appear to be useful...
op keccak_round_spec c (A A': state) =
 exists B C D E,
  keccak_theta_spec A B /\
  keccak_rho_spec B C /\
  keccak_pi_spec C D /\
  keccak_chi_spec D E /\
  keccak_iota_spec c E A'.

lemma keccak_roundP c A A':
 A' = keccak_round_op c A
 <=> keccak_round_spec c A A'.
proof.
rewrite /keccak_round_op /keccak_round_spec; split.
 move=> H.
 exists (keccak_theta_op A) (keccak_rho_op (keccak_theta_op A)) 
   (keccak_pi_op (keccak_rho_op (keccak_theta_op A)))
   (keccak_chi_op (keccak_pi_op (keccak_rho_op (keccak_theta_op A)))).
 split; first by rewrite -keccak_thetaP.
 split; first by rewrite -keccak_rhoP.
 split; first by rewrite -keccak_piP.
 split; first by rewrite -keccak_chiP.
 by rewrite -keccak_iotaP.
move=> [B C D E] [/keccak_thetaP ?] [/keccak_rhoP ?] [/keccak_piP ?]
       [/keccak_chiP ?] /keccak_iotaP ? /#.
qed.
*)

op keccak_f1600_op (A: state) =
 foldl (fun s c => keccak_round_op c s) A (to_list rc_spec).

