(******************************************************************************
   Keccak_f1600_s_avx2_proof.ec:

   Correctness proof for the AVX2 implementation


   The AVX2 implementation is based on OpenSSL's. The proof strategy is
  based on unvectorisation.

******************************************************************************)
require import List Real Distr Int IntDiv CoreMap.

from Jasmin require import JModel.

require import Keccak_f1600_Spec_facts.
require import Keccak_f1600_s_spec_proof.


from JExtract require import Keccakf1600.
from JExtract require import Array6 Array7 Array9 WArray288 WArray768.

import Ring.IntID.

require import Ops.
import Array4.

op unpck (x: W256.t): t4u64 =
 Array4.init (fun i => x \bits64 i).

(*
abbrev KECCAK_RHOTATES_RIGHT = Array6.of_list witness [W256.of_int 144373339913893657577751063007562604548177214458152943091773;
W256.of_int 232252764209307188274174373867837442080505530800860351692863;
W256.of_int 156927543384667019098616994515559168111335794127330162507795;
W256.of_int 351517697181654122777866749001917765472957616589092975280182;
W256.of_int 276192476357013953622045746931053922384479139705868246843454;
W256.of_int 313855086769334038206421612937983674734430261968315659321364].


abbrev KECCAK_RHOTATES_LEFT = Array6.of_list witness [W256.of_int 257361171150853911329517531560668107745210100483895842570243;
W256.of_int 169481746855440380633094220700393270212881784141188433969153;
W256.of_int 244806967680080549808651600052671544182051520814718623154221;
W256.of_int 50216813883093446129401845566312946820429698352955810381834;
W256.of_int 125542034707733615285222847637176789908908175236180538818562;
W256.of_int 87879424295413530700846981630247037558957052973733126340652]*)


module Mvops = {
  proc step1(st0r st1r st2r st3r st4r st5r st6r : W256.t) : W256.t * W256.t * W256.t = {
  var c00, c14, d00, d14: W256.t;
  var t0, t1, t2, t4: W256.t;
  c00 <@ OpsV.iVPSHUFD_256( st2r, ((of_int 78))%W8);
  c14 <@ OpsV.ilxor4u64( st5r, st3r);
  t2 <@ OpsV.ilxor4u64( st4r, st6r);
  c14 <@ OpsV.ilxor4u64( c14, st1r);
  c14 <@ OpsV.ilxor4u64( c14, t2);
  t4 <@ OpsV.iVPERMQ( c14, ((of_int 147))%W8);
  c00 <@ OpsV.ilxor4u64( c00, st2r);
  t0 <@ OpsV.iVPERMQ( c00, ((of_int 78))%W8);
  t1 <@ OpsV.ivshr64u256( c14, ((of_int 63))%W8);
  t2 <@ OpsV.ivadd64u256( c14, c14);
  t1 <@ OpsV.ilor4u64( t1, t2);
  d14 <@ OpsV.iVPERMQ( t1, ((of_int 57))%W8);
  d00 <@ OpsV.ilxor4u64( t1, t4);
  d00 <@ OpsV.iVPERMQ( d00, ((of_int 0))%W8);
  c00 <@ OpsV.ilxor4u64( c00, st0r);
  c00 <@ OpsV.ilxor4u64( c00, t0);
  t0 <@ OpsV.ivshr64u256( c00, ((of_int 63))%W8);
  t1 <@ OpsV.ivadd64u256( c00, c00);
  t1 <@ OpsV.ilor4u64( t1, t0);
  st2r <@ OpsV.ilxor4u64( st2r, d00);
  st0r <@ OpsV.ilxor4u64( st0r, d00);
  d14 <@ OpsV.iVPBLENDD_256( d14, t1, ((of_int 192))%W8);
  t4 <@ OpsV.iVPBLENDD_256( t4, c00, ((of_int 3))%W8);
  d14 <@ OpsV.ilxor4u64( d14, t4);
  return (st0r,st2r, d14);
  }
  proc step2(st0r st1r st2r st3r st4r st5r st6r d14 : W256.t) : W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
      var t1, t2, t3, t4, t5, t6, t7, t8: W256.t;
    
      t3 <@ OpsV.iVPSLLV_4u64( st2r, (KECCAK_RHOTATES_LEFT.[0])%Array6);
      st2r <@ OpsV.iVPSRLV_4u64( st2r, (KECCAK_RHOTATES_RIGHT.[0])%Array6);
      st2r <@ OpsV.ilor4u64( st2r, t3);

      st3r <@ OpsV.ilxor4u64( st3r, d14);

      t4 <@ OpsV.iVPSLLV_4u64( st3r, (KECCAK_RHOTATES_LEFT.[2])%Array6);
      st3r <@ OpsV.iVPSRLV_4u64( st3r, (KECCAK_RHOTATES_RIGHT.[2])%Array6);
      st3r <@ OpsV.ilor4u64( st3r, t4);

      st4r <@ OpsV.ilxor4u64( st4r, d14);

      t5 <@ OpsV.iVPSLLV_4u64( st4r, (KECCAK_RHOTATES_LEFT.[3])%Array6);
      st4r <@ OpsV.iVPSRLV_4u64( st4r, (KECCAK_RHOTATES_RIGHT.[3])%Array6);
      st4r <@ OpsV.ilor4u64( st4r, t5);

      st5r <@ OpsV.ilxor4u64( st5r, d14);

      t6 <@ OpsV.iVPSLLV_4u64( st5r, (KECCAK_RHOTATES_LEFT.[4])%Array6);
      st5r <@ OpsV.iVPSRLV_4u64( st5r, (KECCAK_RHOTATES_RIGHT.[4])%Array6);
      st5r <@ OpsV.ilor4u64( st5r, t6);

      st6r <@ OpsV.ilxor4u64( st6r, d14);

      t3 <@ OpsV.iVPERMQ( st2r, ((of_int 141))%W8);
      t4 <@ OpsV.iVPERMQ( st3r, ((of_int 141))%W8);

      t7 <@ OpsV.iVPSLLV_4u64( st6r, (KECCAK_RHOTATES_LEFT.[5])%Array6);
      t1 <@ OpsV.iVPSRLV_4u64( st6r, (KECCAK_RHOTATES_RIGHT.[5])%Array6);
      t1 <@ OpsV.ilor4u64( t1, t7);

      st1r <@ OpsV.ilxor4u64( st1r, d14);

      t5 <@ OpsV.iVPERMQ( st4r, ((of_int 27))%W8);
      t6 <@ OpsV.iVPERMQ( st5r, ((of_int 114))%W8);

      t8 <@ OpsV.iVPSLLV_4u64( st1r, (KECCAK_RHOTATES_LEFT.[1])%Array6);
      t2 <@ OpsV.iVPSRLV_4u64( st1r, (KECCAK_RHOTATES_RIGHT.[1])%Array6);
      t2 <@ OpsV.ilor4u64( t2, t8);

    return (st1r, st2r, st3r, st4r, st5r, st6r, t1, t2, t3, t4, t5, t6);
  }

  proc step3(st0r st1r st2r st3r st4r st5r st6r t1 t2 t3 t4 t5 t6: W256.t) : W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
      var t0, t7, t8: W256.t;

      t7 <@ OpsV.iVPSRLDQ_256( t1, ((of_int 8))%W8);
      t0 <@ OpsV.ilandn4u64( t1, t7);
      st3r <@ OpsV.iVPBLENDD_256( t2, t6, ((of_int 12))%W8);
      t8 <@ OpsV.iVPBLENDD_256( t4, t2, ((of_int 12))%W8);
      st5r <@ OpsV.iVPBLENDD_256( t3, t4, ((of_int 12))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t2, t3, ((of_int 12))%W8);
      st3r <@ OpsV.iVPBLENDD_256( st3r, t4, ((of_int 48))%W8);
      t8 <@ OpsV.iVPBLENDD_256( t8, t5, ((of_int 48))%W8);
      st5r <@ OpsV.iVPBLENDD_256( st5r, t2, ((of_int 48))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t7, t6, ((of_int 48))%W8);
      st3r <@ OpsV.iVPBLENDD_256( st3r, t5, ((of_int 192))%W8);
      t8 <@ OpsV.iVPBLENDD_256( t8, t6, ((of_int 192))%W8);
      st5r <@ OpsV.iVPBLENDD_256( st5r, t6, ((of_int 192))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t7, t4, ((of_int 192))%W8);
      st3r <@ OpsV.ilandn4u64( st3r, t8);
      st5r <@ OpsV.ilandn4u64( st5r, t7);
      st6r <@ OpsV.iVPBLENDD_256( t5, t2, ((of_int 12))%W8);
      t8 <@ OpsV.iVPBLENDD_256( t3, t5, ((of_int 12))%W8);
      st3r <@ OpsV.ilxor4u64( st3r, t3);
      st6r <@ OpsV.iVPBLENDD_256( st6r, t3, ((of_int 48))%W8);
      t8 <@ OpsV.iVPBLENDD_256( t8, t4, ((of_int 48))%W8);
      st5r <@ OpsV.ilxor4u64( st5r, t5);
      st6r <@ OpsV.iVPBLENDD_256( st6r, t4, ((of_int 192))%W8);
      t8 <@ OpsV.iVPBLENDD_256( t8, t2, ((of_int 192))%W8);
      st6r <@ OpsV.ilandn4u64( st6r, t8);

      st6r <@ OpsV.ilxor4u64( st6r, t6);
      st4r <@ OpsV.iVPERMQ( t1, ((of_int 30))%W8);
      t8 <@ OpsV.iVPBLENDD_256( st4r, st0r, ((of_int 48))%W8);
      st1r <@ OpsV.iVPERMQ( t1, ((of_int 57))%W8);
      st1r <@ OpsV.iVPBLENDD_256( st1r, st0r, ((of_int 192))%W8);
      st1r <@ OpsV.ilandn4u64( st1r, t8);

      st2r <@ OpsV.iVPBLENDD_256( t4, t5, ((of_int 12))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t6, t4, ((of_int 12))%W8);
      st2r <@ OpsV.iVPBLENDD_256( st2r, t6, ((of_int 48))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t7, t3, ((of_int 48))%W8);
      st2r <@ OpsV.iVPBLENDD_256( st2r, t3, ((of_int 192))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t7, t5, ((of_int 192))%W8);
      st2r <@ OpsV.ilandn4u64( st2r, t7);
      st2r <@ OpsV.ilxor4u64( st2r, t2);

      t0 <@ OpsV.iVPERMQ( t0, ((of_int 0))%W8);
      st3r <@ OpsV.iVPERMQ( st3r, ((of_int 27))%W8);
      st5r <@ OpsV.iVPERMQ( st5r, ((of_int 141))%W8);
      st6r <@ OpsV.iVPERMQ( st6r, ((of_int 114))%W8);
      st4r <@ OpsV.iVPBLENDD_256( t6, t3, ((of_int 12))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t5, t6, ((of_int 12))%W8);
      st4r <@ OpsV.iVPBLENDD_256( st4r, t5, ((of_int 48))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t7, t2, ((of_int 48))%W8);
      st4r <@ OpsV.iVPBLENDD_256( st4r, t2, ((of_int 192))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t7, t3, ((of_int 192))%W8);
      st4r <@ OpsV.ilandn4u64( st4r, t7);

      st0r <@ OpsV.ilxor4u64( st0r, t0);
      st1r <@ OpsV.ilxor4u64( st1r, t1);
      st4r <@ OpsV.ilxor4u64( st4r, t4);

    return (st0r, st1r, st2r, st3r, st4r, st5r, st6r);
  }
  proc _keccakf1600_opsvX(st0r st1r st2r st3r st4r st5r st6r : W256.t) :
    W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
    var r;
    var c00 : W256.t;
    var c14 : W256.t;
    var t0, t1, t2, t3, t4, t5, t6, t7, t8: W256.t;
    var d14 : W256.t;
    var d00 : W256.t;
    r <- 0;
    while (r < 24){
      (st0r, st2r, d14) <@ step1(st0r,st1r,st2r,st3r,st4r,st5r,st6r);
      (st1r, st2r, st3r, st4r, st5r, st6r, t1, t2, t3, t4, t5, t6) <@ step2(st0r,st1r,st2r,st3r,st4r,st5r,st6r,d14);
      (st0r, st1r, st2r, st3r, st4r, st5r, st6r) <@ step3(st0r,st1r,st2r,st3r,st4r,st5r,st6r,t1, t2, t3, t4, t5, t6);
      st0r <@ OpsV.ilxor4u64( st0r, KECCAK_IOTAS.[r]);
      r <- r + 1;
    }
    return (st0r, st1r, st2r, st3r, st4r, st5r, st6r);
  }
  proc _keccakf1600_opsv(st0r st1r st2r st3r st4r st5r st6r : W256.t) :
    W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
    var r;
    var c00 : W256.t;
    var c14 : W256.t;
    var t0, t1, t2, t3, t4, t5, t6, t7, t8: W256.t;
    var d14 : W256.t;
    var d00 : W256.t;
    r <- 0;
    while (r < 24){
      c00 <@ OpsV.iVPSHUFD_256( st2r, ((of_int 78))%W8);
      c14 <@ OpsV.ilxor4u64( st5r, st3r);
      t2 <@ OpsV.ilxor4u64( st4r, st6r);
      c14 <@ OpsV.ilxor4u64( c14, st1r);
      c14 <@ OpsV.ilxor4u64( c14, t2);
      t4 <@ OpsV.iVPERMQ( c14, ((of_int 147))%W8);
      c00 <@ OpsV.ilxor4u64( c00, st2r);
      t0 <@ OpsV.iVPERMQ( c00, ((of_int 78))%W8);
      t1 <@ OpsV.ivshr64u256( c14, ((of_int 63))%W8);
      t2 <@ OpsV.ivadd64u256( c14, c14);
      t1 <@ OpsV.ilor4u64( t1, t2);
      d14 <@ OpsV.iVPERMQ( t1, ((of_int 57))%W8);
      d00 <@ OpsV.ilxor4u64( t1, t4);
      d00 <@ OpsV.iVPERMQ( d00, ((of_int 0))%W8);
      c00 <@ OpsV.ilxor4u64( c00, st0r);
      c00 <@ OpsV.ilxor4u64( c00, t0);
      t0 <@ OpsV.ivshr64u256( c00, ((of_int 63))%W8);
      t1 <@ OpsV.ivadd64u256( c00, c00);
      t1 <@ OpsV.ilor4u64( t1, t0);
      st2r <@ OpsV.ilxor4u64( st2r, d00);
      st0r <@ OpsV.ilxor4u64( st0r, d00);
      d14 <@ OpsV.iVPBLENDD_256( d14, t1, ((of_int 192))%W8);
      t4 <@ OpsV.iVPBLENDD_256( t4, c00, ((of_int 3))%W8);
      d14 <@ OpsV.ilxor4u64( d14, t4);

      t3 <@ OpsV.iVPSLLV_4u64( st2r, (KECCAK_RHOTATES_LEFT.[0])%Array6);
      st2r <@ OpsV.iVPSRLV_4u64( st2r, (KECCAK_RHOTATES_RIGHT.[0])%Array6);
      st2r <@ OpsV.ilor4u64( st2r, t3);
      st3r <@ OpsV.ilxor4u64( st3r, d14);
      t4 <@ OpsV.iVPSLLV_4u64( st3r, (KECCAK_RHOTATES_LEFT.[2])%Array6);
      st3r <@ OpsV.iVPSRLV_4u64( st3r, (KECCAK_RHOTATES_RIGHT.[2])%Array6);
      st3r <@ OpsV.ilor4u64( st3r, t4);
      st4r <@ OpsV.ilxor4u64( st4r, d14);
      t5 <@ OpsV.iVPSLLV_4u64( st4r, (KECCAK_RHOTATES_LEFT.[3])%Array6);
      st4r <@ OpsV.iVPSRLV_4u64( st4r, (KECCAK_RHOTATES_RIGHT.[3])%Array6);
      st4r <@ OpsV.ilor4u64( st4r, t5);
      st5r <@ OpsV.ilxor4u64( st5r, d14);
      t6 <@ OpsV.iVPSLLV_4u64( st5r, (KECCAK_RHOTATES_LEFT.[4])%Array6);
      st5r <@ OpsV.iVPSRLV_4u64( st5r, (KECCAK_RHOTATES_RIGHT.[4])%Array6);
      st5r <@ OpsV.ilor4u64( st5r, t6);
      st6r <@ OpsV.ilxor4u64( st6r, d14);
      t3 <@ OpsV.iVPERMQ( st2r, ((of_int 141))%W8);
      t4 <@ OpsV.iVPERMQ( st3r, ((of_int 141))%W8);
      t7 <@ OpsV.iVPSLLV_4u64( st6r, (KECCAK_RHOTATES_LEFT.[5])%Array6);
      t1 <@ OpsV.iVPSRLV_4u64( st6r, (KECCAK_RHOTATES_RIGHT.[5])%Array6);
      t1 <@ OpsV.ilor4u64( t1, t7);
      st1r <@ OpsV.ilxor4u64( st1r, d14);
      t5 <@ OpsV.iVPERMQ( st4r, ((of_int 27))%W8);
      t6 <@ OpsV.iVPERMQ( st5r, ((of_int 114))%W8);
      t8 <@ OpsV.iVPSLLV_4u64( st1r, (KECCAK_RHOTATES_LEFT.[1])%Array6);
      t2 <@ OpsV.iVPSRLV_4u64( st1r, (KECCAK_RHOTATES_RIGHT.[1])%Array6);
      t2 <@ OpsV.ilor4u64( t2, t8);

      t7 <@ OpsV.iVPSRLDQ_256( t1, ((of_int 8))%W8);
      t0 <@ OpsV.ilandn4u64( t1, t7);
      st3r <@ OpsV.iVPBLENDD_256( t2, t6, ((of_int 12))%W8);
      t8 <@ OpsV.iVPBLENDD_256( t4, t2, ((of_int 12))%W8);
      st5r <@ OpsV.iVPBLENDD_256( t3, t4, ((of_int 12))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t2, t3, ((of_int 12))%W8);
      st3r <@ OpsV.iVPBLENDD_256( st3r, t4, ((of_int 48))%W8);
      t8 <@ OpsV.iVPBLENDD_256( t8, t5, ((of_int 48))%W8);
      st5r <@ OpsV.iVPBLENDD_256( st5r, t2, ((of_int 48))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t7, t6, ((of_int 48))%W8);
      st3r <@ OpsV.iVPBLENDD_256( st3r, t5, ((of_int 192))%W8);
      t8 <@ OpsV.iVPBLENDD_256( t8, t6, ((of_int 192))%W8);
      st5r <@ OpsV.iVPBLENDD_256( st5r, t6, ((of_int 192))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t7, t4, ((of_int 192))%W8);
      st3r <@ OpsV.ilandn4u64( st3r, t8);
      st5r <@ OpsV.ilandn4u64( st5r, t7);
      st6r <@ OpsV.iVPBLENDD_256( t5, t2, ((of_int 12))%W8);
      t8 <@ OpsV.iVPBLENDD_256( t3, t5, ((of_int 12))%W8);
      st3r <@ OpsV.ilxor4u64( st3r, t3);
      st6r <@ OpsV.iVPBLENDD_256( st6r, t3, ((of_int 48))%W8);
      t8 <@ OpsV.iVPBLENDD_256( t8, t4, ((of_int 48))%W8);
      st5r <@ OpsV.ilxor4u64( st5r, t5);
      st6r <@ OpsV.iVPBLENDD_256( st6r, t4, ((of_int 192))%W8);
      t8 <@ OpsV.iVPBLENDD_256( t8, t2, ((of_int 192))%W8);
      st6r <@ OpsV.ilandn4u64( st6r, t8);
      st6r <@ OpsV.ilxor4u64( st6r, t6);
      st4r <@ OpsV.iVPERMQ( t1, ((of_int 30))%W8);
      t8 <@ OpsV.iVPBLENDD_256( st4r, st0r, ((of_int 48))%W8);
      st1r <@ OpsV.iVPERMQ( t1, ((of_int 57))%W8);
      st1r <@ OpsV.iVPBLENDD_256( st1r, st0r, ((of_int 192))%W8);
      st1r <@ OpsV.ilandn4u64( st1r, t8);
      st2r <@ OpsV.iVPBLENDD_256( t4, t5, ((of_int 12))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t6, t4, ((of_int 12))%W8);
      st2r <@ OpsV.iVPBLENDD_256( st2r, t6, ((of_int 48))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t7, t3, ((of_int 48))%W8);
      st2r <@ OpsV.iVPBLENDD_256( st2r, t3, ((of_int 192))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t7, t5, ((of_int 192))%W8);
      st2r <@ OpsV.ilandn4u64( st2r, t7);
      st2r <@ OpsV.ilxor4u64( st2r, t2);
      t0 <@ OpsV.iVPERMQ( t0, ((of_int 0))%W8);
      st3r <@ OpsV.iVPERMQ( st3r, ((of_int 27))%W8);
      st5r <@ OpsV.iVPERMQ( st5r, ((of_int 141))%W8);
      st6r <@ OpsV.iVPERMQ( st6r, ((of_int 114))%W8);
      st4r <@ OpsV.iVPBLENDD_256( t6, t3, ((of_int 12))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t5, t6, ((of_int 12))%W8);
      st4r <@ OpsV.iVPBLENDD_256( st4r, t5, ((of_int 48))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t7, t2, ((of_int 48))%W8);
      st4r <@ OpsV.iVPBLENDD_256( st4r, t2, ((of_int 192))%W8);
      t7 <@ OpsV.iVPBLENDD_256( t7, t3, ((of_int 192))%W8);
      st4r <@ OpsV.ilandn4u64( st4r, t7);
      st0r <@ OpsV.ilxor4u64( st0r, t0);
      st1r <@ OpsV.ilxor4u64( st1r, t1);
      st4r <@ OpsV.ilxor4u64( st4r, t4);
      st0r <@ OpsV.ilxor4u64( st0r, KECCAK_IOTAS.[r]);
      r <- r + 1;
    }
    return (st0r, st1r, st2r, st3r, st4r, st5r, st6r);
  }

  proc _keccakf1600_ops(st0r st1r st2r st3r st4r st5r st6r : t4u64) :
    t4u64 * t4u64 * t4u64 * t4u64 * t4u64 * t4u64 * t4u64 = {
    var iotas_p : W256.t Array24.t;
    var iotas_o : W64.t;
    var rhotates_left_p : W256.t Array6.t;
    var rhotates_right_p : W256.t Array6.t;
    var r : W64.t;
    var c00 : t4u64;
    var c14 : t4u64;
    var t0, t1, t2, t3, t4, t5, t6, t7, t8: t4u64;
    var d14 : t4u64;
    var d00 : t4u64;
    var zf : bool;
    var _0 : bool;
    var _1 : bool;
    var _2 : bool;
    
    iotas_p <- witness;
    rhotates_left_p <- witness;
    rhotates_right_p <- witness;
    iotas_p <- KECCAK_IOTAS;
    iotas_o <- W64.zero;
    rhotates_left_p <- KECCAK_RHOTATES_LEFT;
    rhotates_right_p <- KECCAK_RHOTATES_RIGHT;
    r <- (of_int 24)%W64;
    while (W64.zero \ult r){
      c00 <@ Ops.iVPSHUFD_256( st2r, ((of_int 78))%W8);
      c14 <@ Ops.ilxor4u64( st5r, st3r);
      t2 <@ Ops.ilxor4u64( st4r, st6r);
      c14 <@ Ops.ilxor4u64( c14, st1r);
      c14 <@ Ops.ilxor4u64( c14, t2);
      t4 <@ Ops.iVPERMQ( c14, ((of_int 147))%W8);
      c00 <@ Ops.ilxor4u64( c00, st2r);
      t0 <@ Ops.iVPERMQ( c00, ((of_int 78))%W8);
      t1 <@ Ops.ivshr64u256( c14, ((of_int 63))%W8);
      t2 <@ Ops.ivadd64u256( c14, c14);
      t1 <@ Ops.ilor4u64( t1, t2);
      d14 <@ Ops.iVPERMQ( t1, ((of_int 57))%W8);
      d00 <@ Ops.ilxor4u64( t1, t4);
      d00 <@ Ops.iVPERMQ( d00, ((of_int 0))%W8);
      c00 <@ Ops.ilxor4u64( c00, st0r);
      c00 <@ Ops.ilxor4u64( c00, t0);
      t0 <@ Ops.ivshr64u256( c00, ((of_int 63))%W8);
      t1 <@ Ops.ivadd64u256( c00, c00);
      t1 <@ Ops.ilor4u64( t1, t0);
      st2r <@ Ops.ilxor4u64( st2r, d00);
      st0r <@ Ops.ilxor4u64( st0r, d00);
      d14 <@ Ops.iVPBLENDD_256( d14, t1, ((of_int 192))%W8);
      t4 <@ Ops.iVPBLENDD_256( t4, c00, ((of_int 3))%W8);
      d14 <@ Ops.ilxor4u64( d14, t4);

      t3 <@ Ops.iVPSLLV_4u64( st2r, unpck (rhotates_left_p.[0])%Array6);
      st2r <@ Ops.iVPSRLV_4u64( st2r, unpck (rhotates_right_p.[0])%Array6);
      st2r <@ Ops.ilor4u64( st2r, t3);
      st3r <@ Ops.ilxor4u64( st3r, d14);
      t4 <@ Ops.iVPSLLV_4u64( st3r, unpck (rhotates_left_p.[2])%Array6);
      st3r <@ Ops.iVPSRLV_4u64( st3r, unpck (rhotates_right_p.[2])%Array6);
      st3r <@ Ops.ilor4u64( st3r, t4);
      st4r <@ Ops.ilxor4u64( st4r, d14);
      t5 <@ Ops.iVPSLLV_4u64( st4r, unpck (rhotates_left_p.[3])%Array6);
      st4r <@ Ops.iVPSRLV_4u64( st4r, unpck (rhotates_right_p.[3])%Array6);
      st4r <@ Ops.ilor4u64( st4r, t5);
      st5r <@ Ops.ilxor4u64( st5r, d14);
      t6 <@ Ops.iVPSLLV_4u64( st5r, unpck (rhotates_left_p.[4])%Array6);
      st5r <@ Ops.iVPSRLV_4u64( st5r, unpck (rhotates_right_p.[4])%Array6);
      st5r <@ Ops.ilor4u64( st5r, t6);
      st6r <@ Ops.ilxor4u64( st6r, d14);
      t3 <@ Ops.iVPERMQ( st2r, ((of_int 141))%W8);
      t4 <@ Ops.iVPERMQ( st3r, ((of_int 141))%W8);
      t7 <@ Ops.iVPSLLV_4u64( st6r, unpck (rhotates_left_p.[5])%Array6);
      t1 <@ Ops.iVPSRLV_4u64( st6r, unpck (rhotates_right_p.[5])%Array6);
      t1 <@ Ops.ilor4u64( t1, t7);
      st1r <@ Ops.ilxor4u64( st1r, d14);
      t5 <@ Ops.iVPERMQ( st4r, ((of_int 27))%W8);
      t6 <@ Ops.iVPERMQ( st5r, ((of_int 114))%W8);
      t8 <@ Ops.iVPSLLV_4u64( st1r, unpck (rhotates_left_p.[1])%Array6);
      t2 <@ Ops.iVPSRLV_4u64( st1r, unpck (rhotates_right_p.[1])%Array6);
      t2 <@ Ops.ilor4u64( t2, t8);

      t7 <@ Ops.iVPSRLDQ_256( t1, ((of_int 8))%W8);
      t0 <@ Ops.ilandn4u64( t1, t7);
      st3r <@ Ops.iVPBLENDD_256( t2, t6, ((of_int 12))%W8);
      t8 <@ Ops.iVPBLENDD_256( t4, t2, ((of_int 12))%W8);
      st5r <@ Ops.iVPBLENDD_256( t3, t4, ((of_int 12))%W8);
      t7 <@ Ops.iVPBLENDD_256( t2, t3, ((of_int 12))%W8);
      st3r <@ Ops.iVPBLENDD_256( st3r, t4, ((of_int 48))%W8);
      t8 <@ Ops.iVPBLENDD_256( t8, t5, ((of_int 48))%W8);
      st5r <@ Ops.iVPBLENDD_256( st5r, t2, ((of_int 48))%W8);
      t7 <@ Ops.iVPBLENDD_256( t7, t6, ((of_int 48))%W8);
      st3r <@ Ops.iVPBLENDD_256( st3r, t5, ((of_int 192))%W8);
      t8 <@ Ops.iVPBLENDD_256( t8, t6, ((of_int 192))%W8);
      st5r <@ Ops.iVPBLENDD_256( st5r, t6, ((of_int 192))%W8);
      t7 <@ Ops.iVPBLENDD_256( t7, t4, ((of_int 192))%W8);
      st3r <@ Ops.ilandn4u64( st3r, t8);
      st5r <@ Ops.ilandn4u64( st5r, t7);
      st6r <@ Ops.iVPBLENDD_256( t5, t2, ((of_int 12))%W8);
      t8 <@ Ops.iVPBLENDD_256( t3, t5, ((of_int 12))%W8);
      st3r <@ Ops.ilxor4u64( st3r, t3);
      st6r <@ Ops.iVPBLENDD_256( st6r, t3, ((of_int 48))%W8);
      t8 <@ Ops.iVPBLENDD_256( t8, t4, ((of_int 48))%W8);
      st5r <@ Ops.ilxor4u64( st5r, t5);
      st6r <@ Ops.iVPBLENDD_256( st6r, t4, ((of_int 192))%W8);
      t8 <@ Ops.iVPBLENDD_256( t8, t2, ((of_int 192))%W8);
      st6r <@ Ops.ilandn4u64( st6r, t8);
      st6r <@ Ops.ilxor4u64( st6r, t6);
      st4r <@ Ops.iVPERMQ( t1, ((of_int 30))%W8);
      t8 <@ Ops.iVPBLENDD_256( st4r, st0r, ((of_int 48))%W8);
      st1r <@ Ops.iVPERMQ( t1, ((of_int 57))%W8);
      st1r <@ Ops.iVPBLENDD_256( st1r, st0r, ((of_int 192))%W8);
      st1r <@ Ops.ilandn4u64( st1r, t8);
      st2r <@ Ops.iVPBLENDD_256( t4, t5, ((of_int 12))%W8);
      t7 <@ Ops.iVPBLENDD_256( t6, t4, ((of_int 12))%W8);
      st2r <@ Ops.iVPBLENDD_256( st2r, t6, ((of_int 48))%W8);
      t7 <@ Ops.iVPBLENDD_256( t7, t3, ((of_int 48))%W8);
      st2r <@ Ops.iVPBLENDD_256( st2r, t3, ((of_int 192))%W8);
      t7 <@ Ops.iVPBLENDD_256( t7, t5, ((of_int 192))%W8);
      st2r <@ Ops.ilandn4u64( st2r, t7);
      st2r <@ Ops.ilxor4u64( st2r, t2);
      t0 <@ Ops.iVPERMQ( t0, ((of_int 0))%W8);
      st3r <@ Ops.iVPERMQ( st3r, ((of_int 27))%W8);
      st5r <@ Ops.iVPERMQ( st5r, ((of_int 141))%W8);
      st6r <@ Ops.iVPERMQ( st6r, ((of_int 114))%W8);
      st4r <@ Ops.iVPBLENDD_256( t6, t3, ((of_int 12))%W8);
      t7 <@ Ops.iVPBLENDD_256( t5, t6, ((of_int 12))%W8);
      st4r <@ Ops.iVPBLENDD_256( st4r, t5, ((of_int 48))%W8);
      t7 <@ Ops.iVPBLENDD_256( t7, t2, ((of_int 48))%W8);
      st4r <@ Ops.iVPBLENDD_256( st4r, t2, ((of_int 192))%W8);
      t7 <@ Ops.iVPBLENDD_256( t7, t3, ((of_int 192))%W8);
      st4r <@ Ops.ilandn4u64( st4r, t7);
      st0r <@ Ops.ilxor4u64( st0r, t0);
      st1r <@ Ops.ilxor4u64( st1r, t1);
      st4r <@ Ops.ilxor4u64( st4r, t4);
      st0r <@ Ops.ilxor4u64( st0r, unpck (get256_direct ((init256 (fun (i : int) => iotas_p.[i])))%WArray768 (to_uint iotas_o))%WArray768);
      iotas_o <- iotas_o + (of_int 32)%W64;
      (_0, _1, _2, zf, r) <- DEC_64 r;
    }
    return (st0r, st1r, st2r, st3r, st4r, st5r, st6r);
  }
}.

lemma get256_init256 (a: W256.t Array24.t) i:
 0 <= i < 24 =>
 get256 (WArray768.init256 ("_.[_]" a)) i = a.[i].
proof.
move=> Hi; rewrite /get256_direct /init256 -(unpack8K a.[i]).
congr; apply W32u8.Pack.ext_eq => x Hx.
rewrite initiE //= unpack8E !initiE 1..2:/# /=; congr.
 congr; smt().
smt().
qed.


equiv mopsv:
 M._keccakf1600_avx2 ~ Mvops._keccakf1600_opsv:
 ={arg} ==> ={res}.
proof.
proc.
while (#pre /\ 0 <= r{2} <= 24 /\
       to_uint r{1}=24-r{2} /\
       to_uint iotas_o{1}=32*r{2} /\
       iotas_p{1}=KECCAK_IOTAS /\
       rhotates_left_p{1}=KECCAK_RHOTATES_LEFT /\
       rhotates_right_p{1}=KECCAK_RHOTATES_RIGHT).
 seq 24 24: (#pre /\ ={d00,d14}).
  by inline*; auto => /> *.
 seq 18 18: (#pre /\ (t.[3],t.[4],t.[5],t.[6]){1}=(t3,t4,t5,t6){2}).
  by inline*; auto => /> *. 
 seq 27 27: (#pre /\ (t.[0],t.[1],t.[2],t.[3],t.[4],t.[5],t.[6],t.[7],t.[8]){1}=(t0,t1,t2,t3,t4,t5,t6,t7,t8){2}).
  by inline*; auto => /> *.
 inline*; auto => /> &1 &2 ?? E1 E2 *.
 rewrite E2 get256_init256 1:/# => />.
 rewrite /DEC_64 /rflags_of_aluop_nocf_w /= to_uintB /=.
  by rewrite uleE /#.
 split.
  split; first smt().
  split; first smt().
  by rewrite to_uintD_small 1:/# /#.
 rewrite !ultE to_uintB /=.
  by rewrite uleE /#.
 smt().
by auto => />.
qed.

equiv mopsvX:
 M._keccakf1600_avx2 ~ Mvops._keccakf1600_opsvX:
 ={arg} ==> ={res}.
proof.
proc.
while (#pre /\ 0 <= r{2} <= 24 /\
       to_uint r{1}=24-r{2} /\
       to_uint iotas_o{1}=32*r{2} /\
       iotas_p{1}=KECCAK_IOTAS /\
       rhotates_left_p{1}=KECCAK_RHOTATES_LEFT /\
       rhotates_right_p{1}=KECCAK_RHOTATES_RIGHT).
 seq 24 1: (#pre /\ ={d14}).
  by inline*; auto => /> &1 &2 *.
 seq 27 1: (#pre /\ (t.[1],t.[2],t.[3],t.[4],t.[5],t.[6]){1}=(t1,t2,t3,t4,t5,t6){2}).
  by inline*; auto => /> *. 
 inline*; auto => /> &1 &2 ?? E1 E2 *.
 rewrite E2 get256_init256 1:/# => />.
 rewrite /DEC_64 /rflags_of_aluop_nocf_w /= to_uintB /=.
  by rewrite uleE /#.
 split.
  split; first smt().
  split; first smt().
  by rewrite to_uintD_small 1:/# /#.
 rewrite !ultE to_uintB /=.
  by rewrite uleE /#.
 smt().
by auto => />.
qed.

op match_states( st1 : W64.t Array4.t * W64.t Array4.t * W64.t Array4.t * W64.t Array4.t *
    W64.t Array4.t * W64.t Array4.t * W64.t Array4.t, 
                st2 : W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t) =
   is4u64 st1.`1 st2.`1 /\
   is4u64 st1.`2 st2.`2 /\
   is4u64 st1.`3 st2.`3 /\
   is4u64 st1.`4 st2.`4 /\
   is4u64 st1.`5 st2.`5 /\
   is4u64 st1.`6 st2.`6 /\
   is4u64 st1.`7 st2.`7.


module Mopenssl = {
  proc __keccak_f1600_avx2_openssl (a00:W256.t, a01:W256.t, a20:W256.t,
                                    a31:W256.t, a21:W256.t, a41:W256.t,
                                    a11:W256.t, _rhotates_left:W64.t,
                                    _rhotates_right:W64.t, _iotas:W64.t) : 
  W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
    
    var rhotates_left:W64.t;
    var rhotates_right:W64.t;
    var iotas:W64.t;
    var i:W32.t;
    var zf:bool;
    var c00:W256.t;
    var c14:W256.t;
    var t:W256.t Array9.t;
    var d14:W256.t;
    var d00:W256.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    t <- witness;
    rhotates_left <- (_rhotates_left + (W64.of_int 96));
    rhotates_right <- (_rhotates_right + (W64.of_int 96));
    iotas <- _iotas;
    i <- (W32.of_int 24);
    c00 <- VPSHUFD_256 a20 (W8.of_int 78);
    c14 <- (a41 `^` a31);
    t.[2] <- (a21 `^` a11);
    c14 <- (c14 `^` a01);
    c14 <- (c14 `^` t.[2]);
    t.[4] <- VPERMQ c14 (W8.of_int 147);
    c00 <- (c00 `^` a20);
    t.[0] <- VPERMQ c00 (W8.of_int 78);
    t.[1] <- (c14 \vshr64u256 (W8.of_int 63));
    t.[2] <- (c14 \vadd64u256 c14);
    t.[1] <- (t.[1] `|` t.[2]);
    d14 <- VPERMQ t.[1] (W8.of_int 57);
    d00 <- (t.[1] `^` t.[4]);
    d00 <- VPERMQ d00 (W8.of_int 0);
    c00 <- (c00 `^` a00);
    c00 <- (c00 `^` t.[0]);
    t.[0] <- (c00 \vshr64u256 (W8.of_int 63));
    t.[1] <- (c00 \vadd64u256 c00);
    t.[1] <- (t.[1] `|` t.[0]);
    a20 <- (a20 `^` d00);
    a00 <- (a00 `^` d00);
    d14 <- VPBLENDD_256 d14 t.[1]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
    t.[4] <- VPBLENDD_256 t.[4] c00
    (W8.of_int (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    d14 <- (d14 `^` t.[4]);
    t.[3] <- VPSLLV_4u64 a20
    (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((0 * 32) - 96)))));
    a20 <- VPSRLV_4u64 a20
    (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((0 * 32) - 96)))));
    a20 <- (a20 `|` t.[3]);
    a31 <- (a31 `^` d14);
    t.[4] <- VPSLLV_4u64 a31
    (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((2 * 32) - 96)))));
    a31 <- VPSRLV_4u64 a31
    (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((2 * 32) - 96)))));
    a31 <- (a31 `|` t.[4]);
    a21 <- (a21 `^` d14);
    t.[5] <- VPSLLV_4u64 a21
    (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((3 * 32) - 96)))));
    a21 <- VPSRLV_4u64 a21
    (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((3 * 32) - 96)))));
    a21 <- (a21 `|` t.[5]);
    a41 <- (a41 `^` d14);
    t.[6] <- VPSLLV_4u64 a41
    (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((4 * 32) - 96)))));
    a41 <- VPSRLV_4u64 a41
    (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((4 * 32) - 96)))));
    a41 <- (a41 `|` t.[6]);
    a11 <- (a11 `^` d14);
    t.[3] <- VPERMQ a20 (W8.of_int 141);
    t.[4] <- VPERMQ a31 (W8.of_int 141);
    t.[7] <- VPSLLV_4u64 a11
    (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((5 * 32) - 96)))));
    t.[1] <- VPSRLV_4u64 a11
    (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((5 * 32) - 96)))));
    t.[1] <- (t.[1] `|` t.[7]);
    a01 <- (a01 `^` d14);
    t.[5] <- VPERMQ a21 (W8.of_int 27);
    t.[6] <- VPERMQ a41 (W8.of_int 114);
    t.[8] <- VPSLLV_4u64 a01
    (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((1 * 32) - 96)))));
    t.[2] <- VPSRLV_4u64 a01
    (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((1 * 32) - 96)))));
    t.[2] <- (t.[2] `|` t.[8]);
    t.[7] <- VPSRLDQ_256 t.[1] (W8.of_int 8);
    t.[0] <- ((invw t.[1]) `&` t.[7]);
    a31 <- VPBLENDD_256 t.[2] t.[6]
    (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    t.[8] <- VPBLENDD_256 t.[4] t.[2]
    (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    a41 <- VPBLENDD_256 t.[3] t.[4]
    (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    t.[7] <- VPBLENDD_256 t.[2] t.[3]
    (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    a31 <- VPBLENDD_256 a31 t.[4]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    t.[8] <- VPBLENDD_256 t.[8] t.[5]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    a41 <- VPBLENDD_256 a41 t.[2]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    t.[7] <- VPBLENDD_256 t.[7] t.[6]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    a31 <- VPBLENDD_256 a31 t.[5]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
    t.[8] <- VPBLENDD_256 t.[8] t.[6]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
    a41 <- VPBLENDD_256 a41 t.[6]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
    t.[7] <- VPBLENDD_256 t.[7] t.[4]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
    a31 <- VPANDN_256 a31 t.[8];
    a41 <- VPANDN_256 a41 t.[7];
    a11 <- VPBLENDD_256 t.[5] t.[2]
    (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    t.[8] <- VPBLENDD_256 t.[3] t.[5]
    (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    a31 <- (a31 `^` t.[3]);
    a11 <- VPBLENDD_256 a11 t.[3]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    t.[8] <- VPBLENDD_256 t.[8] t.[4]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    a41 <- (a41 `^` t.[5]);
    a11 <- VPBLENDD_256 a11 t.[4]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
    t.[8] <- VPBLENDD_256 t.[8] t.[2]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
    a11 <- VPANDN_256 a11 t.[8];
    a11 <- (a11 `^` t.[6]);
    a21 <- VPERMQ t.[1] (W8.of_int 30);
    t.[8] <- VPBLENDD_256 a21 a00
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    a01 <- VPERMQ t.[1] (W8.of_int 57);
    a01 <- VPBLENDD_256 a01 a00
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
    a01 <- VPANDN_256 a01 t.[8];
    a20 <- VPBLENDD_256 t.[4] t.[5]
    (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    t.[7] <- VPBLENDD_256 t.[6] t.[4]
    (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    a20 <- VPBLENDD_256 a20 t.[6]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    t.[7] <- VPBLENDD_256 t.[7] t.[3]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    a20 <- VPBLENDD_256 a20 t.[3]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
    t.[7] <- VPBLENDD_256 t.[7] t.[5]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
    a20 <- VPANDN_256 a20 t.[7];
    a20 <- (a20 `^` t.[2]);
    t.[0] <- VPERMQ t.[0] (W8.of_int 0);
    a31 <- VPERMQ a31 (W8.of_int 27);
    a41 <- VPERMQ a41 (W8.of_int 141);
    a11 <- VPERMQ a11 (W8.of_int 114);
    a21 <- VPBLENDD_256 t.[6] t.[3]
    (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    t.[7] <- VPBLENDD_256 t.[5] t.[6]
    (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    a21 <- VPBLENDD_256 a21 t.[5]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    t.[7] <- VPBLENDD_256 t.[7] t.[2]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    a21 <- VPBLENDD_256 a21 t.[2]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
    t.[7] <- VPBLENDD_256 t.[7] t.[3]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
    a21 <- VPANDN_256 a21 t.[7];
    a00 <- (a00 `^` t.[0]);
    a01 <- (a01 `^` t.[1]);
    a21 <- (a21 `^` t.[4]);
    a00 <-
    (a00 `^` (loadW256 Glob.mem (W64.to_uint (iotas + (W64.of_int 0)))));
    iotas <- (iotas + (W64.of_int 32));
    ( _0,  _1,  _2, zf, i) <- DEC_32 i;
    while ((! zf)) {
      c00 <- VPSHUFD_256 a20 (W8.of_int 78);
      c14 <- (a41 `^` a31);
      t.[2] <- (a21 `^` a11);
      c14 <- (c14 `^` a01);
      c14 <- (c14 `^` t.[2]);
      t.[4] <- VPERMQ c14 (W8.of_int 147);
      c00 <- (c00 `^` a20);
      t.[0] <- VPERMQ c00 (W8.of_int 78);
      t.[1] <- (c14 \vshr64u256 (W8.of_int 63));
      t.[2] <- (c14 \vadd64u256 c14);
      t.[1] <- (t.[1] `|` t.[2]);
      d14 <- VPERMQ t.[1] (W8.of_int 57);
      d00 <- (t.[1] `^` t.[4]);
      d00 <- VPERMQ d00 (W8.of_int 0);
      c00 <- (c00 `^` a00);
      c00 <- (c00 `^` t.[0]);
      t.[0] <- (c00 \vshr64u256 (W8.of_int 63));
      t.[1] <- (c00 \vadd64u256 c00);
      t.[1] <- (t.[1] `|` t.[0]);
      a20 <- (a20 `^` d00);
      a00 <- (a00 `^` d00);
      d14 <- VPBLENDD_256 d14 t.[1]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
      t.[4] <- VPBLENDD_256 t.[4] c00
      (W8.of_int (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      d14 <- (d14 `^` t.[4]);
      t.[3] <- VPSLLV_4u64 a20
      (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((0 * 32) - 96)))));
      a20 <- VPSRLV_4u64 a20
      (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((0 * 32) - 96)))));
      a20 <- (a20 `|` t.[3]);
      a31 <- (a31 `^` d14);
      t.[4] <- VPSLLV_4u64 a31
      (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((2 * 32) - 96)))));
      a31 <- VPSRLV_4u64 a31
      (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((2 * 32) - 96)))));
      a31 <- (a31 `|` t.[4]);
      a21 <- (a21 `^` d14);
      t.[5] <- VPSLLV_4u64 a21
      (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((3 * 32) - 96)))));
      a21 <- VPSRLV_4u64 a21
      (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((3 * 32) - 96)))));
      a21 <- (a21 `|` t.[5]);
      a41 <- (a41 `^` d14);
      t.[6] <- VPSLLV_4u64 a41
      (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((4 * 32) - 96)))));
      a41 <- VPSRLV_4u64 a41
      (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((4 * 32) - 96)))));
      a41 <- (a41 `|` t.[6]);
      a11 <- (a11 `^` d14);
      t.[3] <- VPERMQ a20 (W8.of_int 141);
      t.[4] <- VPERMQ a31 (W8.of_int 141);
      t.[7] <- VPSLLV_4u64 a11
      (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((5 * 32) - 96)))));
      t.[1] <- VPSRLV_4u64 a11
      (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((5 * 32) - 96)))));
      t.[1] <- (t.[1] `|` t.[7]);
      a01 <- (a01 `^` d14);
      t.[5] <- VPERMQ a21 (W8.of_int 27);
      t.[6] <- VPERMQ a41 (W8.of_int 114);
      t.[8] <- VPSLLV_4u64 a01
      (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((1 * 32) - 96)))));
      t.[2] <- VPSRLV_4u64 a01
      (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((1 * 32) - 96)))));
      t.[2] <- (t.[2] `|` t.[8]);
      t.[7] <- VPSRLDQ_256 t.[1] (W8.of_int 8);
      t.[0] <- ((invw t.[1]) `&` t.[7]);
      a31 <- VPBLENDD_256 t.[2] t.[6]
      (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      t.[8] <- VPBLENDD_256 t.[4] t.[2]
      (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      a41 <- VPBLENDD_256 t.[3] t.[4]
      (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      t.[7] <- VPBLENDD_256 t.[2] t.[3]
      (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      a31 <- VPBLENDD_256 a31 t.[4]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      t.[8] <- VPBLENDD_256 t.[8] t.[5]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      a41 <- VPBLENDD_256 a41 t.[2]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      t.[7] <- VPBLENDD_256 t.[7] t.[6]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      a31 <- VPBLENDD_256 a31 t.[5]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
      t.[8] <- VPBLENDD_256 t.[8] t.[6]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
      a41 <- VPBLENDD_256 a41 t.[6]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
      t.[7] <- VPBLENDD_256 t.[7] t.[4]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
      a31 <- VPANDN_256 a31 t.[8];
      a41 <- VPANDN_256 a41 t.[7];
      a11 <- VPBLENDD_256 t.[5] t.[2]
      (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      t.[8] <- VPBLENDD_256 t.[3] t.[5]
      (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      a31 <- (a31 `^` t.[3]);
      a11 <- VPBLENDD_256 a11 t.[3]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      t.[8] <- VPBLENDD_256 t.[8] t.[4]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      a41 <- (a41 `^` t.[5]);
      a11 <- VPBLENDD_256 a11 t.[4]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
      t.[8] <- VPBLENDD_256 t.[8] t.[2]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
      a11 <- VPANDN_256 a11 t.[8];
      a11 <- (a11 `^` t.[6]);
      a21 <- VPERMQ t.[1] (W8.of_int 30);
      t.[8] <- VPBLENDD_256 a21 a00
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      a01 <- VPERMQ t.[1] (W8.of_int 57);
      a01 <- VPBLENDD_256 a01 a00
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
      a01 <- VPANDN_256 a01 t.[8];
      a20 <- VPBLENDD_256 t.[4] t.[5]
      (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      t.[7] <- VPBLENDD_256 t.[6] t.[4]
      (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      a20 <- VPBLENDD_256 a20 t.[6]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      t.[7] <- VPBLENDD_256 t.[7] t.[3]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      a20 <- VPBLENDD_256 a20 t.[3]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
      t.[7] <- VPBLENDD_256 t.[7] t.[5]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
      a20 <- VPANDN_256 a20 t.[7];
      a20 <- (a20 `^` t.[2]);
      t.[0] <- VPERMQ t.[0] (W8.of_int 0);
      a31 <- VPERMQ a31 (W8.of_int 27);
      a41 <- VPERMQ a41 (W8.of_int 141);
      a11 <- VPERMQ a11 (W8.of_int 114);
      a21 <- VPBLENDD_256 t.[6] t.[3]
      (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      t.[7] <- VPBLENDD_256 t.[5] t.[6]
      (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      a21 <- VPBLENDD_256 a21 t.[5]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      t.[7] <- VPBLENDD_256 t.[7] t.[2]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      a21 <- VPBLENDD_256 a21 t.[2]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
      t.[7] <- VPBLENDD_256 t.[7] t.[3]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 3))));
      a21 <- VPANDN_256 a21 t.[7];
      a00 <- (a00 `^` t.[0]);
      a01 <- (a01 `^` t.[1]);
      a21 <- (a21 `^` t.[4]);
      a00 <-
      (a00 `^` (loadW256 Glob.mem (W64.to_uint (iotas + (W64.of_int 0)))));
      iotas <- (iotas + (W64.of_int 32));
      ( _0,  _1,  _2, zf, i) <- DEC_32 i;
    }
    return (a00, a01, a20, a31, a21, a41, a11);
  }
}.




op flat_state (st : W256.t Array7.t) 
              (axx : W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t ) =
    st.[0] = axx.`1 /\
    st.[1] = axx.`2 /\
    st.[2] = axx.`3 /\
    st.[3] = axx.`4 /\
    st.[4] = axx.`5 /\
    st.[5] = axx.`6 /\
    st.[6] = axx.`7.

(*
  proc _keccakf1600_avx2(st0r : W256.t, st1r : W256.t, st2r : W256.t, st3r : W256.t, st4r : W256.t, st5r : W256.t, st6r : W256.t) :
    W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
*)

equiv avx2_avx2_openssl :
  Mopenssl.__keccak_f1600_avx2_openssl ~ M._keccakf1600_avx2 :
    ={Glob.mem,_rhotates_left,_rhotates_right, _iotas} /\ 
       flat_state state{2} (arg{1}.`1,arg{1}.`2,arg{1}.`3,arg{1}.`4,arg{1}.`5,arg{1}.`6,arg{1}.`7) ==> 
       ={Glob.mem} /\ flat_state res{2} res{1}.
   proc.
   seq 112 112 : (#pre /\ ={zf,iotas,rhotates_left,rhotates_right,t} /\ i{1} = r{2}).
   seq 30 30 : (#pre /\ ={d14,t,iotas,rhotates_left,rhotates_right} /\ i{1} = r{2}).
   by wp;skip; rewrite /flat_state; auto => />.
   seq 30 30 : #pre.
   by wp;skip; rewrite /flat_state; auto => />.
   seq 30 30 : #pre.
   by wp;skip; rewrite /flat_state; auto => />.
   by wp;skip; rewrite /flat_state; auto => />.
   while (#pre).
   seq 30 30 : (#pre /\ ={d14}).
   by wp;skip; rewrite /flat_state; auto => />.
   seq 30 30 : #pre.
   by wp;skip; rewrite /flat_state; auto => />.
   seq 30 30 : #pre.
   by wp;skip; rewrite /flat_state; auto => />.
   by wp;skip; rewrite /flat_state; auto => />.
   by auto => />.
qed.

require import Array4 Array25.
require Keccak_f1600_ref_op.
require Keccak_f1600_ref.
require Keccak_f1600_ref_table.
require import Keccak_f1600_avx2_prevec.
require Keccak_f1600_avx2_prevec_vops.

require import Ops.

op em_states (state : W256.t Array7.t) (st : W64.t Array25.t) = 
  state = 
    Array7.of_list witness [pack4 [st.[index 0 0]; st.[index 0 0]; st.[index 0 0]; st.[index 0 0]];
                            pack4 [st.[index 0 1]; st.[index 0 2]; st.[index 0 3]; st.[index 0 4]];
                            pack4 [st.[index 2 0]; st.[index 4 0]; st.[index 1 0]; st.[index 3 0]];
                            pack4 [st.[index 3 1]; st.[index 1 2]; st.[index 4 3]; st.[index 2 4]];
                            pack4 [st.[index 2 1]; st.[index 4 2]; st.[index 1 3]; st.[index 3 4]];
                            pack4 [st.[index 4 1]; st.[index 3 2]; st.[index 2 3]; st.[index 1 4]];
                            pack4 [st.[index 1 1]; st.[index 2 2]; st.[index 3 3]; st.[index 4 4]]].

lemma avx2corr st mem : 
  equiv [ Keccak_f1600_ref.M.__keccak_f1600_ref ~ M.__keccak_f1600_avx2  : 
         W64.to_uint _rhotates_left{2} + 192 < W64.modulus /\
         W64.to_uint _rhotates_right{2} + 192 < W64.modulus /\
         W64.to_uint _iotas{2} + 768 < W64.modulus /\ Glob.mem{2} = mem /\ 
         Keccak_f1600_avx2_prevec.good_io4x mem (W64.to_uint _iotas{2}) /\ 
         good_rhol mem (to_uint _rhotates_left{2}) /\ 
         good_rhor mem (to_uint _rhotates_right{2}) /\
         em_states  state{2} state{1} /\ st = state{1}  ==>   
            Glob.mem{2} = mem /\ em_states res{2} res{1}   ].
proof.

transitivity Keccak_f1600_ref_table.Mreftable.__keccak_f1600_ref
  (={Glob.mem, state} ==> ={Glob.mem, res})
  (W64.to_uint _rhotates_left{2} + 192 < W64.modulus /\
         W64.to_uint _rhotates_right{2} + 192 < W64.modulus /\
         W64.to_uint _iotas{2} + 768 < W64.modulus /\          Glob.mem{2} = mem /\ 
         Keccak_f1600_avx2_prevec.good_io4x mem (W64.to_uint _iotas{2}) /\ 
         good_rhol mem (to_uint _rhotates_left{2}) /\ 
         good_rhor mem (to_uint _rhotates_right{2}) /\
         em_states  state{2} state{1} /\ st = state{1} ==>   
            Glob.mem{2} = mem /\ em_states res{2} res{1}).
+ smt(). + done.
+ transitivity Keccak_f1600_ref_op.Mrefop.__keccak_f1600_ref
    (={Glob.mem, state} ==> ={Glob.mem, res})
    (={Glob.mem, state} ==> ={Glob.mem, res}) => //.
  + smt().
  + by apply Keccak_f1600_ref_op.ref_refop.
  by conseq Keccak_f1600_ref_table.ref_reftable.
transitivity Mavx2_prevec.__KeccakF1600 
           (to_uint _rhotates_left{2} + 192 < W64.modulus /\
            to_uint _rhotates_right{2} + 192 < W64.modulus /\
            to_uint _iotas{2} + 768 < W64.modulus /\
            Glob.mem{2} = mem /\
            good_io4x mem (to_uint _iotas{2}) /\
            good_rhol mem (to_uint _rhotates_left{2}) /\
            good_rhor mem (to_uint _rhotates_right{2}) /\
            equiv_states ((of_list witness [st.[index 0 0]; st.[index 0 0]; st.[index 0 0]; st.[index 0 0]]))%Array4
              ((of_list witness [st.[index 0 1]; st.[index 0 2]; st.[index 0 3]; st.[index 0 4]]))%Array4
              ((of_list witness [st.[index 2 0]; st.[index 4 0]; st.[index 1 0]; st.[index 3 0]]))%Array4
              ((of_list witness [st.[index 3 1]; st.[index 1 2]; st.[index 4 3]; st.[index 2 4]]))%Array4
              ((of_list witness [st.[index 2 1]; st.[index 4 2]; st.[index 1 3]; st.[index 3 4]]))%Array4
              ((of_list witness [st.[index 4 1]; st.[index 3 2]; st.[index 2 3]; st.[index 1 4]]))%Array4
              ((of_list witness [st.[index 1 1]; st.[index 2 2]; st.[index 3 3]; st.[index 4 4]]))%Array4 st /\
            a00{2} = (of_list witness [st.[index 0 0]; st.[index 0 0]; st.[index 0 0]; st.[index 0 0]])%Array4 /\
            a01{2} = (of_list witness [st.[index 0 1]; st.[index 0 2]; st.[index 0 3]; st.[index 0 4]])%Array4 /\
            a20{2} = (of_list witness [st.[index 2 0]; st.[index 4 0]; st.[index 1 0]; st.[index 3 0]])%Array4 /\
            a31{2} = (of_list witness [st.[index 3 1]; st.[index 1 2]; st.[index 4 3]; st.[index 2 4]])%Array4 /\
            a21{2} = (of_list witness [st.[index 2 1]; st.[index 4 2]; st.[index 1 3]; st.[index 3 4]])%Array4 /\
            a41{2} = (of_list witness [st.[index 4 1]; st.[index 3 2]; st.[index 2 3]; st.[index 1 4]])%Array4 /\
            a11{2} = (of_list witness [st.[index 1 1]; st.[index 2 2]; st.[index 3 3]; st.[index 4 4]])%Array4 /\
            state{1} = st 
            ==>
            Glob.mem{2} = mem /\
            equiv_states res{2}.`1 res{2}.`2 res{2}.`3 res{2}.`4 res{2}.`5 res{2}.`6 res{2}.`7 res{1})

        (W64.to_uint _rhotates_left{2} + 192 < W64.modulus /\
         W64.to_uint _rhotates_right{2} + 192 < W64.modulus /\
         W64.to_uint _iotas{2} + 768 < W64.modulus /\ ={Glob.mem, _rhotates_left, _rhotates_right, _iotas} /\
         Keccak_f1600_avx2_prevec.good_io4x mem (W64.to_uint _iotas{2}) /\ 
         good_rhol mem (to_uint _rhotates_left{2}) /\ 
         good_rhor mem (to_uint _rhotates_right{2}) /\
         state{2} = Array7.of_list witness [pack4 (Array4.to_list a00{1});
                                            pack4 (Array4.to_list a01{1});
                                            pack4 (Array4.to_list a20{1});
                                            pack4 (Array4.to_list a31{1});
                                            pack4 (Array4.to_list a21{1});
                                            pack4 (Array4.to_list a41{1});
                                            pack4 (Array4.to_list a11{1})] /\
         a00{1} = (of_list witness [st.[index 0 0]; st.[index 0 0]; st.[index 0 0]; st.[index 0 0]])%Array4 /\
         a01{1} = (of_list witness [st.[index 0 1]; st.[index 0 2]; st.[index 0 3]; st.[index 0 4]])%Array4 /\
         a20{1} = (of_list witness [st.[index 2 0]; st.[index 4 0]; st.[index 1 0]; st.[index 3 0]])%Array4 /\
         a31{1} = (of_list witness [st.[index 3 1]; st.[index 1 2]; st.[index 4 3]; st.[index 2 4]])%Array4 /\
         a21{1} = (of_list witness [st.[index 2 1]; st.[index 4 2]; st.[index 1 3]; st.[index 3 4]])%Array4 /\
         a41{1} = (of_list witness [st.[index 4 1]; st.[index 3 2]; st.[index 2 3]; st.[index 1 4]])%Array4 /\
         a11{1} = (of_list witness [st.[index 1 1]; st.[index 2 2]; st.[index 3 3]; st.[index 4 4]])%Array4 
         ==>   
            ={Glob.mem} /\ 
            let (a00, a01, a20, a31, a21, a41, a11) = res{1} in
            res{2} = 
              Array7.of_list witness [pack4 (Array4.to_list a00);
                                      pack4 (Array4.to_list a01);
                                      pack4 (Array4.to_list a20);
                                      pack4 (Array4.to_list a31);
                                      pack4 (Array4.to_list a21);
                                      pack4 (Array4.to_list a41);
                                      pack4 (Array4.to_list a11)]).
+ move=> &1 &2 [#] ??? <<- ???.
  rewrite /em_states => h1 <<-.
  rewrite h1.
  exists Glob.mem{2}.
  by exists (Array4.of_list witness [st.[index 0 0]; st.[index 0 0]; st.[index 0 0]; st.[index 0 0]],
          Array4.of_list witness [st.[index 0 1]; st.[index 0 2]; st.[index 0 3]; st.[index 0 4]],
          Array4.of_list witness [st.[index 2 0]; st.[index 4 0]; st.[index 1 0]; st.[index 3 0]],
          Array4.of_list witness [st.[index 3 1]; st.[index 1 2]; st.[index 4 3]; st.[index 2 4]],
          Array4.of_list witness [st.[index 2 1]; st.[index 4 2]; st.[index 1 3]; st.[index 3 4]],
          Array4.of_list witness [st.[index 4 1]; st.[index 3 2]; st.[index 2 3]; st.[index 1 4]],
          Array4.of_list witness [st.[index 1 1]; st.[index 2 2]; st.[index 3 3]; st.[index 4 4]],
          _rhotates_left{2}, _rhotates_right{2}, _iotas{2}) => />.
+ move=> &1 &m &2 />.
  case: ( res{m} ) => a00 a01 a20 a31 a21 a41 a11 /=.
  rewrite /to_list /em_states /= /mkseq /=.
  by move=> 29! ->.
+ apply (Keccak_f1600_avx2_prevec.correct_perm 
           (Array4.of_list witness [st.[index 0 0]; st.[index 0 0]; st.[index 0 0]; st.[index 0 0]])
           (Array4.of_list witness [st.[index 0 1]; st.[index 0 2]; st.[index 0 3]; st.[index 0 4]])
           (Array4.of_list witness [st.[index 2 0]; st.[index 4 0]; st.[index 1 0]; st.[index 3 0]])
           (Array4.of_list witness [st.[index 3 1]; st.[index 1 2]; st.[index 4 3]; st.[index 2 4]])
           (Array4.of_list witness [st.[index 2 1]; st.[index 4 2]; st.[index 1 3]; st.[index 3 4]])
           (Array4.of_list witness [st.[index 4 1]; st.[index 3 2]; st.[index 2 3]; st.[index 1 4]])
           (Array4.of_list witness [st.[index 1 1]; st.[index 2 2]; st.[index 3 3]; st.[index 4 4]])
           st mem).

transitivity Keccak_f1600_avx2_prevec_vops.Mavx2_prevec_vops.__KeccakF1600 
   (={Glob.mem} /\ Keccak_f1600_avx2_prevec_vops.match_ins arg{1} arg{2}==>
    ={Glob.mem} /\ Keccak_f1600_avx2_prevec_vops.match_states res{1} res{2})
   
( to_uint _rhotates_left{2} + 192 < W64.modulus /\
  to_uint _rhotates_right{2} + 192 < W64.modulus /\
  to_uint _iotas{2} + 768 < W64.modulus /\
  ={Glob.mem, _rhotates_left, _rhotates_right, _iotas} /\
  good_io4x mem (to_uint _iotas{2}) /\
  good_rhol mem (to_uint _rhotates_left{2}) /\
  good_rhor mem (to_uint _rhotates_right{2}) /\
  state{2} = 
    Array7.of_list witness [arg.`1; arg.`2; arg.`3; arg.`4; arg.`5; arg.`6; arg.`7]{1} ==>
  ={Glob.mem} /\
  res{2} =  Array7.of_list witness [res.`1; res.`2; res.`3; res.`4; res.`5; res.`6; res.`7]{1}).
+ move=> /> *.
  exists Glob.mem{2}.
  exists (pack4 [st.[index 0 0]; st.[index 0 0]; st.[index 0 0]; st.[index 0 0]],
          pack4 [st.[index 0 1]; st.[index 0 2]; st.[index 0 3]; st.[index 0 4]],
          pack4 [st.[index 2 0]; st.[index 4 0]; st.[index 1 0]; st.[index 3 0]],
          pack4 [st.[index 3 1]; st.[index 1 2]; st.[index 4 3]; st.[index 2 4]],
          pack4 [st.[index 2 1]; st.[index 4 2]; st.[index 1 3]; st.[index 3 4]],
          pack4 [st.[index 4 1]; st.[index 3 2]; st.[index 2 3]; st.[index 1 4]],
          pack4 [st.[index 1 1]; st.[index 2 2]; st.[index 3 3]; st.[index 4 4]],
          _rhotates_left{2}, _rhotates_right{2}, _iotas{2}) => />.
  by rewrite H8 H9 H10 H11 H12 H13 H14 H15 /is4u64=> />.
+ move=> &1 &m &2 /= [#] ->.
  rewrite /Keccak_f1600_avx2_prevec_vops.match_states /is4u64 => [#].
  by case: (res{1}) => a00 a01 a20 a31 a21 a41 a11 /= 7!-> [#] -> ->.
+ by apply Keccak_f1600_avx2_prevec_vops.prevec_vops_prevec.   
transitivity Keccak_f1600_avx2_openssl.M.__keccak_f1600_avx2_openssl 
  (={Glob.mem, arg} ==> ={Glob.mem, res}) 
    ( to_uint _rhotates_left{2} + 192 < W64.modulus /\
    to_uint _rhotates_right{2} + 192 < W64.modulus /\
    to_uint _iotas{2} + 768 < W64.modulus /\
    ={Glob.mem,_rhotates_left, _rhotates_right, _iotas} /\
    good_io4x mem (to_uint _iotas{2}) /\
    good_rhol mem (to_uint _rhotates_left{2}) /\
    good_rhor mem (to_uint _rhotates_right{2}) /\
    state{2} = (of_list witness [a00{1}; a01{1}; a20{1}; a31{1}; a21{1}; a41{1}; a11{1}])%Array7 ==>
  ={Glob.mem} /\
  res{2} = (of_list witness [res{1}.`1; res{1}.`2; res{1}.`3; res{1}.`4; res{1}.`5; res{1}.`6; res{1}.`7])%Array7). 
+ smt(). + done.
+ apply Keccak_f1600_avx2_prevec_vops.prevec_vops_openssl.
conseq avx2_avx2_openssl.
+ by move => /> *; rewrite H8 /=.
move=> /> &1 &2 ?????????? [/=] /> *.
by apply Array7.all_eq_eq;cbv delta.
qed.
