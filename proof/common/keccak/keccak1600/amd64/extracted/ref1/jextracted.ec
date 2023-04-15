require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel.

require import Array5 Array6 Array7 Array24 Array25.
require import WArray40 WArray160 WArray192 WArray200 WArray224 WArray768
               WArray800.

abbrev ROL8 = W256.of_int 13620818001941277694121380808605999856886653716761013959207994299728839901191.


abbrev ROL56 = W256.of_int 10910488462195273559651782724632284871561478246514020268633800075540923875841.


abbrev KECCAK1600_RC_4x = Array24.of_list witness [W256.of_int 6277101735386680764176071790128604879584176795969512275969;
W256.of_int 206504092890751023779864409751650843328560248233805014854828162;
W256.of_int (-57896044618657891154337237002533387566728630465883811983015055433200855646070);
W256.of_int (-57896044605177918687001956587831074660851270707671256656745893357814858874880);
W256.of_int 206560586806369503906741994397762000772476505824968740465311883;
W256.of_int 13479973339852421633450939126351338586088633588469736715148203130881;
W256.of_int (-57896044605177917877255832722949256082138009781081227190387086677747775274879);
W256.of_int (-57896044618657891964083360867415206145441891392473841449373862113267939246071);
W256.of_int 866240039483361945456297907037747473382616397843792694083722;
W256.of_int 853685836012588583927945763457490263623448044251853669531784;
W256.of_int 13480179078138900667299665761280331841242166839448401411882560290825;
W256.of_int 13479973396346337251931066003935984697246077504727327878873813614602;
W256.of_int 13480179894162126267568165104169664557960801185391384887919156166795;
W256.of_int (-57896044618658096836129800417901987324072977609879901317736128966209602322293);
W256.of_int (-57896044618657891160614338737920068330904702256012416862599232229170367922039);
W256.of_int (-57896044618657892001745971279735290730498322133245470726878922889085012901885);
W256.of_int (-57896044618657892008023073015121971494674393923374075606463099685054525177854);
W256.of_int (-57896044618658096905177919507155475730009767301294554993162073721874237357952);
W256.of_int 205750840682504622088163281136835410743010147018288673381711882;
W256.of_int (-57896044605178124312300604384719547540610971740509902075209375727097995067382);
W256.of_int (-57896044605177917877255832722949256082138009781081227190387086677747775274879);
W256.of_int (-57896044618657891217108254356400195208489348367169860778856823392895978405760);
W256.of_int 13479973339852421633450939126351338586088633588469736715148203130881;
W256.of_int (-57896044605177918636785142704737628547442696386642417620072478990058760667128)].


abbrev KECCAK_A_JAGGED = Array25.of_list witness [W64.of_int 0; W64.of_int 4;
W64.of_int 5; W64.of_int 6; W64.of_int 7; W64.of_int 10; W64.of_int 24;
W64.of_int 13; W64.of_int 18; W64.of_int 23; W64.of_int 8; W64.of_int 16;
W64.of_int 25; W64.of_int 22; W64.of_int 15; W64.of_int 11; W64.of_int 12;
W64.of_int 21; W64.of_int 26; W64.of_int 19; W64.of_int 9; W64.of_int 20;
W64.of_int 17; W64.of_int 14; W64.of_int 27].


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
W256.of_int 87879424295413530700846981630247037558957052973733126340652].


abbrev KECCAK_IOTAS = Array24.of_list witness [W256.of_int 6277101735386680764176071790128604879584176795969512275969;
W256.of_int 206504092890751023779864409751650843328560248233805014854828162;
W256.of_int (-57896044618657891154337237002533387566728630465883811983015055433200855646070);
W256.of_int (-57896044605177918687001956587831074660851270707671256656745893357814858874880);
W256.of_int 206560586806369503906741994397762000772476505824968740465311883;
W256.of_int 13479973339852421633450939126351338586088633588469736715148203130881;
W256.of_int (-57896044605177917877255832722949256082138009781081227190387086677747775274879);
W256.of_int (-57896044618657891964083360867415206145441891392473841449373862113267939246071);
W256.of_int 866240039483361945456297907037747473382616397843792694083722;
W256.of_int 853685836012588583927945763457490263623448044251853669531784;
W256.of_int 13480179078138900667299665761280331841242166839448401411882560290825;
W256.of_int 13479973396346337251931066003935984697246077504727327878873813614602;
W256.of_int 13480179894162126267568165104169664557960801185391384887919156166795;
W256.of_int (-57896044618658096836129800417901987324072977609879901317736128966209602322293);
W256.of_int (-57896044618657891160614338737920068330904702256012416862599232229170367922039);
W256.of_int (-57896044618657892001745971279735290730498322133245470726878922889085012901885);
W256.of_int (-57896044618657892008023073015121971494674393923374075606463099685054525177854);
W256.of_int (-57896044618658096905177919507155475730009767301294554993162073721874237357952);
W256.of_int 205750840682504622088163281136835410743010147018288673381711882;
W256.of_int (-57896044605178124312300604384719547540610971740509902075209375727097995067382);
W256.of_int (-57896044605177917877255832722949256082138009781081227190387086677747775274879);
W256.of_int (-57896044618657891217108254356400195208489348367169860778856823392895978405760);
W256.of_int 13479973339852421633450939126351338586088633588469736715148203130881;
W256.of_int (-57896044605177918636785142704737628547442696386642417620072478990058760667128)].


abbrev KECCAK1600_RC = Array24.of_list witness [W64.of_int 1;
W64.of_int 32898; W64.of_int (-9223372036854742902);
W64.of_int (-9223372034707259392); W64.of_int 32907; W64.of_int 2147483649;
W64.of_int (-9223372034707259263); W64.of_int (-9223372036854743031);
W64.of_int 138; W64.of_int 136; W64.of_int 2147516425; W64.of_int 2147483658;
W64.of_int 2147516555; W64.of_int (-9223372036854775669);
W64.of_int (-9223372036854742903); W64.of_int (-9223372036854743037);
W64.of_int (-9223372036854743038); W64.of_int (-9223372036854775680);
W64.of_int 32778; W64.of_int (-9223372034707292150);
W64.of_int (-9223372034707259263); W64.of_int (-9223372036854742912);
W64.of_int 2147483649; W64.of_int (-9223372034707259384)].


module M = {
  proc __index_spec (x:int, y:int) : int = {
    
    var r:int;
    
    r <- ((x %% 5) + (5 * (y %% 5)));
    return (r);
  }
  
  proc __keccak_rho_offsets_spec (i:int) : int = {
    var aux: int;
    
    var r:int;
    var x:int;
    var y:int;
    var t:int;
    var z:int;
    
    r <- 0;
    x <- 1;
    y <- 0;
    t <- 0;
    while (t < 24) {
      if ((i = (x + (5 * y)))) {
        r <- ((((t + 1) * (t + 2)) %/ 2) %% 64);
      } else {
        
      }
      z <- (((2 * x) + (3 * y)) %% 5);
      x <- y;
      y <- z;
      t <- t + 1;
    }
    return (r);
  }
  
  proc __rhotates_spec (x:int, y:int) : int = {
    
    var r:int;
    var i:int;
    
    i <@ __index_spec (x, y);
    r <@ __keccak_rho_offsets_spec (i);
    return (r);
  }
  
  proc __rol_u64_ref (x:W64.t, i:int) : W64.t = {
    
    var  _0:bool;
    var  _1:bool;
    
    if ((i <> 0)) {
      ( _0,  _1, x) <- ROL_64 x (W8.of_int i);
    } else {
      
    }
    return (x);
  }
  
  proc __theta_sum_ref (a:W64.t Array25.t) : W64.t Array5.t = {
    var aux: int;
    
    var c:W64.t Array5.t;
    var x:int;
    var y:int;
    c <- witness;
    x <- 0;
    while (x < 5) {
      c.[x] <- a.[(x + 0)];
      x <- x + 1;
    }
    y <- 1;
    while (y < 5) {
      x <- 0;
      while (x < 5) {
        c.[x] <- (c.[x] `^` a.[(x + (y * 5))]);
        x <- x + 1;
      }
      y <- y + 1;
    }
    return (c);
  }
  
  proc __theta_rol_ref (c:W64.t Array5.t) : W64.t Array5.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var d:W64.t Array5.t;
    var x:int;
    d <- witness;
    x <- 0;
    while (x < 5) {
      d.[x] <- c.[((x + 1) %% 5)];
      aux_0 <@ __rol_u64_ref (d.[x], 1);
      d.[x] <- aux_0;
      d.[x] <- (d.[x] `^` c.[(((x - 1) + 5) %% 5)]);
      x <- x + 1;
    }
    return (d);
  }
  
  proc __rol_sum_ref (a:W64.t Array25.t, d:W64.t Array5.t, y:int) : W64.t Array5.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var b:W64.t Array5.t;
    var x:int;
    var x_:int;
    var y_:int;
    var r:int;
    b <- witness;
    x <- 0;
    while (x < 5) {
      x_ <- ((x + (3 * y)) %% 5);
      y_ <- x;
      r <@ __rhotates_spec (x_, y_);
      b.[x] <- a.[(x_ + (y_ * 5))];
      b.[x] <- (b.[x] `^` d.[x_]);
      aux_0 <@ __rol_u64_ref (b.[x], r);
      b.[x] <- aux_0;
      x <- x + 1;
    }
    return (b);
  }
  
  proc __set_row_ref (e:W64.t Array25.t, b:W64.t Array5.t, y:int, rc:W64.t) : 
  W64.t Array25.t = {
    var aux: int;
    
    var x:int;
    var x1:int;
    var x2:int;
    var t:W64.t;
    
    x <- 0;
    while (x < 5) {
      x1 <- ((x + 1) %% 5);
      x2 <- ((x + 2) %% 5);
      t <- b.[x1];
      t <- (invw t);
      t <- (t `&` b.[x2]);
      t <- (t `^` b.[x]);
      if (((x = 0) /\ (y = 0))) {
        t <- (t `^` rc);
      } else {
        
      }
      e.[(x + (y * 5))] <- t;
      x <- x + 1;
    }
    return (e);
  }
  
  proc __round_ref (a:W64.t Array25.t, rc:W64.t) : W64.t Array25.t = {
    var aux: int;
    
    var e:W64.t Array25.t;
    var c:W64.t Array5.t;
    var d:W64.t Array5.t;
    var y:int;
    var b:W64.t Array5.t;
    b <- witness;
    c <- witness;
    d <- witness;
    e <- witness;
    c <@ __theta_sum_ref (a);
    d <@ __theta_rol_ref (c);
    y <- 0;
    while (y < 5) {
      b <@ __rol_sum_ref (a, d, y);
      e <@ __set_row_ref (e, b, y, rc);
      y <- y + 1;
    }
    return (e);
  }
  
  proc __keccakf1600_ref (a:W64.t Array25.t) : W64.t Array25.t = {
    
    var c:W64.t;
    var rc:W64.t;
    var e:W64.t Array25.t;
    e <- witness;
    c <- (W64.of_int 0);
    rc <- KECCAK1600_RC.[(W64.to_uint c)];
    e <@ __round_ref (a, rc);
    rc <- KECCAK1600_RC.[((W64.to_uint c) + 1)];
    a <@ __round_ref (e, rc);
    c <- (c + (W64.of_int 2));
    while ((c \ult (W64.of_int (24 - 1)))) {
      rc <- KECCAK1600_RC.[(W64.to_uint c)];
      e <@ __round_ref (a, rc);
      rc <- KECCAK1600_RC.[((W64.to_uint c) + 1)];
      a <@ __round_ref (e, rc);
      c <- (c + (W64.of_int 2));
    }
    return (a);
  }
  
  proc __ANDN_64 (a:W64.t, b:W64.t) : W64.t = {
    
    var t:W64.t;
    
    t <- a;
    t <- (invw t);
    t <- (t `&` b);
    return (t);
  }
  
  proc __rol_u64_ref1 (x:W64.t, i:int) : W64.t = {
    
    var  _0:bool;
    var  _1:bool;
    
    if ((i <> 0)) {
      ( _0,  _1, x) <- ROL_64 x (W8.of_int i);
    } else {
      
    }
    return (x);
  }
  
  proc __theta_sum_ref1 (a:W64.t Array25.t) : W64.t Array5.t = {
    var aux: int;
    
    var c:W64.t Array5.t;
    var x:int;
    var y:int;
    c <- witness;
    x <- 0;
    while (x < 5) {
      c.[x] <- a.[(x + 0)];
      x <- x + 1;
    }
    y <- 1;
    while (y < 5) {
      x <- 0;
      while (x < 5) {
        c.[x] <- (c.[x] `^` a.[(x + (y * 5))]);
        x <- x + 1;
      }
      y <- y + 1;
    }
    return (c);
  }
  
  proc __theta_rol_ref1 (c:W64.t Array5.t) : W64.t Array5.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var d:W64.t Array5.t;
    var x:int;
    d <- witness;
    x <- 0;
    while (x < 5) {
      d.[x] <- c.[((x + 1) %% 5)];
      aux_0 <@ __rol_u64_ref1 (d.[x], 1);
      d.[x] <- aux_0;
      d.[x] <- (d.[x] `^` c.[(((x - 1) + 5) %% 5)]);
      x <- x + 1;
    }
    return (d);
  }
  
  proc __rol_sum_ref1 (a:W64.t Array25.t, d:W64.t Array5.t, y:int) : 
  W64.t Array5.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var b:W64.t Array5.t;
    var x:int;
    var x_:int;
    var y_:int;
    var r:int;
    b <- witness;
    x <- 0;
    while (x < 5) {
      x_ <- ((x + (3 * y)) %% 5);
      y_ <- x;
      r <@ __rhotates_spec (x_, y_);
      b.[x] <- a.[(x_ + (y_ * 5))];
      b.[x] <- (b.[x] `^` d.[x_]);
      aux_0 <@ __rol_u64_ref1 (b.[x], r);
      b.[x] <- aux_0;
      x <- x + 1;
    }
    return (b);
  }
  
  proc __set_row_ref1 (e:W64.t Array25.t, b:W64.t Array5.t, y:int, s_rc:W64.t) : 
  W64.t Array25.t = {
    var aux: int;
    
    var x:int;
    var x1:int;
    var x2:int;
    var t:W64.t;
    
    x <- 0;
    while (x < 5) {
      x1 <- ((x + 1) %% 5);
      x2 <- ((x + 2) %% 5);
      t <@ __ANDN_64 (b.[x1], b.[x2]);
      t <- (t `^` b.[x]);
      if (((x = 0) /\ (y = 0))) {
        t <- (t `^` s_rc);
      } else {
        
      }
      e.[(x + (y * 5))] <- t;
      x <- x + 1;
    }
    return (e);
  }
  
  proc __round_ref1 (e:W64.t Array25.t, a:W64.t Array25.t, s_rc:W64.t) : 
  W64.t Array25.t = {
    var aux: int;
    
    var c:W64.t Array5.t;
    var d:W64.t Array5.t;
    var y:int;
    var b:W64.t Array5.t;
    b <- witness;
    c <- witness;
    d <- witness;
    c <@ __theta_sum_ref1 (a);
    d <@ __theta_rol_ref1 (c);
    y <- 0;
    while (y < 5) {
      b <@ __rol_sum_ref1 (a, d, y);
      e <@ __set_row_ref1 (e, b, y, s_rc);
      y <- y + 1;
    }
    return (e);
  }
  
  proc __keccakf1600_ref1 (a:W64.t Array25.t) : W64.t Array25.t = {
    
    var rC:W64.t Array24.t;
    var s_RC:W64.t Array24.t;
    var s_e:W64.t Array25.t;
    var e:W64.t Array25.t;
    var c:W64.t;
    var s_c:W64.t;
    var rc:W64.t;
    var s_rc:W64.t;
    rC <- witness;
    e <- witness;
    s_RC <- witness;
    s_e <- witness;
    rC <- KECCAK1600_RC;
    s_RC <- rC;
    e <- s_e;
    c <- (W64.of_int 0);
    s_c <- c;
    rC <- s_RC;
    rc <- rC.[(W64.to_uint c)];
    s_rc <- rc;
    e <@ __round_ref1 (e, a, s_rc);
    rC <- s_RC;
    rc <- rC.[((W64.to_uint c) + 1)];
    s_rc <- rc;
    a <@ __round_ref1 (a, e, s_rc);
    c <- s_c;
    c <- (c + (W64.of_int 2));
    while ((c \ult (W64.of_int (24 - 1)))) {
      s_c <- c;
      rC <- s_RC;
      rc <- rC.[(W64.to_uint c)];
      s_rc <- rc;
      e <@ __round_ref1 (e, a, s_rc);
      rC <- s_RC;
      rc <- rC.[((W64.to_uint c) + 1)];
      s_rc <- rc;
      a <@ __round_ref1 (a, e, s_rc);
      c <- s_c;
      c <- (c + (W64.of_int 2));
    }
    return (a);
  }
  
  proc _keccakf1600_ref1 (a:W64.t Array25.t) : W64.t Array25.t = {
    
    
    
    a <@ __keccakf1600_ref1 (a);
    return (a);
  }
  
  proc _keccakf1600_ref1_ (a:W64.t Array25.t) : W64.t Array25.t = {
    
    
    
    a <- a;
    a <@ _keccakf1600_ref1 (a);
    a <- a;
    return (a);
  }
  
  proc __7u256_array (st0r:W256.t, st1r:W256.t, st2r:W256.t, st3r:W256.t,
                      st4r:W256.t, st5r:W256.t, st6r:W256.t) : W256.t Array7.t = {
    
    var state:W256.t Array7.t;
    state <- witness;
    state.[0] <- st0r;
    state.[1] <- st1r;
    state.[2] <- st2r;
    state.[3] <- st3r;
    state.[4] <- st4r;
    state.[5] <- st5r;
    state.[6] <- st6r;
    return (state);
  }
  
  proc __array_7u256 (state:W256.t Array7.t) : W256.t * W256.t * W256.t *
                                               W256.t * W256.t * W256.t *
                                               W256.t = {
    
    var st0r:W256.t;
    var st1r:W256.t;
    var st2r:W256.t;
    var st3r:W256.t;
    var st4r:W256.t;
    var st5r:W256.t;
    var st6r:W256.t;
    
    st0r <- state.[0];
    st1r <- state.[1];
    st2r <- state.[2];
    st3r <- state.[3];
    st4r <- state.[4];
    st5r <- state.[5];
    st6r <- state.[6];
    return (st0r, st1r, st2r, st3r, st4r, st5r, st6r);
  }
  
  proc __keccakf1600_pround_avx2 (st0r:W256.t, st1r:W256.t, st2r:W256.t,
                                  st3r:W256.t, st4r:W256.t, st5r:W256.t,
                                  st6r:W256.t,
                                  rhotates_left_p:W256.t Array6.t,
                                  rhotates_right_p:W256.t Array6.t) : 
  W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
    
    var c00:W256.t;
    var c14:W256.t;
    var t2:W256.t;
    var t4:W256.t;
    var t0:W256.t;
    var t1:W256.t;
    var d14:W256.t;
    var d00:W256.t;
    var t3:W256.t;
    var t5:W256.t;
    var t6:W256.t;
    var t7:W256.t;
    var t8:W256.t;
    
    c00 <- VPSHUFD_256 st2r
    (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 1))));
    c14 <- (st5r `^` st3r);
    t2 <- (st4r `^` st6r);
    c14 <- (c14 `^` st1r);
    c14 <- (c14 `^` t2);
    t4 <- VPERMQ c14
    (W8.of_int (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 2))));
    c00 <- (c00 `^` st2r);
    t0 <- VPERMQ c00
    (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 1))));
    t1 <- (c14 \vshr64u256 (W8.of_int 63));
    t2 <- (c14 \vadd64u256 c14);
    t1 <- (t1 `|` t2);
    d14 <- VPERMQ t1
    (W8.of_int (1 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    d00 <- (t1 `^` t4);
    d00 <- VPERMQ d00
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    c00 <- (c00 `^` st0r);
    c00 <- (c00 `^` t0);
    t0 <- (c00 \vshr64u256 (W8.of_int 63));
    t1 <- (c00 \vadd64u256 c00);
    t1 <- (t1 `|` t0);
    st2r <- (st2r `^` d00);
    st0r <- (st0r `^` d00);
    d14 <- VPBLEND_8u32 d14 t1
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t4 <- VPBLEND_8u32 t4 c00
    (W8.of_int (1 %% 2^1 +
               2^1 * (1 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    d14 <- (d14 `^` t4);
    t3 <- VPSLLV_4u64 st2r rhotates_left_p.[0];
    st2r <- VPSRLV_4u64 st2r rhotates_right_p.[0];
    st2r <- (st2r `|` t3);
    st3r <- (st3r `^` d14);
    t4 <- VPSLLV_4u64 st3r rhotates_left_p.[2];
    st3r <- VPSRLV_4u64 st3r rhotates_right_p.[2];
    st3r <- (st3r `|` t4);
    st4r <- (st4r `^` d14);
    t5 <- VPSLLV_4u64 st4r rhotates_left_p.[3];
    st4r <- VPSRLV_4u64 st4r rhotates_right_p.[3];
    st4r <- (st4r `|` t5);
    st5r <- (st5r `^` d14);
    t6 <- VPSLLV_4u64 st5r rhotates_left_p.[4];
    st5r <- VPSRLV_4u64 st5r rhotates_right_p.[4];
    st5r <- (st5r `|` t6);
    st6r <- (st6r `^` d14);
    t3 <- VPERMQ st2r
    (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
    t4 <- VPERMQ st3r
    (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
    t7 <- VPSLLV_4u64 st6r rhotates_left_p.[5];
    t1 <- VPSRLV_4u64 st6r rhotates_right_p.[5];
    t1 <- (t1 `|` t7);
    st1r <- (st1r `^` d14);
    t5 <- VPERMQ st4r
    (W8.of_int (3 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
    t6 <- VPERMQ st5r
    (W8.of_int (2 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 1))));
    t8 <- VPSLLV_4u64 st1r rhotates_left_p.[1];
    t2 <- VPSRLV_4u64 st1r rhotates_right_p.[1];
    t2 <- (t2 `|` t8);
    t7 <- VPSRLDQ_256 t1 (W8.of_int 8);
    t0 <- ((invw t1) `&` t7);
    st3r <- VPBLEND_8u32 t2 t6
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t8 <- VPBLEND_8u32 t4 t2
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    st5r <- VPBLEND_8u32 t3 t4
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t7 <- VPBLEND_8u32 t2 t3
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    st3r <- VPBLEND_8u32 st3r t4
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t8 <- VPBLEND_8u32 t8 t5
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    st5r <- VPBLEND_8u32 st5r t2
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t7 <- VPBLEND_8u32 t7 t6
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    st3r <- VPBLEND_8u32 st3r t5
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t8 <- VPBLEND_8u32 t8 t6
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    st5r <- VPBLEND_8u32 st5r t6
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t7 <- VPBLEND_8u32 t7 t4
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    st3r <- ((invw st3r) `&` t8);
    st5r <- ((invw st5r) `&` t7);
    st6r <- VPBLEND_8u32 t5 t2
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t8 <- VPBLEND_8u32 t3 t5
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    st3r <- (st3r `^` t3);
    st6r <- VPBLEND_8u32 st6r t3
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t8 <- VPBLEND_8u32 t8 t4
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    st5r <- (st5r `^` t5);
    st6r <- VPBLEND_8u32 st6r t4
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t8 <- VPBLEND_8u32 t8 t2
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    st6r <- ((invw st6r) `&` t8);
    st6r <- (st6r `^` t6);
    st4r <- VPERMQ t1
    (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
    t8 <- VPBLEND_8u32 st4r st0r
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    st1r <- VPERMQ t1
    (W8.of_int (1 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    st1r <- VPBLEND_8u32 st1r st0r
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    st1r <- ((invw st1r) `&` t8);
    st2r <- VPBLEND_8u32 t4 t5
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t7 <- VPBLEND_8u32 t6 t4
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    st2r <- VPBLEND_8u32 st2r t6
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t7 <- VPBLEND_8u32 t7 t3
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    st2r <- VPBLEND_8u32 st2r t3
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t7 <- VPBLEND_8u32 t7 t5
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    st2r <- ((invw st2r) `&` t7);
    st2r <- (st2r `^` t2);
    t0 <- VPERMQ t0
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    st3r <- VPERMQ st3r
    (W8.of_int (3 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
    st5r <- VPERMQ st5r
    (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
    st6r <- VPERMQ st6r
    (W8.of_int (2 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 1))));
    st4r <- VPBLEND_8u32 t6 t3
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t7 <- VPBLEND_8u32 t5 t6
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    st4r <- VPBLEND_8u32 st4r t5
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    t7 <- VPBLEND_8u32 t7 t2
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    st4r <- VPBLEND_8u32 st4r t2
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    t7 <- VPBLEND_8u32 t7 t3
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    st4r <- ((invw st4r) `&` t7);
    st0r <- (st0r `^` t0);
    st1r <- (st1r `^` t1);
    st4r <- (st4r `^` t4);
    return (st0r, st1r, st2r, st3r, st4r, st5r, st6r);
  }
  
  proc _keccakf1600_avx2 (st0r:W256.t, st1r:W256.t, st2r:W256.t, st3r:W256.t,
                          st4r:W256.t, st5r:W256.t, st6r:W256.t) : W256.t *
                                                                   W256.t *
                                                                   W256.t *
                                                                   W256.t *
                                                                   W256.t *
                                                                   W256.t *
                                                                   W256.t = {
    
    var iotas_p:W256.t Array24.t;
    var iotas_o:W64.t;
    var rhotates_left_p:W256.t Array6.t;
    var rhotates_right_p:W256.t Array6.t;
    var r:W64.t;
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    iotas_p <- witness;
    rhotates_left_p <- witness;
    rhotates_right_p <- witness;
    iotas_p <- KECCAK_IOTAS;
    iotas_o <- (W64.of_int 0);
    rhotates_left_p <- KECCAK_RHOTATES_LEFT;
    rhotates_right_p <- KECCAK_RHOTATES_RIGHT;
    r <- (W64.of_int 24);
    (st0r, st1r, st2r, st3r, st4r, st5r,
    st6r) <@ __keccakf1600_pround_avx2 (st0r, st1r, st2r, st3r, st4r, st5r,
    st6r, rhotates_left_p, rhotates_right_p);
    st0r <-
    (st0r `^` (get256_direct (WArray768.init256 (fun i => iotas_p.[i]))
              (W64.to_uint iotas_o)));
    iotas_o <- (iotas_o + (W64.of_int 32));
    ( _0,  _1,  _2, zf, r) <- DEC_64 r;
    while ((! zf)) {
      (st0r, st1r, st2r, st3r, st4r, st5r,
      st6r) <@ __keccakf1600_pround_avx2 (st0r, st1r, st2r, st3r, st4r, st5r,
      st6r, rhotates_left_p, rhotates_right_p);
      st0r <-
      (st0r `^` (get256_direct (WArray768.init256 (fun i => iotas_p.[i]))
                (W64.to_uint iotas_o)));
      iotas_o <- (iotas_o + (W64.of_int 32));
      ( _0,  _1,  _2, zf, r) <- DEC_64 r;
    }
    return (st0r, st1r, st2r, st3r, st4r, st5r, st6r);
  }
  
  proc _keccakf1600_avx2_ (state:W256.t Array7.t) : W256.t Array7.t = {
    
    var st0r:W256.t;
    var st1r:W256.t;
    var st2r:W256.t;
    var st3r:W256.t;
    var st4r:W256.t;
    var st5r:W256.t;
    var st6r:W256.t;
    
    (st0r, st1r, st2r, st3r, st4r, st5r, st6r) <@ __array_7u256 (state);
    (st0r, st1r, st2r, st3r, st4r, st5r, st6r) <@ _keccakf1600_avx2 (st0r,
    st1r, st2r, st3r, st4r, st5r, st6r);
    state <@ __7u256_array (st0r, st1r, st2r, st3r, st4r, st5r, st6r);
    return (state);
  }
  
  proc __theta_sum_4x_avx2 (a:W256.t Array25.t) : W256.t Array5.t = {
    var aux: int;
    
    var c:W256.t Array5.t;
    var x:int;
    var y:int;
    c <- witness;
    x <- 0;
    while (x < 5) {
      c.[x] <- a.[(x + 0)];
      x <- x + 1;
    }
    y <- 1;
    while (y < 5) {
      x <- 0;
      while (x < 5) {
        c.[x] <- (c.[x] `^` a.[(x + (y * 5))]);
        x <- x + 1;
      }
      y <- y + 1;
    }
    return (c);
  }
  
  proc __rol_4x_avx2 (x:W256.t, r:int, r8:W256.t, r56:W256.t) : W256.t = {
    
    var t:W256.t;
    
    if ((r <> 0)) {
      if ((r = 8)) {
        x <- VPSHUFB_256 x r8;
      } else {
        if ((r = 56)) {
          x <- VPSHUFB_256 x r56;
        } else {
          t <- VPSLL_4u64 x (W8.of_int r);
          x <- VPSRL_4u64 x (W8.of_int (64 - r));
          x <- (x `|` t);
        }
      }
    } else {
      
    }
    return (x);
  }
  
  proc __theta_rol_4x_avx2 (c:W256.t Array5.t, r8:W256.t, r56:W256.t) : 
  W256.t Array5.t = {
    var aux: int;
    var aux_0: W256.t;
    
    var d:W256.t Array5.t;
    var x:int;
    d <- witness;
    x <- 0;
    while (x < 5) {
      d.[x] <- c.[((x + 1) %% 5)];
      aux_0 <@ __rol_4x_avx2 (d.[x], 1, r8, r56);
      d.[x] <- aux_0;
      d.[x] <- (d.[x] `^` c.[(((x - 1) + 5) %% 5)]);
      x <- x + 1;
    }
    return (d);
  }
  
  proc __rol_sum_4x_avx2 (a:W256.t Array25.t, d:W256.t Array5.t, y:int,
                          r8:W256.t, r56:W256.t) : W256.t Array5.t = {
    var aux: int;
    var aux_0: W256.t;
    
    var b:W256.t Array5.t;
    var x:int;
    var x_:int;
    var y_:int;
    var r:int;
    b <- witness;
    x <- 0;
    while (x < 5) {
      x_ <- ((x + (3 * y)) %% 5);
      y_ <- x;
      r <@ __rhotates_spec (x_, y_);
      b.[x] <- a.[(x_ + (y_ * 5))];
      b.[x] <- (b.[x] `^` d.[x_]);
      aux_0 <@ __rol_4x_avx2 (b.[x], r, r8, r56);
      b.[x] <- aux_0;
      x <- x + 1;
    }
    return (b);
  }
  
  proc __set_row_4x_avx2 (e:W256.t Array25.t, b:W256.t Array5.t, y:int,
                          rc:W256.t) : W256.t Array25.t = {
    var aux: int;
    
    var x:int;
    var x1:int;
    var x2:int;
    var t:W256.t;
    
    x <- 0;
    while (x < 5) {
      x1 <- ((x + 1) %% 5);
      x2 <- ((x + 2) %% 5);
      t <- VPANDN_256 b.[x1] b.[x2];
      t <- (t `^` b.[x]);
      if (((x = 0) /\ (y = 0))) {
        t <- (t `^` rc);
      } else {
        
      }
      e.[(x + (y * 5))] <- t;
      x <- x + 1;
    }
    return (e);
  }
  
  proc __round_4x_avx2 (e:W256.t Array25.t, a:W256.t Array25.t, rc:W256.t,
                        r8:W256.t, r56:W256.t) : W256.t Array25.t = {
    var aux: int;
    
    var c:W256.t Array5.t;
    var d:W256.t Array5.t;
    var y:int;
    var b:W256.t Array5.t;
    b <- witness;
    c <- witness;
    d <- witness;
    c <@ __theta_sum_4x_avx2 (a);
    d <@ __theta_rol_4x_avx2 (c, r8, r56);
    y <- 0;
    while (y < 5) {
      b <@ __rol_sum_4x_avx2 (a, d, y, r8, r56);
      e <@ __set_row_4x_avx2 (e, b, y, rc);
      y <- y + 1;
    }
    return (e);
  }
  
  proc __keccakf1600_4x_avx2 (a:W256.t Array25.t) : W256.t Array25.t = {
    
    var s_e:W256.t Array25.t;
    var e:W256.t Array25.t;
    var rC:W256.t Array24.t;
    var r8:W256.t;
    var r56:W256.t;
    var c:W64.t;
    var rc:W256.t;
    rC <- witness;
    e <- witness;
    s_e <- witness;
    e <- s_e;
    rC <- KECCAK1600_RC_4x;
    r8 <- ROL8;
    r56 <- ROL56;
    c <- (W64.of_int 0);
    rc <-
    (get256_direct (WArray768.init256 (fun i => rC.[i])) (W64.to_uint c));
    e <@ __round_4x_avx2 (e, a, rc, r8, r56);
    rc <-
    (get256_direct (WArray768.init256 (fun i => rC.[i]))
    ((W64.to_uint c) + 32));
    a <@ __round_4x_avx2 (a, e, rc, r8, r56);
    c <- (c + (W64.of_int 64));
    while ((c \ult (W64.of_int (24 * 32)))) {
      rc <-
      (get256_direct (WArray768.init256 (fun i => rC.[i])) (W64.to_uint c));
      e <@ __round_4x_avx2 (e, a, rc, r8, r56);
      rc <-
      (get256_direct (WArray768.init256 (fun i => rC.[i]))
      ((W64.to_uint c) + 32));
      a <@ __round_4x_avx2 (a, e, rc, r8, r56);
      c <- (c + (W64.of_int 64));
    }
    return (a);
  }
  
  proc _keccakf1600_4x_avx2 (a:W256.t Array25.t) : W256.t Array25.t = {
    
    
    
    a <@ __keccakf1600_4x_avx2 (a);
    return (a);
  }
  
  proc _keccakf1600_4x_avx2_ (a:W256.t Array25.t) : W256.t Array25.t = {
    
    
    
    a <- a;
    a <@ _keccakf1600_4x_avx2 (a);
    a <- a;
    return (a);
  }
}.

