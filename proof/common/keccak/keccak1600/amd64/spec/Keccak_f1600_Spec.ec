(******************************************************************************
   Keccak_f1600_Spec.ec:

   Specification of the Keccak-f1600 permutation.

   Normative reference: FIPS PUB 202
   https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.202.pdf
******************************************************************************)
require import List Int IntDiv CoreMap.

from Jasmin require export JWord JUtils.

require export JWordList.

(** State (sec. 3.1)

  We specialise the width of the permutation to [b = 1600], leading to the related
  quantities [w = b / 25 = 64] and [l = log2 (b/25) = 6] (c.f. Table 1).

  The state [A] is organized as a matrix of 5-by-5-by 64 bits. For convenience, and
  since Jasmin does not support directly matrices, we adopt the view of an array of
  25 words of 64 bit.

    A[x,y,z] = st[ x * (5*y)].[z]	, for 0 <= x,y < y, and 0 <= z < 64
*)

from JExtract require export Array5 Array24 Array25.


type state = W64.t Array25.t.

(* Index access: [A[x,y,z] = st.[idx(x,y)].[z] *)
op idx (xy: int*int): int = (xy.`1 %% 5) + (5 * (xy.`2 %% 5)).

op state2bits (st: state): bool list =
 w64L2bits (to_list st).
op bits2state (bs: bool list): state =
 Array25.of_list W64.zero (bits2w64L bs).

(** Initial state *)
op st0 : state = Array25.create W64.zero.

(** Round-constants *)
op rc_spec: W64.t Array24.t =
  Array24.of_list
    witness
    (map W64.of_int
      [                   1
      ;               32898
      ; 9223372036854808714
      ; 9223372039002292224
      ;               32907
      ;          2147483649
      ; 9223372039002292353
      ; 9223372036854808585
      ;                 138
      ;                 136
      ;          2147516425
      ;          2147483658
      ;          2147516555
      ; 9223372036854775947
      ; 9223372036854808713
      ; 9223372036854808579
      ; 9223372036854808578
      ; 9223372036854775936
      ;               32778
      ; 9223372039002259466
      ; 9223372039002292353
      ; 9223372036854808704
      ;          2147483649
      ; 9223372039002292232
      ]).

(** Imperative specification for [Keccak-f1600]. *)
module Spec = {
  proc keccak_theta (a: state) : state = {
    var x, y: int;   
    var c:W64.t Array5.t;
    var d:W64.t Array5.t;

    c <- witness;
    d <- witness;
    x <- 0;
    while (x < 5) {
      c.[x] <- W64.of_int 0;
      y <- 0;
      while (y < 5) {
        c.[x] <- c.[x] `^` a.[idx(x,y)];
        y <- y + 1;
      }
      x <- x + 1;
    }
    x <- 0;
    while (x < 5) {
      d.[x] <- c.[((x + 1) %% 5)];
      d.[x] <- d.[x] `|<<<|` 1;
      d.[x] <- (d.[x] `^` c.[((x + 4) %% 5)]);
      x <- x + 1;
    }
    x <- 0;
    while (x < 5) {
      y <- 0;
      while (y < 5) {
        a.[idx(x,y)] <- (a.[idx(x,y)] `^` d.[x]);
        y <- y + 1;
      }
      x <- x + 1;
    }
    return (a);
  }
  
  proc keccak_rho_offsets (i:int) : int = {
    var r, x, y, z, t:int;

    r <- 0;
    x <- 1;
    y <- 0;
    t <- 0;
    while (t < 24) {
      r <- if i = idx(x,y)
           then ((((t + 1) * (t + 2)) %/ 2) %% 64)
           else r;
      z <- (((2 * x) + (3 * y)) %% 5);
      x <- y;
      y <- z;
      t <- t + 1;
    }
    return r;
  }

  proc keccak_rho (a: state) : state = {
    var i, t: int;
   
    i <- 0;
    while (i < 25) {
      t <@ keccak_rho_offsets(i);
      a.[i] <- a.[i] `|<<<|` t;
      i <- i + 1;
    }
    return a;
  }

  proc keccak_pi (a: state) : state = {
    var b: state;
    var x, y:int;

    b <- a;
    x <- 0;
    while (x < 5) {
      y <- 0;
      while (y < 5) {
        a.[idx(y, 2*x + 3*y)] <- b.[idx(x,y)];
        y <- y + 1;
      }
      x <- x + 1;
    }
    return a;
  }
  
  proc keccak_chi (a: state) : state = {
    var x, y: int;
    var b: W64.t Array25.t;

    b <- witness;
    y <- 0;
    while (y < 5) {
      x <- 0;
      while (x < 5) {
        b.[idx(x,y)] <- a.[idx(x,y)]
                          `^` (invw a.[idx(x+1, y)]
                               `&` a.[idx(x+2, y)]);
        x <- x + 1;
      }
      y <- y + 1;
    }
    return b;
  }

  proc keccak_iota (a: state, c: W64.t) : state = {
    a.[0] <- a.[0] `^` c;
    return a;
  }
  
  proc keccak_round (st: state, c:W64.t) : state = {
    st <@ keccak_theta  (st);
    st <@ keccak_rho    (st);
    st <@ keccak_pi     (st);
    st <@ keccak_chi    (st);
    st <@ keccak_iota   (st, c);
    return (st);
  }
  
  proc keccak_f (st: state) : state = {
    var round:int;
    round <- 0;
    while (round < 24) {
      st <@ keccak_round (st, rc_spec.[round]);
      round <- round + 1;
    }
    return (st);
  }
}.


