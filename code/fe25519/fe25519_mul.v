From Coq Require Import ZArith .
From mQhasm Require Import zDSL zRadix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope zdsl_scope.

Definition fe25519_mul : program :=

let          qtwo :=   zConst (2%Z) in
let         wsize :=   64%positive in
let      pow2 x n := zBinop zMul x (zPow qtwo n) in

let            x0 :=   0 in (* *[uint64 *](xp +  0) *)
let            x1 :=   1 in (* *[uint64 *](xp +  8) *)
let            x2 :=   2 in (* *[uint64 *](xp + 16) *)
let            x3 :=   3 in (* *[uint64 *](xp + 24) *)
let            x4 :=   4 in (* *[uint64 *](xp + 32) *)
let            y0 :=   5 in (* *[uint64 *](yp +  0) *)
let            y1 :=   6 in (* *[uint64 *](yp +  8) *)
let            y2 :=   7 in (* *[uint64 *](yp + 16) *)
let            y3 :=   8 in (* *[uint64 *](yp + 24) *)
let            y4 :=   9 in (* *[uint64 *](yp + 32) *)
let            z0 :=  10 in (* *[uint64 *](rp +  0) *)
let            z1 :=  11 in (* *[uint64 *](rp +  8) *)
let            z2 :=  12 in (* *[uint64 *](rp + 16) *)
let            z3 :=  13 in (* *[uint64 *](rp + 24) *)
let            z4 :=  14 in (* *[uint64 *](rp + 32) *)
let         carry := 999 in
let           tmp := 998 in
let          tmp2 := 997 in

let            r0 :=  20 in
let            r1 :=  21 in
let            r2 :=  22 in
let            r3 :=  23 in
let            r4 :=  24 in

let            c0 :=  30 in
let            c1 :=  31 in
let            c2 :=  32 in
let            c3 :=  33 in
let            c4 :=  34 in

let        mulr01 :=  40 in
let        mulr11 :=  41 in
let        mulr21 :=  42 in
let        mulr31 :=  43 in
let        mulr41 :=  44 in

let        mulrax :=  50 in
let        mulrdx :=  51 in
let          mult :=  52 in
let    mulredmask :=  53 in
let       mulx219 :=  54 in
let       mulx319 :=  55 in
let       mulx419 :=  56 in
[::
      (*  *)
      (* int64 rp *)
      (* int64 xp *)
      (* int64 yp *)
      (*  *)
      (* input rp *)
      (* input xp *)
      (* input yp *)
      (*  *)
      (* int64 r0 *)
      (* int64 r1 *)
      (* int64 r2 *)
      (* int64 r3 *)
      (* int64 r4 *)
      (*  *)
      (* int64 c1 *)
      (* int64 c2 *)
      (* int64 c3 *)
      (* int64 c4 *)
      (* int64 c5 *)
      (* int64 c6 *)
      (* int64 c7 *)
      (* caller c1 *)
      (* caller c2 *)
      (* caller c3 *)
      (* caller c4 *)
      (* caller c5 *)
      (* caller c6 *)
      (* caller c7 *)
      (* stack64 c1_stack *)
      (* stack64 c2_stack *)
      (* stack64 c3_stack *)
      (* stack64 c4_stack *)
      (* stack64 c5_stack *)
      (* stack64 c6_stack *)
      (* stack64 c7_stack *)
      (* stack64 x119_stack *)
      (* stack64 x219_stack *)
      (* stack64 x319_stack *)
      (* stack64 x419_stack *)
      (*  *)
      (* stack64 rp_stack *)
      (*  *)
      (* # required for the mul template *)
      (* int64 mulr01 *)
      (* int64 mulr11 *)
      (* int64 mulr21 *)
      (* int64 mulr31 *)
      (* int64 mulr41 *)
      (* int64 mulrax *)
      (* int64 mulrdx *)
      (* int64 mult *)
      (* int64 mulredmask *)
      (* stack64 mulx219_stack *)
      (* stack64 mulx319_stack *)
      (* stack64 mulx419_stack *)

      (*  *)

      (* enter crypto_sign_ed25519_amd64_51_fe25519_mul *)

      (*  *)

      (*   c1_stack = c1 *)
      (*   c2_stack = c2 *)
      (*   c3_stack = c3 *)
      (*   c4_stack = c4 *)
      (*   c5_stack = c5 *)
      (*   c6_stack = c6 *)
      (*   c7_stack = c7 *)
      (*   rp_stack = rp *)

      (*  *)
      (* yp = yp *)
      (*  *)
      (*  *)

      (*   #BEGIN MACRO mul *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   mulrax *= 19 *)
      (*   mulx319_stack = mulrax *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   r0 = mulrax *)
      (*   mulr01 = mulrdx *)
zAssign mulrax (zVar x3);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zAssign mulx319 (zVar mulrax);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r0 (zVar mulrax);
zAssign mulr01 (zVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 32) *)
      (*   mulrax *= 19 *)
      (*   mulx419_stack = mulrax *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
zAssign mulrax (zVar x4);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zAssign mulx419 (zVar mulrax);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulrax));
zSplit carry r0 (zVar r0) wsize;
zAssign mulr01 (zBinop zAdd (zVar mulr01) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulrax));
zSplit carry r0 (zVar r0) wsize;
zAssign mulr01 (zBinop zAdd (zVar mulr01) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   r1 = mulrax *)
      (*   mulr11 = mulrdx *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r1 (zVar mulrax);
zAssign mulr11 (zVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   r2 = mulrax *)
      (*   mulr21 = mulrdx *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r2 (zVar mulrax);
zAssign mulr21 (zVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   r3 = mulrax *)
      (*   mulr31 = mulrdx *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r3 (zVar mulrax);
zAssign mulr31 (zVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 0) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   r4 = mulrax *)
      (*   mulr41 = mulrdx *)
zAssign mulrax (zVar x0);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r4 (zVar mulrax);
zAssign mulr41 (zVar mulrdx);
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulrax));
zSplit carry r1 (zVar r1) wsize;
zAssign mulr11 (zBinop zAdd (zVar mulr11) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulrax));
zSplit carry r2 (zVar r2) wsize;
zAssign mulr21 (zBinop zAdd (zVar mulr21) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulrax));
zSplit carry r3 (zVar r3) wsize;
zAssign mulr31 (zBinop zAdd (zVar mulr31) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulrax));
zSplit carry r4 (zVar r4) wsize;
zAssign mulr41 (zBinop zAdd (zVar mulr41) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 8) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
zAssign mulrax (zVar x1);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulrax));
zSplit carry r0 (zVar r0) wsize;
zAssign mulr01 (zBinop zAdd (zVar mulr01) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulrax));
zSplit carry r2 (zVar r2) wsize;
zAssign mulr21 (zBinop zAdd (zVar mulr21) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulrax));
zSplit carry r3 (zVar r3) wsize;
zAssign mulr31 (zBinop zAdd (zVar mulr31) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulrax));
zSplit carry r4 (zVar r4) wsize;
zAssign mulr41 (zBinop zAdd (zVar mulr41) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r0 += mulrax *)
      (*   mulr01 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulrax));
zSplit carry r0 (zVar r0) wsize;
zAssign mulr01 (zBinop zAdd (zVar mulr01) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 16) *)
      (*   mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
zAssign mulrax (zVar x2);
zAssign mulrax (zBinop zMul (zVar mulrax) (zConst 19%Z));
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulrax));
zSplit carry r1 (zVar r1) wsize;
zAssign mulr11 (zBinop zAdd (zVar mulr11) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
zAssign mulrax (zVar x3);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulrax));
zSplit carry r3 (zVar r3) wsize;
zAssign mulr31 (zBinop zAdd (zVar mulr31) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 24) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 8) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
zAssign mulrax (zVar x3);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y1)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulrax));
zSplit carry r4 (zVar r4) wsize;
zAssign mulr41 (zBinop zAdd (zVar mulr41) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx319_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
zAssign mulrax (zVar mulx319);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulrax));
zSplit carry r1 (zVar r1) wsize;
zAssign mulr11 (zBinop zAdd (zVar mulr11) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx319_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
zAssign mulrax (zVar mulx319);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulrax));
zSplit carry r2 (zVar r2) wsize;
zAssign mulr21 (zBinop zAdd (zVar mulr21) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = *[uint64 *](xp + 32) *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 0) *)
      (*   carry? r4 += mulrax *)
      (*   mulr41 += mulrdx + carry *)
zAssign mulrax (zVar x4);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y0)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulrax));
zSplit carry r4 (zVar r4) wsize;
zAssign mulr41 (zBinop zAdd (zVar mulr41) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 16) *)
      (*   carry? r1 += mulrax *)
      (*   mulr11 += mulrdx + carry *)
zAssign mulrax (zVar mulx419);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y2)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulrax));
zSplit carry r1 (zVar r1) wsize;
zAssign mulr11 (zBinop zAdd (zVar mulr11) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 24) *)
      (*   carry? r2 += mulrax *)
      (*   mulr21 += mulrdx + carry *)
zAssign mulrax (zVar mulx419);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y3)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulrax));
zSplit carry r2 (zVar r2) wsize;
zAssign mulr21 (zBinop zAdd (zVar mulr21) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*   mulrax = mulx419_stack *)
      (*   #mulrax *= 19 *)
      (*   (uint128) mulrdx mulrax = mulrax * *[uint64 *](yp + 32) *)
      (*   carry? r3 += mulrax *)
      (*   mulr31 += mulrdx + carry *)
zAssign mulrax (zVar mulx419);
zSplit mulrdx mulrax (zBinop zMul (zVar mulrax) (zVar y4)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulrax));
zSplit carry r3 (zVar r3) wsize;
zAssign mulr31 (zBinop zAdd (zVar mulr31) (zBinop zAdd (zVar mulrdx) (zVar carry)));
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   mulredmask = *[uint64 *] &crypto_sign_ed25519_amd64_51_REDMASK51 *)
      (*   mulr01 = (mulr01.r0) << 13 *)
      (*   r0 &= mulredmask *)
zSplit tmp r0 (zVar r0) 51%positive;
zAssign mulr01 (zBinop zAdd (pow2 (zVar mulr01) 13%positive) (zVar tmp));
      (*   mulr11 = (mulr11.r1) << 13 *)
      (*   r1 &= mulredmask *)
      (*   r1 += mulr01 *)
zSplit tmp r1 (zVar r1) 51%positive;
zAssign mulr11 (zBinop zAdd (pow2 (zVar mulr11) 13%positive) (zVar tmp));
zAssign r1 (zBinop zAdd (zVar r1) (zVar mulr01));
      (*   mulr21 = (mulr21.r2) << 13 *)
      (*   r2 &= mulredmask *)
      (*   r2 += mulr11 *)
zSplit tmp r2 (zVar r2) 51%positive;
zAssign mulr21 (zBinop zAdd (pow2 (zVar mulr21) 13%positive) (zVar tmp));
zAssign r2 (zBinop zAdd (zVar r2) (zVar mulr11));
      (*   mulr31 = (mulr31.r3) << 13 *)
      (*   r3 &= mulredmask *)
      (*   r3 += mulr21 *)
zSplit tmp r3 (zVar r3) 51%positive;
zAssign mulr31 (zBinop zAdd (pow2 (zVar mulr31) 13%positive) (zVar tmp));
zAssign r3 (zBinop zAdd (zVar r3) (zVar mulr21));
      (*   mulr41 = (mulr41.r4) << 13 *)
      (*   r4 &= mulredmask *)
      (*   r4 += mulr31 *)
zSplit tmp r4 (zVar r4) 51%positive;
zAssign mulr41 (zBinop zAdd (pow2 (zVar mulr41) 13%positive) (zVar tmp));
zAssign r4 (zBinop zAdd (zVar r4) (zVar mulr31));
      (*   mulr41 = mulr41 * 19 *)
zAssign mulr41 (zBinop zMul (zVar mulr41) (zConst 19%Z));
      (*   r0 += mulr41 *)
zAssign r0 (zBinop zAdd (zVar r0) (zVar mulr41));
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   mult = r0 *)
      (*   (uint64) mult >>= 51 *)
      (*   mult += r1 *)
zAssign mult (zVar r0);
zSplit mult tmp (zVar mult) (51%positive);
zAssign mult (zBinop zAdd (zVar mult) (zVar r1));
      (*   r1 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r0 &= mulredmask *)
      (*   mult += r2 *)
zAssign r1 (zVar mult);
zSplit mult tmp2 (zVar mult) (51%positive);
zAssign r0 (zVar tmp);
zAssign mult (zBinop zAdd (zVar mult) (zVar r2));
      (*   r2 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r1 &= mulredmask *)
      (*   mult += r3 *)
zAssign r2 (zVar mult);
zSplit mult tmp (zVar mult) (51%positive);
zAssign r1 (zVar tmp2);
zAssign mult (zBinop zAdd (zVar mult) (zVar r3));
      (*   r3 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r2 &= mulredmask *)
      (*   mult += r4 *)
zAssign r3 (zVar mult);
zSplit mult tmp2 (zVar mult) (51%positive);
zAssign r2 (zVar tmp);
zAssign mult (zBinop zAdd (zVar mult) (zVar r4));
      (*   r4 = mult *)
      (*   (uint64) mult >>= 51 *)
      (*   r3 &= mulredmask *)
zAssign r4 (zVar mult);
zSplit mult tmp (zVar mult) (51%positive);
zAssign r3 (zVar tmp2);
      (*   mult *= 19 *)
      (*   r0 += mult *)
      (*   r4 &= mulredmask *)
zAssign mult (zBinop zMul (zVar mult) (zConst 19%Z));
zAssign r0 (zBinop zAdd (zVar r0) (zVar mult));
zAssign r4 (zVar tmp);
      (*   #END MACRO mul *)

      (*  *)
      (* *[uint64 *](rp + 0) = r0 *)
      (* *[uint64 *](rp + 8) = r1 *)
      (* *[uint64 *](rp + 16) = r2 *)
      (* *[uint64 *](rp + 24) = r3 *)
      (* *[uint64 *](rp + 32) = r4 *)
zAssign z0 (zVar r0);
zAssign z1 (zVar r1);
zAssign z2 (zVar r2);
zAssign z3 (zVar r3);
zAssign z4 (zVar r4)
      (*  *)

      (* c1 =c1_stack *)
      (* c2 =c2_stack *)
      (* c3 =c3_stack *)
      (* c4 =c4_stack *)
      (* c5 =c5_stack *)
      (* c6 =c6_stack *)
      (* c7 =c7_stack *)
      (*  *)

      (* leave *)
] .

Definition fe25519_mul_inputs : VS.t :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
let            y0 :=   5 in
let            y1 :=   6 in
let            y2 :=   7 in
let            y3 :=   8 in
let            y4 :=   9 in
VSLemmas.OP.P.of_list [:: x0; x1; x2; x3; x4; y0; y1; y2; y3; y4].

Definition fe25519_mul_pre : bexp := zTrue.

Definition fe25519_mul_post : bexp :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
let            y0 :=   5 in
let            y1 :=   6 in
let            y2 :=   7 in
let            y3 :=   8 in
let            y4 :=   9 in
let            r0 :=  20 in
let            r1 :=  21 in
let            r2 :=  22 in
let            r3 :=  23 in
let            r4 :=  24 in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
zEqMod
  (
    (radix51 [::zVar x0; zVar x1; zVar x2; zVar x3; zVar x4])
    @*
    (radix51 [::zVar y0; zVar y1; zVar y2; zVar y3; zVar y4])
  )
  (radix51 [::zVar r0; zVar r1; zVar r2; zVar r3; zVar r4])
  (n25519).

Definition fe25519_mul_spec :=
  {| spre := fe25519_mul_pre;
     sprog := fe25519_mul;
     spost := fe25519_mul_post |}.

From mathcomp Require Import eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_mul : valid_ispec (fe25519_mul_inputs, fe25519_mul_spec).
Proof.
  time "valid_fe25519_mul" verify_ispec.
Qed.

Close Scope zdsl_scope.
Close Scope N_scope.
