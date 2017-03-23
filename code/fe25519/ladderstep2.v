From Coq Require Import ZArith .
From mQhasm Require Import zDSL zRadix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope zdsl_scope.

Definition bi : Set := N * N * N * N * N.

Definition bi_list (X : bi) :=
  let '(x0, x1, x2, x3, x4) := X in
  [:: x0; x1; x2; x3; x4].

Definition bi_limbs (X : bi) :=
  let '(x0, x1, x2, x3, x4) := X in
  radix51 [:: zVar x0; zVar x1; zVar x2; zVar x3; zVar x4].

Definition fe25519_add (X Y R : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(y0, y1, y2, y3, y4) := Y in
let '(r0, r1, r2, r3, r4) := R in
[::
      (* r0 = x0 *)
zAssign r0 (zVar x0);
      (* r1 = x1 *)
zAssign r1 (zVar x1);
      (* r2 = x2 *)
zAssign r2 (zVar x2);
      (* r3 = x3 *)
zAssign r3 (zVar x3);
      (* r4 = x4 *)
zAssign r4 (zVar x4);
      (* r0 += y0 *)
zAssign r0 (zBinop zAdd (zVar r0) (zVar y0));
      (* r1 += y1 *)
zAssign r1 (zBinop zAdd (zVar r1) (zVar y1));
      (* r2 += y2 *)
zAssign r2 (zBinop zAdd (zVar r2) (zVar y2));
      (* r3 += y3 *)
zAssign r3 (zBinop zAdd (zVar r3) (zVar y3));
      (* r4 += y4 *)
zAssign r4 (zBinop zAdd (zVar r4) (zVar y4))
      (*  *)
] .

Definition fe25519_sub (X Y R : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(y0, y1, y2, y3, y4) := Y in
let '(r0, r1, r2, r3, r4) := R in
let crypto_sign_ed25519_amd64_51_2P0 :=
                       4503599627370458%Z in (* 0xFFFFFFFFFFFDA from consts *)
let crypto_sign_ed25519_amd64_51_2P1234 :=
                       4503599627370494%Z in (* 0xFFFFFFFFFFFFE from consts *)
[::
      (* r0 = x0 *)
zAssign r0 (zVar x0);
      (* r1 = x1 *)
zAssign r1 (zVar x1);
      (* r2 = x2 *)
zAssign r2 (zVar x2);
      (* r3 = x3 *)
zAssign r3 (zVar x3);
      (* r4 = x4 *)
zAssign r4 (zVar x4);
      (* r0 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P0 *)
zAssign r0 (zBinop zAdd (zVar r0) (zConst crypto_sign_ed25519_amd64_51_2P0));
      (* r1 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P1234 *)
zAssign r1 (zBinop zAdd (zVar r1) (zConst crypto_sign_ed25519_amd64_51_2P1234));
      (* r2 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P1234 *)
zAssign r2 (zBinop zAdd (zVar r2) (zConst crypto_sign_ed25519_amd64_51_2P1234));
      (* r3 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P1234 *)
zAssign r3 (zBinop zAdd (zVar r3) (zConst crypto_sign_ed25519_amd64_51_2P1234));
      (* r4 += *[uint64 *] &crypto_sign_ed25519_amd64_51_2P1234 *)
zAssign r4 (zBinop zAdd (zVar r4) (zConst crypto_sign_ed25519_amd64_51_2P1234));
      (* r0 -= y0 *)
zAssign r0 (zBinop zSub (zVar r0) (zVar y0));
      (* r1 -= y1 *)
zAssign r1 (zBinop zSub (zVar r1) (zVar y1));
      (* r2 -= y2 *)
zAssign r2 (zBinop zSub (zVar r2) (zVar y2));
      (* r3 -= y3 *)
zAssign r3 (zBinop zSub (zVar r3) (zVar y3));
      (* r4 -= y4 *)
zAssign r4 (zBinop zSub (zVar r4) (zVar y4))
      (*  *)
] .

Definition fe25519_mul121666 (X R : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(r0, r1, r2, r3, r4) := R in
let          qtwo :=   zConst 2%Z in
let         wsize :=   64%positive in
let           rax :=  1000 in
let           rdx :=  1001 in

[::
zAssign rax (zVar x0);
zSplit rdx rax (zBinop zMul (zVar rax) (zConst 121666)) 51;
zAssign r0 (zVar rax);
zAssign r1 (zVar rdx);
      (*    *)
zAssign rax (zVar x1);
zSplit rdx rax (zBinop zMul (zVar rax) (zConst 121666)) 51;
zAssign r1 (zBinop zAdd (zVar r1) (zVar rax));
zAssign r2 (zVar rdx);
      (*    *)
zAssign rax (zVar x2);
zSplit rdx rax (zBinop zMul (zVar rax) (zConst 121666)) 51;
zAssign r2 (zBinop zAdd (zVar r2) (zVar rax));
zAssign r3 (zVar rdx);
      (*    *)
zAssign rax (zVar x3);
zSplit rdx rax (zBinop zMul (zVar rax) (zConst 121666)) 51;
zAssign r3 (zBinop zAdd (zVar r3) (zVar rax));
zAssign r4 (zVar rdx);
      (*    *)
zAssign rax (zVar x4);
zSplit rdx rax (zBinop zMul (zVar rax) (zConst 121666)) 51;
zAssign r4 (zBinop zAdd (zVar r4) (zVar rax));
zAssign rdx (zBinop zMul (zVar rdx) (zConst 19));
zAssign r0 (zBinop zAdd (zVar r0) (zVar rdx))
] .

Definition fe25519_mul (X Y Z : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(y0, y1, y2, y3, y4) := Y in
let '(z0, z1, z2, z3, z4) := Z in

let          qtwo :=   zConst (2%Z) in
let         wsize :=   64%positive in
let      pow2 x n := zBinop zMul x (zPow qtwo n) in

let         carry := 9999 in
let           tmp := 9998 in
let          tmp2 := 9997 in

let            r0 :=  1000 in
let            r1 :=  1001 in
let            r2 :=  1002 in
let            r3 :=  1003 in
let            r4 :=  1004 in

let            c0 :=  1010 in
let            c1 :=  1011 in
let            c2 :=  1012 in
let            c3 :=  1013 in
let            c4 :=  1014 in

let        mulr01 :=  1020 in
let        mulr11 :=  1021 in
let        mulr21 :=  1022 in
let        mulr31 :=  1023 in
let        mulr41 :=  1024 in

let        mulrax :=  1030 in
let        mulrdx :=  1031 in
let          mult :=  1032 in
let    mulredmask :=  1033 in
let       mulx219 :=  1034 in
let       mulx319 :=  1035 in
let       mulx419 :=  1036 in
[::
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

Definition fe25519_sq (X Z : bi) : program :=
let '(x0, x1, x2, x3, x4) := X in
let '(z0, z1, z2, z3, z4) := Z in

let         wsize :=   64%positive in
let          qtwo :=   zConst (2%Z) in
let      pow2 x n := zBinop zMul x (zPow qtwo n) in

let            r0 :=  1000 in
let            r1 :=  1001 in
let            r2 :=  1002 in
let            r3 :=  1003 in
let            r4 :=  1004 in

let            c1 :=  1011 in
let            c2 :=  1012 in
let            c3 :=  1013 in
let            c4 :=  1014 in
let            c5 :=  1015 in
let            c6 :=  1016 in
let            c7 :=  1017 in

let          x119 :=  1021 in
let          x219 :=  1022 in
let          x319 :=  1023 in
let          x419 :=  1024 in

let           r01 :=  1030 in
let           r11 :=  1031 in
let           r21 :=  1032 in
let           r31 :=  1033 in
let           r41 :=  1034 in
let           rax :=  1035 in
let           rdx :=  1036 in

let             t :=  1040 in
let       redmask :=  1041 in

let           tmp := 9998 in
let         carry := 9999 in

[::
      (*  *)
      (* int64 rp *)
      (* int64 xp *)
      (*  *)
      (* input rp *)
      (* input xp *)
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

      (* #required for  macro *)

      (* int64 r01 *)
      (* int64 r11 *)
      (* int64 r21 *)
      (* int64 r31 *)
      (* int64 r41 *)
      (* int64 rax *)
      (* int64 rdx *)

      (* int64 t *)
      (* int64 redmask *)

      (*  *)
      (* enter fe25519_sq *)
      (*  *)
      (* c1_stack = c1 *)
      (* c2_stack = c2 *)
      (* c3_stack = c3 *)
      (* c4_stack = c4 *)
      (* c5_stack = c5 *)
      (* c6_stack = c6 *)
      (* c7_stack = c7 *)
      (*  *)
      (*   #BEGIN MACRO  *)
      (*   rax = *[uint64 *](xp + 0) *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 0) *)
      (*   r0 = rax *)
      (*   r01 = rdx *)
zAssign rax (zVar x0);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x0)) wsize;
zAssign r0 (zVar rax);
zAssign r01 (zVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 8) *)
      (*   r1 = rax *)
      (*   r11 = rdx *)
zAssign rax (zVar x0);
zAssign rax (zBinop zMul (zVar rax) qtwo);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x1)) wsize;
zAssign r1 (zVar rax);
zAssign r11 (zVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
      (*   r2 = rax *)
      (*   r21 = rdx *)
zAssign rax (zVar x0);
zAssign rax (zBinop zMul (zVar rax) qtwo);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x2)) wsize;
zAssign r2 (zVar rax);
zAssign r21 (zVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   r3 = rax *)
      (*   r31 = rdx *)
zAssign rax (zVar x0);
zAssign rax (zBinop zMul (zVar rax) qtwo);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x3)) wsize;
zAssign r3 (zVar rax);
zAssign r31 (zVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   r4 = rax *)
      (*   r41 = rdx *)
zAssign rax (zVar x0);
zAssign rax (zBinop zMul (zVar rax) qtwo);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x4)) wsize;
zAssign r4 (zVar rax);
zAssign r41 (zVar rdx);
      (*  *)
      (*   rax = *[uint64 *](xp + 8) *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 8) *)
      (*   carry? r2 += rax *)
      (*   r21 += rdx + carry *)
zAssign rax (zVar x1);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x1)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar rax));
zSplit carry r2 (zVar r2) wsize;
zAssign r21 (zBinop zAdd (zVar r21) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*   rax = *[uint64 *](xp + 8) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
      (*   carry? r3 += rax *)
      (*   r31 += rdx + carry *)
zAssign rax (zVar x1);
zAssign rax (zBinop zMul (zVar rax) qtwo);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x2)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar rax));
zSplit carry r3 (zVar r3) wsize;
zAssign r31 (zBinop zAdd (zVar r31) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*   rax = *[uint64 *](xp + 8) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   carry? r4 += rax *)
      (*   r41 += rdx + carry *)
zAssign rax (zVar x1);
zAssign rax (zBinop zMul (zVar rax) qtwo);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x3)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar rax));
zSplit carry r4 (zVar r4) wsize;
zAssign r41 (zBinop zAdd (zVar r41) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*   rax = *[uint64 *](xp + 8) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r0 += rax *)
      (*   r01 += rdx + carry *)
zAssign rax (zVar x1);
zAssign rax (zBinop zMul (zVar rax) (zConst 38%Z));
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x4)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar rax));
zSplit carry r0 (zVar r0) wsize;
zAssign r01 (zBinop zAdd (zVar r01) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*    *)
      (*   rax = *[uint64 *](xp + 16) *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
      (*   carry? r4 += rax *)
      (*   r41 += rdx + carry *)
zAssign rax (zVar x2);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x2)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar rax));
zSplit carry r4 (zVar r4) wsize;
zAssign r41 (zBinop zAdd (zVar r41) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*   rax = *[uint64 *](xp + 16) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   carry? r0 += rax *)
      (*   r01 += rdx + carry *)
zAssign rax (zVar x2);
zAssign rax (zBinop zMul (zVar rax) (zConst 38%Z));
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x3)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar rax));
zSplit carry r0 (zVar r0) wsize;
zAssign r01 (zBinop zAdd (zVar r01) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*   rax = *[uint64 *](xp + 16) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r1 += rax *)
      (*   r11 += rdx + carry *)
zAssign rax (zVar x2);
zAssign rax (zBinop zMul (zVar rax) (zConst 38%Z));
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x4)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar rax));
zSplit carry r1 (zVar r1) wsize;
zAssign r11 (zBinop zAdd (zVar r11) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*    *)
      (*   rax = *[uint64 *](xp + 24) *)
      (*   rax *= 19 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   carry? r1 += rax *)
      (*   r11 += rdx + carry *)
zAssign rax (zVar x3);
zAssign rax (zBinop zMul (zVar rax) (zConst 19%Z));
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x3)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar rax));
zSplit carry r1 (zVar r1) wsize;
zAssign r11 (zBinop zAdd (zVar r11) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*   rax = *[uint64 *](xp + 24) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r2 += rax *)
      (*   r21 += rdx + carry *)
zAssign rax (zVar x3);
zAssign rax (zBinop zMul (zVar rax) (zConst 38%Z));
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x4)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar rax));
zSplit carry r2 (zVar r2) wsize;
zAssign r21 (zBinop zAdd (zVar r21) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*    *)
      (*   rax = *[uint64 *](xp + 32) *)
      (*   rax *= 19 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r3 += rax *)
      (*   r31 += rdx + carry *)
zAssign rax (zVar x4);
zAssign rax (zBinop zMul (zVar rax) (zConst 19%Z));
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x4)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar rax));
zSplit carry r3 (zVar r3) wsize;
zAssign r31 (zBinop zAdd (zVar r31) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   redmask = *[uint64 *] &crypto_sign_ed25519_amd64_51_REDMASK51 *)
      (*   r01 = (r01.r0) << 13 *)
      (*   r0 &= redmask *)
zSplit tmp r0 (zVar r0) 51%positive;
zAssign r01 (zBinop zAdd (pow2 (zVar r01) 13%positive) (zVar tmp));
      (*    *)
      (*   r11 = (r11.r1) << 13 *)
      (*   r1 &= redmask *)
      (*   r1 += r01 *)
zSplit tmp r1 (zVar r1) 51%positive;
zAssign r11 (zBinop zAdd (pow2 (zVar r11) 13%positive) (zVar tmp));
zAssign r1 (zBinop zAdd (zVar r1) (zVar r01));
      (*    *)
      (*   r21 = (r21.r2) << 13 *)
      (*   r2 &= redmask *)
      (*   r2 += r11 *)
zSplit tmp r2 (zVar r2) 51%positive;
zAssign r21 (zBinop zAdd (pow2 (zVar r21) 13%positive) (zVar tmp));
zAssign r2 (zBinop zAdd (zVar r2) (zVar r11));
      (*    *)
      (*   r31 = (r31.r3) << 13 *)
      (*   r3 &= redmask *)
      (*   r3 += r21 *)
zSplit tmp r3 (zVar r3) 51%positive;
zAssign r31 (zBinop zAdd (pow2 (zVar r31) 13%positive) (zVar tmp));
zAssign r3 (zBinop zAdd (zVar r3) (zVar r21));
      (*    *)
      (*   r41 = (r41.r4) << 13 *)
      (*   r4 &= redmask *)
      (*   r4 += r31 *)
zSplit tmp r4 (zVar r4) 51%positive;
zAssign r41 (zBinop zAdd (pow2 (zVar r41) 13%positive) (zVar tmp));
zAssign r4 (zBinop zAdd (zVar r4) (zVar r31));
      (*   r41 = r41 * 19 *)
zAssign r41 (zBinop zMul (zVar r41) (zConst 19%Z));
      (*   r0 += r41 *)
zAssign r0 (zBinop zAdd (zVar r0) (zVar r41));
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   t = r0 *)
      (*   (uint64) t >>= 51 *)
      (*   t += r1 *)
      (*   r0 &= redmask *)
zAssign t (zVar r0);
zSplit t tmp (zVar t) (51%positive);
zAssign t (zBinop zAdd (zVar t) (zVar r1));
zAssign r0 (zVar tmp);
      (*    *)
      (*   r1 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t += r2 *)
      (*   r1 &= redmask *)
zAssign r1 (zVar t);
zSplit t tmp (zVar t) (51%positive);
zAssign t (zBinop zAdd (zVar t) (zVar r2));
zAssign r1 (zVar tmp);
      (*    *)
      (*   r2 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t += r3 *)
      (*   r2 &= redmask *)
zAssign r2 (zVar t);
zSplit t tmp (zVar t) (51%positive);
zAssign t (zBinop zAdd (zVar t) (zVar r3));
zAssign r2 (zVar tmp);
      (*    *)
      (*   r3 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t += r4 *)
      (*   r3 &= redmask *)
zAssign r3 (zVar t);
zSplit t tmp (zVar t) (51%positive);
zAssign t (zBinop zAdd (zVar t) (zVar r4));
zAssign r3 (zVar tmp);
      (*    *)
      (*   r4 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t *= 19 *)
      (*   r0 += t *)
      (*   r4 &= redmask *)
zAssign r4 (zVar t);
zSplit t tmp (zVar t) (51%positive);
zAssign t (zBinop zMul (zVar t) (zConst 19%Z));
zAssign r0 (zBinop zAdd (zVar r0) (zVar t));
zAssign r4 (zVar tmp);
      (*   #END MACRO  *)
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (* *[uint64 *](rp + 0) = r0 *)
zAssign z0 (zVar r0);
      (* *[uint64 *](rp + 8) = r1 *)
zAssign z1 (zVar r1);
      (* *[uint64 *](rp + 16) = r2 *)
zAssign z2 (zVar r2);
      (* *[uint64 *](rp + 24) = r3 *)
zAssign z3 (zVar r3);
      (* *[uint64 *](rp + 32) = r4 *)
zAssign z4 (zVar r4)
      (*   *)
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

Definition fe25519_ladderstep : program :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
fe25519_add X2 Z2 T1 ++
fe25519_sub X2 Z2 T2 ++
fe25519_sq T2 T7 ++
fe25519_sq T1 T6 ++
fe25519_sub T6 T7 T5 ++
fe25519_add X3 Z3 T3 ++
fe25519_sub X3 Z3 T4 ++
fe25519_mul T3 T2 T9 ++
fe25519_mul T4 T1 T8 ++
fe25519_add T8 T9 X3_1 ++
fe25519_sub T8 T9 Z3_1 ++
fe25519_sq X3_1 X3' ++
fe25519_sq Z3_1 Z3_2 ++
fe25519_mul Z3_2 X1 Z3' ++
fe25519_mul T6 T7 X2' ++
fe25519_mul121666 T5 Z2_1 ++
fe25519_add Z2_1 T7 Z2_2 ++
fe25519_mul Z2_2 T5 Z2'.

Definition fe25519_ladderstep_inputs : VS.t :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
VSLemmas.OP.P.of_list (bi_list X1 ++ bi_list X2 ++ bi_list Z2 ++
                               bi_list X3 ++ bi_list Z3).

Definition fe25519_ladderstep_pre : bexp := zTrue.

Definition fe25519_ladderstep_post1 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
zEqMod
  (bi_limbs X2')
  (zPow (zsub (zPow (bi_limbs X2) 2) (zPow (bi_limbs Z2) 2)) 2)
  n25519.

Definition fe25519_ladderstep_post2 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
zEqMod
  (bi_limbs Z2')
  (zmuls [:: zConst 4;
            bi_limbs X2;
            bi_limbs Z2;
            zadds [:: zPow (bi_limbs X2) 2;
                     zmuls [:: zConst 486662; bi_limbs X2; bi_limbs Z2];
                     zPow (bi_limbs Z2) 2]
         ])
  n25519.

Definition fe25519_ladderstep_post3 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
zEqMod
  (zmul (bi_limbs X3')
        (zmul (bi_limbs X1)
              (zPow (zsub (zmul (bi_limbs X3) (bi_limbs Z2))
                          (zmul (bi_limbs X2) (bi_limbs Z3))) 2)))
  (zmul (bi_limbs Z3')
        (zPow (zsub (zmul (bi_limbs X2) (bi_limbs X3))
                    (zmul (bi_limbs Z2) (bi_limbs Z3))) 2))
  n25519.

Definition fe25519_ladderstep_post3_1 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
zEqMod
  (bi_limbs X3')
  (zmul (zConst 4)
        (zPow (zsub (zmul (bi_limbs X2) (bi_limbs X3))
                    (zmul (bi_limbs Z2) (bi_limbs Z3))) 2))
  n25519.

Definition fe25519_ladderstep_post3_2 : bexp :=
let X1   := (10, 11, 12, 13, 14) in
let X2   := (20, 21, 22, 23, 24) in
let X2'  := (30, 31, 32, 33, 34) in
let Z2   := (40, 41, 42, 43, 44) in
let Z2_1 := (50, 51, 52, 53, 54) in
let Z2_2 := (60, 61, 62, 63, 64) in
let Z2'  := (70, 71, 72, 73, 74) in
let X3   := (80, 81, 82, 83, 84) in
let X3_1 := (90, 91, 92, 93, 94) in
let X3'  := (100, 101, 102, 103, 104) in
let Z3   := (110, 111, 112, 113, 114) in
let Z3_1 := (120, 121, 122, 123, 124) in
let Z3_2 := (130, 131, 132, 133, 134) in
let Z3'  := (140, 141, 142, 143, 144) in
let T1   := (150, 151, 152, 153, 154) in
let T2   := (160, 161, 162, 163, 164) in
let T3   := (170, 171, 172, 173, 174) in
let T4   := (180, 181, 182, 183, 184) in
let T5   := (190, 191, 192, 193, 194) in
let T6   := (200, 201, 202, 203, 204) in
let T7   := (210, 211, 212, 213, 214) in
let T8   := (220, 221, 222, 223, 224) in
let T9   := (230, 231, 232, 233, 234) in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
zEqMod
  (bi_limbs Z3')
  (zmul (zConst 4)
        (zmul (bi_limbs X1)
              (zPow (zsub (zmul (bi_limbs X3) (bi_limbs Z2))
                          (zmul (bi_limbs X2) (bi_limbs Z3))) 2)))
  n25519.

Definition fe25519_ladderstep_post : bexp :=
  zands [:: fe25519_ladderstep_post1;
            fe25519_ladderstep_post2;
            fe25519_ladderstep_post3 ].

Definition fe25519_ladderstep_spec :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post |}.

Definition fe25519_ladderstep_spec1 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post1 |}.

Definition fe25519_ladderstep_spec2 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post2 |}.

Definition fe25519_ladderstep_spec3 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post3 |}.

Definition fe25519_ladderstep_spec3_1 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post3_1 |}.

Definition fe25519_ladderstep_spec3_2 :=
  {| spre := fe25519_ladderstep_pre;
     sprog := fe25519_ladderstep;
     spost := fe25519_ladderstep_post3_2 |}.

From mathcomp Require Import eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_ladderstep2 : valid_ispec (fe25519_ladderstep_inputs, fe25519_ladderstep_spec2).
Proof.
  time "valid_fe25519_ladderstep2" verify_ispec.
Qed.

Close Scope zdsl_scope.
Close Scope N_scope.
