From Coq Require Import ZArith .
From mathcomp Require Import ssreflect ssrbool ssrnat seq .
From Common Require Import Bits .
From mQhasm Require Import bvDSL bvVerify Options .
Set Implicit Arguments .
Unset Strict Implicit .
Import Prenex Implicits .
Open Scope N_scope.
Open Scope bvdsl_scope.

Definition radix64 := @limbs 64 .

Definition check_inputs : VS.t :=
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  VSLemmas.OP.P.of_list [:: a0; a1; a2; a3 ].

Definition check_pre : bexp := bvrands [::].

Definition nistz256_from_mont_post : bexp :=
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  let  t0 := 3000 in
  let  t1 := 3001 in
  let  t2 := 3002 in
  let  t3 := 3003 in
  let  p0 := 18446744073709551615%Z in (* FFFFFFFFFFFFFFFF *)
  let  p1 := 4294967295%Z in           (* 00000000FFFFFFFF *)
  let  p2 := 0%Z in                    (* 0000000000000000 *)
  let  p3 := 18446744069414584321%Z in (* FFFFFFFF00000001 *)
  bvands2
    [::
       bveEqMod
       (
         (radix64 [::bvevar a0; bvevar a1; bvevar a2; bvevar a3])
       )

       (
         (radix64 [::bvconst 0; bvconst 0; bvconst 0; bvconst 0;
                     bvevar t0; bvevar t1; bvevar t2; bvevar t3])
       )    

       (
         (radix64 [::bvconst p0; bvconst p1; bvconst p2; bvconst p3])
       )
    ]
    [::]
      
.

Definition program :=
let L0x62c080 := 7 in
let L0x62c088 := 1 in
let L0x62c090 := 6 in
let L0x62c098 := 0 in

let L0x427008 := 11 in
let L0x427018 := 10 in

let r13 := 2 in
let r10 := 3 in
let r11 := 4 in
let r8 := 5 in
let r9 := 8 in
let rdx := 9 in
let rcx := 12 in
let r12 := 13 in
let rax := 14 in

let carry := 999 in

let a0 := 1000 in
let a1 := 1001 in
let a2 := 1002 in
let a3 := 1003 in
let t0 := 3000 in
let t1 := 3001 in
let t2 := 3002 in
let t3 := 3003 in
let p0 := 18446744073709551615%Z in (* FFFFFFFFFFFFFFFF *)
let p1 := 4294967295%Z in           (* 00000000FFFFFFFF *)
let p2 := 0%Z in                    (* 0000000000000000 *)
let p3 := 18446744069414584321%Z in (* FFFFFFFF00000001 *)
[::

bvAssign L0x62c080 (bvVar a0);
bvAssign L0x62c088 (bvVar a1);
bvAssign L0x62c090 (bvVar a2);
bvAssign L0x62c098 (bvVar a3);

bvAssign L0x427008 (bvConst (fromPosZ p1));
bvAssign L0x427018 (bvConst (fromPosZ p3));

(* mov    (%rsi),%rax                              #! EA = L0x62c080 *)
bvAssign rax (bvVar L0x62c080);
(* mov    -0xdb6(%rip),%r13        # 0x427018      #! EA = L0x427018 *)
bvAssign r13 (bvVar L0x427018);
(* mov    0x8(%rsi),%r9                            #! EA = L0x62c088 *)
bvAssign r9 (bvVar L0x62c088);
(* mov    0x10(%rsi),%r10                          #! EA = L0x62c090 *)
bvAssign r10 (bvVar L0x62c090);
(* mov    0x18(%rsi),%r11                          #! EA = L0x62c098 *)
bvAssign r11 (bvVar L0x62c098);
(* mov    %rax,%r8 *)
bvAssign r8 (bvVar rax);
(* mov    -0xddc(%rip),%r12        # 0x427008      #! EA = L0x427008 *)
bvAssign r12 (bvVar L0x427008);
(* mov    %rax,%rcx *)
bvAssign rcx (bvVar rax);
(* shl    $0x20,%r8 *)
(* bvShl r8 (bvVar r8) (fromNat 32); *)
(* mul    %r13 *)
bvMulf rdx rax (bvVar r13) (bvVar rax);
(* shr    $0x20,%rcx *)
(* bvSplit rcx tmp (bvVar rcx) (fromNat 32); *)
(* NOTE: merge 'shl $0x20,%r8' with 'shr $0x20,%rcx' *)
bvSplit rcx r8 (bvVar r8) (fromNat 32);
bvShl r8 (bvVar r8) (fromNat 32);
(* add    %r8,%r9 *)
bvAddC carry r9 (bvVar r8) (bvVar r9);
(* adc    %rcx,%r10 *)
bvAdcC carry r10 (bvVar rcx) (bvVar r10) carry;
(* adc    %rax,%r11 *)
bvAdcC carry r11 (bvVar rax) (bvVar r11) carry;
(* mov    %r9,%rax *)
bvAssign rax (bvVar r9);
(* adc    $0x0,%rdx *)
bvAdcC carry rdx (bvVar rdx) (bvConst (fromPosZ 0%Z)) carry;
(* mov    %r9,%rcx *)
bvAssign rcx (bvVar r9);
(* shl    $0x20,%r9 *)
(* bvShl r9 (bvVar r9) (fromNat 32); *)
(* mov    %rdx,%r8 *)
bvAssign r8 (bvVar rdx);
(* mul    %r13 *)
bvMulf rdx rax (bvVar r13) (bvVar rax);
(* shr    $0x20,%rcx *)
(* bvSplit rcx tmp (bvVar rcx) (fromNat 32); *)
(* NOTE: merge 'shl $0x20,%r9' with 'shr $0x20,%rcx' *)
bvSplit rcx r9 (bvVar r9) (fromNat 32);
bvShl r9 (bvVar r9) (fromNat 32);
(* add    %r9,%r10 *)
bvAddC carry r10 (bvVar r9) (bvVar r10);
(* adc    %rcx,%r11 *)
bvAdcC carry r11 (bvVar rcx) (bvVar r11) carry;
(* adc    %rax,%r8 *)
bvAdcC carry r8 (bvVar rax) (bvVar r8) carry;
(* mov    %r10,%rax *)
bvAssign rax (bvVar r10);
(* adc    $0x0,%rdx *)
bvAdcC carry rdx (bvVar rdx) (bvConst (fromPosZ 0%Z)) carry;
(* mov    %r10,%rcx *)
bvAssign rcx (bvVar r10);
(* shl    $0x20,%r10 *)
(* bvShl r10 (bvVar r10) (fromNat 32); *)
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* mul    %r13 *)
bvMulf rdx rax (bvVar r13) (bvVar rax);
(* shr    $0x20,%rcx *)
(* bvSplit rcx tmp (bvVar rcx) (fromNat 32); *)
(* NOTE: merge 'shl $0x20,%r10' with 'shr $0x20,%rcx' *)
bvSplit rcx r10 (bvVar r10) (fromNat 32);
bvShl r10 (bvVar r10) (fromNat 32);
(* add    %r10,%r11 *)
bvAddC carry r11 (bvVar r10) (bvVar r11);
(* adc    %rcx,%r8 *)
bvAdcC carry r8 (bvVar rcx) (bvVar r8) carry;
(* adc    %rax,%r9 *)
bvAdcC carry r9 (bvVar rax) (bvVar r9) carry;
(* mov    %r11,%rax *)
bvAssign rax (bvVar r11);
(* adc    $0x0,%rdx *)
bvAdcC carry rdx (bvVar rdx) (bvConst (fromPosZ 0%Z)) carry;
(* mov    %r11,%rcx *)
bvAssign rcx (bvVar r11);
(* shl    $0x20,%r11 *)
(* bvShl r11 (bvVar r11) (fromNat 32); *)
(* mov    %rdx,%r10 *)
bvAssign r10 (bvVar rdx);
(* mul    %r13 *)
bvMulf rdx rax (bvVar r13) (bvVar rax);
(* shr    $0x20,%rcx *)
(* bvSplit rcx tmp (bvVar rcx) (fromNat 32); *)
(* NOTE: merge 'shl $0x20,%r11' with 'shr $0x20,%rcx' *)
bvSplit rcx r11 (bvVar r11) (fromNat 32);
bvShl r11 (bvVar r11) (fromNat 32);
(* add    %r11,%r8 *)
bvAddC carry r8 (bvVar r11) (bvVar r8);
(* adc    %rcx,%r9 *)
bvAdcC carry r9 (bvVar rcx) (bvVar r9) carry;
(* adc    %rax,%r10 *)
bvAdcC carry r10 (bvVar rax) (bvVar r10) carry;
(* adc    $0x0,%rdx *)
bvAdcC carry rdx (bvVar rdx) (bvConst (fromPosZ 0%Z)) carry;
(* mov    %r10,%rax *)
bvAssign rax (bvVar r10);
(* mov    %rdx,%r11 *)
bvAssign r11 (bvVar rdx);

bvAssign t0 (bvVar r8);
bvAssign t1 (bvVar r9);
bvAssign t2 (bvVar r10);
bvAssign t3 (bvVar r11)
].
