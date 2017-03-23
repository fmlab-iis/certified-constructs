A variable is represented by an integer <var id>, its identifier.

An expression <exp> is of the form:
* QVar <var id>            - a variable
* QConst <an integer>      - a constant
* QUnop QNeg <exp>         - negation of <exp>
* QBinop QAdd <exp> <exp>  - <exp> + <exp>
* QBinop QSub <exp> <exp>  - <exp> - <exp>
* QBinop QMul <exp> <exp>  - <exp> * <exp>
* QBinop QPow <exp> <positive> - <exp> ** <positive>

Two kinds of instructions <instr> are available:
* QAssign <var id> <exp>  - assign <exp> to variable <var id>
* QSplit <var id> <var id> <exp> <a positive integer>
                          - split <exp> and assign to two variables

For instance, x0 := x2 * 5 is represented by

QAssign 0 (QBinop QMul (QVar 2) (QConst 5%Z)

Similarly, we can split a big constant into two variables by

QSplit 1 2 (QConst 12345678901234567890%Z) (31%positive)

We have x1 * 2^(31) + x2 := 12345678901234567890 .

A program is a sequence of instructions:
* [:: <instr>; <instr>; ...; <instr> ]

For instance, swapping x0 and x1 by a temporary variable x2 is represented by

[:: QAssign 2 1;
    QAssign 1 0;
    QAssign 0 2 ]
