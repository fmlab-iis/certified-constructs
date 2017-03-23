# Important Notes

This is an evaluation version without gbarith developed by Loïc Pottier [1].
This version is sufficient to verify examples in the fe25519 folder but not
some other examples that requires gbarith.

1. Pottier, L.: Connecting Groebner bases programs with Coq to do proofs in
   algebra, geometry and arithmetics. In: Sutcliffe, G., Rudnicki, P., 
   Schmidt, R., Konev, B., Schulz, S. (eds.) Knowledge Exchange: Automated 
   Provers and Proof Assistants. p. 418 (2008)

# Compilation Instructions

The following instructions are based on 64bit Ubuntu 16.04.1 desktop.
If you use a virtual machine, please make sure that your virtual machine has
more than 3GB memory.
Otherwise, coq may fail to compile.

1. Install [opam](https://opam.ocaml.org).
   For Ubuntu 14.10, follow the [binary installation steps](https://opam.ocaml.org/doc/Install.html#Binarydistribution)
   to install opam instead of using the apt-get command below.
```
   $ sudo apt-get install opam
```
2. Configure opam.
```
   $ opam init
     (press y to update ~/.profile)
   $ eval `opam config env`
```
3. Add additional opam repositories.
```
   $ opam repo add coq-released https://coq.inria.fr/opam/released
   $ opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```
4. Switch OCaml version.
```
   $ opam switch 4.02.3
   $ eval `opam config env`
```
5. Install Coq.
```
   $ opam pin add coq 8.5.2
     (press y to install coq)
```
6. Install mathcomp and other Coq packages.
```
   $ opam install \
       coq-mathcomp-algebra.1.6 \
       coq-mathcomp-character.1.6 \
       coq-mathcomp-field.1.6 \
       coq-mathcomp-fingroup.1.6 \
       coq-mathcomp-solvable.1.6 \
       coq-mathcomp-ssreflect.1.6 \
       coq-bits
```
7. Install [Singular 4.x.x](https://www.singular.uni-kl.de).
   For some older Linux distributions with Singular 3.x, follow
   the compilation instructions from sources on [this GitHub page](https://github.com/Singular/Sources/wiki/Step-by-Step-Installation-Instructions-for-Singular).
```
   $ sudo apt-get install singular
```
8. Compile submodules.
```
   $ make -C lib/gbarith
   $ make -C lib/polyop
```
9. Compile Coq code.
```
   $ make
```

# Verify Examples

Use the following two scripts to verify examples in the fe25519 folder.
```
   $ ./verify_ops
   $ ./verify_laddersteps
```
For an example fe25519/X.v, a log file X.log will be created.
