# AGDA checked proof of "Calculus of Implicits" soundness

Based on "The implicit calculus: a new foundation for generic programming."
([Oliveira, Bruno CdS, et al.](http://ropas.snu.ac.kr/~wtchoi/paper/pldi12.pdf)).
The proof consists of the composition of a denotational semantics of the calculus into SystemF and
the small step semantics of SystemF.

# Usage

The code has been compiled against agda 2.4.2.4 (783b5ccf1d0032)
with the associated version of the standard library.
The standard library is included as a submodule;

    git submodule init
    git submodule update

### Typechecking

Typechecking the proofs is as simple as:

    make

### Browsable docs

This generates the browsable, syntax highlighted source in `doc/html/`:

    make doc
