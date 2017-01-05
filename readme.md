# AGDA checked proof of "Calculus of Implicits" related theorems

Developed for my thesis ["Programs for Free: Towards a formalization of Implicit Resolution in Scala"](http://repository.tudelft.nl/islandora/object/uuid:aef3c8fc-677a-4ecd-8850-d9d76937ba6f?collection=education]).
Building on top of earlier work by ([Oliveira, Bruno CdS, et al.](http://ropas.snu.ac.kr/~wtchoi/paper/pldi12.pdf)).

# Usage

The code has been compiled against *agda 2.4.2.3* and beyond.
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
