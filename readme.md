# AGDA checked proof of "Calculus of Implicits" related theorems

Developed for my thesis ["Programs for Free: Towards a formalization of Implicit Resolution in Scala"](http://repository.tudelft.nl/islandora/object/uuid:aef3c8fc-677a-4ecd-8850-d9d76937ba6f?collection=education]).
Building on top of earlier work by ([Oliveira, Bruno CdS, et al.](http://ropas.snu.ac.kr/~wtchoi/paper/pldi12.pdf)).

# Usage

The code has been compiled against *agda 2.4.2.3* and beyond and should be compatible with the latest version
of the agda [stdlib](https://github.com/agda/agda-stdlib).

### Typechecking

Install the standard library somewhere by cloning it and add the following snippet to your agda libraries file
`~/.agda/libraries`:

    <AGDA_STDLIB_PATH>/standard-library.agda-lib

Typechecking the proofs is as simple as:

    make

### Browsable docs

This generates the browsable, syntax highlighted source in `doc/html/`:

    make doc
