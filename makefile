
SRC = src

AGDA_OPTS = -i ./src/ -i ./lib/agda-stdlib/src/
AGDA = agda $(AGDA_OPTS)
AGDA_DOC = agda $(AGDA_OPTS) --html --html-dir=./doc/html/

# main
CALC_MAIN = $(SRC)/Implicits/Calculus.agda
MAIN = $(SRC)/Implicits/Everything.agda

calculus: $(CALC_MAIN)i

all: $(MAIN)i

# generate browsable documentation for our main proofs
.PHONY: doc
doc:
	$(AGDA_DOC) $(MAIN)

# rules for typechecking agda sourcecode
.SUFFIXES: .agdai .agda
%.agdai: %.agda
	$(AGDA) $<

# only clean src
clean:
	find $(SRC) -iname "*.agdai" -exec rm {} \;

# clean src and lib
clean-all:
	find . -iname "*.agdai" -exec rm {} \;

push-doc:
	scp -r doc legolas:/srv/http/arjen.inkworks.nl/thesis/
