
SRC = src

AGDA_OPTS = -i ./src/ -i ./lib/agda-stdlib/src/
AGDA = agda $(AGDA_OPTS)
AGDA_DOC = agda $(AGDA_OPTS) --html --html-dir=./doc/html/

# main proofs
systemf_main = $(SRC)/Implicits/SystemF/SmallStep
calculus_main = $(SRC)/Implicits/Calculus/Denotational

all: systemf calculus
systemf: $(systemf_main).agdai
calculus: $(calculus_main).agdai

# generate browsable documentation for our main proofs
doc:
	$(AGDA_DOC) $(systemf_main).agda
	$(AGDA_DOC) $(calculus_main).agda

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
