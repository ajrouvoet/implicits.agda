
SRC = src

AGDA_OPTS = -i ./src/ -i ./lib/agda-stdlib/src/
AGDA = agda $(AGDA_OPTS)
AGDA_DOC = agda $(AGDA_OPTS) --html --html-dir=./doc/html/

EVERYTHING = $(SRC)/Everything.agdai

all: $(EVERYTHING)

# generate browsable documentation for our main proofs
.PHONY: doc
doc:
	$(AGDA_DOC) $(SRC)/Implicits/Everything.agda

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
