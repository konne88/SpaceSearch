BUILD=.build
SRC_COQ=src/coq
SRC_RKT=src/racket
EXA_COQ=examples/coq
EXA_RKT=examples/racket

.PHONY: build clean examples

build: 
	cd $(SRC_COQ); find . -name '*.v' -exec coq_makefile -R . "SpaceSearch" -o Makefile {} +
	make -j4 -C$(SRC_COQ)

examples: build
	cd $(EXA_COQ); find . -name '*.v' -exec coq_makefile -R ../../${SRC_COQ} "SpaceSearch" -o Makefile {} +
	make -j4 -C$(EXA_COQ)
	# queens
	cp $(EXA_RKT)/header.rkt queens.rkt
	tail -n +4 $(EXA_COQ)/queens.scm >> queens.rkt
	cat $(EXA_RKT)/queens.rkt >> queens.rkt
	raco make queens.rkt
	chmod +x queens.rkt
	# integers
	cp $(EXA_RKT)/header.rkt integer-tests.rkt
	tail -n +4 $(EXA_COQ)/integer-tests.scm >> integer-tests.rkt
	cat $(EXA_RKT)/integer-tests.rkt >> integer-tests.rkt
	raco make integer-tests.rkt
	chmod +x integer-tests.rkt

clean:
	find . \( \
          -name "*.glob" -o \
	  -name "*.v.d" -o \
          -name "*.scm" -o \
          -name "*.vo" -o \
          -name ".*.aux" -o \
          -name "#*#" -o \
          -name ".#*" -o \
          -name "*~" \
        \) -exec rm {} +
	find . -name .coq-native -o -name compiled -exec rm -r {} +
	rm -f $(EXA_COQ)/Makefile $(SRC_COQ)/Makefile queens.rkt integer-tests.rkt

