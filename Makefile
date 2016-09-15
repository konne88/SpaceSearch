BUILD=.build
SRC_COQ=src/coq
SRC_RKT=src/racket
EXA_COQ=example/coq
EXA_RKT=example/racket

.PHONY: build clean example

build: 
	cd $(SRC_COQ); find . -name '*.v' -exec coq_makefile -R . "SpaceSearch" -o Makefile {} +
	make -j4 -C$(SRC_COQ)

example: build
	cd $(EXA_COQ); find . -name '*.v' -exec coq_makefile -R ../../${SRC_COQ} "SpaceSearch" -o Makefile {} +   # -R $(COQ_SRC) "SpaceSearch" 
	make -j4 -C$(EXA_COQ)
	cp $(EXA_RKT)/header.rkt queens.rkt
	tail -n +4 $(EXA_COQ)/queens.scm >> queens.rkt
	cat $(EXA_RKT)/footer.rkt >> queens.rkt
	raco make queens.rkt
	chmod +x queens.rkt

clean:
	cd $(SRC_COQ); rm -rf Makefile *.glob *.v.d *.scm *.vo .coq-native .*.aux "#"*"#" ".#"*
	cd $(EXA_COQ); rm -rf Makefile *.glob *.v.d *.scm *.vo .coq-native .*.aux "#"*"#" ".#"*
	cd $(SRC_RKT); rm -rf compiled
	rm -rf queens.rkt compiled

