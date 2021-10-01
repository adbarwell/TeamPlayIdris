all : run

run : compile
	./proofgen

compile : Main.idr
	idris Main.idr -o proofgen

clean :
	rm -f **/*.ibc
	rm -f ./proofgen