
all: main.exe

syntax: main.exe
	for f in tests/syntax/good/*.java; do dune exec ./main.exe $$f; done

main.exe:
	dune build main.exe

clean:
	dune clean

.PHONY: all clean syntax main.exe
