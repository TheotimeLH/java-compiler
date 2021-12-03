
all: main.exe

tests: main.exe
	for f in tests/syntax/bad/*.java; do dune exec ./main.exe $$f; done

main.exe:
	dune build main.exe

clean:
	dune clean

.PHONY: all clean main.exe
