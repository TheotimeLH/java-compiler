
all: pjava

tests: pjava syntax typing

syntax: syntax_bad syntax_good

typing: typing_bad typing_good

syntax_bad:
	-for f in tests/syntax/bad/*.java ; do _build/default/main.exe --parse-only $$f; done

syntax_good:
	for f in tests/syntax/good/*.java; do _build/default/main.exe --parse-only $$f; done

typing_bad:
	-for f in tests/typing/bad/*.java ; do _build/default/main.exe --type-only $$f; done

typing_good:
	for f in tests/typing/good/*.java; do _build/default/main.exe --type-only $$f; done

pjava:
	dune build main.exe
	cp _build/default/main.exe pjava

clean:
	dune clean
	rm -f pjava

.PHONY: all clean pjava
