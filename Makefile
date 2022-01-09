
all: pjava

tests: syntax typing exec_good

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

exec_good:
	for f in tests/exec/*.java; do _build/default/main.exe $$f; done

pjava:
	dune build main.exe
	rm -f $@
	cp _build/default/main.exe $@

clean:
	dune clean
	rm -f pjava

.PHONY: all clean pjava
