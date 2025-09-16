all: compile extract

compile: systemf_erased.vo

systemf_erased.vo: systemf_erased.v
	rocq compile systemf_erased.v

extract: systemf_erased_eval.ml

systemf_erased_eval.ml: systemf_erased_extract.v systemf_erased.vo
	rocq compile systemf_erased_extract.v -output-directory .

systemf_erased_eval_test: systemf_erased_eval.ml systemf_erased_eval_test.ml
	rm -f systemf_erased_eval.mli
	ocamlc -o systemf_erased_eval_test systemf_erased_eval.ml systemf_erased_eval_test.ml

run: systemf_erased_eval_test
	./systemf_erased_eval_test

clean:
	rm -f systemf_erased_eval.ml systemf_erased_eval_test *.cmi *.cmo *.glob *.vo *.vok *.vos *.mli

test: all run

.PHONY: all compile extract compile run clean test
