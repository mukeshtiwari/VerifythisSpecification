LATEX ?= pdflatex -interaction=nonstopmode


main.pdf: main.tex references.bib
	@echo "latex first pass..."
	@((${LATEX} $< > .log); \
	if [ $$? -ne 0 ]; then \
            echo "latex failed. Output follows: "; cat .log; \
            exit 1; \
        fi)
	@echo "bibtex...";
	@bibtex ${<:%.tex=%} > .log
	@echo "latex second pass...";
	@${LATEX} $< > .log
	@while ( grep -q 'may have changed' $*.log) \
	do echo "latex nth pass..."; ${LATEX} $< > .log; done
	@grep -i 'undefined' .log > .undef; \
	if [ ! -z "$$(cat .undef)" ]; then \
            echo "Undefined references: "; cat .undef; \
        fi


clean:
	rm -f *.out *.aux *.bbl *.blg *.log main.pdf
