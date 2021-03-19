FILE=stringlytyped

all:
	agda -i . --latex ${FILE}.lagda
	cp unicode.tex commands.tex main.bib latex/
	cd latex && latexmk -pdf -bibtex ${FILE}.tex
	ln -sf latex/${FILE}.pdf .

clean:
	rm -rf latex/ ${FILE}.pdf
