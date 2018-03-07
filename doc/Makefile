all:
	agda -i . --latex strinagda.lagda
	cd latex && latexmk -xelatex -pdf -e '$$pdflatex=q/xelatex %O %S/' strinagda.tex
	ln -sf latex/strinagda.pdf .

clean:
	rm -rf latex/ strinagda.pdf
