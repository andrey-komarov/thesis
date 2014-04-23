all:
	rm example.pdf ; make example.pdf

%.pdf: %.tex 
	pdflatex $< $@ && \
	pdflatex $< $@

clean:
	rm *.aux *.dvi *.log *~ *.ps *.pdf

cleantrash:
	rm *.aux *.dvi *.log *~ *.ps
