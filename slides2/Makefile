all:
	rm slides.pdf ; make slides.pdf

%.pdf: %.tex 
	pdflatex $< $@ && \
	pdflatex $< $@

clean:
	rm *.aux *.dvi *.log *~ *.ps *.pdf *.nav *.out *.snm *.toc *.vrb

cleantrash:
	rm *.aux *.dvi *.log *~ *.ps
