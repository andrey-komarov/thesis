
thesis.pdf: $(futuretex) thesis.tex chapters/*.tex thesis.bib
	pdflatex thesis
	biber thesis
	pdflatex thesis
	pdflatex thesis

lagda=$(wildcard ../src/*.lagda)
futuretex=$(patsubst ../src/%.lagda,./chapters/%.tex,$(lagda))

alltex : $(futuretex)

$(futuretex) : chapters/%.tex : ../src/%.lagda
	cd ../src; agda --latex --latex-dir ../report/chapters $<

clean:
	rm *.aux *.bbl *.bcf *.blg *.log *.pdf *.xml *.toc *.ptb
