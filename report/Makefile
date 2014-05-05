
report.pdf: thesis.tex chapters/*.tex thesis.bib
	pdflatex thesis
	biber thesis
	pdflatex thesis
	pdflatex thesis

clean:
	rm *.aux *.bbl *.bcf *.blg *.log *.pdf *.xml *.toc
