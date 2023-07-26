DEP_Files = typeclassestut.tex \
	morebiblio.bib \
	biblio.bib

.PHONY:all
all: typeclassestut.pdf

typeclassestut.pdf: ${DEP_Files}
	lualatex typeclassestut.tex
	bibtex typeclassestut
	lualatex typeclassestut.tex
	lualatex typeclassestut.tex
	lualatex typeclassestut.tex


.PHONY:clean
clean:
	@${RM} typeclassestut.pdf *.aux *.ind   *.bbl *.blg *.log  *.out 
