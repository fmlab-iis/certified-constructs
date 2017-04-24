TARGET = main

INPUT_SOURCES = $(shell cat $(TARGET).tex | grep \\\\input | grep -v ^% | cut -d{ -f2 | cut -d} -f1) 
INCLUDE_SOURCES = $(shell cat $(TARGET).tex | grep \\\\include | grep -v ^% | cut -d{ -f2 | cut -d} -f1)

SOURCES = \
	$(TARGET).tex \
	$(INPUT_SOURCES:%=%.tex) \
	$(INCLUDE_SOURCES:%=%.tex) \

all: $(TARGET).pdf

$(TARGET).pdf: $(TARGET).tex $(SOURCES) refs.bib
	pdflatex $(TARGET).tex
	bibtex $(TARGET) || echo Suppressed BIBTEX error
	pdflatex $(TARGET).tex
	bibtex $(TARGET) || echo Suppressed BIBTEX error
	pdflatex $(TARGET).tex

clean:
	-rm -f $(TARGET).brf $(TARGET).ind $(TARGET).toc $(TARGET).bbl $(TARGET).blg $(TARGET).ilg $(TARGET).idx 
	-rm -f $(TARGET).log $(TARGET).lot $(TARGET).lfm $(TARGET).out $(TARGET).lof
	-rm -f $(SOURCES:%.tex=%.aux)
	-rm -f $(TARGET).pdf
