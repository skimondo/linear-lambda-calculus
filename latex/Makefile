# Main LaTeX file (without extension)
MAIN = main

# Compiler and bibliography tool
LATEX = pdflatex
BIBER = biber

# Automatically detect all .tex files for dependency tracking
TEX_FILES = $(wildcard *.tex frontmatter/*.tex mainmatter/*.tex)

# Auxiliary files to clean
CLEAN_FILES = $(MAIN).aux $(MAIN).log $(MAIN).out $(MAIN).toc \
              $(MAIN).bbl $(MAIN).blg $(MAIN).bcf $(MAIN).run.xml \
              $(MAIN).synctex.gz $(MAIN).lot $(MAIN).lof \
              $(MAIN).idx $(MAIN).ilg $(MAIN).ind \
              mainmatter/*.aux

# Default target: build the PDF
all: $(MAIN).pdf

# Rule to build the PDF
$(MAIN).pdf: $(TEX_FILES) thesisRefs.bib
	$(LATEX) $(MAIN).tex
	$(BIBER) $(MAIN)
	$(LATEX) $(MAIN).tex
	$(LATEX) $(MAIN).tex

# Clean intermediate files
clean:
	rm -f $(CLEAN_FILES)

# Clean everything, including the final PDF
cleanall: clean
	rm -f $(MAIN).pdf

# Phony targets to avoid conflicts with files of the same name
.PHONY: all clean cleanall
