# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _RocqProject

# Directories for documentation generation
SRC_DIR = src
LATEX_DIR = latex

# Tools
ROQC = rocq
PDFLATEX = pdflatex

# Main LaTeX document (without extension)
DOC = paa-2026-2-projeto-enunciado

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _RocqProject
	$(ROQC) makefile -f _RocqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

$(KNOWNFILES): ;

####################################################################
##                      Your targets here                         ##
####################################################################

# Find all .v files in src directory
V_FILES := $(wildcard $(SRC_DIR)/*.v)
# Get just the filenames without path or extension
V_NAMES := $(notdir $(V_FILES:.v=))
# Generate corresponding .v.tex filenames in latex directory
TEX_FILES := $(addprefix $(LATEX_DIR)/, $(addsuffix .v.tex, $(V_NAMES)))

# Create latex directory if it doesn't exist
$(LATEX_DIR):
	mkdir -p $(LATEX_DIR)

# Prevent the catch-all "%: invoke-coqmakefile" rule below from being used
# to (re)build the .v source files: without this, make treats them as
# reachable via that pattern too and forwards the top-level goal to
# CoqMakefile, which breaks targets like `doc` that CoqMakefile doesn't know.
$(SRC_DIR)/%.v: ;
$(LATEX_DIR)/%.tex: ;
$(LATEX_DIR)/%.sty: ;
tools/%.py: ;

# Logical path of src/ (must match _RocqProject) and the repository URL that
# identifiers in the PDF link to. REV pins the links to a commit so that line
# numbers stay valid; override it with e.g. `make doc REV=main`.
LOGICAL = BST
REPO_URL = https://github.com/flaviodemoura/bst-rocq
REV ?= $(shell git rev-parse HEAD)

# The .glob files (needed for hyperlinks) are produced by compiling the .v files
$(SRC_DIR)/%.glob: $(SRC_DIR)/%.v CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(SRC_DIR)/$*.vo

# Generate all .v.tex files in a single rocq doc run, so that identifiers
# defined in one file are linked where they are used in another.
# --body-only ensures only the body content is included
$(TEX_FILES) &: $(V_FILES) $(V_FILES:.v=.glob) tools/tidy_coqdoc.py | $(LATEX_DIR)
	cd $(LATEX_DIR) && $(ROQC) doc --latex --body-only -l -s \
	  -R ../$(SRC_DIR) $(LOGICAL) $(addprefix ../,$(V_FILES))
	@# rocq doc names the files after their logical path; rename them to <name>.v.tex
	cd $(LATEX_DIR) && for f in $(V_NAMES); do mv $(LOGICAL).$$f.tex $$f.v.tex; done
	@# drop empty code blocks and annotate each block with its first definition
	python3 tools/tidy_coqdoc.py $(TEX_FILES)

# Line number of every definition, used to link blocks to the repository
$(LATEX_DIR)/coqsrclinks.tex: tools/glob2links.py $(V_FILES:.v=.glob) | $(LATEX_DIR)
	python3 tools/glob2links.py $(SRC_DIR) $(LOGICAL) $(V_NAMES) > $@

$(LATEX_DIR)/coqsrcbase.tex: FORCE | $(LATEX_DIR)
	@printf '%s\n' '\newcommand{\coqsrcbase}{$(REPO_URL)/blob/$(REV)/$(SRC_DIR)/}' > $@.tmp
	@cmp -s $@.tmp $@ && rm $@.tmp || mv $@.tmp $@
	@git diff --quiet HEAD -- $(SRC_DIR) || echo "Warning: $(SRC_DIR) has uncommitted changes; links point to $(REV)"

.PHONY: FORCE
FORCE:

# Target to generate all .v.tex files
.PHONY: tex-fragments
tex-fragments: $(TEX_FILES)
	@echo "All documentation files generated in $(LATEX_DIR)/"
	@ls -la $(LATEX_DIR)/*.v.tex 2>/dev/null || echo "No .v.tex files found"

# Main documentation target
.PHONY: doc
doc: $(LATEX_DIR)/$(DOC).pdf

$(LATEX_DIR)/$(DOC).pdf: $(LATEX_DIR)/$(DOC).tex $(TEX_FILES) $(LATEX_DIR)/coqdoc.sty \
                           $(LATEX_DIR)/coqsrclinks.tex $(LATEX_DIR)/coqsrcbase.tex | $(LATEX_DIR)
	cd $(LATEX_DIR) && $(PDFLATEX) -interaction=nonstopmode -halt-on-error $(DOC)
	cd $(LATEX_DIR) && $(PDFLATEX) -interaction=nonstopmode -halt-on-error $(DOC)

# Clean documentation files
.PHONY: clean-doc
clean-doc:
	rm -f $(LATEX_DIR)/*.aux $(LATEX_DIR)/*.log $(LATEX_DIR)/*.out $(LATEX_DIR)/*.toc
	rm -f $(LATEX_DIR)/*.v.tex $(LATEX_DIR)/$(DOC).pdf
	rm -f $(LATEX_DIR)/coqsrclinks.tex $(LATEX_DIR)/coqsrcbase.tex

# Add doc cleaning to the main clean target
.PHONY: clean
clean: clean-doc
	-$(MAKE) --no-print-directory -f CoqMakefile clean
	rm -f CoqMakefile* .CoqMakefile.d
	rm -f solucao/*.vo solucao/*.vok solucao/*.vos solucao/*.glob solucao/.*.aux

# Show debug information
.PHONY: debug-doc
debug-doc:
	@echo "SRC_DIR = $(SRC_DIR)"
	@echo "LATEX_DIR = $(LATEX_DIR)"
	@echo "V_FILES = $(V_FILES)"
	@echo "V_NAMES = $(V_NAMES)"
	@echo "TEX_FILES = $(TEX_FILES)"
	@echo "ROQC = $(ROQC)"
	@echo "PDFLATEX = $(PDFLATEX)"

# Check that the reference solution compiles (it is not part of _RocqProject)
.PHONY: solucao
solucao:
	cd solucao && $(ROQC) compile bst.v

# Regenerate src/bst.v (statement without proofs) from the reference solution
.PHONY: enunciado
enunciado:
	python3 solucao/gera_enunciado.py solucao/bst.v $(SRC_DIR)/bst.v

# Open pdf with evince
.PHONY: pdf
pdf:
	zathura $(LATEX_DIR)/$(DOC).pdf&

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
