-include Makefile.config

THEORY=\
	Monads.v Error.v MapList.v Common.v Array.v Struct.v Types.v Syntax.v Typing.v \
	Barocq.v BarocqBNF.v BarocqBNFgen.v BarocqBNFgen2.v ImpBNF.v ImpBNFgen.v \
	ImpABNF.v ImpABNFgen.v Imp1.v Imp1gen.v Imp2.v Imp2gen.v Clightgen.v Compiler.v \
	BarocqShallow.v BarocqShallowgen.v

VSOURCE=$(addprefix theories/,$(THEORY))

VBUILD=$(addprefix $(BUILD_DIR)/theories/,$(THEORY))

EXTRDEP=$(BUILD_DIR)/theories/extractionMachdep.v

COQINCLUDES=-R $(BUILD_DIR)/theories BarocqComp
COQC=coqc $(COQINCLUDES)
COQEXEC=coqtop $(COQINCLUDES) -batch -load-vernac-source
COQDEP=coqdep $(COQINCLUDES)
OCAMLFORMAT=ocamlformat -i

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) barocq

$(BUILD_DIR)/theories:
	@mkdir -p _build/theories

builddir: $(BUILD_DIR)/theories

# Retrieve file from CompCert build folder

compcert.ini :
	@echo RETRIEVE compcert.ini
	@cp $(COMPCERT_DIR)/compcert.ini compcert.ini

$(EXTRDEP): | builddir
	@echo RETRIEVE extractionMachdep.v
	@cp $(COMPCERT_DIR)/$(ARCH)/extractionMachdep.v $(BUILD_DIR)/theories
	@sed -i 's\Require\From compcert Require\g' $(EXTRDEP)

extrdep: $(EXTRDEP)

# Copy Coq source files to the build directory

$(BUILD_DIR)/theories/%.v: theories/%.v | builddir
	@echo COPY $< to $@
	@cp $< $(BUILD_DIR)/theories

vbuild: $(VBUILD) extrdep

$(BUILD_DIR)/extraction.v: extraction.v | builddir
	@echo COPY extraction.v to $@
	@cp extraction.v $(BUILD_DIR)

# Generate dependencies between Coq files

depend1: $(VBUILD) $(EXTRDEP) $(BUILD_DIR)/extraction.v
	@echo Analyzing Coq dependencies
	@$(COQDEP) $^ > .depend

depend: depend1

# Compile Coq source files

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) $*.v

theories: $(VBUILD:.v=.vo)

vofiles: $(VBUILD:.v=.vo) $(EXTRDEP.v=.vo)

# Extraction

$(BUILD_DIR)/extraction/STAMP: $(VBUILD:.v=.vo) $(EXTRDEP.v=.vo) $(BUILD_DIR)/extraction.v
	rm -f $(BUILD_DIR)/extraction/*.ml $(BUILD_DIR)/extraction/*.mli
	@echo COQTOP $(BUILD_DIR)/extraction.v
	@$(COQEXEC) $(BUILD_DIR)/extraction.v
	touch $(BUILD_DIR)/extraction/STAMP

extraction: $(BUILD_DIR)/extraction/STAMP

.depend.extr: $(BUILD_DIR)/extraction/STAMP
	$(MAKE) -f Makefile.extr depend

barocq: .depend.extr compcert.ini FORCE
	$(MAKE) -f Makefile.extr barocq

install:
	@echo INSTALL barocq to $(INSTALL_DIR)/barocq
	@install barocq $(INSTALL_DIR)/barocq

uninstall:
	rm -f $(INSTALL_DIR)/barocq

# Formatting

MLSOURCE=$(foreach dir,$(BDIRS_SOURCE),$(wildcard $(dir)/*.ml $(dir)/*.mli))

format: $(MLSOURCE)
	@echo OCAMLFORMAT $^
	@$(OCAMLFORMAT) $^

clean_theories:
	rm -f $(VBUILD)
	rm -f $(VBUILD:.v=.vo)
	rm -f $(VBUILD:.v=.vok)
	rm -f $(VBUILD:.v=.vos)
	rm -f $(VBUILD:.v=.glob)
	rm -f $(addprefix $(BUILD_DIR)/theories/.,$(THEORY:.v=.aux))

clean:
	rm -rf $(BUILD_DIR)
	rm -f compcert.ini
	rm -f .depend.extr
	rm -f .depend
	rm -f barocq

FORCE:

.PHONY:\
	builddir extrdep vbuild depend depend1\
    vofiles clean extraction format install FORCE\
	bonsoir theories

-include .depend