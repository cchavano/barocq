-include Makefile.config

COMMON=\
	Monads.v Error.v Utils.v Barray.v Brecord.v Maps2.v\
	Types.v Syntax.v Typing.v Intop.v Ident.v Target.v

FRONTEND=\
	Barocq.v BarocqTransf.v BarocqBNF.v BarocqBNFgen.v BarocqShallow.v BarocqShallowgen.v

BACKEND=\
	ImpBNF.v ImpBNFgen.v ImpABNF.v ImpABNFgen.v\
	Imp1.v Imp1gen.v Imp2.v Imp2gen.v ClightCegen.v

BCOMP=Compiler.v

VDIRS=common frontend backend bcomp

VDIRS_BUILD=$(addprefix $(BUILD_DIR)/, $(VDIRS))

VSOURCE=\
	$(addprefix common/,$(COMMON)) $(addprefix frontend/,$(FRONTEND))\
	$(addprefix backend/,$(BACKEND)) $(addprefix bcomp/,$(BCOMP))

VBUILD=$(addprefix $(BUILD_DIR)/, $(VSOURCE))

EXTRDEP=$(BUILD_DIR)/extractionMachdep.v

COQINCLUDES=$(foreach d, $(VDIRS), -R $(BUILD_DIR)/$(d) BarocqComp.$(d))
COQC=coqc $(COQINCLUDES)
COQEXEC=coqtop $(COQINCLUDES) -batch -load-vernac-source
COQDEP=coqdep $(COQINCLUDES)
OCAMLFORMAT=ocamlformat -i

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) barocq

$(VDIRS_BUILD):
	@for dir in $(VDIRS) ; do \
		mkdir -p $(BUILD_DIR)/$$dir ; \
	done

builddir: $(VDIRS_BUILD)

# Retrieve necessary files from the CompCert build folder

compcert.ini:
	@echo RETRIEVE compcert.ini
	@cp $(COMPCERT_DIR)/compcert.ini compcert.ini

$(EXTRDEP): | builddir
	@echo RETRIEVE extractionMachdep.v
	@cp $(COMPCERT_DIR)/$(ARCH)/extractionMachdep.v $(BUILD_DIR)
	@sed -i 's\Require\From compcert Require\g' $(EXTRDEP)

extrdep: $(EXTRDEP)

# Copy Coq source files to the build directory

$(BUILD_DIR)/%.v: %.v | builddir
	@echo COPY $< to $@
	@cp $< $@

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

uninstall-dev:
	rm -rf $(INSTALL_DEV_DIR)

install-dev:
	@echo INSTALL Rocq files in $(INSTALL_DEV_DIR)
	@for d in $(VDIRS); do \
		set -e; \
		install -d $(INSTALL_DEV_DIR)/$$d; \
		install -m 0644 $(BUILD_DIR)/$$d/*.v $(BUILD_DIR)/$$d/*.vo $(BUILD_DIR)/$$d/*.glob $(INSTALL_DEV_DIR)/$$d/; \
	done

# Formatting

MLSOURCE=$(foreach dir,$(MLDIRS),$(wildcard $(dir)/*.ml $(dir)/*.mli))

format: $(MLSOURCE)
	@echo OCAMLFORMAT $^
	@$(OCAMLFORMAT) $^

clean_theories:
	rm -f $(VBUILD)
	rm -f $(VBUILD:.v=.vo)
	rm -f $(VBUILD:.v=.vok)
	rm -f $(VBUILD:.v=.vos)
	rm -f $(VBUILD:.v=.glob)
	rm -f $(BUILD_DIR)/backend/.*.aux
	rm -f $(BUILD_DIR)/common/.*.aux
	rm -f $(BUILD_DIR)/frontend/.*.aux
	rm -f $(BUILD_DIR)/bcomp/.*.aux

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
	theories install-dev uninstall uninstall-dev

-include .depend