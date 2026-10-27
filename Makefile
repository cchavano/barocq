-include Makefile.config

NOLIB=false

LIB=\
	Unsigned63.v ZifyUint63.v StateMonads.v BSet.v Res.v Utils0.v Utils.v Barray.v Brecord.v Benum.v Maps2.v Option.v\
	While.v WhileLib.v ZlistPlus.v Intop.v Ident.v DList.v ExtOrdered.v Pp.v MergeSort.v ShallowLib.v

COMMON=\
	Denot.v Graph.v Printer.v Syntax.v Types.v Typing.v

FRONTEND=\
	Barocq.v Renaming.v BarocqBNF.v BarocqBNFgen.v\
	ImpBNF.v ImpBNFgen.v Imp1gen.v Imp1Pure.v

BACKEND=\
	Imp1.v Imp1Imp.v Imp1Instr.v Imp1ElimAlias.v InvAnalysis.v\
	Imp2Copy.v Imp2.v Imp2gen.v GlobRewrite.v Csyntaxgen.v

ROCQGEN=\
	ShallowAST.v ShallowASTgen.v BarocqBNFUndo.v\
	ExtEqual.v  BarocqBNFVC.v CorresBD_Tactics.v # BarocqVC.v is out-dated

BCOMP=Compiler.v

VDIRS=common frontend backend rocqgen bcomp

VSOURCE=\
	$(addprefix common/,$(COMMON)) $(addprefix frontend/,$(FRONTEND))\
	$(addprefix backend/,$(BACKEND)) $(addprefix rocqgen/, $(ROCQGEN))\
	$(addprefix bcomp/,$(BCOMP))

ifeq ($(NOLIB), false)
    VDIRS+=lib
	VSOURCE+=$(addprefix lib/,$(LIB))
endif

VDIRS_BUILD=$(addprefix $(BUILD_DIR)/, $(VDIRS))

VBUILD=$(addprefix $(BUILD_DIR)/, $(VSOURCE))

EXTRDEP=$(BUILD_DIR)/bcomp/extractionMachdep.v 

COQINCLUDES=$(foreach d, $(VDIRS), -R $(BUILD_DIR)/$(d) BarocqComp.$(d))
COQOPT= #-set "Universe Polymorphism"
COQC=coqc $(COQOPT) $(COQINCLUDES)
COQEXEC=coqtop $(COQOPT) $(COQINCLUDES) -batch -load-vernac-source
COQDEP=coqdep $(COQINCLUDES)
OCAMLFORMAT=ocamlformat -i

all:
	@if [ "$(NOLIB)" = false ]; then \
		rm -f .nolib; \
	else \
		echo Building without the lib directory; \
	fi
	@test -f .depend || $(MAKE) depend
	$(MAKE) barocq

nolib:
	@touch .nolib
	@$(MAKE) all NOLIB=true

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
	@cp $(COMPCERT_DIR)/$(ARCH)/extractionMachdep.v $(BUILD_DIR)/bcomp/
	@sed -i'' 's\Require\From compcert Require\g' $(EXTRDEP)

extrdep: $(EXTRDEP) 

# Copy Rocq source files to the build directory

$(BUILD_DIR)/%.v: %.v | builddir
	@echo COPY $< to $@
	@cp $< $@

vbuild: $(VBUILD) extrdep

$(BUILD_DIR)/extraction.v: extraction.v | builddir
	@echo COPY extraction.v to $@
	@cp extraction.v $(BUILD_DIR)

# Generate dependencies between Rocq files

depend1: $(VBUILD) $(EXTRDEP) $(BUILD_DIR)/extraction.v
	@echo Analyzing Rocq dependencies
	@$(COQDEP) $^ > .depend

depend: depend1

# Compile Rocq source files

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) $*.v

theories: $(VBUILD:.v=.vo)

vofiles: $(VBUILD:.v=.vo) $(EXTRDEP.v=.vo)

# Extraction

$(BUILD_DIR)/extraction/STAMP: $(VBUILD:.v=.vo) $(EXTRDEP.v=.vo) $(BUILD_DIR)/extraction.v
	rm -f $(BUILD_DIR)/extraction_tmp/*.ml $(BUILD_DIR)/extraction_tmp/*.mli
	@echo COQTOP $(BUILD_DIR)/extraction.v
	@mkdir -p $(BUILD_DIR)/extraction_tmp
	@$(COQEXEC) $(BUILD_DIR)/extraction.v
	@touch $(BUILD_DIR)/extraction_tmp/STAMP
	@if ! [ -d "$(BUILD_DIR)/extraction" ]; then \
		mkdir $(BUILD_DIR)/extraction; \
    fi
	@./sync.sh $(BUILD_DIR)/extraction_tmp $(BUILD_DIR)/extraction

.depend.extr: $(BUILD_DIR)/extraction/STAMP
	$(MAKE) -f Makefile.extr depend

barocq: .depend.extr compcert.ini FORCE
	$(MAKE) -f Makefile.extr barocq

# Lib only

lib: Makefile.lib
	$(MAKE) -f $<

# Binary and Rocq library installation

install:
	@echo INSTALL barocq to $(INSTALL_DIR)/barocq
	@install barocq $(INSTALL_DIR)/barocq

install-dev:
	@echo INSTALL source files to $(INSTALL_DEV_DIR)
	@for d in $(VDIRS); do \
		set -e; \
		if ! ([ "$$d" = lib ] && [ -f ".nolib" ]); then \
			install -d $(INSTALL_DEV_DIR)/$$d; \
			install -m 0644 $(BUILD_DIR)/$$d/*.v $(BUILD_DIR)/$$d/*.vo $(BUILD_DIR)/$$d/*.glob $(INSTALL_DEV_DIR)/$$d/; \
		fi; \
	done
	@install -d $(INSTALL_DEV_DIR)/misc
	@install misc/CorresBD_Proof.v $(INSTALL_DEV_DIR)/misc/CorresBD_Proof.v

install-all:
	$(MAKE) install install-dev

install-lib: Makefile.lib
	$(MAKE) -f $< install

uninstall:
	rm -f $(INSTALL_DIR)/barocq

uninstall-lib:
	rm -rf $(addprefix $(INSTALL_DEV_DIR)/, lib)

uninstall-dev:
	@echo Uninstalling dev files
	@if [ -f ".nolib" ]; then \
		rm -rf $(addprefix $(INSTALL_DEV_DIR)/, $(filter-out lib, $(VDIRS))); \
		rm -rf $(INSTALL_DEV_DIR)/misc; \
	else \
		rm -rf $(INSTALL_DEV_DIR); \
	fi

uninstall-all:
	$(MAKE) uninstall uninstall-dev

# Formatting

MLSOURCE=$(foreach dir,$(MLDIRS),$(wildcard $(dir)/*.ml $(dir)/*.mli))
MLFORMAT=$(filter-out common/uint63.ml common/uint63.mli, $(MLSOURCE))

format: $(MLFORMAT)
	@echo OCAMLFORMAT $^
	@$(OCAMLFORMAT) $^

# Cleaning

clean-theories:
	rm -f $(VBUILD)
	rm -f $(VBUILD:.v=.vo)
	rm -f $(VBUILD:.v=.vok)
	rm -f $(VBUILD:.v=.vos)
	rm -f $(VBUILD:.v=.glob)
	rm -f $(BUILD_DIR)/lib/.*.aux
	rm -f $(BUILD_DIR)/common/.*.aux
	rm -f $(BUILD_DIR)/frontend/.*.aux
	rm -f $(BUILD_DIR)/backend/.*.aux
	rm -f $(BUILD_DIR)/rocqgen/.*.aux
	rm -f $(BUILD_DIR)/bcomp/.*.aux

clean:
	rm -rf $(BUILD_DIR)
	rm -f compcert.ini
	rm -f .depend.extr
	rm -f .depend
	rm -f barocq
	rm -f .lia.cache

clean-lib:
	$(MAKE) -f Makefile.lib clean

cleanall:
	$(MAKE) clean
	$(MAKE) uninstall-all

FORCE:

.PHONY:\
	lib nolib builddir extrdep vbuild depend depend1\
    vofiles extraction format theories FORCE\
	install install-dev install-all\
	uninstall uninstall-lib uninstall-dev uninstall-all\
	clean clean_theories cleanall

-include .depend
