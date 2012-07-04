.PHONY = clean builddir debug
OBJDIR=../obj
TARGET=main

comma:= ,
empty:=
space:= $(empty) $(empty)
INCLUDES = util,RegLang,patterns,css,DomStructure,LambdaJS/src

UNAME := $(shell uname)
ifeq ($(UNAME), Linux)
MENHIR := /contrib/projects/ocaml3.12.1/share/menhir
else
MENHIR := \"C:\cygwin\usr\local\share\menhir\"
endif

OCAMLBUILD = ocamlbuild -build-dir $(OBJDIR) -libs unix,str \
	-menhir "menhir --stdlib $(MENHIR)" \
	-lflags -I,../lib -Is $(INCLUDES) -cflags -annot -cflags -I,../lib -Is $(INCLUDES)

debug: builddir
	$(OCAMLBUILD) $(TARGET).d.byte
	@ln -sf ../obj/$(TARGET).d.byte run
	@echo ocamldebug $(shell find $(OBJDIR) -type d -printf "-I %p ") $(OBJDIR)/$(TARGET).d.byte > debug
	@chmod 744 debug

opt: builddir
	@rm -f debug
	$(OCAMLBUILD) $(TARGET).native
	@ln -sf ../obj/$(TARGET).native run

clean:
	rm -rf ../obj
	rm -rf run debug

builddir:
	@mkdir ../obj 2> /dev/null || true


