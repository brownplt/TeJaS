.PHONY = clean builddir debug
OBJDIR=../obj
TARGET=main

comma:= ,
empty:=
space:= $(empty) $(empty)
INCLUDES = util,RegLang,patterns,css,DomStructure,LambdaJS/src,bare,jquery,typescript

UNAME := $(shell uname)
ifeq ($(UNAME), Linux)
MENHIR := /usr/share/menhir
else
MENHIR := \"C:\cygwin\usr\local\share\menhir\"
endif

PROFILING = $(EMPTY)

OCAMLBUILD = ocamlbuild $(PROFILING) -build-dir $(OBJDIR) -libs unix,str \
	-menhir "menhir --stdlib $(MENHIR)" \
	-lflags -I,../lib -Is $(INCLUDES) -cflags -annot -cflags -I,../lib -Is $(INCLUDES)

debug: builddir
	$(OCAMLBUILD) $(TARGET).d.byte
	@ln -sf ../obj/$(TARGET).d.byte run
	@echo ocamldebug $(shell find $(OBJDIR) -type d -printf "-I %p ") $(OBJDIR)/$(TARGET).d.byte > debug
	@chmod 744 debug

profile: builddir
	set PROFILING = ocamlcp
	$(OCAMLBUILD) $(TARGET).byte
	@ln -sf ../obj/$(TARGET).byte profile

profopt: builddir
	$(OCAMLBUILD) $(TARGET).p.native
	@ln -sf ../obj/$(TARGET).p.native profopt


opt: builddir
	@rm -f debug
	$(OCAMLBUILD) $(TARGET).native
	@ln -sf ../obj/$(TARGET).native run

clean:
	rm -rf ../obj
	rm -rf run debug profile profopt ocamlprof.dump gmon.out

builddir:
	@mkdir ../obj 2> /dev/null || true


