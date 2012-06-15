.PHONY = clean builddir debug
OBJDIR=../obj

comma:= ,
empty:=
space:= $(empty) $(empty)
INCLUDES = util,RegLang,patterns,css

OCAMLBUILD = ocamlbuild -build-dir $(OBJDIR) -libs unix,str \
	-menhir "menhir --stdlib \"C:\cygwin\usr\local\share\menhir\"" \
	-lflags -I,../lib -Is $(INCLUDES) -cflags -annot -cflags -I,../lib -Is $(INCLUDES)

debug: builddir
	$(OCAMLBUILD) jq.d.byte
	@ln -sf ../obj/jq.d.byte run
	@echo ocamldebug $(shell find $(OBJDIR) -type d -printf "-I %p ") $(OBJDIR)/jq.d.byte > debug
	@chmod 744 debug

opt: builddir
	@rm -f debug
	$(OCAMLBUILD) jq.native
	@ln -sf ../obj/jq.native run

clean:
	rm -rf ../obj
	rm -rf run debug

builddir:
	@mkdir ../obj 2> /dev/null || true


