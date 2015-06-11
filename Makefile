# 
# Rules for compiling and linking the typechecker/evaluator
#
# Type
#   make         to rebuild the executable file f
#   make windows to rebuild the executable file f.exe
#   make test    to rebuild the executable and run it on input file test.f
#   make clean   to remove all intermediate and temporary files
#   make depend  to rebuild the intermodule dependency graph that is used
#                  by make to determine which order to schedule 
#	           compilations.  You should not need to do this unless
#                  you add new modules or new dependencies between 
#                  existing modules.  (The graph is stored in the file
#                  .depend)

# These are the object files needed to rebuild the main executable file
#
OBJS = support.cmo range.cmo syntax.cmo core.cmo main.cmo

# When "make" is invoked with no arguments, we build an executable 
# typechecker, after building everything that it depends on
all: $(DEPEND) $(OBJS) f

# On a Windows machine, we do exactly the same except that the executable
# file that gets built needs to have the extension ".exe"
windows: $(DEPEND) $(OBJS) f.exe

# Include an automatically generated list of dependencies between source files
include .depend

# Build an executable typechecker
f: $(OBJS) main.cmo 
	@echo Linking $@
	ocamlc -o $@ $(COMMONOBJS) $(OBJS) 

# Build an executable typechecker for Windows
f.exe: $(OBJS) main.cmo 
	@echo Linking $@
	ocamlc -o $@ $(COMMONOBJS) $(OBJS) 

# Build and test
test: all
	./f

# Compile an ML module interface
%.cmi : %.mli
	ocamlc -c $<

# Compile an ML module implementation
%.cmo : %.ml
	ocamlc -c $<

# Clean up the directory
clean::
	rm -rf *.o *.cmo *.cmi f f.exe TAGS *~ *.bak

# Rebuild intermodule dependencies
depend:: $(DEPEND) 
	ocamldep $(INCLUDE) *.mli *.ml > .depend

# 
