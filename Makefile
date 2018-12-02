INSTALL_ARGS := $(if $(PREFIX),--prefix $(PREFIX),)
d := ~/.bondi

# Default rule
default:
	dune build @install
	test -d $d || mkdir -p $d && cp -r prelude $d

install:
	dune install $(INSTALL_ARGS)

uninstall:
	dune uninstall $(INSTALL_ARGS)

reinstall: uninstall reinstall

clean:;
	rm -rf _build

.PHONY: default install uninstall reinstall clean