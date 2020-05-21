output.pm: Main.hs
	cabal -v0 run examples > examples.pm

.PHONY: clean cleandist

clean:
	rm output.pm

cleandist:
	rm -rf output.pm dist-newstyle/
