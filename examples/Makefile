output.pm: Main.hs
	cabal -v0 run examples -- -o output.pm

.PHONY: clean cleandist

clean:
	rm output.pm

cleandist:
	rm -rf output.pm dist-newstyle/
