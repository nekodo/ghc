DEBUG := false

ifeq ($(DEBUG), true)
  DEBUG_FLG := -debug
else
  DEBUG_FLG :=
endif

GHC_OPTS += -threaded -O3 -fforce-recomp $(DEBUG_FLG) -rtsopts --make

GHCV := $(HOME)/install/ghc7.4.1/bin/ghc $(GHC_OPTS)
GHCLWC := $(HOME)/test-install/ghc-7.4.1-lwc/bin/ghc $(GHC_OPTS)

all: $(TARGETS)

%-V.bin:	%-V.hs
	$(GHCV) $< -o $@

%-LWC.bin:	%-LWC.hs
	$(GHCLWC) $< -o $@

%-LWC.cmm:  %-LWC.hs
	$(GHCLWC) -c $< -ddump-cmm >$@

%-V.cmm:  %-V.hs
	$(GHCV) -c $< -ddump-cmm >$@

clean:
	rm -f *.bin *.o *.hi *.cmm *~ *.stat
