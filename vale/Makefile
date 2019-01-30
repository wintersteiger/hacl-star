all: vale-all

ifndef MAKE_RESTARTS
obj/Makefile.include: .FORCE
	./run_python.sh makegen.py --OUT-MAKE obj/Makefile.include --FSTAR-MY-VERSION --FSTAR-EXTRACT --FARGS='--already_cached "Spec FStar LowStar C" $(OTHERFLAGS)' $(VALEFLAGS)

.PHONY: .FORCE
.FORCE:
endif

include obj/Makefile.include

clean:
	rm -rf obj

.PHONY: all clean
