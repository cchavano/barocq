# Tests that should not compile
FAIL=invalid_return.br

FAILTRACE= $(FAIL:.br=.fail)

fail : $(FAILTRACE)
	echo $(FAILTRACE)

%.fail:%.br
	barocq $*.br > $*.fail
	cat $*.fail
