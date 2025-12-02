# Tests that should not compile
FAIL=invalid_return.br
SUCCESS= update_array_in_record.br update_record_in_record.br suspend.br suspend_in.br

KO= $(FAIL:.br=.fail)
OK= $(SUCCESS:.br=.ok)

fail : $(KO)

ok : $(OK)

%.fail:%.br
	barocq $*.br > $*.fail
	@cat $*.fail

%.ok:%.br
	barocq $*.br > $*.ok
	@cat $*.ok

clean :
	rm -f *ok
	rm -f *fail
