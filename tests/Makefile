# Tests that should not compile
FAIL=invalid_return.br get_multiple_index.br redef_index3.br
SUCCESS= update_array_in_record.br update_record_in_record.br suspend.br suspend_in.br

KO= $(FAIL:.br=.fail)
OK= $(SUCCESS:.br=.ok)

fail : $(KO)

ok : $(OK)

%.fail:%.br
	@echo barocq $*.br
	@barocq $*.br &> $*.fail ; exit 0
	@cat $*.fail

%.ok:%.br
	@echo barocq $*.br
	@barocq $*.br > $*.ok
	@cat $*.ok

clean :
	rm -f *ok
	rm -f *fail
