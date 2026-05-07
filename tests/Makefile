# Tests that should not compile
FAIL=invalid_return.brc get_multiple_index.brc redef_index3.brc outscope_return.brc array_may_alias_index.brc write_annot.brc
SUCCESS= update_array_in_record.brc update_record_in_record.brc suspend.brc \
	 suspend_in.brc inscope_return.brc non_pure.brc update_array_struct.brc array_alias.brc

KO= $(FAIL:.brc=.fail)
OK= $(SUCCESS:.brc=.ok)

all : ok fail

fail : $(KO)

ok : $(OK)

%.fail:%.brc
	@echo SHOULD FAIL
	@echo barocq $*.brc
	@barocq $*.brc &> $*.fail ; exit 0
	@cat $*.fail

%.ok:%.brc
	@echo SHOULD SUCCEED
	@echo barocq $*.brc
	@barocq $*.brc > $*.ok
	@cat $*.ok

clean :
	rm -f *ok
	rm -f *fail
