From BarocqComp Require Import Error Utils Barocq BarocqBNFgen.
From BarocqComp Require Import ImpBNFgen ImpABNFgen Imp1 Imp1gen Imp2gen Clightgen.

Definition compile (show_debug: bool) (prog: Barocq.program) : res Clight.program :=
  let* btyped := Barocq.Typing.typecheck_program prog in
  let* bbnf := BarocqBNFgen.normalize_program btyped in
  let ibnf := ImpBNFgen.transl_program bbnf in
  let* iabnf := ImpABNFgen.normalize_program ibnf in
  let imp1 := Imp1gen.transl_program iabnf in
  let* imp1_typed := Imp1Typing.typecheck_program imp1 in
  let* imp1_alias := Imp1gen.AliasingCheck.gen_aliasing_program show_debug imp1_typed in
  let* imp1_typed := Imp1gen.AliasingCheck.check_program imp1_alias in
  let imp2 := Imp2gen.transl_program imp1_typed in
  let* clight := Clightgen.transl_program imp2 in
  eret clight.

Definition compile_to_imp1 (prog: Barocq.program) : res Imp1.program :=
  let* btyped := Barocq.Typing.typecheck_program prog in
  let* bbnf := BarocqBNFgen.normalize_program btyped in
  let ibnf := ImpBNFgen.transl_program bbnf in
  let* iabnf := ImpABNFgen.normalize_program ibnf in
  let imp1 := Imp1gen.transl_program iabnf in
  eret imp1.