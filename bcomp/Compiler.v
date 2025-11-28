From BarocqComp Require Import Error Utils Ident Barocq BarocqBNFgen.
From BarocqComp Require Import ImpBNFgen Imp1 Imp1gen2 Imp1ElimAlias InvAnalysis Unboxing Imp2gen GlobRewrite ClightCegen.

Definition compile (show_debug: bool) (arch: Target.archi) (globinfo: option (ident * ident)) (prog: Barocq.program) : res ClightCe.program :=
  let* bbnf := BarocqBNFgen.norm_program arch prog in
  let ibnf := ImpBNFgen.transl_program bbnf in
  (* let* iabnf := ImpABNFgen.norm_program ibnf in *)
  let* imp1 := Imp1gen2.norm_program ibnf in
  let* imp1_typed := Imp1Typing.typecheck_program arch imp1 in
  let* _ := InvAnalysis.check_program imp1_typed in (* Maybe, we could reuse the analysis result *)
  let* imp1_typed := Imp1ElimAlias.transl_program imp1_typed in
  if Unboxing.check_program imp1_typed then
    let imp2 := Imp2gen.transl_program imp1_typed in
    let imp2_grw :=
      match globinfo with
      | Some ginfo => GlobRewrite.rewrite_program ginfo imp2
      | None => imp2
      end
    in 
    let* clight := ClightCegen.transl_program imp2_grw in
    eret clight
  else fail.

Definition compile_to_imp1 (arch: Target.archi) (prog: Barocq.program) : res Imp1.program :=
  let* bbnf := BarocqBNFgen.norm_program arch prog in
  let ibnf := ImpBNFgen.transl_program bbnf in
  (* let* iabnf := ImpABNFgen.norm_program ibnf in *)
  let* imp1 := Imp1gen2.norm_program ibnf in
  eret imp1.

Definition aliascheck_program (show_debug: bool) (arch: Target.archi) (prog: Barocq.program) : res Imp1Typed.program :=
  let* imp1 := compile_to_imp1 arch prog in
  let* imp1_typed := Imp1Typing.typecheck_program arch imp1 in
  let* imp1_alias := Imp1gen2.gen_aliasing_program show_debug imp1_typed in
  Imp1gen2.check_program_aliasing imp1_alias.
