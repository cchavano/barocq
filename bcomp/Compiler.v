From BarocqComp Require Import Error Utils Ident Barocq BarocqBNFgen.
From BarocqComp Require Import ImpBNFgen Imp1 Imp1gen2 Imp1ElimAlias InvAnalysis Unboxing Imp2gen GlobRewrite Csyntaxgen.
From BarocqComp Require Import Pp.
From Coq Require Import String.

(** Debug flags *)
Inductive ir_name :=
| Barocq
| BBNF
| IBNF
| Imp1
| Imp2.

Definition pp_ir (i:ir_name) :=
  match i with
  | Barocq => Bstr "barocq"
  | BBNF   => Bstr "bbnf"
  | IBNF   => Bstr "ibnf"
  | Imp1   => Bstr "imp1"
  | Imp2   => Bstr "imp2"
  end.

Definition ir_name_eq_dec (p1 p2:ir_name) : {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality.
Defined.


Record compiler_opt :=
  {
    dbg_analysis : bool; (* outputs the static analysis result - this makes the compiler fail *)
    trace : list ir_name
  }.

Definition compile (opt : compiler_opt) (arch: Target.archi) (globinfo: option (ident * ident)) (prog: Barocq.program) : res (Csyntax.program * Log.t) :=
  let insert_log {A : Type} (F: A -> box) (ir:ir_name) (a:A) (l:Log.t) :=
    if List.In_dec ir_name_eq_dec ir (opt.(trace))
    then Log.add_entry (pp_ir ir) (F a) l
    else l
  in
  let log := insert_log Barocq.Pp.pp_program Barocq prog Log.empty in
  let* bbnf := BarocqBNFgen.norm_program arch prog in
  let log   := insert_log BarocqBNF.Pp.pp_program BBNF bbnf log in
  let ibnf := ImpBNFgen.transl_program bbnf in
  let* imp1 := Imp1gen2.norm_program ibnf in
  let* imp1_typed := Imp1Typing.typecheck_program arch imp1 in
  let log := insert_log  Imp1Typed.Pp.pp_program Imp1 imp1_typed log in
  (* let* (te,age) := InvAnalysis.check_program imp1_typed in *) (* Maybe, we could reuse the analysis result
  if (dbg_analysis opt)
  then Error (msg (Pp.pp (InvAnalysis.pp_inv (snd age))))
  else *)
  let* te := Typing.tenv_of_type_defs (Syntax.prog_types imp1_typed) in
  let* imp1_typed := Imp1ElimAlias.transl_program te imp1_typed in
  if Unboxing.check_program imp1_typed then
    let imp2 := Imp2gen.transl_program imp1_typed in
    let imp2_grw :=
      match globinfo with
      | Some ginfo => GlobRewrite.rewrite_program ginfo imp2
      | None => imp2
      end
    in 
    let* clight := Csyntaxgen.transl_program imp2_grw in
    eret (clight,log)
  else fail.

Definition compile_to_imp1 (arch: Target.archi) (prog: Barocq.program) : res Imp1.program :=
  let* bbnf := BarocqBNFgen.norm_program arch prog in
  let ibnf := ImpBNFgen.transl_program bbnf in
  let* imp1 := Imp1gen2.norm_program ibnf in
  eret imp1.

Definition aliascheck_program (show_debug: bool) (arch: Target.archi) (prog: Barocq.program) : res Imp1Typed.program :=
  let* imp1 := compile_to_imp1 arch prog in
  let* imp1_typed := Imp1Typing.typecheck_program arch imp1 in
  let* imp1_alias := Imp1gen2.gen_aliasing_program show_debug imp1_typed in
  Imp1gen2.check_program_aliasing imp1_alias.
