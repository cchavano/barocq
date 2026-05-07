From Stdlib Require Import String List.
From BarocqComp Require Import Res StateMonads Utils Ident Pp Barocq Imp1.
From BarocqComp Require Import Renaming BarocqBNFgen ImpBNFgen Imp1gen Imp2gen GlobRewrite Csyntaxgen.
From BarocqComp Require Import Imp1ElimAlias InvAnalysis.
From BarocqComp Require Import Imp2Copy.
From BarocqComp Require Import BarocqBNFUndo. (* force dependency *)

Inductive ir_name :=
| Ir_Barocq
| Ir_BBNF
| Ir_IBNF
| Ir_Imp1
| Ir_Copy (* After copy propagation *)
| Ir_Imp2
| Ir_Csyntax.

Inductive opt_flag :=
| Opt_Copy (* Perform copy propagation *)
| Opt_Other (* Just to trick extraction *)
.

Definition opt_flag_eqb (o1 o2:opt_flag) :=
  match o1, o2 with
  | Opt_Copy , Opt_Copy => true
  | Opt_Other , Opt_Other => true
  | _ , _ => false
  end.

Definition pp_ir (i:ir_name) :=
  match i with
  | Ir_Barocq     => Bstr "barocq"
  | Ir_BBNF       => Bstr "bbnf"
  | Ir_IBNF       => Bstr "ibnf"
  | Ir_Imp1       => Bstr "imp1"
  | Ir_Copy       => Bstr "copy"
  | Ir_Imp2       => Bstr "imp2"
  | Ir_Csyntax    => Bstr "csyntax"
  end.

Definition ir_name_eq_dec (p1 p2:ir_name) : {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality.
Defined.

Record compiler_opt :=
  {
    dbg_analysis : bool; (* outputs the static analysis result - this makes the compiler to fail *)
    ir_log : list ir_name;
    ir_gen : list ir_name;
    ir_opt : list opt_flag
  }.

Definition has_opt (o:opt_flag) (c:compiler_opt) :=
  List.existsb (opt_flag_eqb o) (ir_opt c).

(* Compiler target *)

Inductive ir_prog :=
| Barocq   (p:Barocq.program)
| BarocqBNF (p:BarocqBNF.program)
| ImpBNF   (p:ImpBNF.program)
| Imp1     (p:Imp1.program)
| Imp2     (p:Imp2.program)
| Csyntax  (p:Csyntax.program).

Module StateLog <: STATE_TYPE.
  Definition t : Type := (list ir_prog * Log.t).
End StateLog.

Module MonComp. 
  Include MonStateErr2(StateLog).

  Definition insert_log (opt:compiler_opt) (ir:ir_name) {A : Type} (F: A -> box) (G: A -> ir_prog) (a:A) : M unit :=
    fun '(progs, l) =>
      let l := if List.In_dec ir_name_eq_dec ir (opt.(ir_log))
              then Log.add_entry (pp_ir ir) (F a) l else l in
      let progs := if List.In_dec ir_name_eq_dec ir (opt.(ir_gen))
                  then (G a) :: progs else progs in
      (OK tt, (progs, l)).
End MonComp.

Import MonComp.
Local Open Scope state_err2_monad_scope.

Definition compile_aux (opt : compiler_opt) (globinfo: option (ident * ident)) (prog: Barocq.program) : MonComp.M unit :=
  let prog := Renaming.rename_program prog in
  do _ <- insert_log opt Ir_Barocq Barocq.Pp.pp_program Barocq prog ;
  do/l btyped <- Barocq.Typing.typecheck_program prog;
  do/l bbnf <- BarocqBNFgen.norm_program btyped;
  do _ <- insert_log opt Ir_BBNF BarocqBNF.Pp.pp_program BarocqBNF bbnf;
  do/l ibnf <- ImpBNFgen.transl_program bbnf;
  do/l imp1 <- Imp1gen.norm_program ibnf;
  do/l imp1_typed <- Imp1Typing.typecheck_program imp1;
  do _ <- insert_log  opt Ir_Imp1 Imp1.Pp.pp_program Imp1 imp1_typed;
  do/l (te,age) <- InvAnalysis.check_program imp1_typed; (* Maybe, we could reuse the analysis result *)
  if (dbg_analysis opt)
  then sfailwith (Pp.pp (InvAnalysis.pp_inv (snd age)))
  else
    do/l imp1_typed <- Imp1ElimAlias.transl_program te imp1_typed;
      let imp2 := Imp2gen.transl_program imp1_typed in
      do _ <- insert_log opt Ir_Imp2 Imp2.Pp.pp_program Imp2 imp2;
      let imp2 := if has_opt Opt_Copy opt then Imp2Copy.transl_program imp2 else imp2 in
      do _ <- insert_log opt Ir_Copy Imp2.Pp.pp_program Imp2 imp2;
      let imp2_grw :=
        match globinfo with
        | Some ginfo => GlobRewrite.rewrite_program ginfo imp2
        | None => imp2
        end
      in 
      do/l clight <- Csyntaxgen.transl_program imp2_grw;
      (fun '(p, log) =>
        let p :=
          if List.In_dec ir_name_eq_dec Ir_Csyntax (opt.(ir_gen))
          then Csyntax clight :: p 
          else p
        in (OK tt, (p, log))).

Definition compile (opt : compiler_opt) (globinfo: option (ident * ident)) (prog: Barocq.program) : (res unit * (list ir_prog * Log.t)) :=
  compile_aux opt globinfo prog (nil, Log.empty).

Local Open Scope error_monad_scope.

Definition compile_to_imp1 (prog: Barocq.program) : res Imp1.program :=
  let prog := Renaming.rename_program prog in
  do btyped <- Barocq.Typing.typecheck_program prog;
  do bbnf <- BarocqBNFgen.norm_program btyped;
  do ibnf <- ImpBNFgen.transl_program bbnf;
  do imp1 <- Imp1gen.norm_program ibnf;
  eret imp1.

Definition aliascheck_program (opt : compiler_opt) (prog: Barocq.program) : res Imp1.program :=
  do imp1 <- compile_to_imp1 prog;
  do imp1_typed <- Imp1Typing.typecheck_program imp1;
  do (te,age) <- InvAnalysis.check_program imp1_typed;
  if (dbg_analysis opt) then
    Error (msg (Pp.pp (InvAnalysis.pp_inv (snd age))))
  else eret imp1_typed.
