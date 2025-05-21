From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlString.

From Coq Require BinInt BinPos.
From compcert Require Integers Floats Machregs Archi AST Memdata Csyntax Initializers Ctyping Ctypes Clight Ctypesdefs Values.
From BarocqComp Require Imp1 Imp1gen Barocq Compiler BarocqShallowgen.

(* Extraction language *)
Extraction Language OCaml.

(* Datatypes *)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

(* Errors *)
Extraction Inline Errors.bind Errors.bind2.

Load extractionMachdep.

(* Avoid name clashes *)
Extraction Blacklist List String Int Array.

(* Extraction directory *)
Set Extraction Output Directory "_build/extraction".

Extract Constant Imp1.Aliasing_AST.ABSDOM => "Aliasing_defs.AbsDom.t".
Extract Constant Imp1gen.gen_aliasing_program => "Aliasing_impl.gen_aliasing_program".
Extract Constant Imp1gen.check_program_aliasing => "Aliasing_check.check_program".

Separate Extraction
  BinPos.Pos.pred
  BinPosDef.Pos.max
  BinPosDef.Pos.add
  BinPosDef.Pos.leb
  BinInt.Z.succ
  BinPosDef.Pos.compare
  Integers.Ptrofs.signed
  Floats.Float.of_bits
  Floats.Float.to_bits
  Floats.Float32.of_bits
  Floats.Float32.to_bits
  Floats.Float32.from_parsed
  Floats.Float.from_parsed
  Machregs.mreg
  Machregs.register_by_name
  Archi.win64
  AST.builtin_arg
  AST.builtin_res
  Memdata.size_chunk
  Values
  Csyntax.program
  Initializers.constval_cast
  Initializers.Init_single
  Initializers.transl_init
  Ctyping
  Ctypes.signature_of_type
  Ctypes.layout_struct
  Ctypesdefs.string_of_ident
  Ctypesdefs.ident_of_string
  Clight.type_of_function
  Clightgen.program_idents
  Barocq.Typing.typecheck_program
  Barocq.interpret
  Barocq.iprog_to_prog
  Barocq.eval_def
  Barocq.eval_struct_btyp
  Compiler.aliascheck_program
  Compiler.compile_to_imp1
  Compiler.compile
  BarocqShallowgen.monadify_norm_program
  BarocqShallow.Monadic.get_struct_defs
  Imp1.Aliasing_AST.program
  Ident.