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

(* Separate Extraction
  BinPos.Pos.pred
  BinInt.Z.succ
  Integers.Ptrofs.signedBSDOM => "Aliasing_defs.AbsDom.t".
Extract Constant Imp1gen.
  Machregs.mreg
  Machregs.register_names
  Machregs.register_by_name
  Archi.win64
  AST.builtin_arg
  AST.builtin_res
  (* Memdata *)
  Csyntax
  (* Initializers *)
  Clight.program
  Ctyping
  Ctypes.layout_struct
  Ctypes.signature_of_type
  Ctypes.make_program
  Ctypesdefs.string_of_ident
  Ctypesdefs.ident_of_string
  Barocq.xprogram
  Barocq.interpret
  Barocq.xprog_to_prog
  Clightgen.program_idents
  Compiler.compile_to_imp1
  Compiler.compile. *)

Extract Constant Imp1.Aliasing_AST.ABSDOM => "Aliasing_defs.AbsDom.t".
Extract Constant Imp1gen.AliasingCheck.path => "Aliasing_defs.path".
Extract Inlined Constant Imp1gen.AliasingCheck.make_path => "".
Extract Constant Imp1gen.AliasingCheck.is_valid_path => "Aliasing_defs.AbsDom.is_valid_path".
Extract Constant Imp1gen.AliasingCheck.is_valid_atom => "Aliasing_impl.is_valid_atom".
Extract Constant Imp1gen.AliasingCheck.is_valid_return => "Aliasing_defs.AbsDom.is_valid_return".
Extract Constant Imp1gen.AliasingCheck.gen_aliasing_program => "Aliasing_impl.gen_aliasing_program".

Separate Extraction
  BinPos.Pos.pred
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
  Barocq.xprog_to_prog
  Barocq.eval_def
  Barocq.eval_struct_ctyp
  Compiler.compile_to_imp1
  Compiler.compile
  Compiler.compile2_to_imp1
  Compiler.compile2
  BarocqShallowgen.monadify_norm_program
  Imp1.Aliasing_AST.program.