From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNativeString.
From Stdlib Require Import ExtrOCamlInt63.

From Stdlib Require BinInt BinPos.
From compcert Require Integers Floats Machregs Archi AST Memdata Csyntax Initializers.
From compcert Require Import Ctyping Ctypes Clight Ctypesdefs Values Cabs Parser.
From BarocqComp Require Imp1 Imp1gen Barocq BarocqBNFUndo Compiler ShallowASTgen BarocqBNFVC.

(* Extraction language *)
Extraction Language OCaml.

(* Datatypes *)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

Load extractionMachdep.

(* Avoid name clashes *)
Extraction Blacklist List String Int Array.

(* Extraction directory *)
Set Extraction Output Directory "_build/extraction_tmp".

(* Extract Constant Imp1.Aliasing_AST.ABSDOM => "Aliasing_defs.AbsDom.t".
Extract Constant Imp1gen.gen_aliasing_program => "Aliasing_impl.gen_aliasing_program".
Extract Constant Imp1gen.check_program_aliasing => "Aliasing_check.check_program". *)

(* Cabs *)
Extract Constant Cabs.loc =>
"{ lineno : int;
   filename: string;
   byteno: int;
   ident : int;
 }".
Extract Inlined Constant Cabs.string => "String.t".
Extract Constant Cabs.char_code => "int64".

Separate Extraction
  BinPos.Pos.pred
  BinPosDef.Pos.max
  BinPosDef.Pos.add
  BinPosDef.Pos.leb
  BinInt.Z.succ
  BinPosDef.Pos.compare
  Archi
  Integers.Ptrofs.signed
  Floats.Float.of_bits
  Floats.Float.to_bits
  Floats.Float32.of_bits
  Floats.Float32.to_bits
  Floats.Float32.from_parsed
  Floats.Float.from_parsed
  Machregs.mreg
  Machregs.register_by_name
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
  Csyntaxgen.program_idents
  Csyntaxgen.program_glob_arrays
  (*Barocq.Typing.atom_of_expr*)
  Barocq.Typing.typecheck_program
  Barocq.Typing.typecheck_iprogram
  Barocq.Typing.program_of_iprogram
  Barocq.typof_expr
  Barocq.interpret
  Barocq.iprog_to_prog
  Barocq.eval_def
  BarocqBNFUndo.decompile_program
  Compiler.aliascheck_program
  Compiler.compile_to_imp1
  Compiler.compile Compiler.ir_name Compiler.opt_flag
  ShallowAST.Monadic.get_record_typedefs
  ShallowASTgen.monadify_norm_program
  ShallowASTgen.monadify_norm2_program
  Syntax.get_enum_typedefs
  Syntax.get_record_typedefs
  Syntax.get_record_typedefs
  Types.btyp_is_prim
  Ident
  BarocqBNFVC Pp.Log.pp
  Cabs
  Parser.translation_unit_file.
