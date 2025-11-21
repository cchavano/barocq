open Syntax
open Syntax.Typed
open Imp1.Aliasing_AST
open Aliasing_defs

let curr_fun_name : string ref = ref "UNKNOWN"

type error_cause =
  | Invalid_atom of atom
  | Invalid_path of ident * path
  | Invalid_deep_access of atom * access list
  | Invalid_retval
  | Invalid_param_at_return of ident

exception Invalid_program of error_cause * statement option

let msg_from_failure (cause : error_cause) : string =
  match cause with
  | Invalid_atom a ->
      Printf.sprintf "atom %s is not valid" (PrintSyntax.Typed.atom_to_string a)
  | Invalid_path (v, p) ->
      Printf.sprintf
        "path %s%s is not valid"
        (PrintUtils.ident_to_string v)
        (path_to_string p)
  | Invalid_deep_access (a, acs) ->
      let acs_str =
        PrintUtils.list_to_string
          (fun ac ->
            PrintSyntax.Typed.untype_access ac |> PrintSyntax.access_to_string)
          acs
      in
      Printf.sprintf
        "deep access %s%s is not valid"
        (PrintSyntax.Typed.atom_to_string a)
        acs_str
  | Invalid_retval -> "invalid return value"
  | Invalid_param_at_return p ->
      Printf.sprintf
        "parameter %s may have been modified but is not returned"
        (PrintUtils.ident_to_string p)

let error ?(stmt : statement option = None) (cause : error_cause) =
  raise (Invalid_program (cause, stmt))

let update_error_stmt (cause : error_cause) (s1 : statement option)
    (s2 : statement) =
  match s1 with
  | Some _ -> error cause ~stmt:s1
  | None -> begin
      match s2 with
      | StIfThenElse _ | StSwitch _ | StSequence _ -> error cause
      | _ -> error cause ~stmt:(Some s2)
    end

(** [check_atom d a] checks wether the atom [a] is valid in [d]. If [a] contains
    variables x1, ..., xn, it checks wether paths x1, ..., xn are valid in [d].
*)
let rec check_atom (d : absdom) (a : atom) : bool =
  match a with
  | AVar (x, _) -> AbsDom.is_valid_path d x []
  | AUnaryOp (op, a', _) -> check_atom d a'
  | ABinaryOp (op, a1, a2, _) -> check_atom d a1 && check_atom d a2
  | _ -> true

(** [check_deep_access d a acs] checks that the deep access from [a] with access
    list [acs] is valid in [d].*)
let check_deep_access (d : absdom) (a : atom) (acs : access list) : bool =
  let rec aux acs =
    match acs with
    | [] -> true
    | Syntax.Typed.AcArrayIndex (i, _, _) :: acs' -> check_atom d i && aux acs'
    | Syntax.Typed.AcRecordField _ :: acs' -> aux acs'
  in
  match a with
  | AVar (x, _) -> aux acs && AbsDom.is_valid_path d x (path_of_access_list acs)
  | _ -> assert false

let check_comp (d : absdom) (c : comp) : comp =
  match c with
  | CpAtom (a, _) -> if check_atom d a then c else error (Invalid_atom a)
  | CpArrayGet (a, i, _, _) ->
      if check_atom d a then
        if check_atom d i then c else error (Invalid_atom i)
      else error (Invalid_atom a)
  | CpArraySet (_, i, v, _) ->
      if check_atom d i then
        if check_atom d v then c else error (Invalid_atom v)
      else error (Invalid_atom i)
  | CpRecordProj (AVar (y, _), f, _, _) ->
      if AbsDom.is_valid_path d y [f] then c else error (Invalid_path (y, [f]))
  | CpRecordUpdate (_, _, v, _) ->
      if check_atom d v then c else error (Invalid_atom v)
  | CpCall (_, args, _) -> begin
      match List.filter (fun a -> not (check_atom d a)) args with
      | [] -> c
      | a :: _ -> error (Invalid_atom a)
    end
  | CpDeepAccess (a, acs, _) ->
      if check_deep_access d a acs then c
      else error (Invalid_deep_access (a, acs))
  | CpRecordProj _ -> assert false

(** [check_params_on_return_rec st params] checks that any parameter in [params]
    is not modified if the returned locations does not match the locations
    pointed to by the parameter. *)
let rec check_params_on_return_rec (st : AbsDom.absstate)
    (params : (ident * Types.btyp) list) : unit =
  match params with
  | [] -> ()
  | (p, ty) :: params' ->
      let plocs =
        match IdentMap.find_opt p st.AbsDom.st_env with
        | Some locs -> locs
        | None -> LocSet.empty
      in
      if Types.btyp_is_prim ty || LocSet.equal st.AbsDom.st_res plocs then
        check_params_on_return_rec st params'
      else if AbsDom.is_valid_path (AbsDom.AbsState st) p [] then
        check_params_on_return_rec st params'
      else error (Invalid_param_at_return p)

(** [check_params_on_return d params] checks that any parameter in [params] is
    not modified if the returned locations does not match the locations pointed
    to by the parameter. *)
let check_params_on_return (d : absdom) (params : (ident * Types.btyp) list) :
    unit =
  match d with
  | AbsDom.AbsState st -> check_params_on_return_rec st params
  | AbsDom.Top _ -> assert false

let check_statement (params : (ident * Types.btyp) list) (s : statement) :
    Imp1.Typed.statement =
  let rec check_rec (s : statement) : Imp1.Typed.statement =
    try
      match s with
      | StSet (x, c, d_in, _) -> Imp1.Typed.StSet (x, check_comp d_in c)
      | StIfThenElse (a, s1, s2, d_in, _) ->
          if check_atom d_in a then
            let s1' = check_rec s1 in
            let s2' = check_rec s2 in
            Imp1.Typed.StIfThenElse (a, s1', s2')
          else error (Invalid_atom a)
      | StSwitch (a, cases, d_in, _) ->
          if check_atom d_in a then
            let cases' = Maps2.MapList.map check_rec cases in
            Imp1.Typed.StSwitch (a, cases')
          else error (Invalid_atom a)
      | StSequence (s1, s2) ->
          let s1' = check_rec s1 in
          let s2' = check_rec s2 in
          Imp1.Typed.StSequence (s1', s2')
      | StReturn (a, _, d_out) ->
          if AbsDom.is_valid_return d_out then begin
            check_params_on_return d_out params;
            Imp1.Typed.StReturn a
          end
          else error Invalid_retval
    with Invalid_program (cause, s1) -> update_error_stmt cause s1 s
  in
  check_rec s

let check_function (f : coq_function) : Imp1.Typed.coq_function =
  let body = check_statement f.fn_params f.fn_body in
  { fn_return = f.fn_return; fn_params = f.fn_params; fn_body = body }

let check_globdef (def : globdef) : Imp1.Typed.globdef =
  match def with
  | DefConst (x, l, ty) -> DefConst (x, l, ty)
  | DefFun (x, f) ->
      curr_fun_name := PrintUtils.ident_to_string x;
      DefFun (x, check_function f)
  | DeclConst (x, ty) -> DeclConst (x, ty)
  | DeclFun (f, tparams, tret) -> DeclFun (f, tparams, tret)

let check_program (prog : program) : Imp1.Typed.program Errors.res =
  try
    let defs = List.map check_globdef prog.prog_defs in
    Errors.OK { prog_defs = defs; prog_types = prog.prog_types }
  with Invalid_program (cause, stmt) ->
    let stmt_str =
      match stmt with
      | Some s ->
          Printf.sprintf
            ", statement \"%s\""
            (PrintImp1.PrintAliasing.statement_to_string_pref "" s)
      | None -> ""
    in
    let msg =
      Printf.sprintf
        "alias checking of function %s%s\n>> %s"
        !curr_fun_name
        stmt_str
        (msg_from_failure cause)
    in
    Errors.Error [Errors.MSG (Camlcoq.coqstring_of_camlstring msg)]
