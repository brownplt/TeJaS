open Prelude
open Sig

module P = Dprle.Set

module RT = struct
  type t =
    | Num
    | Re of P.t
    | Bool
    | Function
    | Object
    | Undefined

  let compare = Pervasives.compare

  open FormatExt

  let pp v = match v with
    | Num -> text "number"
    | Re pat -> text ("string:" ^ (P.pretty pat))
    | Bool -> text "boolean"
    | Function -> text "function"
    | Object -> text "object"
    | Undefined -> text "undefined"

  let any_fld = P.all
end

module RTSet = Set.Make (RT)
module RTSetExt = SetExt.Make (RTSet)


(******************************************************************************)
module type EXP = sig
  module Typs : Strobe_sigs.STROBE_MODULE
  type typ = Typs.extTyp
  type ref_kind =
    | RefCell
    | SourceCell
    | SinkCell


  type func_info = {
    func_owned: IdSet.t;
    func_loop : bool; (* used by semicps.ml *)
  }

  (** Typed JavaScript expressions. Additional well-formedness criteria are
    inline. *)
  type exp =
    | EConst of Pos.t * JavaScript_syntax.const
    | EBot of Pos.t
    | EAssertTyp of Pos.t * typ * exp
    | EArray of Pos.t * exp list
    | EObject of Pos.t * (string * exp) list
    | EId of Pos.t * id
    | EBracket of Pos.t * exp * exp
    | EUpdate of Pos.t * exp * exp * exp
    | EPrefixOp of Pos.t * id * exp
    | EInfixOp of Pos.t * id * exp * exp
    | EIf of Pos.t * exp * exp * exp
    | EApp of Pos.t * exp * exp list
    | EFunc of Pos.t * id list * func_info * exp
    | ELet of Pos.t * id * exp * exp
    | ERec of Pos.t * (id * typ * exp) list * exp
    | ESeq of Pos.t * exp * exp
    | ELabel of Pos.t * id * exp
    | EBreak of Pos.t * id * exp
    | ETryCatch of Pos.t * exp * id * exp
    | ETryFinally of Pos.t * exp * exp
    | EThrow of Pos.t * exp
    | ETypecast of Pos.t * RTSet.t * exp
    | ERef of Pos.t * ref_kind * exp
    | EDeref of Pos.t * exp
    | ESetRef of Pos.t * exp * exp
    | ESubsumption of Pos.t * typ * exp
    | EDowncast of Pos.t * typ * exp
    | ETypAbs of Pos.t * id * typ * exp
    | ETypApp of Pos.t * exp * typ
    | ECheat of Pos.t * typ * exp
    | EParen of Pos.t * exp

  val pos : exp -> Pos.t

  module Pretty : sig
    val exp : exp -> FormatExt.printer
  end


  val string_of_exp : exp -> string
  val assigned_free_vars : exp -> IdSet.t
  val unique_ids : exp -> exp * (string, string) Hashtbl.t
end

(******************************************************************************)
module Exp (TypImpl : Strobe_sigs.STROBE_MODULE) : (EXP with module Typs = TypImpl) = struct
  module Typs = TypImpl
  type typ = TypImpl.extTyp


  type ref_kind =
    | RefCell
    | SourceCell
    | SinkCell


  type func_info = {
    func_owned: IdSet.t;
    func_loop : bool; (* used by semicps.ml *)
  }

  (** Typed JavaScript expressions. Additional well-formedness criteria are
    inline. *)
  type exp =
    | EConst of Pos.t * JavaScript_syntax.const
    | EBot of Pos.t
    | EAssertTyp of Pos.t * typ * exp
    | EArray of Pos.t * exp list
    | EObject of Pos.t * (string * exp) list
    | EId of Pos.t * id
    | EBracket of Pos.t * exp * exp
    | EUpdate of Pos.t * exp * exp * exp
    | EPrefixOp of Pos.t * id * exp
    | EInfixOp of Pos.t * id * exp * exp
    | EIf of Pos.t * exp * exp * exp
    | EApp of Pos.t * exp * exp list
    | EFunc of Pos.t * id list * func_info * exp
    | ELet of Pos.t * id * exp * exp
    | ERec of Pos.t * (id * typ * exp) list * exp
    | ESeq of Pos.t * exp * exp
    | ELabel of Pos.t * id * exp
    | EBreak of Pos.t * id * exp
    | ETryCatch of Pos.t * exp * id * exp
    | ETryFinally of Pos.t * exp * exp
    | EThrow of Pos.t * exp
    | ETypecast of Pos.t * RTSet.t * exp
    | ERef of Pos.t * ref_kind * exp
    | EDeref of Pos.t * exp
    | ESetRef of Pos.t * exp * exp
    | ESubsumption of Pos.t * typ * exp
    | EDowncast of Pos.t * typ * exp
    | ETypAbs of Pos.t * id * typ * exp
    | ETypApp of Pos.t * exp * typ
    | ECheat of Pos.t * typ * exp
    | EParen of Pos.t * exp

  let pos exp = match exp with
    | EConst (p, _) -> p
    | EBot p -> p
    | EAssertTyp (p, _, _) -> p
    | EArray (p, _) -> p
    | EObject (p, _) -> p
    | EId (p, _) -> p
    | EBracket (p, _, _) -> p
    | EUpdate (p, _, _, _) -> p
    | EPrefixOp (p, _, _) -> p
    | EInfixOp (p, _, _, _) -> p
    | EIf (p, _, _, _) -> p
    | EApp (p, _, _) -> p
    | EFunc (p, _, _, _) -> p
    | ELet (p, _, _, _) -> p
    | ERec (p, __, _) -> p
    | ESeq (p, _, _) -> p
    | ELabel (p, _, _) -> p
    | EBreak (p, _, _) -> p
    | ETryCatch (p, _, _, _) -> p
    | ETryFinally (p, _, _) -> p
    | EThrow (p, _) -> p
    | ETypecast (p, _, _) -> p
    | ERef (p, _, _) -> p
    | EDeref (p, _) -> p
    | ESetRef (p, _, _) -> p
    | ESubsumption (p, _, _) -> p
    | EDowncast (p, _, _) -> p
    | ETypApp (p, _, _) -> p
    | ETypAbs (p, _, _, _) -> p
    | ECheat (p, _, _) -> p
    | EParen (p, _) -> p

  module Pretty : sig
    val exp : exp -> FormatExt.printer
  end = struct

    open Format
    open FormatExt

    let typ t = TypImpl.Ext.Pretty.typ t

    let rec exp e = match e with
      | EConst (_, c) -> JavaScript.Pretty.p_const c
      | EBot _ -> text "bot"
      | EAssertTyp (_, t, e) ->
        parens [hov 1 2 [ text "assert-typ"; parens [typ t]; exp e ]]
      | EArray (_, es) -> brackets [horz (map exp es)]
      | EObject (_, ps) -> brackets [vert (map fld ps)]
      | EId (_, x) -> text x
      | EBracket (_, e1, e2) -> hov 0 1 [ exp e1; brackets [exp e2] ]
      | EUpdate (_, e1, e2, e3) -> 
        hov 0 0 [ exp e1; 
                  brackets [hov 1 1 [ horz [exp e2; text ":="]; exp e3]]]
      | EIf (_, e1, e2, e3) ->
        parens [vert [ horz [ text "if"; exp e1 ]; exp e2; exp e3 ]]
      | EApp (_, f, args) -> parens [hov 1 1 (text "app" :: exp f :: map exp args)]
      | EFunc (_, args, t, body) ->
        parens [vert [ horz [ text "fun"; parens [horz (map text args)]; 
                              IdSetExt.p_set text t.func_owned;
                            ];
                       exp body]]
      | ELet (_, x, bound, body) ->
        parens [vert [ horz [ text "let";
                              parens [vert (map bind [(x, bound)])]];
                       exp body ]]
      | ERec (_, binds, body) ->
        parens [vert [ horz [ text "rec"; parens [vert (map rec_bind binds)] ];
                       exp body ]]
      | ESeq (_, e1, e2) -> parens [hov 1 0 [ text "seq"; exp e1; exp e2 ]]
      | ELabel (_, x, e) -> parens [hov 1 0 [ horz [text "label"; text x]; exp e ]]
      | EBreak (_, x, e) -> parens [hov 1 0 [ horz [text "break"; text x]; exp e ]]
      | ETryCatch (_, body, x, catch) ->
        parens [vert [ text "try"; exp body; 
                       parens [vert [ text "catch"; text x; exp body ]]]]
      | ETryFinally (_, body, finally) ->
        parens [vert [ text "try"; exp body;
                       parens [vert [ text "finally"; exp finally ]] ]]
      | EThrow (_, e) -> parens [vert [ text "throw"; exp e ]]
      | EPrefixOp (_, op, e) -> parens [vert [ text "prefix"; text op; exp e ]]
      | EInfixOp (_, op, e1, e2) -> parens [horz [ exp e1; text op; exp e2 ]]
      | ETypecast (_, t, e) ->
        parens [vert [ text "cast"; RTSetExt.p_set RT.pp t; exp e ]]
      | ERef (_, _, e) -> parens [hov 1 1 [ text "ref"; exp e ]]
      | EDeref (_, e) -> parens [hov 1 1 [ text "deref"; exp e ]]
      | ESetRef (_, e1, e2) -> parens [hov 1 1 [ text "set-ref!"; exp e1; exp e2 ]]
      | ESubsumption (_, t, e) ->
        parens [vert [ text "upcast"; parens [typ t]; exp e ]]
      | EDowncast (_, t, e) ->
        parens [vert [ text "downcast"; parens [typ t]; exp e ]]
      | ETypApp (_, e, t) -> parens [horz [ text "typ-app"; exp e; typ t ]]
      | ETypAbs (_, x, t, e) -> 
        parens [horz [ text "typ-abs"; text x; text "<:"; typ t; exp e ]]
      | ECheat (_, t, e) -> parens [hov 1 0 [horz [ text "cheat"; typ t]; exp e ]]
      | EParen (_, e) -> parens [hov 1 0 [ text "parens"; exp e ]]

    and fld (s, e) =
      parens [hov 1 0 [ horz[ text s; text ":"]; exp e ]]

    and bind (x, e) = 
      parens [horz [text x; exp e]]

    and rec_bind (x, t, e) = 
      parens [horz [text x; text ":"; typ t; exp e]]

  end


  let string_of_exp = FormatExt.to_string Pretty.exp

  let assigned_free_vars (e : exp) = 
    let rec exp : exp -> IdSet.t = function
      | EConst _ -> IdSet.empty
      | EBot _ -> IdSet.empty
      | EAssertTyp (_, _, e) -> exp e
      | EArray (_, es) -> IdSetExt.unions (map exp es)
      | EObject (_, fs) -> IdSetExt.unions (map (fun (_, e) -> exp e) fs)
      | EId _ -> IdSet.empty
      | EBracket (_, e1, e2) -> IdSet.union (exp e1) (exp e2)
      | EUpdate (_, e1, e2, e3) -> IdSetExt.unions [ exp e1; exp e2; exp e3 ]
      | EPrefixOp (_, _, e) -> exp e
      | EInfixOp (_, _, e1, e2) -> IdSet.union (exp e1) (exp e2)
      | EIf (_, e1, e2, e3) -> IdSetExt.unions [ exp e1; exp e2; exp e3 ]
      | EApp (_, e, es) -> IdSetExt.unions (map exp (e :: es))
      | EFunc (_, args, _, e) -> fold_right IdSet.remove args (exp e)
      | ELet (_, x, e1, e2) ->  IdSet.union (exp e1) (IdSet.remove x (exp e2))
      | ERec (_, binds, e) ->
        let (xs, es) = 
          fold_right (fun (x, _, e) (xs, es) -> (x::xs, e::es))
            binds ([], []) in
        fold_right IdSet.remove xs (IdSetExt.unions (map exp (e :: es)))
      | ESeq (_, e1, e2) -> IdSet.union (exp e1) (exp e2)
      | ELabel (_, _, e) -> exp e
      | EBreak (_, _, e) -> exp e
      | ETryCatch (_, e1, x, e2) -> IdSet.union (exp e1) (IdSet.remove x (exp e2))
      | ETryFinally (_, e1, e2) -> IdSet.union (exp e1) (exp e2)
      | EThrow (_, e) -> exp e
      | ETypecast (_, _, e) -> exp e
      | ERef (_, _, e) -> exp e
      | EDeref (_, e) -> exp e
      | ESetRef (_, EId (_, x), e) -> IdSet.add x (exp e)
      | ESetRef (_, e1, e2) -> IdSet.union (exp e1) (exp e2)
      | ESubsumption (_, _, e) -> exp e
      | EDowncast (_, _, e) -> exp e
      | ETypAbs (_, _, _, e) -> exp e
      | ETypApp (_, e, _) -> exp e
      | ECheat _ -> IdSet.empty
      | EParen (_, e) -> exp e
    in exp e

  let unique_ids (prog : exp) : exp * (string, string) Hashtbl.t = 
    let module H = Hashtbl in
    let ht : (string, string) H.t = H.create 200 in
    let name : id -> id =
      let next = ref 0 in
      fun old_name ->
        let new_name = "#" ^ (string_of_int !next) in
        H.add ht new_name old_name;
        incr next; 
        new_name in
    let find x env = 
      if IdMap.mem x env then IdMap.find x env
      else x (* assume global *) in
    let rec exp (env : id IdMap.t) = function
      | EConst (p, c) -> EConst (p, c)
      | EBot p -> EBot p
      | EAssertTyp (p, t, e) -> EAssertTyp (p, t, exp env e)
      | EArray (p, es) -> EArray (p, map (exp env) es)
      | EObject (p, flds) -> EObject (p, map (second2 (exp env)) flds)
      | EId (p, x) -> EId (p, find x env)
      | EBracket (p, e1, e2) -> EBracket (p, exp env e1, exp env e2)
      | EUpdate (p, e1, e2, e3) -> EUpdate (p, exp env e1, exp env e2, exp env e3)
      | EPrefixOp (p, op, e) -> EPrefixOp (p, op, exp env e)
      | EInfixOp (p, op, e1, e2) -> EInfixOp (p, op, exp env e1, exp env e2)
      | EIf (p, e1, e2, e3) -> EIf (p, exp env e1, exp env e2, exp env e3)
      | EApp (p, e, es) -> EApp (p, exp env e, map (exp env) es)
      | EFunc (p, xs, fi, e) ->
        let xs' = map name xs in
        EFunc (p, xs', fi, exp (List.fold_right2 IdMap.add xs xs' env) e)
      | ELet (p, x, e1, e2) ->
        let x' = name x in
        ELet (p, x', exp env e1, exp (IdMap.add x x' env) e2)
      | ERec (p, binds, body) ->
        let (xs, xs') =
          fold_right 
            (fun (x, _, _) (xs, xs') -> (x::xs, (name x)::xs'))
            binds ([], []) in
        let env = List.fold_right2 IdMap.add xs xs' env in
        ERec (p, map (fun (x, t, e) -> (find x env, t, exp env e)) binds,
              exp env body)
      | ESeq (p, e1, e2) -> ESeq (p, exp env e1, exp env e2)
      | ELabel (p, x,  e) -> ELabel (p, x, exp env e)
      | EBreak (p, x, e) -> EBreak (p, x, exp env e)
      | ETryCatch (p, e1, x, e2) ->
        let x' = name x in
        ETryCatch (p, exp env e1, x', exp env e2)
      | ETryFinally (p, e1, e2) -> ETryFinally (p, exp env e1, exp env e2)
      | EThrow (p, e) -> EThrow (p, exp env e)
      | ETypecast (p, s, e) -> ETypecast (p, s, exp env e)
      | ERef (p, k, e) -> ERef (p, k, exp env e)
      | EDeref (p, e) -> EDeref (p, exp env e)
      | ESetRef (p, e1, e2) -> ESetRef (p, exp env e1, exp env e2)
      | ESubsumption (p, t, e) -> ESubsumption (p, t, exp env e)
      | EDowncast (p, t, e) -> EDowncast (p, t, exp env e)
      | ETypAbs (p, x, t, e) -> ETypAbs (p, x, t, exp env e)
      | ETypApp (p, e, t) -> ETypApp (p, exp env e, t)
      | ECheat (p, t, e) -> ECheat (p, t, e)
      | EParen (p, e) -> EParen (p, exp env e)
    in (exp IdMap.empty prog, ht)

end







module type STATIC = sig
  type env
  type typ
  val static : env -> RTSet.t -> typ -> typ
end



(* module Typ = struct *)


(*   let rec forall_arrow (typ : TypImpl.typ) : (id list * TypImpl.typ) option = match typ with *)
(*     | TypImpl.TArrow _ -> Some ([], typ) *)
(*     | TypImpl.TForall (_, x, _, typ') -> begin match forall_arrow typ' with *)
(*       | None -> None *)
(*       | Some (xs, t) -> Some (x :: xs, t) *)
(*     end *)
(*     | TypImpl.TRec (_, x, t) -> forall_arrow (TypImpl.typ_subst x typ t) *)
(*     | _ -> None *)

(*   let rec match_func_typ (typ : TypImpl.typ) : (TypImpl.typ list * TypImpl.typ option * TypImpl.typ) option = match typ with *)
(*     | TypImpl.TForall (_, _, _, t) -> match_func_typ t *)
(*     | TypImpl.TArrow (args, varargs, ret) -> Some (args, varargs, ret) *)
(*     | _ -> None *)

(*   let is_present (fld : TypImpl.field) = match fld with *)
(*     | (_, TypImpl.Present, _) -> true *)
(*     | _ -> false *)

(* end *)

