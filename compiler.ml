#use "pc.ml";;
#use "reader.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen of string;;

    
(* the tag-parser *)

exception X_syntax of string;;

type var = 
  | Var of string;;

type lambda_kind =
  | Simple
  | Opt of string;;

type expr =
  | ScmConst of sexpr
  | ScmVarGet of var
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmOr of expr list
  | ScmVarSet of var * expr
  | ScmVarDef of var * expr
  | ScmLambda of string list * lambda_kind * expr
  | ScmApplic of expr * expr list;;

module type TAG_PARSER = sig
  val tag_parse : sexpr -> expr
end;;

module Tag_Parser : TAG_PARSER = struct
  open Reader;;
  
  let reserved_word_list =
    ["and"; "begin"; "cond"; "do"; "else"; "if"; "lambda";
     "let"; "let*"; "letrec"; "or"; "quasiquote"; "quote";
     "unquote"; "unquote-splicing"];;

  let rec scheme_list_to_ocaml = function
    | ScmNil -> ([], ScmNil)
    | ScmPair(car, cdr) ->
       ((fun (rdc, last) -> (car :: rdc, last))
          (scheme_list_to_ocaml cdr))  
    | rac -> ([], rac);;

  let is_reserved_word name = is_member name reserved_word_list;;

  let unsymbolify_var = function
    | ScmSymbol var -> var
    | _ -> raise (X_syntax "not a symbol");;

  let unsymbolify_vars = List.map unsymbolify_var;;

  let list_contains_unquote_splicing =
    ormap (function
        | ScmPair (ScmSymbol "unquote-splicing",
                   ScmPair (_, ScmNil)) -> true
        | _ -> false);;

  let rec macro_expand_qq = function
    | ScmNil -> ScmPair (ScmSymbol "quote", ScmPair (ScmNil, ScmNil))
    | (ScmSymbol _) as sexpr ->
       ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
    | ScmPair (ScmSymbol "unquote", ScmPair (sexpr, ScmNil)) -> sexpr
    | ScmPair (ScmPair (ScmSymbol "unquote",
                        ScmPair (car, ScmNil)),
               cdr) ->
       let cdr = macro_expand_qq cdr in
       ScmPair (ScmSymbol "cons", ScmPair (car, ScmPair (cdr, ScmNil)))
    | ScmPair (ScmPair (ScmSymbol "unquote-splicing",
                        ScmPair (sexpr, ScmNil)),
               ScmNil) ->
       sexpr
    | ScmPair (ScmPair (ScmSymbol "unquote-splicing",
                        ScmPair (car, ScmNil)), cdr) ->
       let cdr = macro_expand_qq cdr in
       ScmPair (ScmSymbol "append",
                ScmPair (car, ScmPair (cdr, ScmNil)))
    | ScmPair (car, cdr) ->
       let car = macro_expand_qq car in
       let cdr = macro_expand_qq cdr in
       ScmPair
         (ScmSymbol "cons",
          ScmPair (car, ScmPair (cdr, ScmNil)))
    | ScmVector sexprs ->
       if (list_contains_unquote_splicing sexprs)
       then let sexpr = macro_expand_qq
                          (scheme_sexpr_list_of_sexpr_list sexprs) in
            ScmPair (ScmSymbol "list->vector",
                     ScmPair (sexpr, ScmNil))
       else let sexprs = 
              (scheme_sexpr_list_of_sexpr_list
                 (List.map macro_expand_qq sexprs)) in
            ScmPair (ScmSymbol "vector", sexprs)
    | sexpr -> sexpr;;

  let rec macro_expand_and_clauses expr = function
    | [] -> expr
    | expr' :: exprs -> ScmPair (ScmSymbol "if",
                            ScmPair (expr, ScmPair (macro_expand_and_clauses expr' exprs, ScmPair (ScmBoolean(false), ScmNil))));;

    let rec macro_expand_cond_ribs ribs =
      match ribs with
      | ScmNil -> ScmVoid
      | ScmPair (ScmPair (ScmSymbol "else", exprs), ribs) ->
         ScmPair (ScmSymbol "begin", exprs)
      | ScmPair (ScmPair (expr,
                          ScmPair (ScmSymbol "=>",
                                   ScmPair (func, ScmNil))),
                 ribs) ->
         let remaining = macro_expand_cond_ribs ribs in
         ScmPair
           (ScmSymbol "let",
            ScmPair
              (ScmPair
                 (ScmPair (ScmSymbol "value", ScmPair (expr, ScmNil)),
                  ScmPair
                    (ScmPair
                       (ScmSymbol "f",
                        ScmPair
                          (ScmPair
                             (ScmSymbol "lambda",
                              ScmPair (ScmNil, ScmPair (func, ScmNil))),
                           ScmNil)),
                     ScmPair
                       (ScmPair
                          (ScmSymbol "rest",
                           ScmPair
                             (ScmPair
                                (ScmSymbol "lambda",
                                 ScmPair (ScmNil, ScmPair (remaining, ScmNil))),
                              ScmNil)),
                        ScmNil))),
               ScmPair
                 (ScmPair
                    (ScmSymbol "if",
                     ScmPair
                       (ScmSymbol "value",
                        ScmPair
                          (ScmPair
                             (ScmPair (ScmSymbol "f", ScmNil),
                              ScmPair (ScmSymbol "value", ScmNil)),
                           ScmPair (ScmPair (ScmSymbol "rest", ScmNil), ScmNil)))),
                  ScmNil)))
      | ScmPair (ScmPair (pred, exprs), ribs) ->
         let remaining = macro_expand_cond_ribs ribs in
         ScmPair (ScmSymbol "if",
                  ScmPair (pred,
                           ScmPair
                             (ScmPair (ScmSymbol "begin", exprs),
                              ScmPair (remaining, ScmNil))))
      | _ -> raise (X_syntax "malformed cond-rib");;
  
  let rec names_values = function
    | ScmNil -> ([], [])
    | ScmPair (ScmPair (name, ScmPair (value, ScmNil)), ribs) ->
      let (names, values) = names_values ribs in
      (name :: names, value :: values)
    | _ -> raise (X_syntax "Invalid let-rib structure");;
  
  let rec names_whatevers = function
    | ScmNil -> ([], [])
    | ScmPair (ScmPair (name, ScmPair ((ScmSymbol "'whatever"), ScmNil)), ribs) ->
      let (names, whatevers) = names_whatevers ribs in
      (name :: names, (ScmSymbol "'whatever") :: whatevers)
    | _ -> raise (X_syntax "Invalid let-rib structure");;

  let rec tag_parse sexpr =
    match sexpr with
    | ScmVoid | ScmBoolean _ | ScmChar _ | ScmString _ | ScmNumber _ ->
       ScmConst sexpr
    | ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil)) ->
      ScmConst sexpr
    | ScmPair (ScmSymbol "quasiquote", ScmPair (sexpr, ScmNil)) ->
       tag_parse (macro_expand_qq sexpr)
    | ScmSymbol var ->
       if (is_reserved_word var)
       then raise (X_syntax "Variable cannot be a reserved word")
       else ScmVarGet(Var var)
    | ScmPair (ScmSymbol "if",
               ScmPair (test, ScmPair (dit, ScmNil))) ->
       ScmIf(tag_parse test,
             tag_parse dit,
             tag_parse ScmVoid)
    | ScmPair (ScmSymbol "if",
               ScmPair (test, ScmPair (dit, ScmPair (dif, ScmNil)))) ->
       ScmIf(tag_parse test,
             tag_parse dit,
             tag_parse dif)
    | ScmPair (ScmSymbol "begin", ScmNil) -> ScmConst(ScmVoid)
    | ScmPair (ScmSymbol "begin", ScmPair (sexpr, ScmNil)) ->
       tag_parse sexpr
    | ScmPair (ScmSymbol "begin", sexprs) ->
       (match (scheme_list_to_ocaml sexprs) with
        | (sexprs', ScmNil) -> ScmSeq(List.map tag_parse sexprs')
        | _ -> raise (X_syntax "Improper sequence"))
    | ScmPair (ScmSymbol "or", ScmNil) -> ScmConst(ScmBoolean false)
    | ScmPair (ScmSymbol "or", sexprs) ->
       (match (scheme_list_to_ocaml sexprs) with
        | (sexprs', ScmNil) -> ScmOr(List.map tag_parse sexprs')
        | _ -> raise (X_syntax "invalid"))
    | ScmPair (ScmSymbol "set!",
               ScmPair (ScmSymbol var,
                        ScmPair (expr, ScmNil))) ->
       if (is_reserved_word var)
       then raise (X_syntax "cannot assign a reserved word")
       else ScmVarSet(Var var, tag_parse expr)
    | ScmPair (ScmSymbol "define", ScmPair (ScmPair (var, params), exprs)) ->
       tag_parse
         (ScmPair (ScmSymbol "define",
                   ScmPair (var,
                            ScmPair (ScmPair (ScmSymbol "lambda",
                                              ScmPair (params, exprs)),
                                     ScmNil))))
    | ScmPair (ScmSymbol "define",
               ScmPair (ScmSymbol var,
                        ScmPair (expr, ScmNil))) ->
       if (is_reserved_word var)
       then raise (X_syntax "cannot define a reserved word")
       else ScmVarDef(Var var, tag_parse expr)
    | ScmPair (ScmSymbol "lambda", ScmPair (params, exprs)) ->
       let expr = tag_parse (ScmPair(ScmSymbol "begin", exprs)) in
       (match (scheme_list_to_ocaml params) with
        | params, ScmNil -> ScmLambda(unsymbolify_vars params, Simple, expr)
        | params, ScmSymbol opt ->
           ScmLambda(unsymbolify_vars params, Opt opt, expr)
        | _ -> raise (X_syntax "invalid parameter list"))
        | ScmPair (ScmSymbol "let", ScmPair (ribs, exprs)) ->
          let (names, values) = names_values ribs in 
          let names = scheme_sexpr_list_of_sexpr_list names 
          and values = scheme_sexpr_list_of_sexpr_list values in
           tag_parse (ScmPair (ScmPair (ScmSymbol "lambda", ScmPair (names, exprs)), values))
        | ScmPair (ScmSymbol "let*", ScmPair (ScmNil, exprs)) ->
            tag_parse (ScmPair (ScmSymbol "let", ScmPair (ScmNil, exprs)))
        | ScmPair (ScmSymbol "let*", ScmPair (ScmPair (ScmPair (var, ScmPair (value, ScmNil)), ScmNil), exprs)) -> 
              tag_parse (ScmPair (ScmSymbol "let", 
                ScmPair (ScmPair (ScmPair (var, ScmPair (value, ScmNil)), ScmNil), exprs)))
        | ScmPair (ScmSymbol "let*", ScmPair (ScmPair (ScmPair (var, ScmPair (arg, ScmNil)), ribs), exprs)) -> 
          tag_parse (ScmPair (ScmSymbol "let",
                              ScmPair
                                (ScmPair
                                  (ScmPair (var,
                                            ScmPair (arg,
                                                      ScmNil)),
                                    ScmNil),
                                    ScmPair
                                    (ScmPair
                                       (ScmSymbol "let*",
                                       ScmPair
                                          (ribs,
                                          exprs)),
                                         ScmNil))))
        | ScmPair (ScmSymbol "letrec", ScmPair (ribs, exprs)) ->
          let (names, values) = names_values ribs in 
          let names_whatevers_ribs = List.fold_right(fun name ribs  -> ScmPair (ScmPair (name, ScmPair (ScmSymbol "'whatever", ScmNil)), ribs)) names ScmNil in
          let make_sets = List.map2 (fun el1 el2 -> ScmPair (ScmSymbol "set!",
                  ScmPair (el1, ScmPair (el2, ScmNil)))) names values in
          let sets_and_exprs = List.fold_right (fun car cdr -> ScmPair (car, cdr)) make_sets exprs in
            tag_parse (ScmPair (ScmSymbol "let", ScmPair (names_whatevers_ribs, sets_and_exprs)))
    | ScmPair (ScmSymbol "and", ScmNil) -> tag_parse (ScmBoolean(true))
    | ScmPair (ScmSymbol "and", exprs) ->
       (match (scheme_list_to_ocaml exprs) with
        | expr :: exprs, ScmNil ->
           tag_parse (macro_expand_and_clauses expr exprs)
        | _ -> raise (X_syntax "malformed and-expression"))
    | ScmPair (ScmSymbol "cond", ribs) ->
       tag_parse (macro_expand_cond_ribs ribs)
    | ScmPair (proc, args) ->
       let proc =
         (match proc with
          | ScmSymbol var ->
             if (is_reserved_word var)
             then raise (X_syntax "reserved word in proc position")
             else proc
          | proc -> proc) in
       (match (scheme_list_to_ocaml args) with
        | args, ScmNil ->
           ScmApplic (tag_parse proc, List.map tag_parse args)
        | _ -> raise (X_syntax "malformed application"))
    | sexpr -> raise (X_syntax (Printf.sprintf "Unknown form: \n%a\n" sprint_sexpr sexpr));;

    
end;; (* end of struct Tag_Parser *)

let rec sexpr_of_expr = function
  | ScmConst(ScmVoid) -> ScmVoid
  | ScmConst((ScmBoolean _) as sexpr) -> sexpr
  | ScmConst((ScmChar _) as sexpr) -> sexpr
  | ScmConst((ScmString _) as sexpr) -> sexpr
  | ScmConst((ScmNumber _) as sexpr) -> sexpr
  | ScmConst((ScmSymbol _) as sexpr)
    | ScmConst(ScmNil as sexpr)
    | ScmConst(ScmPair _ as sexpr)
    | ScmConst((ScmVector _) as sexpr) ->
     ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
  | ScmVarGet(Var var) -> ScmSymbol var
  | ScmIf(test, dit, ScmConst ScmVoid) ->
     let test = sexpr_of_expr test in
     let dit = sexpr_of_expr dit in
     ScmPair (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmNil)))
  | ScmIf(e1, e2, ScmConst (ScmBoolean false)) ->
     let e1 = sexpr_of_expr e1 in
     (match (sexpr_of_expr e2) with
      | ScmPair (ScmSymbol "and", exprs) ->
         ScmPair (ScmSymbol "and", ScmPair(e1, exprs))
      | e2 -> ScmPair (ScmSymbol "and", ScmPair (e1, ScmPair (e2, ScmNil))))
  | ScmIf(test, dit, dif) ->
     let test = sexpr_of_expr test in
     let dit = sexpr_of_expr dit in
     let dif = sexpr_of_expr dif in
     ScmPair
       (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmPair (dif, ScmNil))))
  | ScmOr([]) -> ScmBoolean false
  | ScmOr([expr]) -> sexpr_of_expr expr
  | ScmOr(exprs) ->
     ScmPair (ScmSymbol "or",
              scheme_sexpr_list_of_sexpr_list
                (List.map sexpr_of_expr exprs))
  | ScmSeq([]) -> ScmVoid
  | ScmSeq([expr]) -> sexpr_of_expr expr
  | ScmSeq(exprs) ->
     ScmPair(ScmSymbol "begin", 
             scheme_sexpr_list_of_sexpr_list
               (List.map sexpr_of_expr exprs))
  | ScmVarSet(Var var, expr) ->
     let var = ScmSymbol var in
     let expr = sexpr_of_expr expr in
     ScmPair (ScmSymbol "set!", ScmPair (var, ScmPair (expr, ScmNil)))
  | ScmVarDef(Var var, expr) ->
     let var = ScmSymbol var in
     let expr = sexpr_of_expr expr in
     ScmPair (ScmSymbol "define", ScmPair (var, ScmPair (expr, ScmNil)))
  | ScmLambda(params, Simple, expr) ->
     let params = scheme_sexpr_list_of_sexpr_list
                    (List.map (fun str -> ScmSymbol str) params) in
     let expr = sexpr_of_expr expr in
     ScmPair (ScmSymbol "lambda",
              ScmPair (params,
                       ScmPair (expr, ScmNil)))
  | ScmLambda([], Opt opt, expr) ->
     let expr = sexpr_of_expr expr in
     let opt = ScmSymbol opt in
     ScmPair
       (ScmSymbol "lambda",
        ScmPair (opt, ScmPair (expr, ScmNil)))
  | ScmLambda(params, Opt opt, expr) ->
     let expr = sexpr_of_expr expr in
     let opt = ScmSymbol opt in
     let params = List.fold_right
                    (fun param sexpr -> ScmPair(ScmSymbol param, sexpr))
                    params
                    opt in
     ScmPair
       (ScmSymbol "lambda", ScmPair (params, ScmPair (expr, ScmNil)))
  | ScmApplic (ScmLambda (params, Simple, expr), args) ->
     let ribs =
       scheme_sexpr_list_of_sexpr_list
         (List.map2
            (fun param arg -> ScmPair (ScmSymbol param, ScmPair (arg, ScmNil)))
            params
            (List.map sexpr_of_expr args)) in
     let expr = sexpr_of_expr expr in
     ScmPair
       (ScmSymbol "let",
        ScmPair (ribs,
                 ScmPair (expr, ScmNil)))
  | ScmApplic (proc, args) ->
     let proc = sexpr_of_expr proc in
     let args =
       scheme_sexpr_list_of_sexpr_list
         (List.map sexpr_of_expr args) in
     ScmPair (proc, args)
  | _ -> raise (X_syntax "Unknown form");;


  let string_of_expr expr =
    Printf.sprintf "%a" sprint_sexpr (sexpr_of_expr expr);;

  let print_expr chan expr =
    output_string chan
      (string_of_expr expr);;

  let print_exprs chan exprs =
    output_string chan
      (Printf.sprintf "[%s]"
          (String.concat "; "
            (List.map string_of_expr exprs)));;

  let sprint_expr _ expr = string_of_expr expr;;

  let sprint_exprs chan exprs =
    Printf.sprintf "[%s]"
      (String.concat "; "
         (List.map string_of_expr exprs));;


type app_kind = Tail_Call | Non_Tail_Call;;

type lexical_address =
  | Free
  | Param of int
  | Bound of int * int;;

type var' = Var' of string * lexical_address;;

type expr' =
  | ScmConst' of sexpr
  | ScmVarGet' of var'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmOr' of expr' list
  | ScmVarSet' of var' * expr'
  | ScmVarDef' of var' * expr'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmLambda' of string list * lambda_kind * expr'
  | ScmApplic' of expr' * expr' list * app_kind;;

module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_address : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val auto_box : expr' -> expr'
  val semantics : expr -> expr'  
end;; (* end of signature SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> Var' (name, Free)
        | Some(major, minor) -> Var' (name, Bound (major, minor)))
    | Some minor -> Var' (name, Param minor);;

  
  (* run this first *)
  let annotate_lexical_address =
    let rec run expr params env =
      match expr with
      | ScmConst sexpr -> ScmConst' sexpr
      | ScmVarGet (Var str) -> ScmVarGet' (tag_lexical_address_for_var str params env) 
      | ScmIf (test, dit, dif) -> ScmIf' (run test params env, run dit params env, run dif params env)
      | ScmSeq exprs -> ScmSeq' (List.map (fun exp-> run exp params env) exprs) 
      | ScmOr exprs -> ScmOr' (List.map (fun exp-> run exp params env) exprs) 
      | ScmVarSet(Var v, expr) -> ScmVarSet' (tag_lexical_address_for_var v params env,run expr params env)
      (* this code does not [yet?] support nested define-expressions *)
      | ScmVarDef(Var v, expr) -> ScmVarDef' (tag_lexical_address_for_var v params env,run expr params env)
      | ScmLambda (params', Simple, expr) -> ScmLambda' (params',Simple,run expr params' (params :: env))
      | ScmLambda (params', Opt opt, expr) -> ScmLambda' (params',Opt opt,run expr (params'@[opt]) (params :: env))
      | ScmApplic (proc, args) ->
         ScmApplic' (run proc params env,
                     List.map (fun arg -> run arg params env) args,
                     Non_Tail_Call)
    in
    fun expr ->
    run expr [] [];;

  (* run this second *)
  let annotate_tail_calls = 
    let rec run in_tail = function
      | (ScmConst' _) as orig -> orig
      | (ScmVarGet' _) as orig -> orig
      | ScmIf' (test, dit, dif) -> ScmIf'(run false test, run in_tail dit, run in_tail dif)
      | ScmSeq' [] -> ScmSeq'([])
      | ScmSeq' (expr :: exprs) -> ScmSeq' (runl in_tail expr exprs)
      | ScmOr' [] -> ScmOr'([])
      | ScmOr' (expr :: exprs) -> ScmOr' (runl in_tail expr exprs)
      | ScmVarSet' (var', expr') -> ScmVarSet'(var', run false expr')
      | ScmVarDef' (var', expr') -> ScmVarDef'(var', run false expr')
      | (ScmBox' _) as expr' -> expr'
      | (ScmBoxGet' _) as expr' -> expr'
      | ScmBoxSet' (var', expr') -> ScmBoxSet'(var', run false expr')
      | ScmLambda' (params, Simple, expr) -> ScmLambda'(params, Simple, run true expr)
      | ScmLambda' (params, Opt opt, expr) -> ScmLambda'(params, Opt opt, run true expr)
      | ScmApplic' (proc, args, app_kind) ->
         if in_tail
         then ScmApplic' (run false proc,
                          List.map (fun arg -> run false arg) args,
                          Tail_Call)
         else ScmApplic' (run false proc,
                          List.map (fun arg -> run false arg) args,
                          Non_Tail_Call)
    and runl in_tail expr = function
      | [] -> [run in_tail expr]
      | expr' :: exprs -> (run false expr) :: (runl in_tail expr' exprs)
    in
    fun expr' -> run false expr';;

  (* auto_box *)

  let copy_list = List.map (fun si -> si);;

  let combine_pairs =
    List.fold_left
      (fun (rs1, ws1) (rs2, ws2) -> (rs1 @ rs2, ws1 @ ws2))
      ([], []);;

  let find_reads_and_writes =
    let rec run name expr params env =
      match expr with
      | ScmConst' _ -> ([], [])
      | ScmVarGet' (Var' (_, Free)) -> ([], [])
      | ScmVarGet' (Var' (name', _) as v) ->
         if name = name'
         then ([(v, env)], [])
         else ([], [])
      | ScmBox' _ -> ([], [])
      | ScmBoxGet' _ -> ([], [])
      | ScmBoxSet' (_, expr) -> run name expr params env
      | ScmIf' (test, dit, dif) ->
         let (rs1, ws1) = (run name test params env) in
         let (rs2, ws2) = (run name dit params env) in
         let (rs3, ws3) = (run name dif params env) in
         (rs1 @ rs2 @ rs3, ws1 @ ws2 @ ws3)
      | ScmSeq' exprs ->
         combine_pairs
           (List.map
              (fun expr -> run name expr params env)
              exprs)
      | ScmVarSet' (Var' (_, Free), expr) -> run name expr params env
      | ScmVarSet' ((Var' (name', _) as v), expr) ->
         let (rs1, ws1) =
           if name = name'
           then ([], [(v, env)])
           else ([], []) in
         let (rs2, ws2) = run name expr params env in
         (rs1 @ rs2, ws1 @ ws2)
      | ScmVarDef' (_, expr) -> run name expr params env
      | ScmOr' exprs ->
         combine_pairs
           (List.map
              (fun expr -> run name expr params env)
              exprs)
      | ScmLambda' (params', Simple, expr) ->
         if (List.mem name params')
         then ([], [])
         else run name expr params' ((copy_list params) :: env)
      | ScmLambda' (params', Opt opt, expr) ->
         let params' = params' @ [opt] in
         if (List.mem name params')
         then ([], [])
         else run name expr params' ((copy_list params) :: env)
      | ScmApplic' (proc, args, app_kind) ->
         let (rs1, ws1) = run name proc params env in
         let (rs2, ws2) = 
           combine_pairs
             (List.map
                (fun arg -> run name arg params env)
                args) in
         (rs1 @ rs2, ws1 @ ws2)
    in
    fun name expr params ->
    run name expr params [];;

  let cross_product as' bs' =
    List.concat (List.map (fun ai ->
    List.map (fun bj -> (ai, bj)) bs')
      as');;

  let rec get_var_rib varName = function
  | [] -> raise (X_this_should_not_happen "var isnt in env")
  | rib :: env ->
    if (List.mem varName rib)
      then (rib)
      else get_var_rib varName env
  
  let is_equal_env varName env1 env2 = 
    (get_var_rib varName env1) == (get_var_rib varName env2)
  
  let should_box_var name expr params =
    let (reads, writes) = find_reads_and_writes name expr params in
    let corss_read_and_write = cross_product reads writes in
    let rec run = function 
      |[] -> false
      |((Var' (_, Param _), _), (Var' (_, Param _), _)) :: rest -> run rest
      |((Var' (_, Param _), _), (Var' (_, Bound _), _)) :: rest -> true
      |((Var' (_, Bound _), _), (Var' (_, Param _), _)) :: rest -> true
      |((Var' (_, Bound _), env1), (Var' (_, Bound _), env2)) :: rest -> 
        ((not (is_equal_env name env1 env2)) || (run rest))
      | _ :: rest -> run rest in
      run corss_read_and_write;;

  let box_sets_and_gets name body =
    let rec run expr =
      match expr with
      | ScmConst' _ -> expr
      | ScmVarGet' (Var' (_, Free)) -> expr
      | ScmVarGet' (Var' (name', _) as v) ->
         if name = name'
         then ScmBoxGet' v
         else expr
      | ScmBox' _ -> expr
      | ScmBoxGet' _ -> expr
      | ScmBoxSet' (v, expr) -> ScmBoxSet' (v, run expr)
      | ScmIf' (test, dit, dif) ->
         ScmIf' (run test, run dit, run dif)
      | ScmSeq' exprs -> ScmSeq' (List.map run exprs)
      | ScmVarSet' (Var' (_, Free) as v, expr') ->
         ScmVarSet'(v, run expr')
      | ScmVarSet' (Var' (name', _) as v, expr') ->
         if name = name'
         then ScmBoxSet' (v, run expr')
         else ScmVarSet' (v, run expr')
      | ScmVarDef' (v, expr) -> ScmVarDef' (v, run expr)
      | ScmOr' exprs -> ScmOr' (List.map run exprs)
      | (ScmLambda' (params, Simple, expr)) as expr' ->
         if List.mem name params
         then expr'
         else ScmLambda' (params, Simple, run expr)
      | (ScmLambda' (params, Opt opt, expr)) as expr' ->
         if List.mem name (params @ [opt])
         then expr'
         else ScmLambda' (params, Opt opt, run expr)
      | ScmApplic' (proc, args, app_kind) ->
         ScmApplic' (run proc, List.map run args, app_kind)
    in
    run body;;

  let make_sets =
    let rec run minor names params =
      match names, params with
      | [], _ -> []
      | name :: names', param :: params' ->
         if name = param
         then let v = Var' (name, Param minor) in
              (ScmVarSet' (v, ScmBox' v)) :: (run (minor + 1) names' params')
         else run (minor + 1) names params'
      | _, _ -> raise (X_this_should_not_happen
                        "no free vars should be found here")
    in
    fun box_these params -> run 0 box_these params;;

  let rec auto_box expr =
    match expr with
    | ScmConst' _ | ScmVarGet' _ | ScmBox' _ | ScmBoxGet' _ -> expr
    | ScmBoxSet' (v, expr) -> ScmBoxSet' (v, auto_box expr)
    | ScmIf' (test, dit, dif) ->
       ScmIf' (auto_box test, auto_box dit, auto_box dif)
    | ScmSeq' exprs -> ScmSeq' (List.map auto_box exprs)
    | ScmVarSet' (v, expr) -> ScmVarSet'(v, auto_box expr)
    | ScmVarDef' (v, expr) -> ScmVarDef'(v, auto_box expr)
    | ScmOr' exprs -> ScmOr'(List.map auto_box exprs)
    | ScmLambda' (params, Simple, expr') ->
       let box_these =
         List.filter
           (fun param -> should_box_var param expr' params)
           params in
       let new_body = 
         List.fold_left
           (fun body name -> box_sets_and_gets name body)
           (auto_box expr')
           box_these in
       let new_sets = make_sets box_these params in
       let new_body = 
         match box_these, new_body with
         | [], _ -> new_body
         | _, ScmSeq' exprs -> ScmSeq' (new_sets @ exprs)
         | _, _ -> ScmSeq'(new_sets @ [new_body]) in
       ScmLambda' (params, Simple, new_body)
    | ScmLambda' (params, Opt opt, expr') ->
      let box_these =
        List.filter
          (fun param-> should_box_var param expr' (params @ [opt]))
          (params @ [opt]) in
      let new_body = 
        List.fold_left
          (fun body name -> box_sets_and_gets name body)
          (auto_box expr')
          box_these in
      let new_sets = make_sets box_these (params @ [opt]) in
      let new_body = 
        match box_these, new_body with
        | [], _ -> new_body
        | _, ScmSeq' exprs -> ScmSeq' (new_sets @ exprs)
        | _, _ -> ScmSeq'(new_sets @ [new_body]) in
      ScmLambda' (params, Opt opt, new_body)
    | ScmApplic' (proc, args, app_kind) ->
       ScmApplic' (auto_box proc, List.map auto_box args, app_kind);;

  let semantics expr =
    auto_box
      ( annotate_tail_calls
         (annotate_lexical_address expr));;

end;; (* end of module Semantic_Analysis *)

let sexpr_of_var' (Var' (name, _)) = ScmSymbol name;;

let rec sexpr_of_expr' = function
  | ScmConst' (ScmVoid) -> ScmVoid
  | ScmConst' ((ScmBoolean _) as sexpr) -> sexpr
  | ScmConst' ((ScmChar _) as sexpr) -> sexpr
  | ScmConst' ((ScmString _) as sexpr) -> sexpr
  | ScmConst' ((ScmNumber _) as sexpr) -> sexpr
  | ScmConst' ((ScmSymbol _) as sexpr) ->
     ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
  | ScmConst'(ScmNil as sexpr) ->
     ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
  | ScmConst' ((ScmVector _) as sexpr) ->
     ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))      
  | ScmVarGet' var -> sexpr_of_var' var
  | ScmIf' (test, dit, ScmConst' ScmVoid) ->
     let test = sexpr_of_expr' test in
     let dit = sexpr_of_expr' dit in
     ScmPair (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmNil)))
  | ScmIf' (e1, e2, ScmConst' (ScmBoolean false)) ->
     let e1 = sexpr_of_expr' e1 in
     (match (sexpr_of_expr' e2) with
      | ScmPair (ScmSymbol "and", exprs) ->
         ScmPair (ScmSymbol "and", ScmPair(e1, exprs))
      | e2 -> ScmPair (ScmSymbol "and", ScmPair (e1, ScmPair (e2, ScmNil))))
  | ScmIf' (test, dit, dif) ->
     let test = sexpr_of_expr' test in
     let dit = sexpr_of_expr' dit in
     let dif = sexpr_of_expr' dif in
     ScmPair
       (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmPair (dif, ScmNil))))
  | ScmOr'([]) -> ScmBoolean false
  | ScmOr'([expr']) -> sexpr_of_expr' expr'
  | ScmOr'(exprs) ->
     ScmPair (ScmSymbol "or",
              scheme_sexpr_list_of_sexpr_list
                (List.map sexpr_of_expr' exprs))
  | ScmSeq' ([]) -> ScmVoid
  | ScmSeq' ([expr]) -> sexpr_of_expr' expr
  | ScmSeq' (exprs) ->
     ScmPair (ScmSymbol "begin", 
              scheme_sexpr_list_of_sexpr_list
                (List.map sexpr_of_expr' exprs))
  | ScmVarSet' (var, expr) ->
     let var = sexpr_of_var' var in
     let expr = sexpr_of_expr' expr in
     ScmPair (ScmSymbol "set!", ScmPair (var, ScmPair (expr, ScmNil)))
  | ScmVarDef' (var, expr) ->
     let var = sexpr_of_var' var in
     let expr = sexpr_of_expr' expr in
     ScmPair (ScmSymbol "define", ScmPair (var, ScmPair (expr, ScmNil)))
  | ScmLambda' (params, Simple, expr) ->
     let expr = sexpr_of_expr' expr in
     let params = scheme_sexpr_list_of_sexpr_list
                    (List.map (fun str -> ScmSymbol str) params) in
     ScmPair (ScmSymbol "lambda",
              ScmPair (params,
                       ScmPair (expr, ScmNil)))
  | ScmLambda' ([], Opt opt, expr) ->
     let expr = sexpr_of_expr' expr in
     let opt = ScmSymbol opt in
     ScmPair
       (ScmSymbol "lambda",
        ScmPair (opt, ScmPair (expr, ScmNil)))
  | ScmLambda' (params, Opt opt, expr) ->
     let expr = sexpr_of_expr' expr in
     let opt = ScmSymbol opt in
     let params = List.fold_right
                    (fun param sexpr -> ScmPair(ScmSymbol param, sexpr))
                    params
                    opt in
     ScmPair
       (ScmSymbol "lambda", ScmPair (params, ScmPair (expr, ScmNil)))
  | ScmApplic' (ScmLambda' (params, Simple, expr), args, app_kind) ->
     let ribs =
       scheme_sexpr_list_of_sexpr_list
         (List.map2
            (fun param arg -> ScmPair (ScmSymbol param, ScmPair (arg, ScmNil)))
            params
            (List.map sexpr_of_expr' args)) in
     let expr = sexpr_of_expr' expr in
     ScmPair
       (ScmSymbol "let",
        ScmPair (ribs,
                 ScmPair (expr, ScmNil)))
  | ScmApplic' (proc, args, app_kind) ->
     let proc = sexpr_of_expr' proc in
     let args =
       scheme_sexpr_list_of_sexpr_list
         (List.map sexpr_of_expr' args) in
     ScmPair (proc, args)
  (* for reversing macro-expansion... *)
  | _ -> raise X_not_yet_implemented;;


let string_of_expr' expr =
  Printf.sprintf "%a" sprint_sexpr (sexpr_of_expr' expr);;

let print_expr' chan expr =
  output_string chan
    (string_of_expr' expr);;

let print_exprs' chan exprs =
  output_string chan
    (Printf.sprintf "[%s]"
       (String.concat "; "
          (List.map string_of_expr' exprs)));;

let sprint_expr' _ expr = string_of_expr' expr;;

let sprint_exprs' chan exprs =
  Printf.sprintf "[%s]"
    (String.concat "; "
       (List.map string_of_expr' exprs));;

(* end-of-input *)
