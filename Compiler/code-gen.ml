#use "compiler.ml";;
let file_to_string input_file =
  let in_channel = open_in input_file in
  let rec run () =
    try
      let ch = input_char in_channel in ch :: (run ())
    with End_of_file ->
      ( close_in in_channel;
	[] )
  in string_of_list (run ());;

let string_to_file output_file out_string =
  let out_channel = open_out output_file in
  ( output_string out_channel out_string;
    close_out out_channel );;
    let scm_number_eq n1 n2 =
      match n1, n2 with
      | ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
              numerator1 = numerator2 && denominator1 = denominator2
      | ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
      | _, _ -> false;;
    
    let rec sexpr_eq s1 s2 =
      match s1, s2 with
      | (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
      | ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
      | ScmChar(char1), ScmChar(char2) -> char1 = char2
      | ScmString(string1), ScmString(string2) -> String.equal string1 string2
      | ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
      | ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
      | ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
      | ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
      | _, _ -> false;;
    
      let reverse lst =
        let rec reverse_helper lst acc =
          match lst with
          | [] -> acc
          | hd :: tl -> reverse_helper tl (hd :: acc)
        in
        reverse_helper lst [];;
module type CODE_GENERATION =
  sig
    val compile_scheme_string : string -> string -> unit
    val compile_scheme_file : string -> string -> unit
  end;;

module Code_Generation : CODE_GENERATION= struct

  (* areas that raise this exception are NOT for the
   * final project! please leave these unimplemented,
   * as this will require major additions to your
   * compilers
   *)
  exception X_not_yet_supported;;

  let word_size = 8;;
  let label_start_of_constants_table = "L_constants";;
  let comment_length = 20;;

  let list_and_last =
    let rec run a = function
      | [] -> ([], a)
      | b :: s ->
         let (s, last) = run b s in
         (a :: s, last)
    in function
    | [] -> None
    | a :: s -> Some (run a s);;

  let split_to_sublists n = 
    let rec run = function
      | ([], _, f) -> [f []]
      | (s, 0, f) -> (f []) :: (run (s, n, (fun s -> s)))
      | (a :: s, i, f) ->
         (run (s, i - 1, (fun s -> f (a :: s))))
    in function
    | [] -> []
    | s -> run (s, n, (fun s -> s));;

    let remove_duplicates lst =
      let rec run lst expr_set =
        match lst with
        | expr::exprs ->
            if List.mem expr expr_set
            then run exprs expr_set
            else run exprs (expr_set @ [expr])
        | [] -> expr_set
      in
      run lst [];;
     let rec collect_constants =
      let rec run = function
        | ScmConst' s -> [s]
        | ScmBoxSet'(Var'(s, l), e) -> (run e)
        | ScmIf'(cond, dit, dif) -> (run cond) @ (run dit) @ (run dif)
        | ScmSeq'(expr_lst) -> List.flatten (List.map run expr_lst)
        | ScmVarSet'(Var'(s, l), e) -> (run e)
        | ScmVarDef'(Var'(s, l), e) -> (run e)
        | ScmOr'(expr_lst) -> List.flatten (List.map run expr_lst)
        | ScmLambda'(str_lst,_, body) -> List.map (fun name -> ScmSymbol name) str_lst @  (run body)
        | ScmApplic'(proc, expr_lst,_) -> List.flatten (List.map run ([proc] @ expr_lst))
        | other -> []
      and runs exprs' =
        List.fold_left
          (fun consts expr' -> consts @ (run expr'))
          []
          exprs'
      in runs;;

      let add_sub_constants =
        let rec run sexpr = match sexpr with
          | ScmVoid -> []
          | ScmNil -> []
          | ScmBoolean _ | ScmChar _ | ScmString _ | ScmNumber _ ->
             [sexpr]
          | ScmSymbol sym -> [ScmString sym; sexpr]
          | ScmPair (car, cdr) -> (run car) @ (run cdr) @ [sexpr]
          | ScmVector sexprs -> (runs sexprs) @ [sexpr]
        and runs sexprs =
          List.fold_left (fun full sexpr -> full @ (run sexpr)) [] sexprs
        in fun exprs' ->
           [ScmVoid; ScmNil; ScmBoolean false; ScmBoolean true; ScmChar '\000'] @ (runs exprs');;
    
  type initialized_data =
    | RTTI of string
    | Byte of int
    | ASCII of string
    | Quad of int
    | QuadFloat of float
    | ConstPtr of int;;

    let search_constant_address = 
      let rec run con = function
        | [] -> raise (X_this_should_not_happen
                        (Printf.sprintf
                           "The variable %s was not found in the constants table"
                           (string_of_sexpr con)))
        | (con', loc, _) :: _ when sexpr_eq con con' -> loc
        | _ :: table -> run con table
      in run;;

  let const_repr sexpr loc table = match sexpr with
    | ScmVoid -> ([RTTI "T_void"], 1)
    | ScmNil -> ([RTTI "T_nil"], 1)
    | ScmBoolean false ->
       ([RTTI "T_boolean_false"], 1)
    | ScmBoolean true ->
       ([RTTI "T_boolean_true"], 1)
    | ScmChar ch ->
       ([RTTI "T_char"; Byte (int_of_char ch)], 2)
    | ScmString str ->
       let count = String.length str in
       ([RTTI "T_string"; Quad count; ASCII str],
        1 + word_size + count)
    | ScmSymbol sym ->
       let addr = search_constant_address (ScmString sym) table in
       ([RTTI "T_symbol"; ConstPtr addr], 1 + word_size)
    | ScmNumber (ScmRational (numerator, denominator)) ->
       ([RTTI "T_rational"; Quad numerator; Quad denominator],
        1 + 2 * word_size)
    | ScmNumber (ScmReal x) ->
       ([RTTI "T_real"; QuadFloat x], 1 + word_size)
    | ScmVector s ->
       let addrs =
         List.map
           (fun si -> ConstPtr (search_constant_address si table)) s in
       let count = List.length s in
       ((RTTI "T_vector") :: (Quad count) :: addrs,
        1 + (count + 1) * word_size)
    | ScmPair (car, cdr) ->
       let (addr_car, addr_cdr) =
         (search_constant_address car table,
          search_constant_address cdr table) in
       ([RTTI "T_pair"; ConstPtr addr_car; ConstPtr addr_cdr],
        1 + 2 * word_size);;

  let make_constants_table =
    let rec run table loc = function
      | [] -> table
      | sexpr :: sexprs ->
          let (repr, len) = const_repr sexpr loc table in
          run (table @ [(sexpr, loc, repr)]) (loc + len) sexprs
    in
    fun exprs' ->
    run [] 0
      (remove_duplicates
          (add_sub_constants
            (remove_duplicates
                (collect_constants exprs'))));;  

  let asm_comment_of_sexpr sexpr =
    let str = string_of_sexpr sexpr in
    let str =
      if (String.length str) <= comment_length
      then str
      else (String.sub str 0 comment_length) ^ "..." in
    "; " ^ str;;

  let asm_of_representation sexpr =
    let str = asm_comment_of_sexpr sexpr in
    let run = function
      | [RTTI str] -> Printf.sprintf "\tdb %s" str
      | [RTTI "T_char"; Byte byte] ->
         Printf.sprintf "\tdb T_char, 0x%02X\t%s" byte str
      | [RTTI "T_string"; Quad length; ASCII const_str] ->
         Printf.sprintf "\tdb T_string\t%s\n\tdq %d%s"
           str length
           (let s = list_of_string const_str in
            let s = List.map
                      (fun ch -> Printf.sprintf "0x%02X" (int_of_char ch))
                      s in
            let s = split_to_sublists 8 s in
            let s = List.map (fun si -> "\n\tdb " ^ (String.concat ", " si)) s in
            String.concat "" s)
      | [RTTI "T_symbol"; ConstPtr addr] ->
         Printf.sprintf "\tdb T_symbol\t%s\n\tdq %s + %d"
           str label_start_of_constants_table addr
      | [RTTI "T_rational"; Quad numerator; Quad denominator] ->
         Printf.sprintf "\tdb T_rational\t%s\n\tdq %d, %d"
           str
           numerator denominator
      | [RTTI "T_real"; QuadFloat x] ->
         Printf.sprintf "\tdb T_real\t%s\n\tdq %f" str x
      | (RTTI "T_vector") :: (Quad length) :: addrs ->
         Printf.sprintf "\tdb T_vector\t%s\n\tdq %d%s"
           str length
           (let s = List.map
                      (function
                       | ConstPtr ptr ->
                          Printf.sprintf "%s + %d"
                            label_start_of_constants_table ptr
                       | _ -> raise
                               (X_this_should_not_happen
                                  "incorrect representation for a vector"))
                      addrs in
            let s = split_to_sublists 3 s in
            let s = List.map (fun si -> "\n\tdq " ^ (String.concat ", " si)) s in
            String.concat "" s)
      | [RTTI "T_pair"; ConstPtr car; ConstPtr cdr] ->
         Printf.sprintf "\tdb T_pair\t%s\n\tdq %s + %d, %s + %d"
           str
           label_start_of_constants_table car
           label_start_of_constants_table cdr
      | _ -> raise (X_this_should_not_happen "invalid representation!")
    in run;;

  let asm_of_constants_table =
    let rec run = function
      | [] -> ""
      | (sexpr, _, repr) :: rest ->
         (asm_of_representation sexpr repr) ^ "\n" ^ (run rest)
    in
    fun table ->
    Printf.sprintf "%s:\n%s"
      label_start_of_constants_table (run table);;

  let global_bindings_table =
    [ (* 1-10 *)
      ("null?", "L_code_ptr_is_null");
      ("pair?", "L_code_ptr_is_pair");
      ("void?", "L_code_ptr_is_void");
      ("char?", "L_code_ptr_is_char");
      ("string?", "L_code_ptr_is_string");
      ("symbol?", "L_code_ptr_is_symbol");
      ("vector?", "L_code_ptr_is_vector");
      ("procedure?", "L_code_ptr_is_closure");
      ("real?", "L_code_ptr_is_real");
      ("rational?", "L_code_ptr_is_rational");
      ("boolean?", "L_code_ptr_is_boolean");
      (* 11-20 *)
      ("number?", "L_code_ptr_is_number");
      ("collection?", "L_code_ptr_is_collection");
      ("cons", "L_code_ptr_cons");
      ("display-sexpr", "L_code_ptr_display_sexpr");
      ("write-char", "L_code_ptr_write_char");
      ("car", "L_code_ptr_car");
      ("cdr", "L_code_ptr_cdr");
      ("string-length", "L_code_ptr_string_length");
      ("vector-length", "L_code_ptr_vector_length");
      ("real->integer", "L_code_ptr_real_to_integer");
      (* 21-30*)
      ("exit", "L_code_ptr_exit");
      ("integer->real", "L_code_ptr_integer_to_real");
      ("rational->real", "L_code_ptr_rational_to_real");
      ("char->integer", "L_code_ptr_char_to_integer");
      ("integer->char", "L_code_ptr_integer_to_char");
      ("trng", "L_code_ptr_trng");
      ("zero?", "L_code_ptr_is_zero");
      ("integer?", "L_code_ptr_is_integer");
      ("__bin-apply", "L_code_ptr_bin_apply");
      ("__bin-add-rr", "L_code_ptr_raw_bin_add_rr");
      (* 31-40*)
      ("__bin-sub-rr", "L_code_ptr_raw_bin_sub_rr");
      ("__bin-mul-rr", "L_code_ptr_raw_bin_mul_rr");
      ("__bin-div-rr", "L_code_ptr_raw_bin_div_rr");
      ("__bin-add-qq", "L_code_ptr_raw_bin_add_qq");
      ("__bin-sub-qq", "L_code_ptr_raw_bin_sub_qq");
      ("__bin-mul-qq", "L_code_ptr_raw_bin_mul_qq");
      ("__bin-div-qq", "L_code_ptr_raw_bin_div_qq");
      ("error", "L_code_ptr_error");
      ("__bin-less-than-rr", "L_code_ptr_raw_less_than_rr");
      ("__bin-less-than-qq", "L_code_ptr_raw_less_than_qq");
      (* 41-50 *)
      ("__bin-equal-rr", "L_code_ptr_raw_equal_rr");
      ("__bin-equal-qq", "L_code_ptr_raw_equal_qq");
      ("quotient", "L_code_ptr_quotient");
      ("remainder", "L_code_ptr_remainder");
      ("set-car!", "L_code_ptr_set_car");
      ("set-cdr!", "L_code_ptr_set_cdr");
      ("string-ref", "L_code_ptr_string_ref");
      ("vector-ref", "L_code_ptr_vector_ref");
      ("vector-set!", "L_code_ptr_vector_set");
      ("string-set!", "L_code_ptr_string_set");
      (* 51-60 *)
      ("make-vector", "L_code_ptr_make_vector");
      ("make-string", "L_code_ptr_make_string");
      ("numerator", "L_code_ptr_numerator");
      ("denominator", "L_code_ptr_denominator");
      ("eq?", "L_code_ptr_eq")
    ];;

  let collect_free_vars =
    let rec run = function
      | ScmConst' _ -> []
      | ScmVarGet' (Var' (v, Free)) -> [v]
      | ScmVarGet' _ -> []
      | ScmIf' (test, dit, dif) -> (run test) @ (run dit) @ (run dif)
      | ScmSeq' exprs' -> runs exprs'
      | ScmOr' exprs' -> runs exprs'
      | ScmVarSet' (Var' (v, Free), expr') -> [v] @ (run expr')
      | ScmVarSet' (_, expr') -> run expr'
      | ScmVarDef' (Var' (v, Free), expr') -> [v] @ (run expr')
      | ScmVarDef' (_, expr') -> run expr'
      | ScmBox' (Var' (v, Free)) -> [v]
      | ScmBox' _ -> []
      | ScmBoxGet' (Var' (v, Free)) -> [v]
      | ScmBoxGet' _ -> []
      | ScmBoxSet' (Var' (v, Free), expr') -> [v] @ (run expr')
      | ScmBoxSet' (_, expr') -> run expr'
      | ScmLambda' (_, _, expr') -> run expr'
      | ScmApplic' (expr', exprs', _) -> (run expr') @  (runs exprs')
    and runs exprs' =
      List.fold_left
        (fun vars expr' -> vars @ (run expr'))
        []
        exprs'
    in fun exprs' ->
       let primitives =
         List.map
           (fun (scheme_name, _) -> scheme_name)
           global_bindings_table
       and free_vars_in_code = runs exprs' in
       remove_duplicates
         (primitives @ free_vars_in_code);;

  let make_free_vars_table =
    let rec run index = function
      | [] -> []
      | v :: vars ->
         let x86_label = Printf.sprintf "free_var_%d" index in
         (v, x86_label) :: (run (index + 1) vars)
    in fun exprs' -> run 0 (collect_free_vars exprs');;

  let search_free_var_table =
    let rec run v = function
      | [] -> raise (X_this_should_not_happen
                      (Printf.sprintf
                         "The variable %s was not found in the free-var table"
                         v))
      | (v', x86_label) :: _ when v = v' -> x86_label
      | _ :: table -> run v table
    in run;;

  let asm_of_global_bindings global_bindings_table free_var_table =
    String.concat "\n"
      (List.map
         (fun (scheme_name, asm_code_ptr) ->
           let free_var_label =
             search_free_var_table scheme_name free_var_table in
           (Printf.sprintf "\t; building closure for %s\n" scheme_name)
           ^ (Printf.sprintf "\tmov rdi, %s\n" free_var_label)
           ^ (Printf.sprintf "\tmov rsi, %s\n" asm_code_ptr)
           ^ "\tcall bind_primitive\n")
         global_bindings_table);;
  
  let asm_of_free_vars_table table =
    let tmp = 
      List.map
        (fun (scm_var, asm_label) ->
          Printf.sprintf "%s:\t; location of %s\n\tresq 1"
            asm_label scm_var)
        table in
    String.concat "\n" tmp;;

   let make_make_label prefix =
    let index = ref 0 in
    fun () ->
    (index := !index + 1;
     Printf.sprintf "%s_%04x" prefix !index);;

  let make_if_else = make_make_label ".L_if_else";;                                                    
  let make_if_end = make_make_label ".L_if_end";;
  let make_or_end = make_make_label ".L_or_end";;
  let make_lambda_simple_loop_env =                                                                
    make_make_label ".L_lambda_simple_env_loop";;
  let make_lambda_simple_loop_env_end =
    make_make_label ".L_lambda_simple_env_end";;
  let make_lambda_simple_loop_params =
    make_make_label ".L_lambda_simple_params_loop";;
  let make_lambda_simple_loop_params_end =
    make_make_label ".L_lambda_simple_params_end";;
  let make_lambda_simple_code = make_make_label ".L_lambda_simple_code";;
  let make_lambda_simple_end = make_make_label ".L_lambda_simple_end";;
  let make_lambda_simple_arity_ok =
    make_make_label ".L_lambda_simple_arity_check_ok";;
  let make_lambda_opt_loop_env =
    make_make_label ".L_lambda_opt_env_loop";;
  let make_lambda_opt_loop_env_end =
    make_make_label ".L_lambda_opt_env_end";;
  let make_lambda_opt_loop_params =
    make_make_label ".L_lambda_opt_params_loop";;
  let make_lambda_opt_loop_params_end =
    make_make_label ".L_lambda_opt_params_end";;
  let make_lambda_opt_code = make_make_label ".L_lambda_opt_code";;
  let make_lambda_opt_end = make_make_label ".L_lambda_opt_end";;
  let make_lambda_opt_arity_exact =
    make_make_label ".L_lambda_opt_arity_check_exact";;
  let make_lambda_opt_arity_more =
    make_make_label ".L_lambda_opt_arity_check_more";;
  let make_lambda_opt_stack_ok =
    make_make_label ".L_lambda_opt_stack_adjusted";;
  let make_lambda_opt_loop =
    make_make_label ".L_lambda_opt_stack_shrink_loop";;
  let make_lambda_opt_loop_exit =
    make_make_label ".L_lambda_opt_stack_shrink_loop_exit";;
  let make_lambda_opt_move_args =
    make_make_label ".L_lambda_opt_loop_move_args";;
  let make_lambda_opt_enlarge_loop =
    make_make_label ".L_lambda_opt_enalrge_copying_params_loop";;
  let make_tc_applic_recycle_frame_loop =
    make_make_label ".L_tc_recycle_frame_loop";;
  let make_tc_applic_recycle_frame_done =
    make_make_label ".L_tc_recycle_frame_done";;
  let make_opt_upwards =
    make_make_label ".L_opt_upward_loop";;

  let code_gen exprs' =
    let consts = make_constants_table exprs' in
    let free_vars = make_free_vars_table exprs' in
    let rec run params env = function
      | ScmConst' sexpr -> 
        ";Const\n"
        ^(Printf.sprintf
          "\tmov rax, %s+%d\n"
          label_start_of_constants_table (search_constant_address sexpr consts))
      | ScmVarGet' (Var' (v, Free)) ->
         let label = search_free_var_table v free_vars in
         Printf.sprintf
           "\tmov rax, qword [%s]\n"
           label
      | ScmVarGet' (Var' (v, Param minor)) ->
      (Printf.sprintf
          "\tmov rax, qword [rbp + %d * (4 + %d)]\n"
          word_size minor)
      | ScmVarGet' (Var' (v, Bound (major, minor))) ->
        (Printf.sprintf
        "\tmov rax, qword [rbp + %d * 2]\n\tmov rax, qword [rax + %d * %d]\n\tmov rax, qword [rax + %d * %d]\n"
        word_size word_size major word_size minor)
      | ScmIf' (test, dit, dif) -> 
        let label_else =  make_if_else ()
        and label_end = make_if_end () in
        (run params env test) ^
        (Printf.sprintf
          "\t cmp rax, sob_boolean_false\n\tje %s\n" label_else)
        ^(run params env dit)^
        (Printf.sprintf
          "\tjmp %s\n\t%s:" label_end label_else)
          ^(run params env dif)^
        (Printf.sprintf 
          "%s:\n" label_end)
      | ScmSeq' exprs' ->
         String.concat "\n"
           (List.map (run params env) exprs')
      | ScmOr' exprs' ->
         let label_end = make_or_end () in
         let asm_code =
           (match (list_and_last exprs') with
            | Some (exprs', last_expr') ->
               let exprs_code =
                 String.concat ""
                   (List.map
                      (fun expr' ->
                        let expr_code = run params env expr' in
                        expr_code
                        ^ "\tcmp rax, sob_boolean_false\n"
                        ^ (Printf.sprintf "\tjne %s\n" label_end))
                      exprs') in
               let last_expr_code = run params env last_expr' in
               exprs_code
               ^ last_expr_code
               ^ (Printf.sprintf "%s:\n" label_end)
            (* and just in case someone messed up the tag-parser: *)
            | None -> run params env (ScmConst' (ScmBoolean false)))
         in asm_code
      | ScmVarSet' (Var' (v, Free), expr') ->
        let label = search_free_var_table v free_vars in
        (run params env expr')
        ^ (Printf.sprintf "\tmov qword [%s], rax\n" label)
        ^ "\tmov rax, sob_void\n"
      | ScmVarSet'(Var' (v, Param minor), ScmBox' _ ) ->
          "\tmov rdi, 8\n"
          ^ "\tcall malloc\n"
          ^ (Printf.sprintf "\tmov rbx, PARAM(%d)\n" minor)
          ^ "\tmov qword[rax], rbx\n"
          ^ (Printf.sprintf "\tmov PARAM(%d), rax\n" minor)
          ^ "\tmov rax, sob_void\n"
      | ScmVarSet' (Var' (v, Param minor), expr') ->
        (run params env expr')^
        (Printf.sprintf
          "\n\tmov qword [rbp+%d*(4+%d)], rax\n\tmov rax, sob_void\n" word_size minor)
      | ScmVarSet' (Var' (v, Bound (major, minor)), expr') ->
        (run params env expr')^
        (Printf.sprintf
        "\n\tmov rbx,  qword[rbp + %d*2]\n\tmov rbx,  qword[rbx + %d* %d]\n\tmov qword[rbx + %d* %d], rax\n\tmov rax,  sob_void\n"
          word_size word_size major word_size minor)
      | ScmVarDef' (Var' (v, Free), expr') ->
         let label = search_free_var_table v free_vars in
         (run params env expr')
         ^ (Printf.sprintf "\tmov qword [%s], rax\n" label)
         ^ "\tmov rax, sob_void\n"
      | ScmVarDef' (Var' (v, Param minor), expr') ->
         raise X_not_yet_supported
      | ScmVarDef' (Var' (v, Bound (major, minor)), expr') ->
         raise X_not_yet_supported
      | ScmBox' (Var' (v, Param minor)) -> 
      (Printf.sprintf
          "\t%s\n
          \tmov rdi, %d\n
          \tcall malloc\n
          \tmov [rbx], rax\n
          \tmov rax, rbx\n" (run params env (ScmVarGet' (Var' (v, Param minor)))) word_size)
      | ScmBox' _ -> raise (X_this_should_not_happen
          (Printf.sprintf "The box _ should_not_happen"))
      | ScmBoxGet' var' ->
         (run params env (ScmVarGet' var'))
         ^ Printf.sprintf("\tmov rax, qword [rax]\n")
      | ScmBoxSet' (var', expr') -> 
          (run params env expr')^
          "\tpush rax\n"
          ^(run params env (ScmVarGet' var'))^
          "\tpop qword [rax]\n\tmov rax, sob_void\n"
      | ScmLambda' (params', Simple, body) ->
        let label_loop_env = make_lambda_simple_loop_env ()
        and label_loop_env_end = make_lambda_simple_loop_env_end ()
        and label_loop_params = make_lambda_simple_loop_params ()
        and label_loop_params_end = make_lambda_simple_loop_params_end ()
        and label_code = make_lambda_simple_code ()
        and label_arity_ok = make_lambda_simple_arity_ok ()
        and label_end = make_lambda_simple_end ()
        in
        ";Lambda Simple\n"
        ^"\tmov rdi, (1 + 8 + 8)\t; sob closure\n"
        ^ "\tcall malloc\n"
        ^ "\tpush rax\n"
        ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; new rib\n" params)
        ^ "\tcall malloc\n"
        ^ "\tpush rax\n"
        ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; extended env\n" (env + 1))
        ^ "\tcall malloc\n"
        ^ "\tmov rdi, ENV\n"
        ^ "\tmov rsi, 0\n"
        ^ "\tmov rdx, 1\n"
        ^ (Printf.sprintf "%s:\t; ext_env[i + 1] <-- env[i]\n"
              label_loop_env)
        ^ (Printf.sprintf "\tcmp rsi, %d\n" (env + 1))
        ^ (Printf.sprintf "\tje %s\n" label_loop_env_end)
        ^ "\tmov rcx, qword [rdi + 8 * rsi]\n"
        ^ "\tmov qword [rax + 8 * rdx], rcx\n"
        ^ "\tinc rsi\n"
        ^ "\tinc rdx\n"
        ^ (Printf.sprintf "\tjmp %s\n" label_loop_env)
        ^ (Printf.sprintf "%s:\n" label_loop_env_end)
        ^ "\tpop rbx\n"
        ^ "\tmov rsi, 0\n"
        ^ (Printf.sprintf "%s:\t; copy params\n" label_loop_params)
        ^ (Printf.sprintf "\tcmp rsi, %d\n" params)
        ^ (Printf.sprintf "\tje %s\n" label_loop_params_end)
        ^ "\tmov rdx, qword [rbp + 8 * rsi + 8 * 4]\n"
        ^ "\tmov qword [rbx + 8 * rsi], rdx\n"
        ^ "\tinc rsi\n"
        ^ (Printf.sprintf "\tjmp %s\n" label_loop_params)
        ^ (Printf.sprintf "%s:\n" label_loop_params_end)
        ^ "\tmov qword [rax], rbx\t; ext_env[0] <-- new_rib \n"
        ^ "\tmov rbx, rax\n"
        ^ "\tpop rax\n"
        ^ "\tmov byte [rax], T_closure\n"
        ^ "\tmov SOB_CLOSURE_ENV(rax), rbx\n"
        ^ (Printf.sprintf "\tmov SOB_CLOSURE_CODE(rax), %s\n" label_code)
        ^ (Printf.sprintf "\tjmp %s\n" label_end)
        ^ (Printf.sprintf "%s:\t; lambda-simple body\n" label_code)

        ^ (Printf.sprintf "\tcmp qword [rsp + 8 * 2], %d\n"
              (List.length params'))
        ^ (Printf.sprintf "\tje %s\n" label_arity_ok)
        ^ "\tpush qword [rsp + 8 * 2]\n"
        ^ (Printf.sprintf "\tpush %d\n" (List.length params'))
        ^ "\tjmp L_error_incorrect_arity_simple\n"
        ^ (Printf.sprintf "%s:\n" label_arity_ok)
        ^ "\tenter 0, 0\n"
        ^ (run (List.length params') (env + 1) body)
        ^ "\tleave\n"
        ^ (Printf.sprintf "\tret 8 * (2 + %d)\n" (List.length params'))
        ^ (Printf.sprintf "%s:\t; new closure is in rax\n" label_end)
      | ScmLambda' (params', Opt opt, body) ->
        let label_loop_env = make_lambda_opt_loop_env ()
        and label_loop_env_end = make_lambda_opt_loop_env_end ()
        and label_loop_params = make_lambda_opt_loop_params ()
        and label_loop_params_end = make_lambda_opt_loop_params_end ()
        and label_code = make_lambda_opt_code ()
        and label_end = make_lambda_opt_end ()
        and label_arity_exact = make_lambda_opt_arity_exact ()
        and label_arity_more = make_lambda_opt_arity_more ()
        and label_stack_ok = make_lambda_opt_stack_ok ()
        and label_opt_loop_exact = make_lambda_opt_loop ()
        and label_opt_loop_exit_exact = make_lambda_opt_loop_exit ()
        and label_opt_loop_more = make_lambda_opt_loop ()
        and label_opt_loop_exit_more = make_lambda_opt_loop_exit ()
        and label_opt_loop_more_update_stack = make_lambda_opt_loop ()
        and label_opt_loop_exit_more_update_stack = make_lambda_opt_loop_exit ()
        in
        ";Lambda Opt\n"
        ^"\tmov rdi, (1 + 8 + 8)\t; sob closure\n"
        ^ "\tcall malloc\n"
        ^ "\tpush rax\n"
        ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; new rib\n" params)
        ^ "\tcall malloc\n"
        ^ "\tpush rax\n"
        (*extended start*)
        ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; extended env\n" (env + 1))
        ^ "\tcall malloc\n"
        ^ "\tmov rdi, ENV\n"
        ^ "\tmov rsi, 0\n"
        ^ "\tmov rdx, 1\n"
        ^ (Printf.sprintf "%s:\t; ext_env[i + 1] <-- env[i]\n"
            label_loop_env)
        ^ (Printf.sprintf "\tcmp rsi, %d\n" (env))
        ^ (Printf.sprintf "\tje %s\n" label_loop_env_end)
        ^ "\tmov rcx, qword [rdi + 8 * rsi]\n"
        ^ "\tmov qword [rax + 8 * rdx], rcx\n"
        ^ "\tinc rsi\n"
        ^ "\tinc rdx\n"
        ^ (Printf.sprintf "\tjmp %s\n" label_loop_env)
        ^ (Printf.sprintf "%s:\n" label_loop_env_end)
        ^ "\tpop rbx\n"
        ^ "\tmov rsi, 0\n"
        ^ (Printf.sprintf "%s:\t; copy params\n" label_loop_params)
        ^ (Printf.sprintf "\tcmp rsi, %d\n" params)
        ^ (Printf.sprintf "\tje %s\n" label_loop_params_end)
        ^ "\tmov rdx, qword [rbp + 8 * rsi + 8 * 4]\n"
        ^ "\tmov qword [rbx + 8 * rsi], rdx\n"
        ^ "\tinc rsi\n"
        ^ (Printf.sprintf "\tjmp %s\n" label_loop_params)
        ^ (Printf.sprintf "%s:\n" label_loop_params_end)
        ^ "\tmov qword [rax], rbx\t; ext_env[0] <-- new_rib \n"
        ^ "\tmov rbx, rax\n"
        ^ "\tpop rax\n"
        (*extended env*)
        ^ "\tmov byte [rax], T_closure\n"
        ^ "\tmov SOB_CLOSURE_ENV(rax), rbx\n"
        ^ (Printf.sprintf "\tmov SOB_CLOSURE_CODE(rax), %s\n" label_code)
        ^ (Printf.sprintf "\tjmp %s\n" label_end)
        (*closuer body  start*)
        ^ (Printf.sprintf "%s:\t; lambda-opt body\n" label_code)
        (*update stack - start*)
        (* r8 <- argc *)
        ^ "\tmov r8, qword [rsp + 8*2]\n" 
        (* r9 <-- = parms.length = new argc = argc' *)
        ^ (Printf.sprintf "\tmov r9, %d\n" (List.length params' + 1))
        (* r13 <-- argc + 2*)
        ^ "\tlea r13, [r8 + 2] \n" 
        (*argc ? param length*)
        ^ (Printf.sprintf "\tcmp qword [rsp + 8 * 2], %d\n"
            (List.length params'))
        ^ (Printf.sprintf "\tje %s\n" label_arity_exact)
        ^ (Printf.sprintf "\tja %s\n" label_arity_more)
        (*argc < param length*)
        ^ "\tpush qword [rsp + 8 * 2]\n"
        ^ (Printf.sprintf "\tpush %d\n" (List.length params'))
        ^ "\tjmp L_error_incorrect_arity_opt\n"
        (*argc > param length*)
        ^ (Printf.sprintf "%s: ;More case\n" label_arity_more)
        ^ "\tmov r15, r8\n"
        ^ "\tsub r15, r9\n" (* r15 <-- argc - new argc*)
        ^ "\tlea rcx, [r15 + 1]\n" (* rcx <-- argc - new argc + 1*)
        (* pack the more args to list *)
        ^(Printf.sprintf "\tlea r12, [rsp + %d*r8 + %d*2]\n" word_size word_size)
        ^ "\tmov r11, sob_nil\n"
        ^ (Printf.sprintf "%s:\n" label_opt_loop_more)
        ^"\tcmp rcx, 0\n"
        ^ (Printf.sprintf "\tje %s\n" label_opt_loop_exit_more)
        ^(Printf.sprintf "\tmov rdi, %d\n" (1 + word_size + word_size))
        ^ "\tcall malloc\n"
        ^ "\tmov byte [rax], T_pair\n"
        ^ "\tmov rbx, qword [r12]\n"
        ^"\tmov qword [rax + 1], rbx\n"
        ^(Printf.sprintf "\tmov qword [rax + 1 + %d], r11\n" word_size)
        ^ "\tmov r11, rax\n"
        ^ (Printf.sprintf "\tsub r12, %d\n" word_size)
        ^"\tdec rcx\n"
        ^ (Printf.sprintf "\tjmp %s\n" label_opt_loop_more)
        ^ (Printf.sprintf "%s:\n" label_opt_loop_exit_more)
        (*Copy the other args to the stack and order the stack frame*)
        ^(Printf.sprintf "\tlea r10, [rsp + %d* %d + %d*3]\n" word_size (List.length params') word_size)
        ^"\tmov qword [r10], r11\n"
        ^ "\tlea r13, [8 * r13]\n"
        ^ "\tadd r13, rsp\n"
        ^ (Printf.sprintf "\tmov r14, %d\n" (List.length params' + 3))
        ^ (Printf.sprintf "\tmov rcx, 4 + %d\n" (List.length params'))
        ^ (Printf.sprintf "%s:\n" label_opt_loop_more_update_stack)
        ^"\tcmp rcx, 0\n"
        ^ (Printf.sprintf "\tje %s\n" label_opt_loop_exit_more_update_stack)
        ^ "\tmov r11, qword [r10]\n"
        ^ "\tmov qword [r13], r11\n"
        ^ (Printf.sprintf "\tsub r10, %d\n" word_size)
        ^ (Printf.sprintf "\tsub r13, %d\n" word_size)
        ^ "\tdec rcx\n"
        ^ (Printf.sprintf "\tjmp %s\n" label_opt_loop_more_update_stack)
        ^ (Printf.sprintf "%s:\n" label_opt_loop_exit_more_update_stack)
        ^ (Printf.sprintf "\tadd r13, %d\n" word_size)
        ^ "\tmov rsp, r13\n"
        ^ (Printf.sprintf "jmp %s\n" label_stack_ok)
        
        (*argc == param length*)
        ^ (Printf.sprintf "%s: ;Exact case\n" label_arity_exact)
        ^(Printf.sprintf "\tmov r8, qword [rsp -%d * 0]\n" word_size)
        ^(Printf.sprintf "\tmov qword [rsp -%d * 1], r8\n" word_size)
        ^(Printf.sprintf "\tmov r8, qword [rsp +%d * 1]\n" word_size)
        ^(Printf.sprintf "\tmov qword [rsp +%d * 0], r8\n" word_size)
        ^(Printf.sprintf "\tmov r8, qword [rsp +%d * 2]\n" word_size)
        ^"\tmov rcx, r8\n"
        ^"\tinc r8\n"
        ^(Printf.sprintf "\tmov qword [rsp +%d * 1], r8\n" word_size)
        ^ "\tmov rdx, rsp\n"
        ^"\tadd rdx, 24\n"
        ^ (Printf.sprintf "%s:\n" label_opt_loop_exact)
        ^"\tcmp rcx, 0\n"
        ^ (Printf.sprintf "\tje %s\n" label_opt_loop_exit_exact)
        ^"\tmov r8, [rdx]\n"
        ^(Printf.sprintf "\tmov qword [rdx -%d], r8\n" word_size)
        ^"\tadd rdx, 8\n"
        ^"\tdec rcx\n"
        ^ (Printf.sprintf "\tjmp %s\n" label_opt_loop_exact)
        ^ (Printf.sprintf "%s:\n" label_opt_loop_exit_exact)
        ^(Printf.sprintf "\tmov qword [rdx -%d], sob_nil\n" word_size)
        ^(Printf.sprintf "\tsub rsp, %d\n" word_size)
        (*Update stack - end*)
        ^ (Printf.sprintf "%s:\n" label_stack_ok)
        (*Update argc:*)
        ^ (Printf.sprintf "\tmov qword [rsp + 8*2], %d\n" (List.length params' + 1))
        ^ "\tenter 0, 0\n"
        ^ (run (List.length params' + 1) (env + 1) body)
        ^ "\tleave\n"
        ^ (Printf.sprintf "\tret 8 * (2 + %d)\n" (List.length params' + 1))
        ^ (Printf.sprintf "%s:\t; new closure is in rax\n" label_end) 
      | ScmApplic' (proc, args, Non_Tail_Call) -> 
          ";Applic - Non Tail Call\n"
          ^(String.concat ""
                     (List.map
                        (fun arg ->
                          (run params env arg)
                          ^ "\tpush rax\n")
                        (reverse args)))
          ^ (Printf.sprintf "\tpush %d\n" (List.length args))
          ^ (run params env proc)
          (*Verify that rax has type closure*)
          ^ "\tassert_closure(rax)\n"
          (*push rax→ env*)
          ^ "\tpush SOB_CLOSURE_ENV(rax)\n"
          (*call rax→ code*)
          ^ "\tcall SOB_CLOSURE_CODE(rax)\n"
      | ScmApplic' (proc, args, Tail_Call) ->
        let label_tc_applic_recycle_frame_loop = make_tc_applic_recycle_frame_loop ()
        and label_tc_applic_recycle_frame_done = make_tc_applic_recycle_frame_done () in
        ";Applic - Tail Call\n"
        ^(String.concat ""
                   (List.map
                      (fun arg ->
                        (run params env arg)
                        ^ "\tpush rax\n")
                      (reverse args)))
        ^ (Printf.sprintf "\tpush %d\n" (List.length args))
        ^ (run params env proc)
        (*Verify that rax has type closure*)
        ^ "\tassert_closure(rax)\n"
        (*push rax→ env*)
        ^ "\tpush SOB_CLOSURE_ENV(rax)\n"
        ^ (Printf.sprintf  "\tpush qword [rbp + %d * 1] ; old ret addr\n" word_size)
        ^ "\tpush qword [rbp]; same the old rbp\n"
        (*Fix stack - start*)
        ^(Printf.sprintf "\tmov rdi, qword [rbp +%d * 3]\n" word_size)
        ^(Printf.sprintf "\tlea rdi, [rbp + %d*rdi + %d*3] ; rdi point to the start old frame stack\n" word_size word_size)
        ^ (Printf.sprintf "\tmov rcx, 4 + %d\n" (List.length args))
        ^(Printf.sprintf "\tlea rsi, [rbp - %d] ; rsi point to the start new frame stack\n" word_size)        
        ^ (Printf.sprintf "%s:\n" label_tc_applic_recycle_frame_loop)
        ^"\tcmp rcx, 0\n"
        ^ (Printf.sprintf "\tje %s\n" label_tc_applic_recycle_frame_done)
        ^ "\tmov r10, qword [rsi]\n"
        ^ "\tmov qword [rdi], r10\n"
        ^ (Printf.sprintf "\tsub rdi, %d\n" word_size)
        ^ (Printf.sprintf "\tsub rsi, %d\n" word_size)
        ^ "\tdec rcx\n"
        ^ (Printf.sprintf "\tjmp %s\n" label_tc_applic_recycle_frame_loop)
        ^ (Printf.sprintf "%s:\n" label_tc_applic_recycle_frame_done)
        ^ (Printf.sprintf "\tlea rsp, [rdi + %d]\n" word_size)
        (*Fix stack - end*)
        ^ "\tpop rbp; restore the old rbp\n"
        ^ "\tjmp SOB_CLOSURE_CODE(rax)\n"
    and runs params env exprs' =
      List.map
        (fun expr' ->
          let code = run params env expr' in
          let code =
            code
            ^ "\n\tmov rdi, rax"
            ^ "\n\tcall print_sexpr_if_not_void\n" in
          code)
        exprs' in
    let codes = runs 0 0 exprs' in
    let code = String.concat "\n" codes in
    let code =
      (file_to_string "prologue-1.asm")
      ^ (asm_of_constants_table consts)
      ^ "\nsection .bss\n"
      ^ (asm_of_free_vars_table free_vars)
      ^ (file_to_string "prologue-2.asm")
      ^ (asm_of_global_bindings global_bindings_table free_vars)
      ^ "\n"
      ^ code
      ^ (file_to_string "epilogue.asm") in
    code;;

  let compile_scheme_string file_out user =
    let init = file_to_string "init.scm" in
    let source_code = init ^ user in
    let sexprs = (PC.star Reader.nt_sexpr source_code 0).found in
    let exprs = List.map Tag_Parser.tag_parse sexprs in
    let exprs' = List.map Semantic_Analysis.semantics exprs in
    let asm_code = code_gen exprs' in
    (string_to_file file_out asm_code;
     Printf.printf "!!! Compilation finished. Time to assemble!\n");;  

  let compile_scheme_file file_in file_out =
    compile_scheme_string file_out (file_to_string file_in);;

end;; (* end of Code_Generation struct *)

(* end-of-input *)

