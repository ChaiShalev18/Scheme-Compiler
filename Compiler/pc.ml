(* pc.ml
 * The new implementation of the parsing-combinators package for ocaml
 *
 * Prorammer: Mayer Goldberg, 2021
 *)

(* general list-processing procedures *)

let list_of_string string =
  let rec run i s =
    if i < 0 then s
    else run (i - 1) (string.[i] :: s) in
  run (String.length string - 1) [];;

let string_of_list s =
  List.fold_left
    (fun str ch -> str ^ (String.make 1 ch))
    ""
    s;;

let rec ormap f s =
  match s with
  | [] -> false
  | car :: cdr -> (f car) || (ormap f cdr);;

let rec andmap f s =
  match s with
  | [] -> true
  | car :: cdr -> (f car) && (andmap f cdr);;	  

module PC = struct

  type 'a parsing_result = {
      index_from : int;
      index_to : int;
      found : 'a
    };;

  type 'a parser = string -> int -> 'a parsing_result;;

  (* the parsing combinators defined here *)
  
  exception X_not_yet_implemented;;

  exception X_no_match;;

  let const pred =
    ((fun str index ->
      if (index < String.length str) && (pred str.[index])
      then {
          index_from = index;
          index_to = index + 1;
          found = str.[index]
        }
      else raise X_no_match) : 'a parser);;

  let caten (nt_1 : 'a parser) (nt_2 : 'b parser) =
    ((fun str index ->
      let {index_from = index_from_1;
           index_to = index_to_1;
           found = e_1} = (nt_1 str index) in
      let {index_from = index_from_2;
           index_to = index_to_2;
           found = e_2} = (nt_2 str index_to_1) in
      {index_from = index_from_1;
       index_to = index_to_2;
       found = (e_1, e_2)}) : (('a * 'b) parser));;

  let pack (nt : 'a parser) (f : 'a -> 'b) =
    ((fun str index -> 
      let {index_from; index_to; found} = (nt str index) in
      {index_from; index_to; found = (f found)})
     : 'b parser);;

  let nt_epsilon =
    ((fun str index ->
      {index_from = index;
       index_to = index;
       found = []}) : 'a parser);;

  let caten_list nts =
    List.fold_right
      (fun nt1 nt2 ->
        pack (caten nt1 nt2)
	  (fun (e, es) -> (e :: es)))
      nts
      nt_epsilon;;

  let disj (nt1 : 'a parser) (nt2 : 'a parser) =
    ((fun str index -> 
      try (nt1 str index)
      with X_no_match -> (nt2 str index)) : 'a parser);;

  let nt_none = ((fun _str _index -> raise X_no_match) : 'a parser);;
  
  let disj_list nts = List.fold_right disj nts nt_none;;

  let delayed (thunk : unit -> 'a parser) =
    ((fun str index -> thunk() str index) : 'a parser);;

  let nt_end_of_input str index = 
    if (index < String.length str)
    then raise X_no_match
    else {index_from = index; index_to = index; found = []};;

  let rec star (nt : 'a parser) =
    ((fun str index ->
      try let {index_from = index_from_1;
               index_to = index_to_1;
               found = e} = (nt str index) in
          let {index_from = index_from_rest;
               index_to = index_to_rest;
               found = es} = (star nt str index_to_1) in
          {index_from = index_from_1;
           index_to = index_to_rest;
           found = (e :: es)}
      with X_no_match -> {index_from = index; index_to = index; found = []})
     : 'a list parser);;

  let plus nt =
    pack (caten nt (star nt))
      (fun (e, es) -> (e :: es));;

  let rec power nt n =
    if n = 0 then nt_epsilon
    else pack(caten nt (power nt (n - 1)))
           (fun (e, es) -> e :: es);;    

  let at_least nt n =
    pack (caten (power nt n) (star nt))
      (fun (es_1, es_2) -> es_1 @ es_2);;

  let only_if (nt : 'a parser) pred =
    ((fun str index ->
      let ({index_from; index_to; found} as result) = (nt str index) in
      if (pred found) then result
      else raise X_no_match) : 'a parser);;

  let maybe (nt : 'a parser) =
    ((fun str index ->
      try let {index_from; index_to; found} = (nt str index) in
          {index_from; index_to; found = Some(found)}
      with X_no_match ->
        {index_from = index; index_to = index; found = None})
     : 'a option parser);;  

  let diff nt1 nt2 =
    ((fun str index ->
      match (maybe nt1 str index) with
      | {index_from; index_to; found = None} -> raise X_no_match
      | {index_from; index_to; found = Some(e)} ->
         match (maybe nt2 str index) with
         | {index_from = _; index_to = _; found = None} ->
            {index_from; index_to; found = e}
         | _ -> raise X_no_match) : 'a parser);;

  let followed_by (nt1 : 'a parser) (nt2 : 'b parser) =
    ((fun str index -> 
      let ({index_from; index_to; found} as result) = (nt1 str index) in
      let _ = (nt2 str index_to) in
      result) : 'a parser);;

  let not_followed_by (nt1 : 'a parser) (nt2 : 'b parser) =
    ((fun str index ->
      match (let ({index_from; index_to; found} as result) = (nt1 str index) in
	     try let _ = (nt2 str index_to) in
	         None
	     with X_no_match -> (Some(result))) with
      | None -> raise X_no_match
      | Some(result) -> result) : 'a parser);;
  
  (* useful general parsers for working with text *)

  let make_char equal ch1 = const (fun ch2 -> equal ch1 ch2);;

  let char = make_char (fun ch1 ch2 -> ch1 = ch2);;

  let char_ci =
    make_char (fun ch1 ch2 ->
	(Char.lowercase_ascii ch1) =
	  (Char.lowercase_ascii ch2));;

  let make_word char str = 
    List.fold_right
      (fun nt1 nt2 -> pack (caten nt1 nt2) (fun (a, b) -> a :: b))
      (List.map char (list_of_string str))
      nt_epsilon;;

  let word = make_word char;;

  let word_ci = make_word char_ci;;

  let make_one_of char str =
    List.fold_right
      disj
      (List.map char (list_of_string str))
      nt_none;;

  let one_of = make_one_of char;;

  let one_of_ci = make_one_of char_ci;;

  let nt_whitespace = const (fun ch -> ch <= ' ');;

  let make_range leq ch1 ch2 =
    const (fun ch -> (leq ch1 ch) && (leq ch ch2));;

  let range = make_range (fun ch1 ch2 -> ch1 <= ch2);;

  let range_ci =
    make_range (fun ch1 ch2 ->
	(Char.lowercase_ascii ch1) <=
	  (Char.lowercase_ascii ch2));;

  let nt_any = ((fun str index -> const (fun ch -> true) str index) : 'a parser);;

  let trace_pc desc (nt : 'a parser) =
    ((fun str index ->
      try let ({index_from; index_to; found} as value) = (nt str index)
          in
          (Printf.printf ";;; %s matched from char %d to char %d, leaving %d chars unread\n"
	     desc
	     index_from index_to
             ((String.length str) - index_to) ;
           value)
      with X_no_match ->
        (Printf.printf ";;; %s failed\n"
	   desc ;
         raise X_no_match)) : 'a parser);;

  (* testing the parsers *)

  let test_string (nt : 'a parser) str index =
    nt str index;;

  let search_forward (nt : 'a parser) str =
    let limit = String.length str in
    let rec run i =
      if (i < limit)
      then (match (maybe nt str i) with
            | {index_from; index_to; found = None} -> run (i + 1)
            | {index_from; index_to; found = Some(e)} ->
               {index_from; index_to; found = e})
      else raise X_no_match in
    run 0;; 

  let search_forward_all (nt : 'a parser) str =
    let limit = String.length str in
    let rec run i = 
      if (i < limit)
      then (match (maybe nt str i) with
            | {index_from; index_to; found = None} -> run (i + 1)
            | {index_from; index_to; found = Some(e)} ->
               {index_from; index_to; found = e} :: (run (i + 1)))
      else [] in
    run 0;;

  let search_backward (nt : 'a parser) str =
    let rec run i =
      if (-1 < i)
      then (match (maybe nt str i) with
            | {index_from; index_to; found = None} -> run (i - 1)
            | {index_from; index_to; found = Some(e)} ->
               {index_from; index_to; found = e})
      else raise X_no_match in
    run (String.length str - 1);; 

  let search_backward_all (nt : 'a parser) str =
    let limit = String.length str in
    let rec run i = 
      if (-1 < i)
      then (match (maybe nt str i) with
            | {index_from; index_to; found = None} -> run (i - 1)
            | {index_from; index_to; found = Some(e)} ->
               {index_from; index_to; found = e} :: (run (i - 1)))
      else [] in
    run (limit - 1);;

end;; (* end of struct PC *)

(* end-of-input *)
