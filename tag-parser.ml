(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "reader.ml";;
 
 type constant =
   | Sexpr of sexpr
   | Void
 
 type expr =
   | Const of constant
   | Var of string
   | If of expr * expr * expr
   | Seq of expr list
   | Set of expr * expr
   | Def of expr * expr
   | Or of expr list
   | LambdaSimple of string list * expr
   | LambdaOpt of string list * string * expr
   | Applic of expr * (expr list);;
 
 let rec expr_eq e1 e2 =
   match e1, e2 with
   | Const Void, Const Void -> true
   | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
   | Var(v1), Var(v2) -> String.equal v1 v2
   | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                             (expr_eq th1 th2) &&
                                               (expr_eq el1 el2)
   | (Seq(l1), Seq(l2)
     | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
   | (Set(var1, val1), Set(var2, val2)
     | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                              (expr_eq val1 val2)
   | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
      (List.for_all2 String.equal vars1 vars2) &&
        (expr_eq body1 body2)
   | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (List.for_all2 String.equal vars1 vars2) &&
          (expr_eq body1 body2)
   | Applic(e1, args1), Applic(e2, args2) ->
      (expr_eq e1 e2) &&
        (List.for_all2 expr_eq args1 args2)
   | _ -> false;;
   
                        
 exception X_syntax_error;;

 module type TAG_PARSER = sig
   val tag_parse_expression : sexpr -> expr
   val tag_parse_expressions : sexpr list -> expr list
 end;; (*signature TAG_PARSER*)
 
 module Tag_Parser : TAG_PARSER = struct  
 
 let reserved_word_list =
   ["and"; "begin"; "cond"; "define"; "else";
    "if"; "lambda"; "let"; "let*"; "letrec"; "or";
    "quasiquote"; "quote"; "set!"; "unquote";
    "unquote-splicing"];;  
 
 (* work on the tag parsier starts here *)
 (*-------- Helper Functions -------- *)
 (* form that should be macro-expanded *)
  let forms_to_expand = 
    ["quasiquote";"cond";"let";"let*";"letrec";"and"]
  
 (* return true if sym is a reserved SYMBOL *)
 let is_reserved sym =  List.mem sym reserved_word_list ;;
 (* True if the list has unique elements, False otherwise *)
 let list_unique ls =
    let unique = List.sort_uniq compare ls in
    (List.length ls) == (List.length unique);;
  (* INPUT: Pair (Pair (Symbol "a", Pair (Symbol "b", Pair (Symbol "c", Nil))) *)
  (* OUTPUT: ["a"; "b"; "c"] *)
  let rec make_stringlist = function
    | Nil -> []
    | Pair(Symbol(sym), rest) -> if (not(List.mem sym reserved_word_list)) then (sym::make_stringlist rest)
                                                                           else raise X_syntax_error
    | _->  raise X_syntax_error;;
  
  (* same as above, but for improper lists *)
  let rec make_stringlist_improper  = function
    | Symbol(sym) -> [sym]
    | Pair(Symbol(sym), rest) -> if (not(List.mem sym reserved_word_list)) then (sym::make_stringlist_improper rest)
                                                                           else raise X_syntax_error
    | _->    raise X_syntax_error;;

  (* input: list of stuff, output: tuple (list_of_all_but_last, last) *)
  let rec make_tuple_from_list ls =
      let sublist_for_lambda_opt ls2=
        let rev = List.rev ls2 in
        match rev with
        | []->[]
        | tail::head -> List.rev head in
      let get_last ls3 =
        List.hd (List.rev ls3) in
    match ls with
    |car::cdr -> let last = (get_last ls) in
                  if (List.length [last]) == 0 then raise X_syntax_error else      
                      ((sublist_for_lambda_opt ls), last)
    | _ ->  raise X_syntax_error;;
      
  (* turn a LIST into nested pairs. for using "vector" in quasiquote Expansion *)
  let rec make_list_to_pairs = function
  | [] -> Nil
  | car::cdr -> Pair(car,make_list_to_pairs cdr)
  (* | _->  raise X_syntax_error;; *)

  let rec make_sexprlist = function
    | Nil -> []
    | Pair(sexpr, rest) -> sexpr::make_sexprlist rest
    | _->  raise X_syntax_error;;
    
  (*  (Pair (Pair (Symbol "a", Pair (Number (Int 1), Nil)),
      Pair (Pair (Symbol "b", Pair (Number (Int 2), Nil)), Nil)), *)
  let rec make_symslist = function
  | Nil -> []
  | Pair(Pair (Symbol(sym), sexpr), rest) -> if (not(List.mem sym reserved_word_list)) then (sym::make_symslist rest) 
                                                                                        else raise X_syntax_error
  
  | _->  raise X_syntax_error;;
  
  let rec make_valslist = function
  | Nil -> []
  | Pair (Pair (Symbol(sym), Pair (sexpr, Nil)), rest) -> (sexpr::make_valslist rest) 
  | _->  raise X_syntax_error;;

  (* | Pair (Symbol "let", Pair (Pair (Pair (Symbol "a", Pair (Number (Int 1), Nil)),  Pair (Pair (Symbol "b", Pair (Number (Int 2), Nil)), Nil)),Pair (Symbol "a", Nil))) *)
  let rec make_sym = function
  | Nil -> []
  | (Pair(Symbol(sym), Pair(sexpr,rest))) -> if (not(List.mem sym reserved_word_list)) then (sym::make_sym rest)
                                                                                        else raise X_syntax_error
  | _->  raise X_syntax_error;;

  let rec make_val = function
  | Nil -> []
  | (Pair (Symbol(sym), Pair(sexpr,rest))) -> (sexpr::make_val rest)
  | _->  raise X_syntax_error;;

  (* for letrec *)
  let ls_to_pairs sexpr_ls = List.fold_right (fun a b -> Pair(a, b)) sexpr_ls Nil;;

  let rec make_var_ls = function
  | Nil -> []
  | (Pair(Symbol(sym), Pair(sexpr,rest))) -> Symbol(sym)::make_var_ls rest
  | _->  raise X_syntax_error;;

  let rec make_vars_ls = function
  | Nil -> []
  | Pair (Pair (Symbol(sym), Pair (sexpr, Nil)), rest) -> Symbol(sym)::make_vars_ls rest
  | _->  raise X_syntax_error;;

  let rec make_sym_with_whatever = function
  | Nil -> Nil
  | (Pair(Symbol(sym), Pair(sexpr,rest))) -> if (not(List.mem sym reserved_word_list)) 
                                             then (Pair(Symbol(sym), Pair(Pair (Symbol "quote", Pair (Symbol "whatever", Nil)), make_sym_with_whatever rest))) 
                                             else raise X_syntax_error
  | _->  raise X_syntax_error;;

  let rec make_symslist_with_whatever = function
  | Nil -> Nil
  | Pair (Pair (Symbol(sym), Pair (sexpr, Nil)), rest) -> if (not(List.mem sym reserved_word_list)) 
                                                          then Pair (Pair (Symbol(sym), Pair (Pair (Symbol "quote", Pair (Symbol "whatever", Nil)), Nil)), make_symslist_with_whatever rest)
                                             
                                             else raise X_syntax_error
  | _->  raise X_syntax_error;;
  
  (* disj Tag Parsers *)
  let disj_of_tp tp1 tp2 =
  fun s ->
  try (tp1 s)
  with X_syntax_error -> (tp2 s);;

let disj_list_of_tp tps =
  let tp_none _ = raise X_syntax_error in
   List.fold_right disj_of_tp tps tp_none;;

 (*-------- TagParser of an Sexpr -------- *)
 let rec tp_sexpr sexpr = 
   let tag_parsers = disj_list_of_tp [tp_constant; tp_variable;me_mit_define; tp_define; tp_quasiquote;
                                      tp_if;tp_cond ;tp_lambda_simple; tp_lambda_opt;tp_lambda_variadic; tp_applic;
                                      tp_or; tp_assignment; tp_seq;
                                       tp_and; tp_let; tp_let_star; tp_let_rec] in
   tag_parsers sexpr
 
   (* expand an if-then expression *)
   and expand_if _cond _then = 
       If(tp_sexpr _cond, tp_sexpr _then, Const(Void))
 
   (* Constant *)
   and tp_constant s =
     match s with
       | Bool(b)  -> Const(Sexpr(s))
       | Number(n) -> Const(Sexpr(s))
       | Char(c) -> Const(Sexpr(s))
       | String(str) -> Const(Sexpr(s))
       | Pair(Symbol("quote") ,Pair(e, Nil)) -> Const(Sexpr(e))
       | Nil -> Const(Void)
       | _  ->  raise X_syntax_error

   (* Variable *)
   (* Variables are literal symbols that are NOT reserved words *)
   and tp_variable s =
     match s with
      | Symbol(sym)-> if (not(is_reserved sym)) then Var(sym) else raise X_syntax_error
      | _  ->  raise X_syntax_error
 
   (* Conditionals: IF-THEN or IF-THEN-ELSE *)
    and tp_if s= 
      match s with
      (* if - then - else *)
      | Pair(Symbol("if"), Pair (_cond, Pair (_then, Pair (_else, Nil)))) -> If
                                                                            (tp_sexpr _cond, tp_sexpr _then,tp_sexpr _else)
      (* if - then -> expand *)
      | Pair(Symbol("if"), Pair (_cond as c, Pair (_then as t, Nil))) ->     (expand_if c t)
      | _->  raise X_syntax_error
    
    
    
    (* Micro expand a cond expression *)
    and me_cond s =
      match s with
      
      | Pair(Symbol("cond"), ribs) ->   (me_cond_rib ribs)
                                
                       
      | _ ->  
              raise X_syntax_error
    and make_let_for_cond expr_k expr_f rest_ribs=
          match rest_ribs with
          |Nil ->
              (Pair (Symbol("let"), Pair (Pair (Pair 
              (Symbol("value"), Pair 
              (expr_k, Nil)), Pair (Pair 
              (Symbol("f"), Pair (Pair 
              (Symbol("lambda"), Pair (Nil, Pair 
              (expr_f, Nil))), Nil)), Nil)), Pair (Pair 
              (Symbol("if"), Pair 
              (Symbol("value"), Pair (Pair (Pair 
              (Symbol("f"), Nil), Pair 
              (Symbol("value"), Nil)), Nil))), Nil))))
      

              
          |_ ->
         
            (Pair (Symbol("let"), Pair (Pair (Pair 
            (Symbol("value"), Pair 
            (expr_k, Nil)), Pair (Pair 
            (Symbol("f"), Pair (Pair 
            (Symbol("lambda"), Pair (Nil, Pair 
            (expr_f, Nil))), Nil)), Pair (Pair 
            (Symbol("rest"), Pair (Pair 
            (Symbol("lambda"), Pair (Nil, Pair (Pair 
            (Symbol("begin"), Pair 
            ((me_cond_rib rest_ribs), Nil)), Nil))), Nil)), Nil))), Pair (Pair 
            (Symbol "if", Pair 
            (Symbol "value", Pair (Pair (Pair 
            (Symbol "f", Nil), Pair 
            (Symbol "value", Nil)), Pair (Pair 
            (Symbol "rest", Nil), Nil)))), Nil))))
      
      

    and me_cond_rib s =
      match s with
      | Nil -> Nil
      | Pair(Pair(Symbol("else"),rest),Nil) -> 
                                                Pair(Symbol("begin"),rest)
      | Pair(Pair(expr_k, Pair(Symbol("=>"), Pair(expr_f,Nil))), rest) -> (make_let_for_cond expr_k expr_f rest)
      
      | Pair(Pair(test1, exprs), rest) -> 
                            (Pair(Symbol("if"),Pair(test1,   Pair(Pair(Symbol("begin"),exprs),Pair((me_cond_rib rest), Nil)))))
      | _ -> s
    (* Micro expand all ribs for cond expession *)
    and me_cond_ribs s=
      match s with
      | Nil -> s 
      | Pair(rib, rest) -> Pair((me_cond_rib rib), (me_cond_ribs s))
      | _ -> raise X_syntax_error
    
    and tp_cond s =
      match s with
      | Pair(Symbol("cond"), Pair(sexpr, rest)) ->(tp_sexpr (me_cond s))

      | _ -> 
              raise X_syntax_error
    

    and tp_quasiquote s =
      match s with
      | Pair(Symbol("quasiquote"), Pair(sexpr, Nil)) ->(tp_sexpr (me_quasiquote sexpr))

      | _ -> raise X_syntax_error


    (* (Pair(Symbol "quasiquote", Pair( Char '\n', Nil)))) *)
    and me_quasiquote s =
      match s with
      
      | Pair(Symbol("unquote"), Pair(sexpr, Nil)) -> sexpr
      | Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil)) ->  raise X_syntax_error
      | Nil -> Pair(Symbol("quote"),Pair(Nil,Nil))
      | Symbol(sym) -> Pair(Symbol("quote"),Pair(Symbol(sym),Nil))
      | Vector(v) ->Pair(Symbol("vector"), (make_list_to_pairs (List.map me_quasiquote v)))
                     
      (* Pair(Symbol("append"),Pair(sexpr, Pair((me_quasiquote b),Nil))) *)
      | Pair(Pair(Symbol("unquote-splicing"), Pair(sexpr,Nil)), b) -> Pair(Symbol("append"),Pair(sexpr, Pair((me_quasiquote b),Nil)))
      | Pair(a, Pair(Symbol("unquote-splicing"), Pair(sexpr,Nil))) -> Pair(Symbol("cons"),Pair((me_quasiquote a), Pair(sexpr,Nil)))
      | Pair(a, b) -> (*print_string "here\n";*)
                      Pair(Symbol("cons"),Pair((me_quasiquote a), Pair((me_quasiquote b), Nil )))
      | _->  s


   (* (define <name> <expr>) *)
   and tp_define s= 
      match s with
      | Pair(Symbol("define"), Pair(Symbol(sym), Pair(expr, Nil))) -> 
              if (is_reserved sym) || (expr == Nil) then raise X_syntax_error else
                Def((tp_variable (Symbol(sym))), (tp_sexpr expr))

      |_-> raise X_syntax_error
  
    
   (* micro expand mit_define into lambda *)
   and me_mit_define s= 
      match s with
      | Pair(Symbol("define"), Pair(Pair(Symbol(sym), arglist), body)) -> 
              (tp_define (Pair(Symbol("define"), Pair(Symbol(sym), Pair(Pair(Symbol("lambda"), Pair(arglist, body)),Nil)  ))))
      |_ -> raise X_syntax_error

   (* LambdaSimple Expressions *)
   (* (lambda ⟨arglist⟩ . (⟨expr⟩+)) *)
   and tp_lambda_simple s = 
      match s with
        | Pair (Symbol "lambda", Pair (_symlist, _body)) -> 
                let arglist = make_stringlist _symlist in
                if not(list_unique arglist) then raise X_syntax_error else
                let exprls = make_sexprlist _body in
                if List.length exprls == 0 then raise X_syntax_error else
                let exprls_tp = List.map tp_sexpr exprls in
                if List.length exprls_tp == 1 then LambdaSimple(arglist, List.nth exprls_tp 0)
                else LambdaSimple(arglist, Seq(exprls_tp))
              
        | _->  raise X_syntax_error

   (* LambdaOpt Expressions *)
   (* (lambda ⟨arglist⟩ . (⟨expr⟩+)) *)
   and tp_lambda_opt s = 
   match s with
    | Pair (Symbol "lambda", Pair (_symlist, _body)) -> 
            
            let arglist, opt =(make_tuple_from_list (make_stringlist_improper _symlist)) in
            
            if not(list_unique (opt::arglist)) then raise X_syntax_error else
            
            let sexprls = make_sexprlist _body in
            if List.length sexprls == 0 then raise X_syntax_error else
            let sexprls_tp = List.map tp_sexpr sexprls in
            if List.length sexprls_tp == 1 then LambdaOpt(arglist, opt,  List.nth sexprls_tp 0)
            else LambdaOpt(arglist, opt, Seq(sexprls_tp))
    | _->  raise X_syntax_error


   (* LambdaOpt Expressions *)
   (* (lambda ⟨arglist⟩ . (⟨expr⟩+)) *)
   and tp_lambda_variadic s = 
   match s with
    | Pair (Symbol "lambda", Pair (Symbol(opt), _body)) -> 
            let sexprls = make_sexprlist _body in
            if List.length sexprls == 0 then raise X_syntax_error else
            let sexprls_tp = List.map tp_sexpr sexprls in
            if List.length sexprls_tp == 1 then LambdaOpt([], opt,  List.nth sexprls_tp 0)
            else LambdaOpt([], opt, Seq(sexprls_tp))
    | _->  raise X_syntax_error


  (* Or *)
  (* 1. (or) -> [#f]  because its unit element *)
  (* 2. (or ⟨expr⟩) = [⟨expr⟩] *)
  (* 3. (or ⟨expr1⟩ ... ⟨exprn⟩) = Or([⟨expr1⟩; ... ; ⟨exprn⟩] *)
   and tp_or s = 
   match s with
   | Pair (Symbol "or", Nil) -> Const (Sexpr (Bool false))
   | Pair (Symbol "or", Pair(_sexpr, Nil)) -> tp_sexpr _sexpr
   | Pair (Symbol "or", ls_sexpr) -> 
            let arglist = make_sexprlist ls_sexpr in
            let arglist_expr = List.map tp_sexpr arglist in
            Or(arglist_expr)
   | _->  raise X_syntax_error
 
 (* Application *)
 (* (⟨expr⟩ ⟨expr1⟩ ... ⟨exprn⟩) = Applic(⟨expr⟩, [⟨expr1⟩; ... ;⟨exprn⟩]) *)
 and tp_applic s = 
 match s with 
 | Pair (_procedure, _args) ->
          Applic((tp_sexpr _procedure) ,(List.map tp_sexpr (make_sexprlist _args))) 
 | _->  raise X_syntax_error

  (* Assignment *)
 and tp_assignment s =
 match s with
 | Pair (Symbol "set!", Pair (_var, Pair (_val, Nil))) ->
         Set((tp_variable _var), (tp_sexpr) _val) 
 | _->  raise X_syntax_error

   (* Sequence *)
  and tp_seq s = 
  match s with
  | Pair (Symbol "begin", Nil) -> Const(Void)
  | Pair (Symbol "begin", Pair (_single, Nil)) -> (tp_sexpr _single)
  | Pair (Symbol "begin", _sexprs) -> 
        Seq(List.map tp_sexpr (make_sexprlist _sexprs))
  | _->  raise X_syntax_error

(* Macro Expansions *)
(* and *)
(* 1. (and) -> [#t]  because its unit element *)
(* 2. (and ⟨expr⟩) = [⟨expr⟩] *)
(* 3. (and ⟨expr1⟩⟨expr2⟩ ... ⟨exprn⟩) =If( ⟨expr1⟩ (and⟨expr2⟩ ...⟨exprn⟩) #f *)
and tp_and s =
match s with
| Pair (Symbol "and", Nil) -> Const (Sexpr (Bool true))
| Pair (Symbol "and", Pair(_sexpr, Nil)) -> (tp_sexpr _sexpr)
| Pair (Symbol "and", Pair(_sexpr1, _cdr)) ->
      If(tp_sexpr _sexpr1, tp_sexpr (Pair(Symbol "and", _cdr)) , Const (Sexpr (Bool false)))
| _->  raise X_syntax_error

(* Let *)
 (* (let ((v1 ⟨Expr1⟩) ... (vn ⟨Exprn⟩)) ⟨expr1⟩ ... ⟨exprm⟩) = ((lambda (v1 ... vn)⟨expr1⟩ ... ⟨exprm⟩) ⟨Expr1⟩ ... ⟨Exprn⟩) *)
and tp_let s = 
match s with 
| Pair (Symbol "let", Pair (Nil, _body)) -> 
      Applic( tp_lambda_simple (Pair (Symbol "lambda", Pair (Nil, _body))) , [])
| Pair (Symbol "let", Pair (Pair (_rib, _ribs), _body)) -> 
        let first_sym, first_val = make_sym _rib, make_val _rib in 
        let symslist, valslist = make_symslist _ribs, make_valslist _ribs in
        let vals_expr = List.map tp_sexpr (List.append first_val valslist) in
        let exprls = make_sexprlist _body in
        if List.length exprls == 0 then raise X_syntax_error else
        let exprls_tp = List.map tp_sexpr exprls in
        if List.length exprls_tp == 1 then Applic (LambdaSimple(List.append first_sym symslist,  (List.nth exprls_tp 0)), vals_expr)
        else Applic (LambdaSimple(List.append first_sym symslist, Seq(exprls_tp)), vals_expr)
| _->  raise X_syntax_error

(* Let Star *)
(* (let* () ⟨expr1⟩ ... ⟨exprm⟩) = let () ⟨expr1⟩ ... ⟨exprm⟩)*)
(* (let* ((v ⟨Expr⟩) ) ⟨expr1⟩ ... ⟨exprm⟩) = (let ((v Expr)) ⟨expr1⟩ ... ⟨exprm⟩) *)
(* (let* ( (v1 ⟨Expr1⟩ ) ... (vn ⟨Exprn⟩)) ⟨expr1⟩ ... ⟨exprm⟩) = 
(let ((v1⟨Expr1⟩)) (let* ((v2⟨Expr2⟩) ... (vn⟨Exprn⟩))⟨expr1⟩ ... ⟨exprm⟩)) *)
and tp_let_star s =
match s with
| Pair (Symbol "let*", Pair (Nil, _body)) -> 
      tp_sexpr (Pair (Symbol "let", Pair (Nil, _body)) )
| Pair (Symbol "let*", Pair (Pair (_rib, Nil), _body)) -> 
      tp_sexpr (Pair (Symbol "let", Pair (Pair (_rib, Nil), _body)))
| Pair (Symbol "let*", Pair (Pair ( _rib, _ribs), _body)) -> 
      tp_sexpr (Pair (Symbol "let", Pair (Pair (_rib, Nil), Pair (Pair (Symbol "let*", Pair (_ribs, _body)), Nil))))
             
| _->  raise X_syntax_error

(* Let Rec *)
(* (letrec ( (f1 ⟨Expr1⟩) (f2 ⟨Expr2⟩) ... (fn⟨Exprn⟩)) ⟨expr1⟩ ... ⟨exprm⟩) =
(let  ((f1 'whatever) (f2 'whatever) ... (fn 'whatever)) (set! f1 ⟨Expr1⟩) ... (set! fn ⟨Exprn⟩) ⟨expr1⟩ ...⟨exprm⟩)*)
and tp_let_rec s = 
match s with
| Pair (Symbol "letrec", Pair (Nil, _body)) ->
        tp_sexpr (Pair (Symbol "let", Pair (Nil, _body)))
| Pair (Symbol "letrec", Pair (Pair ( _rib, _ribs), _body)) -> 
        let rib_modified = make_sym_with_whatever _rib in
        let ribs_modified = make_symslist_with_whatever _ribs in 
        let vars = List.append (make_var_ls _rib) (make_vars_ls _ribs) in
        let vals = List.append (make_val _rib) (make_valslist _ribs) in
        let sets_body = List.map2 (fun var value -> Pair (Symbol "set!", Pair (var, Pair (value, Nil))) ) vars vals in
        let sexpr_body = make_sexprlist _body in
        let all_body = (ls_to_pairs (List.append sets_body sexpr_body)) in
        tp_sexpr (Pair (Symbol "let", Pair (Pair ( rib_modified, ribs_modified), all_body)))
 
| _->  raise X_syntax_error;;

(* ---------------------------- *)

 let tag_parse_expression sexpr = tp_sexpr sexpr;;
    
 let tag_parse_expressions sexpr = List.map tag_parse_expression sexpr;;
 
   
 end;;   (*struct Tag_Parser *)
