(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "tag-parser.ml";;

 type var = 
   | VarFree of string
   | VarParam of string * int
   | VarBound of string * int * int;;
 
 type expr' =
   | Const' of constant
   | Var' of var
   | Box' of var
   | BoxGet' of var
   | BoxSet' of var * expr'
   | If' of expr' * expr' * expr'
   | Seq' of expr' list
   | Set' of expr' * expr'
   | Def' of expr' * expr'
   | Or' of expr' list
   | LambdaSimple' of string list * expr'
   | LambdaOpt' of string list * string * expr'
   | Applic' of expr' * (expr' list)
   | ApplicTP' of expr' * (expr' list);;
 
   let rec expr'_eq e1 e2 =
     match e1, e2 with
     | Const' Void, Const' Void -> true
     | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
     | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
     | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
     | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
     | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                               (expr'_eq th1 th2) &&
                                                 (expr'_eq el1 el2)
     | (Seq'(l1), Seq'(l2)
     | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
     | (Set'(var1, val1), Set'(var2, val2)
     | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                                (expr'_eq val1 val2)
     | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
        (List.for_all2 String.equal vars1 vars2) &&
          (expr'_eq body1 body2)
     | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
        (String.equal var1 var2) &&
          (List.for_all2 String.equal vars1 vars2) &&
            (expr'_eq body1 body2)
     | Applic'(e1, args1), Applic'(e2, args2)
     | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
      (expr'_eq e1 e2) &&
        (List.for_all2 expr'_eq args1 args2)
     | Box'(_), Box'(_) -> true
     | BoxGet'(_), BoxGet'(_) -> true
     | BoxSet'(_, v1), BoxSet'(_, v2) -> expr'_eq v1 v2 
     | _ -> false;;
   
                        
 exception X_syntax_error;;
 
 module type SEMANTICS = sig
   val run_semantics : expr -> expr'
   val annotate_lexical_addresses : expr -> expr'
   val annotate_tail_calls : expr' -> expr'
   val box_set : expr' -> expr'
 end;;
 
 module Semantics : SEMANTICS = struct
 
 (* HELPER FUNCTIONS *)
 
 (* Used to mainatain a global counter *)
 (* ----------------------------------- *)
 let glob_num = ref 0 ;;
 
 let count num =
     incr num;
     num;;
 let reset num = 
     num := 0;;
 
 
 (* get the next number *)
 let get_num()  =  
    !(count glob_num);;
   
 (* reset the global counter *)
 let reset_num() =
   reset glob_num;;
 (* ----------------------------------- *)
 
 
 
 (* ANNOTATE LEXICAL ADDR *)
 (* start with empty table *)
 (* table[i] ---> vars (means a string list) *)
 (* search from top of the table *)
 
 let rec an_lexical expr table = 
   match expr with
   | Const Void ->                     Const'(Void)
   | Const(Sexpr s) ->                 Const'(Sexpr s)
   | If(_test, _then, _else) ->        If'((an_lexical _test table), (an_lexical _then table), (an_lexical _else table)) 
   | Seq(_list) ->                     Seq'((List.map (fun e -> (an_lexical e table)) _list))
   | Set(_var, _val) ->                Set'((an_lexical _var table), (an_lexical _val table))
   | Def(_var, _val) ->                Def'((an_lexical _var table), (an_lexical _val table))
   | Or(_list) ->                      Or'((List.map (fun e -> (an_lexical e table)) _list))
   | Applic(_e, _args) ->              Applic'((an_lexical _e table) , (List.map (fun e -> (an_lexical e table)) _args))
   | LambdaSimple(_vars, _body) ->     
           LambdaSimple'(_vars, (an_lexical _body (_vars::table)))
   | LambdaOpt(_vars, _var, _body) ->  
           let all_vars = List.append _vars [_var] in
           LambdaOpt'(_vars, _var,(an_lexical _body (all_vars::table))) 
   | Var(s) -> (find_var s table (-1))
   
   and find_var name table i= 
     match table with
     | [] -> Var'(VarFree(name))
     | car :: cdr -> if (List.mem name car) 
                     then (if (i == -1) then Var'(VarParam(name, (get_index name car))) else Var'(VarBound(name,i,(get_index name car))))
                     else (find_var name cdr (i+1))
 
   and get_index name lst =
     match lst with
     | [] -> raise (Failure "not supposed to happen")
     | h :: t -> if name = h then 0 else 1 + get_index name t
 
 (* ANNOTATE TAIL CALLS *)
 (* start with in_tp false *)
 (* if Lambda' - call recursive with in_tp = true *)
 (* if Set' - The body of Set' is never in tail-position! *)
 (* if If' is in_tp - then & else are also in tail-position *)
 (* if Def' - never in tail-position! *)
 (* if Seq' / Or' is in_tp, whether explicit or implicit - last expr' in the sequence is also in_tp *)
 (* if Applic' expr' in_tp - ApplicTP' and reset the in_tp to FALSE*)
 (* Const' Var' - return as it is *)
 
 let rec an_tail expr in_tp = 
   match expr with
   | Const' Void ->                        Const'(Void)
   | Const'(Sexpr s) ->                    Const'(Sexpr s)
   | Var'(VarFree(name)) ->                Var'(VarFree(name))
   | Var'(VarParam(name, minor)) ->        Var'(VarParam(name, minor))
   | Var'(VarBound(name, major, minor)) -> Var'(VarBound(name, major, minor))
   | Set'(_var, _val) ->                   Set'((an_tail _var in_tp), (an_tail _val false))
   | Def'(_var, _val) ->                   Def'((an_tail _var false), (an_tail _val false))
   | LambdaSimple'(_vars, _body) ->        LambdaSimple'(_vars, (an_tail _body true))
   | LambdaOpt'(_vars, _var, _body) ->     LambdaOpt'(_vars, _var,(an_tail _body true))
 
   | If'(_test, _then, _else) -> 
             if in_tp  then If'((an_tail _test false), (an_tail _then true), (an_tail _else true))
                       else If'((an_tail _test in_tp), (an_tail _then in_tp), (an_tail _else in_tp))
 
   | Seq'(_list) ->   
             let last_element = List.nth _list (List.length _list -1) in 
             if in_tp 
             then Seq'((List.map (fun e -> if (e == last_element) then (an_tail e true) else (an_tail e false)) _list))
             else Seq'((List.map (fun e -> (an_tail e false)) _list))        
   
 
   | Or'(_list) ->                         
             let last_element = List.nth _list (List.length _list -1) in 
             if in_tp 
             then Or'((List.map (fun e -> if (e == last_element) then (an_tail e true) else (an_tail e false)) _list))
             else Or'((List.map (fun e -> (an_tail e false)) _list))             
 
   | Applic'(_e, _args) -> 
       if in_tp  then ApplicTP'((an_tail _e false) , (List.map (fun e -> (an_tail e false)) _args)) else
                 Applic'((an_tail _e false) , (List.map (fun e -> (an_tail e false)) _args))
 
   | _ -> raise X_syntax_error
 
 (* SET BOX *)
 (* vars_to_box = list of args known to be wraped in box *)
 (* vars_to_box = [["x",minor_of_x];["y":minor_of_y];["x":minor_of_x]] *)
 (* if Lambda-expr' - bools[i]       = vars[i] need to be boxed 
                        body_head      = if vars[i] need to be boxed then add Set-expr'
                        to_add         = the names of vars of this Lambda-expr' that need to be boxed
                        check if there was any var to box (because if not and the body was NOT a seq - call recursive only the body) 
                        if there is a var to be boxed       = Set_expr'_list(=body_head) + modified_body -- all of it in Seq
                        if no var to be boxed then call recursive only the body *)
                        
 
   let rec an_box expr vars_to_box= 
   match expr with
   | Const' Void ->                        Const'(Void)
   | Const'(Sexpr s) ->                    Const'(Sexpr s)
   | Var'(VarFree(name)) ->                Var'(VarFree(name))
   | Seq'(_list) ->                        Seq'((List.map (fun e -> (an_box e vars_to_box)) _list))
   | Or'(_list) ->                         Or'((List.map (fun e -> (an_box e vars_to_box)) _list))
   | Def'(_var, _val) ->                   Def'((an_box _var vars_to_box), (an_box _val vars_to_box))
   | Applic'(_e, _args)  ->                Applic'((an_box _e  vars_to_box) , (List.map (fun e -> (an_box e  vars_to_box)) _args)) 
   | ApplicTP'(_e, _args) ->               ApplicTP'((an_box _e  vars_to_box) , (List.map (fun e -> (an_box e  vars_to_box)) _args))
   | If'(_test, _then, _else) ->           If'((an_box _test vars_to_box), (an_box _then vars_to_box), (an_box _else vars_to_box))
 
   | Var'(VarParam(name, minor)) ->   
         if pvar_in_list name minor vars_to_box
         then BoxGet'(VarParam(name, minor))
         else Var'(VarParam(name, minor))
 
   | Var'(VarBound(name, major, minor)) -> 
         if bvar_in_list name major minor vars_to_box (-1)
         then BoxGet'(VarBound(name, major, minor))
         else Var'(VarBound(name, major, minor))
 
   | Set'((Var'(VarParam(name, minor))), _val)  -> 
       if pvar_in_list name minor vars_to_box
       then BoxSet'(VarParam(name, minor), (an_box _val vars_to_box))
       else Set'((Var'(VarParam(name, minor))), (an_box _val vars_to_box))
 
   |  Set'((Var'(VarBound(name, major, minor))), _val) -> 
       if bvar_in_list name major minor vars_to_box (-1)
       then BoxSet'(VarBound(name, major, minor),(an_box _val vars_to_box))
       else Set'((Var'(VarBound(name, major, minor))), (an_box _val vars_to_box))
 
   | Set'(_var, _val) -> Set'(_var, (an_box _val vars_to_box))         
 
   | LambdaSimple'(_vars, _body) -> 
       let bools = List.map (fun vname -> (box vname expr)) _vars in
 
       let head = List.map2 (fun v b -> if (b) then (Set'((Var'(VarParam(v, (get_index v _vars)))), (Box'(VarParam(v, (get_index v _vars)))))) else Const'(Void)) _vars bools in
       let body_head = List.filter (fun e -> match e with |Const'(Void) -> false | _-> true) head in
       
       let to_add = List.map  (fun v -> let idx = get_index v _vars in
                                           if (List.nth bools idx)
                                           then [v; (string_of_int idx)]
                                           else []
                                 ) _vars in
       let vars_idx_to_add = List.filter (fun ls -> ls != []) to_add in
   
 
       if List.mem true bools
       then LambdaSimple'(_vars, Seq'(List.append body_head [(an_box _body (List.append [vars_idx_to_add] vars_to_box))]))
       else LambdaSimple'(_vars, (an_box _body (List.append [[[]]] vars_to_box)))
        
   | LambdaOpt'(_vars, _var, _body) ->
       let all_vars = List.append _vars [_var] in
       let bools = List.map (fun vname -> (box vname expr)) all_vars in
 
       let head = List.map2 (fun v b -> if (b) then (Set'((Var'(VarParam(v, (get_index v all_vars)))), (Box'(VarParam(v, (get_index v all_vars)))))) else Const'(Void)) all_vars bools in
       let body_head = List.filter (fun e -> match e with |Const'(Void) -> false | _-> true) head in
       
       let to_add = List.map  (fun v -> let idx = get_index v all_vars in
                                           if (List.nth bools idx)
                                           then [v; (string_of_int idx)]
                                           else []
                                 ) all_vars in
       let vars_idx_to_add = List.filter (fun ls -> ls != []) to_add in
       
       if List.mem true bools
       then LambdaOpt'(_vars, _var, Seq'(List.append body_head [(an_box _body (List.append [vars_idx_to_add] vars_to_box))]))
       else LambdaOpt'(_vars, _var, (an_box _body (List.append [[[]]] vars_to_box)))
       
   | _ -> raise X_syntax_error
 
     and get_index name lst =
     match lst with
     | [] -> raise (Failure "not supposed to happen")
     | h :: t -> if name = h then 0 else 1 + get_index name t
 
   (* no need to up *)
   (* element in ls = ["NAME_OF_VAR", MINOR_INDEX] *)
     and pvar_in_list name minor ls =
     match ls with
     | [[]] :: cdr -> false
     | something :: cdr -> List.mem [name; string_of_int minor] something
     | _ -> false
 
   (* up (cdr major times) and search there *)
     and bvar_in_list name major minor ls i= 
     match ls with
     | something :: cdr ->
       if (i == major) 
       then List.mem [name; string_of_int minor] something
       else bvar_in_list name major minor cdr (i+1)
     | _ -> false
     
     (* the whole tree stuff *)
     and tree_for_lambda exp param = 
       let acc = ref [] in
       
       let rec tree_for_lambda_rec e parent =
         (* number all lambdas in exp *)
         match e with
         
         | Seq'(car::cdr) ->                     (tree_for_lambda_rec car parent);
                                                 (tree_for_lambda_rec (Seq'(cdr)) parent)
         
         | Or'(car::cdr)          ->            (tree_for_lambda_rec car parent);
                                                 (tree_for_lambda_rec (Or'(cdr)) parent)
                                                 
         | If'(_test, _then, _else) ->           (tree_for_lambda_rec _test parent);
                                                 (tree_for_lambda_rec _then parent);
                                                 (tree_for_lambda_rec _else parent);
                                                 
         | LambdaSimple'(_vars, _body)     ->    let lambda_id = get_num() in
                                                 (acc := (create_node parent lambda_id param e false) :: !acc);
                                                 if (not (lambda_has_param e param)) then (tree_for_lambda_rec _body lambda_id)
                                         
         | LambdaOpt'(_vars, _var, _body)  ->    let lambda_id = get_num() in
                                                 (acc := (create_node parent lambda_id param e false) :: !acc);
                                                 if (not (lambda_has_param e param)) then (tree_for_lambda_rec _body lambda_id)
     
         | Set'(_var, _val) ->                   (tree_for_lambda_rec _val parent)
         
         | Def'(_var, _val) ->                   (tree_for_lambda_rec _val parent)
     
         | ApplicTP' (expr, lst) ->              (tree_for_lambda_rec expr parent);
                                                 (tree_for_lambda_rec (Seq'(lst)) parent)
     
         | Applic' (expr, lst) ->                (tree_for_lambda_rec expr parent);
                                                 (tree_for_lambda_rec (Seq'(lst)) parent)
         | _  -> () in
       match exp with
       | LambdaSimple'(_vars, _body) ->              let lambda_id = get_num() in
                                                     (acc := (create_node 1 lambda_id param exp true) ::!acc);
                                                     (tree_for_lambda_rec _body lambda_id);
                                                     let ret_ls = !acc in
                                                     acc := [] ;
                                                     reset_num();
                                                     (List.rev ret_ls)
     
       | LambdaOpt'(_vars, _var, _body) ->           let lambda_id = get_num() in
                                                     (acc := (create_node 1 lambda_id param exp true) ::!acc);
                                                     (tree_for_lambda_rec _body lambda_id);
                                                     let ret_ls = !acc in
                                                     acc := [] ;
                                                     reset_num();
                                                     (List.rev ret_ls)
       | _ -> [(0, false, false, 0)]
     
     
       (* true - if the lambda has a param similar to 'param' *)
       and lambda_has_param lambda param =
         match lambda with
         | LambdaSimple'(_vars, _body) ->        (List.mem param _vars)
         | LambdaOpt'(_vars, _var, _body) ->     (List.mem param _vars)
         | _ -> false
     
       (* create a node for the tree, according to the lambda's body (lambda_num, read, write) *)
       and create_node parent_id new_id param lambda is_root =
         if ((lambda_has_param lambda param) && (not is_root)) then (new_id, false, false, parent_id)
         else
           match lambda with
           | LambdaSimple'(_vars, _body) ->       (new_id, (body_reads_param _body param), 
                                                 (body_writes_to_param _body param), parent_id) 
                                                 
                                                   
           | LambdaOpt'(_vars, _var, _body) ->     (new_id, (body_reads_param _body param), 
                                                   (body_writes_to_param _body param), parent_id)
           | _ -> (-1, false, false, parent_id)
     
       (* true if this body writes a value to 'param'  *)
       and body_writes_to_param _body param =
         let rec body_writes_to_param_rec body =
           match body with
           | Set'(Var'((VarBound(p, major, minor))), _val) -> if p = param then true else (body_writes_to_param_rec _val)
           | Set'(Var'((VarParam(p, minor))), _val) -> if p = param then true else (body_writes_to_param_rec _val)
           | Set'(Var'((VarFree(p))), _val) -> if p = param then true else (body_writes_to_param_rec _val)
           | Seq'(car::cdr) -> (body_writes_to_param_rec car) || (body_writes_to_param_rec (Seq'(cdr)))
           | Or'(car::cdr) -> (body_writes_to_param_rec car) || (body_writes_to_param_rec (Or'(cdr)))
           | ApplicTP' (expr, lst) -> (body_writes_to_param_rec expr) || (body_writes_to_param_rec (Seq'(lst)))
     
           | Applic' (expr, lst) ->   (body_writes_to_param_rec expr) || (body_writes_to_param_rec (Seq'(lst)))
           | If'(_test, _then, _else) ->  (body_writes_to_param_rec _test) ||   (body_writes_to_param_rec _then)  
                                                                           ||   (body_writes_to_param_rec _else) 
           | _ -> false in
         (body_writes_to_param_rec _body)
     
       (* true if this body reads the value of 'param'  *)
       and body_reads_param _body param =
         let rec body_reads_param_rec body=
           match body with
           | Var'(VarBound(p, major, minor)) -> if p = param then true else false
           | Var'(VarParam(p, minor)) -> if p = param then true else false
           | Var'(VarFree(p)) -> if p = param then true else false
           | Set'(Var'((VarFree(some_p))), _val) ->  (body_reads_param_rec _val)
           | Set'(Var'((VarParam(some_p, minor))), _val) ->  (body_reads_param_rec _val)
           | Set'(Var'((VarBound(some_p, major, minor))), _val) ->  (body_reads_param_rec _val)
           | ApplicTP' (expr, lst) -> (body_reads_param_rec expr) || (body_reads_param_rec (Seq'(lst)))
           | Applic' (expr, lst) ->   (body_reads_param_rec expr) || (body_reads_param_rec (Seq'(lst)))
           | If'(_test, _then, _else) ->  (body_reads_param_rec _test) ||   (body_reads_param_rec _then)  
                                                                       ||   (body_reads_param_rec _else) 
           | Seq'(car::cdr) -> (body_reads_param_rec car) || (body_reads_param_rec (Seq'(cdr)))
           | Or'(car::cdr) -> (body_reads_param_rec car) || (body_reads_param_rec (Or'(cdr)))
           | _ -> false in
         (body_reads_param_rec _body)
     
       (* return all possible pairs according to number of lambdas *)
       and get_all_pairs num_of_lambdas =    
         let pair_list = ref [] in
         for left = 1 to num_of_lambdas do
           for right = 1 to num_of_lambdas do
             if left != right then
               pair_list := (left, right) :: !pair_list
             else ();
           done
         done;    
         List.rev !pair_list
       
       
     
       and get_node_for_id tree lambda_id = 
         List.nth tree (lambda_id - 1)
     
       and lambda_writes_to_param tree lambda_id =
         let is_writing data =
           match data with
           | (id, read, true, parent) -> true
           | (id, read, false, parent) -> false  in
         is_writing (get_node_for_id tree lambda_id)
       
       and lambda_reads_param tree lambda_id =
         let is_reading data =
           match data with
           | (id, true, write, parent) -> true
           | (id, false, write, parent) -> false  in
         is_reading (get_node_for_id tree lambda_id)
       
       and get_parent_id_of node =
           match node with
           | (id, read, write, parent) -> parent    
     
       and have_shared_ancestor tree a b =
         let get_path_up tree id =
           let path = ref [] in
           let current = ref id in
           while (!current) != 1 do
             path := (!current) :: !path;
             current := (get_parent_id_of (get_node_for_id tree (!current)))
           done;
           !path in
         let path_a = get_path_up tree a in
         let path_b = get_path_up tree b in
         let together = List.append path_a path_b in
         if (List.length together) = (List.length (List.sort_uniq compare together))
         then false
         else true
     
     
     (* to box or not *)
     and box param lambda_exp =
           let tree = tree_for_lambda lambda_exp param in
           let last_node = (List.nth (List.rev tree) 0) in
           let num_lambdas = match last_node with | (id, read, write, parent) -> id in
           let pairs = get_all_pairs num_lambdas in
           let satisfies_1 tree pair =
             let a =   match pair with (a, b) -> a in
             let b =   match pair with (a, b) -> b in
             let read_a = (lambda_reads_param tree a) in
             let read_b = (lambda_reads_param tree b) in
             let write_a = (lambda_writes_to_param tree a) in
             let write_b = (lambda_writes_to_param tree b) in
             (read_a && write_b) || (write_a && read_b) in
           let satisfies_2 tree pair=
             let a =   match pair with (a, b) -> a in
             let b =   match pair with (a, b) -> b in
             (not (have_shared_ancestor tree a b)) in
           let to_box tree pair = 
             (satisfies_1 tree pair) && (satisfies_2 tree pair) in
           (List.length (List.filter (to_box tree) pairs) != 0);;
               
 
 let annotate_lexical_addresses e = an_lexical e [];;
 
 let annotate_tail_calls e = an_tail e false;;
 
 let box_set e = an_box e [];;
 
 let run_semantics expr =
   box_set
     (annotate_tail_calls
        (annotate_lexical_addresses expr));;
   
 end;; (* struct Semantics *)
 