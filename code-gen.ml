#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : (string * string) list-> expr' list ->  (string * int * string) list
  val generate : (constant * (int * string)) list -> (string * int * string) list -> expr' -> int -> int -> string
end;;


module Code_Gen : CODE_GEN = struct

(* Used to mainatain a global counter *)
(* ----------------------------------- *)
let glob_num = ref (-1) ;;

let count num =
    incr num;
    num;;
let reset num = 
    num := (-1);;
(* get the next number *)
let get_num()  =  
    !(count glob_num);;

(* reset the global counter *)
let reset_num() =
  reset glob_num;;


let undef = "MAKE_UNDEF" ;;
(* ----------------------------------- *)

(* tuple representation of a VarFree *)
let var_free_to_tuple var_free =
  let index = get_num() in
  match var_free with
  | Var'(VarFree(s)) -> (s, index, undef) 
  | _ -> ("bad", -1, "bad");;

let primitive_mapping_to_tuple primitive_mapping =
  let index = get_num() in
  match primitive_mapping with
  | (name, label) -> (name, index, label)

(* get a name list from a tuple list of VarFrees *)
let var_free_name_list table = 
  let name_of_tuple tuple =
    match tuple with
    | (name, index, value) -> name in
  List.map name_of_tuple table;;
(* boolean - true of the var_free_name already exists in table *)
let var_free_exists var_free_name table = 
  let name_list = (var_free_name_list table) in
  List.mem var_free_name name_list;;


(* create a compile time table (list) of FreeVars *)
let rec asts_to_internal_fvar_tbl names_to_labels asts = 
  (* turn primitives given into fvar table *)
  let rec primitives_to_internal_fvar_tbl names_to_labels =
    List.map primitive_mapping_to_tuple names_to_labels in
    let tuple_list = ref [] in
    let rec ast_to_fvar_tbl_rec sub_ast = 
        match sub_ast with
        | Var'(VarFree(s)) ->                   if (var_free_exists s (!tuple_list)) then () else
                                                (tuple_list := !tuple_list @ [(var_free_to_tuple sub_ast)])
                                                
                                                
            
        | Seq'(car::cdr) ->                     (ast_to_fvar_tbl_rec car ) ;
                                                (ast_to_fvar_tbl_rec (Seq'(cdr)) )
        
        | Or'(car::cdr)          ->            (ast_to_fvar_tbl_rec car ) ;
                                                (ast_to_fvar_tbl_rec (Or'(cdr)) )
                                                
        | If'(_test, _then, _else) ->           (ast_to_fvar_tbl_rec _test ) ;
                                                (ast_to_fvar_tbl_rec _then ) ;
                                                (ast_to_fvar_tbl_rec _else ) 
                                                
        | LambdaSimple'(_vars, _body)     ->    (ast_to_fvar_tbl_rec _body )
                                        
        | LambdaOpt'(_vars, _var, _body)  ->     (ast_to_fvar_tbl_rec _body )

        | Set'(_var, _val) ->                   (ast_to_fvar_tbl_rec _val )
        
        | Def'(_var, _val) ->                   (ast_to_fvar_tbl_rec _var );
                                                (ast_to_fvar_tbl_rec _val )

        | ApplicTP' (expr, lst) ->              (ast_to_fvar_tbl_rec expr ) ;
                                                (ast_to_fvar_tbl_rec (Seq'(lst)) )

        | Applic' (expr, lst) ->                (ast_to_fvar_tbl_rec expr ) ;
                                                (ast_to_fvar_tbl_rec (Seq'(lst)) )
        | BoxSet'(to_set, expr) ->              (ast_to_fvar_tbl_rec expr )  
        | _  -> () in
       (* ignore type unit - () warning*)
    tuple_list := (primitives_to_internal_fvar_tbl names_to_labels) @ !tuple_list;
    ignore (List.map ast_to_fvar_tbl_rec asts);
    reset_num();
    !tuple_list;;


  



let asts_to_fvar_tbl names_to_labels asts = 
  let table = (asts_to_internal_fvar_tbl names_to_labels asts) in

  table;;
(* ----------------------------------- *)

let compare_tuples t1 t2 = 
  match t1 with | (_,(i1,_)) -> (match t2 with | (_,(i2,_)) -> i1-i2);;

  let rec sexprs_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexprs_eq car1 car2) && (sexprs_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> 
  (if ((List.length l1) != (List.length l2)) 
  then false 
  else (List.for_all2 sexprs_eq l1 l2))
  | _ -> false;;

    (* -------- const eq func -------- *)
let rec const_eq e1 e2 =
  match e1, e2 with
  | Void, Void -> true
  | (Sexpr s1), (Sexpr s2) -> sexprs_eq s1 s2
  | _ -> false;;


 let rec remove_from_left ls set_ls= 
  match ls with
  | [] ->  set_ls
  | h :: t -> 
    if (List.exists (const_eq h) set_ls)
    then remove_from_left t set_ls
    else remove_from_left t (set_ls@[h])

let constant_table = ref [(Void, (0, "MAKE_VOID")); (Sexpr Nil, (1, "MAKE_NIL")); (Sexpr( Bool false), (2, "MAKE_BOOL(0)")); (Sexpr( Bool true), (4, "MAKE_BOOL(1)"))];;

(* ----------------------------------- *)
let rec create_const_tbl consts_ls i  =  
match consts_ls with
| [] -> !constant_table
| const :: rest -> 
    (let tuple = (create_tuple const i); in
    (match const with
      | Sexpr (Char c) ->               constant_table := !constant_table @ tuple ; create_const_tbl rest (i+1+1) 
      | Sexpr (String s) ->             constant_table := !constant_table @ tuple ; create_const_tbl rest (i+1+8+(String.length s))
      | Sexpr (Number (n)) ->           constant_table := !constant_table @ tuple ;create_const_tbl rest (i+1+8)
      | Sexpr (Symbol _sym) ->          constant_table := !constant_table @ tuple ; create_const_tbl rest (i+1+8)
      | Sexpr (Pair (_car, _cdr)) ->    constant_table := !constant_table @ tuple ; create_const_tbl rest (i+1+8+8)
      | Sexpr (Vector _elements) ->     constant_table := !constant_table @ tuple ; create_const_tbl rest (i+1+8+(8 * (List.length _elements)))
      | _ -> create_const_tbl rest i
    ))

and create_tuple const i = 
  match const with
  | Sexpr (Char c) ->             [(const, (i, "MAKE_LITERAL_CHAR(" ^ (string_of_int (int_of_char c)) ^ ")"))]
  | Sexpr (String s) ->           [(const, (i,  "MAKE_LITERAL_STRING_V " ^ (string_to_chars (string_to_list s))))]
  | Sexpr (Number ((Int n))) ->   [(const, (i, "MAKE_LITERAL_INT(" ^ (int_to_string n) ^ ")"))]
  | Sexpr (Number ((Float n))) -> [(const, (i, "MAKE_LITERAL_FLOAT(" ^ (float_to_string n) ^ ")" ))]
  | Sexpr (Symbol (_sym)) ->      [(const, (i, "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (string_of_int (get_offset_for_symbol (Sexpr (String _sym)) (!constant_table))) ^ ")"))]
  | Sexpr (Pair (_car, _cdr)) ->  [(const, (i, "MAKE_LITERAL_PAIR(const_tbl+" ^ (string_of_int (get_offset (Sexpr _car) (!constant_table))) ^ ", const_tbl+" ^ (string_of_int (get_offset (Sexpr _cdr) (!constant_table))) ^ ")" ))]
  | Sexpr (Vector _elements) ->   [(const, (i,  "MAKE_LITERAL_VECTOR " ^ (elements_to_string _elements)))]
  | _ -> [(const, ((-1), "not supposed to be in the table"))]


and string_to_chars ls = 
match ls with
| [] -> ""
| [c] -> (string_of_int (int_of_char c))
| h :: t -> 
  String.concat "" 
  [(string_of_int (int_of_char h))
  ^ ", " ^ (string_to_chars t)]

and elements_to_string elements =
match elements with
| [] -> ""
| [e] -> "const_tbl+" ^ (string_of_int (get_offset (Sexpr e) (!constant_table)))
| h :: t -> 
  String.concat "" 
  [("const_tbl+" ^ (string_of_int (get_offset (Sexpr h) (!constant_table)))
  ^ ", " ^ (elements_to_string t))]

and int_to_string n = 
  Printf.sprintf (format_of_string "%d") n

and float_to_string n = 
  Printf.sprintf (format_of_string "%f") n

and get_offset_for_symbol sym_as_str lst=
match lst with
| (something, (i, _)) :: rest -> if sym_as_str = something then i else get_offset_for_symbol sym_as_str rest
| _ -> raise (Failure "get_offset_for_symbol - NOT supposed to happen")

and get_offset sexpr lst = 
match lst with
| (something,(i,_)) :: rest -> if sexpr = something  then i else get_offset sexpr rest
| [] -> raise (Failure "get_offset - NOT supposed to happen")

let rec expand_with_subconst sexpr subconsts_ls =
match sexpr with
| Sexpr (Symbol (_sym)) ->       [(Sexpr (String (_sym)))]@subconsts_ls@[sexpr]
| Sexpr(Pair (_car, _cdr)) ->   
    let car_subs = expand_with_subconst (Sexpr _car) subconsts_ls in
    let cdr_subs = expand_with_subconst (Sexpr _cdr) subconsts_ls in
    car_subs@cdr_subs@[Sexpr _car]@[Sexpr _cdr]@subconsts_ls@[sexpr]
  
| Sexpr (Vector _elements_ls) ->
    let ls_of_subs = List.flatten (List.map (fun e -> expand_with_subconst (Sexpr e) subconsts_ls) _elements_ls) in
    ls_of_subs@subconsts_ls@[sexpr]
  
| _ -> subconsts_ls@[sexpr]


let rec collect_sexprs ast sexpr_ls=
  match ast with
  | Const' Void ->                      sexpr_ls
  | Const'(Sexpr s) ->                  sexpr_ls@[(Sexpr s)]
  | Set'(_var, _val) ->                 collect_sexprs _val sexpr_ls
  | BoxSet'(_var, _val) ->              collect_sexprs _val sexpr_ls
  | Def'(_var, _val) ->              
      let val_const = collect_sexprs _val sexpr_ls in
      sexpr_ls@val_const
  | LambdaSimple'(_vars, _body) ->      collect_sexprs _body sexpr_ls
  | LambdaOpt'(_vars, _var, _body) ->   collect_sexprs _body sexpr_ls
  | Seq'(_list) ->                      sexpr_ls@(List.flatten (List.map (fun e -> (collect_sexprs e sexpr_ls)) _list))
  | Or'(_list) ->                       sexpr_ls@(List.flatten (List.map (fun e -> (collect_sexprs e sexpr_ls)) _list))
  | Applic'(_e, _args)  ->              
        let const_from_e = collect_sexprs _e sexpr_ls in
        let const_from_args = (List.flatten (List.map (fun e -> (collect_sexprs e sexpr_ls)) _args)) in
        sexpr_ls@const_from_e@const_from_args
  
  | ApplicTP'(_e, _args)  ->        
        let const_from_e = collect_sexprs _e sexpr_ls in
        let const_from_args = (List.flatten (List.map (fun e -> (collect_sexprs e sexpr_ls)) _args)) in
        sexpr_ls@const_from_e@const_from_args
  | If'(_test, _then, _else) -> 
        let const_from_test = collect_sexprs _test sexpr_ls in
        let const_from_then = collect_sexprs _then sexpr_ls in
        let const_from_else = collect_sexprs _else sexpr_ls in
        sexpr_ls@const_from_test@const_from_then@const_from_else
  
  | _ -> sexpr_ls
  
let get_const_table asts =
let consts_ls = remove_from_left (List.flatten (List.map (fun ast -> collect_sexprs ast []) asts)) [] in
let expanded_const_ls = remove_from_left (List.flatten (List.map (fun const -> expand_with_subconst const []) consts_ls)) [] in
List.sort compare_tuples (create_const_tbl expanded_const_ls (4+2));;

(* ----------------------------------- *)

(* ----------------------------------- *)

let make_consts_tbl asts = get_const_table asts;;
let make_fvars_tbl primitive_names_to_labels asts = asts_to_fvar_tbl primitive_names_to_labels asts;; 

(* generate a label *)
let gen_label label_name =
  let num = get_num() in
  (label_name^(string_of_int num));;


  


  
  


let rec generate consts fvars e env_size num_of_args =

  match e with
  | Const' (c) -> 
      let tuple = List.find (fun (const,(_,_)) -> const_eq const c) consts in 
      let offset = (fun (_,(offset,_)) -> offset) tuple in
      Printf.sprintf "mov rax, const_tbl+%d\n" offset
  
  | Var' VarFree (name) -> 
      let tuple = List.find (fun (var_name, _, _) -> name = var_name) fvars in
      let index = ((fun (_, index, _) -> index) tuple) in
      Printf.sprintf "mov rax, [FVAR(%d)]\n" index

  | Var' VarParam(_, minor) ->
      "mov rax, qword [rbp + WORD_SIZE * (4 + "^ (string_of_int minor) ^")]\n"

  | Var' VarBound(_, major, minor) ->
      "mov rax, qword [rbp + WORD_SIZE * 2]\n" ^
      "mov rax, qword [rax + WORD_SIZE * " ^ (string_of_int major) ^ "]\n" ^
      "mov rax, qword [rax + WORD_SIZE * " ^ (string_of_int minor) ^ "]\n" 

  | BoxGet' (VarFree (name) ) -> 
      (generate consts fvars (Var'(VarFree (name))) env_size num_of_args) ^
      "mov rax, qword [rax]\n"

  | BoxGet' (VarBound (name, major, minor)) -> 
      (generate consts fvars (Var'(VarBound (name, major, minor))) env_size num_of_args) ^
      "mov rax, qword [rax]\n"
      
  | BoxGet' (VarParam(name, minor)) -> 
      (generate consts fvars (Var' (VarParam(name, minor))) env_size num_of_args) ^
      "mov rax, qword [rax]\n"    
  
  
  | Set'((Var' VarFree (name)), _val) ->
      let tuple = List.find (fun (var_name, _, _) -> name = var_name) fvars in
      let index = ((fun (_, index, _) -> index) tuple) in
      (generate consts fvars _val env_size num_of_args) ^ "\n" ^
      "mov qword [FVAR(" ^ (string_of_int index) ^ ")], rax\n" ^
      "mov rax, SOB_VOID_ADDRESS\n"

  | Set'((Var' VarBound (name, major, minor)), _val) ->
      (generate consts fvars _val env_size num_of_args) ^ "\n" ^
      "mov rbx, qword [rbp + WORD_SIZE * 2]\n" ^
      "mov rbx, qword [rbx + WORD_SIZE * " ^ (string_of_int major) ^ "]\n" ^
      "mov qword [rbx + WORD_SIZE * " ^ (string_of_int minor) ^ "], rax \n" ^
      "mov rax, SOB_VOID_ADDRESS\n"

  | Set'(Var'(VarParam(_, minor)), _val) ->
      (generate consts fvars _val env_size num_of_args) ^"\n" ^
      "mov qword [rbp + WORD_SIZE * (4 + "^(string_of_int minor)^")], rax
      mov rax, SOB_VOID_ADDRESS\n"  

  | BoxSet' (VarFree (name), _val ) -> 
      (generate consts fvars _val env_size num_of_args) ^ "\n" ^
      "push rax\n" ^
      (generate consts fvars (Var'(VarFree (name))) env_size num_of_args) ^ "\n" ^
      "pop qword [rax]\n" ^
      "mov rax, SOB_VOID_ADDRESS\n"

  | BoxSet' (VarBound (name, major, minor), _val ) -> 
      (generate consts fvars _val env_size num_of_args) ^ "\n" ^
      "push rax\n" ^
      (generate consts fvars (Var'(VarBound (name, major, minor))) env_size num_of_args) ^ "\n" ^
      "pop qword [rax]\n" ^
      "mov rax, SOB_VOID_ADDRESS\n"

  | BoxSet' (VarParam (name, minor), _val ) -> 
      (generate consts fvars _val env_size num_of_args) ^ "\n" ^
      "push rax\n" ^
      (generate consts fvars (Var'(VarParam(name, minor))) env_size num_of_args) ^ "\n" ^
      "pop qword [rax]\n" ^
      "mov rax, SOB_VOID_ADDRESS\n"

  | Def'((Var' VarFree (name)), _val) -> 
      let tuple = List.find (fun (var_name, _, _) -> name = var_name) fvars in
      let index = ((fun (_, index, _) -> index) tuple) in
      (generate consts fvars _val env_size num_of_args) ^ "\n" ^
      "mov qword [FVAR(" ^ (string_of_int index) ^ ")], rax\n" ^
      "mov rax, SOB_VOID_ADDRESS\n"
      
  | Seq'(car::cdr) -> (generate consts fvars car env_size num_of_args) ^ (generate consts fvars (Seq'(cdr)) env_size num_of_args)
         
  | Or'(exp_list) ->  
      let lexit_label = gen_label "Lexit" in
      (String.concat ""
      (List.map
      (fun (exp) ->                   
          (generate consts fvars exp env_size num_of_args) ^ "\n" ^
          "cmp rax, SOB_FALSE_ADDRESS\n" ^
          "jne " ^ lexit_label ^ "\n"
      )
      exp_list)) ^ lexit_label ^ ":\n"
          
  | If'(_test, _then, _else) ->  
      let exit_label = gen_label "Lexit" in
      let else_label = gen_label "Lelse" in
      (generate consts fvars _test env_size num_of_args) ^ "\n" ^
      "cmp rax, SOB_FALSE_ADDRESS\n" ^
      "je " ^ else_label ^ "\n" ^
      (generate consts fvars _then env_size num_of_args) ^ "\n" ^
      "jmp " ^ exit_label ^ "\n" ^
      else_label ^ ":\n" ^
      (generate consts fvars _else env_size num_of_args) ^ "\n" ^
      exit_label ^ ":\n"
  
  | Applic'(_proc, _args)  ->
      let n = List.length _args in
      "push 542525648 ;; MAGIC\n" ^
      (String.concat "" (List.map 
                       (fun arg -> (generate consts fvars arg env_size num_of_args) ^ "push rax ;; finish take care of arg\n")
                       (List.rev _args))) ^
      "push " ^ (string_of_int n) ^ " ;;push arg count\n" ^
      (generate consts fvars _proc env_size num_of_args) ^ "\n" ^
      "mov rdx, rax ;;save the closure on rbx\n" ^
      "CLOSURE_ENV rax, rdx ;;in rax we got env\n" ^
      "push rax ;;push rax->env\n" ^
      "CLOSURE_CODE rcx, rdx ;;in rcx we got code\n" ^
      "call rcx ;;call rax->code\n" ^
      "add rsp, 8*1 ;;pop env\n" ^
      "pop rbx ;;pop arg count\n" ^
      "shl rbx, 3 ;;rbx = rbx * 8\n" ^
      "add rsp, rbx ;;pop _args\n" ^
      "add rsp, 8 ;; CLEAN MAGIC\n"
  
  | LambdaSimple'(params, body) -> 
        let ext_env_size_string = (string_of_int (env_size + 1)) in
        let lambda_id = (gen_label "_") ^ "_" ^ ext_env_size_string in
      "
          LambdaSimple" ^ lambda_id ^ ":" ^ "

          mov rdi,  " ^ ext_env_size_string ^ "                         ; rbx =size of ExtEnv
          mov rax, WORD_SIZE
          mul rdi   ;  rax <- WORD_SIZE * EXT_ENV_SIZE 
          MALLOC rbx, rax                                               ; rbx -> ExtEnv
          mov rsi, rbx                                                  ; keep ExtEnv pointer for later
          mov rcx, 0                                                    ; for index
          mov rax, qword [rbp + 2 * WORD_SIZE]                          ; rax -> ENV
        
        copy_minors" ^ lambda_id ^ ":
          
          cmp rcx, " ^ (string_of_int env_size) ^ "                      ; compare rcx to size of ENV
          je end_copy_minors" ^ lambda_id ^ "                                            ; if equal, loop is done
          mov rdx, qword [rax + rcx * WORD_SIZE]                        ; rdx = ENV[rcx]
          mov [rbx + (rcx + 1) * WORD_SIZE], rdx                        ; copy pointer to the EXT_ENV
          inc rcx
          jmp copy_minors" ^ lambda_id ^ "

        end_copy_minors" ^ lambda_id ^ ":
          mov rdi,  qword " ^ (string_of_int num_of_args) ^ "
          mov rax, WORD_SIZE
          mul rdi   ; rax <- num_params * WORD_SIZE
          MALLOC rax, rax                                                      ; rax -> param_vector
          
          mov qword [rbx], rax                                                 ; ExtEnv[0] -> param_vector
          mov rcx,  0 
          mov rbx, [rbx]                                ;now point to the 0th vector

        copy_param" ^ lambda_id ^ ":
          cmp rcx,  qword " ^ (string_of_int num_of_args) ^ "
          je allocate_closure" ^ lambda_id ^ "
          mov rax,  qword [rbp + (rcx + 4) * WORD_SIZE] ; rax = param n
          mov qword [rbx + rcx * WORD_SIZE], rax        ; copy param to new vector
          inc rcx
          jmp copy_param" ^ lambda_id ^ "

        allocate_closure" ^ lambda_id ^ ":
          MAKE_CLOSURE (rax, rsi, Lcode" ^ lambda_id ^ ")
          jmp Lcont" ^ lambda_id ^ "

        Lcode" ^ lambda_id ^ ":
          push rbp
          mov rbp, rsp
          "^ 
          (generate consts fvars body (env_size + 1) (List.length params))  
          ^"
          leave
          ret
        Lcont" ^ lambda_id ^ ":\n\n

          "
          
  | LambdaOpt'(vars, var, body) -> 
  let ext_env_size_string = (string_of_int (env_size + 1)) in
  let lambda_id = (gen_label "_") ^ "_" ^ ext_env_size_string in
  let count_opt = "count_opt"^lambda_id in
  let create_list = "create_list"^lambda_id in
  let override_var = "override_var"^lambda_id in
  let apply_body = "apply_body"^lambda_id in
  let override_with_nil = "override_with_nil"^lambda_id in
  
        "
            LambdaOpt" ^ lambda_id ^ ":" ^ "
  
            mov rdi,  " ^ ext_env_size_string ^ "                         ; rbx =size of ExtEnv
            mov rax, WORD_SIZE
            mul rdi   ;  rax <- WORD_SIZE * EXT_ENV_SIZE 
            MALLOC rbx, rax                                               ; rbx -> ExtEnv
            mov rsi, rbx                                                  ; keep ExtEnv pointer for later
            mov rcx, 0                                                    ; for index
            mov rax, qword [rbp + 2 * WORD_SIZE]                          ; rax -> ENV
          
          copy_minors" ^ lambda_id ^ ":
            
            cmp rcx, " ^ (string_of_int env_size) ^ "                      ; compare rcx to size of ENV
            je end_copy_minors" ^ lambda_id ^ "                                            ; if equal, loop is done
            mov rdx, qword [rax + rcx * WORD_SIZE]                        ; rdx = ENV[rcx]
            mov [rbx + (rcx + 1) * WORD_SIZE], rdx                        ; copy pointer to the EXT_ENV
            inc rcx
            jmp copy_minors" ^ lambda_id ^ "
  
          end_copy_minors" ^ lambda_id ^ ":
            mov rdi,  qword " ^ (string_of_int num_of_args) ^ "
            mov rax, WORD_SIZE
            mul rdi   ; rax <- num_params * WORD_SIZE
            MALLOC rax, rax                                                      ; rax -> param_vector
            
            mov qword [rbx], rax                                                 ; ExtEnv[0] -> param_vector
            mov rcx,  0 
            mov rbx, [rbx]                                ;now point to the 0th vector
  
          copy_param" ^ lambda_id ^ ":
            cmp rcx,  qword " ^ (string_of_int num_of_args) ^ "
            je allocate_closure" ^ lambda_id ^ "
            mov rax,  qword [rbp + (rcx + 4) * WORD_SIZE] ; rax = param n
            mov qword [rbx + rcx * WORD_SIZE], rax        ; copy param to new vector
            inc rcx
            jmp copy_param" ^ lambda_id ^ "
  
          allocate_closure" ^ lambda_id ^ ":
            MAKE_CLOSURE (rax, rsi, Lcode" ^ lambda_id ^ ")
            jmp Lcont" ^ lambda_id ^ "
  
          Lcode" ^ lambda_id ^ ":
            push rbp
            mov rbp, rsp
            ;; ----- ADJUST STACK IF NEEDED ----- ;;
            ;; r9, r13 pointers on var - the optional
            mov r9, qword [rbp + (4 * WORD_SIZE) + (WORD_SIZE * " ^ (string_of_int (List.length vars)) ^ ")]
            mov r13, qword [rbp + (4 * WORD_SIZE) + (WORD_SIZE * " ^ (string_of_int (List.length vars)) ^ ")]

            mov r11, SOB_NIL_ADDRESS ;; FOR CREATE LIST
            ;; if we have there magic - means no optional so skip and goto Lcont (act like simple)
            cmp r9, 542525648
            je " ^ override_with_nil ^ "
            
            ;; else - count the optionals and then create from them list 
            ;; count the optionals, r10 is the counter
            mov r10, 0
            
            " ^ count_opt ^ ":
            cmp r13, 542525648
            je " ^ create_list ^ "
            inc r10 
            mov r13, [rbp + (4 * WORD_SIZE) + (WORD_SIZE * " ^ (string_of_int (List.length vars)) ^ ") + WORD_SIZE * r10]
            jmp " ^ count_opt ^ "

            ;; create list by count length
            ;; r12 holds the list
            ;; r10 is our counter
            " ^ create_list ^ ":
            cmp r10, 0
            jz " ^ override_var ^ "
            dec r10
            mov r14, [rbp + (4 * WORD_SIZE) + (WORD_SIZE * " ^ (string_of_int (List.length vars)) ^ ") + (WORD_SIZE * r10)]
            MAKE_PAIR(r12, r14, r11)
            mov r11, r12
            jmp " ^ create_list ^ "
            
            ;; override var by putting there our list of the optinals
            " ^ override_var ^ ":
            mov qword [rbp + (4 * WORD_SIZE) + (WORD_SIZE * " ^ (string_of_int (List.length vars)) ^ ")], r12
            jmp " ^ apply_body ^ "

            " ^ override_with_nil ^ ":
            mov qword [rbp + (4 * WORD_SIZE) + (WORD_SIZE * " ^ (string_of_int (List.length vars)) ^ ")], SOB_NIL_ADDRESS\n"

            ^ apply_body ^ ":
            "^ 
            (generate consts fvars body (env_size + 1) ((List.length vars) + 1))
            ^"
            leave
            ret
          Lcont" ^ lambda_id ^ ":\n\n
  
            "
  


  | Box'(v) -> let generated_var = (generate consts fvars (Var'(v)) env_size num_of_args ) in    

  generated_var ^ "\n" ^"
      ;BOX
      MALLOC rbx, WORD_SIZE
      mov [rbx],  rax
      mov rax,  rbx
      ;END_BOX
      "
  | ApplicTP'(_proc, _args) ->
 
    "push 542525648 ;; MAGIC\n" ^
    (String.concat "" (List.map 
                     (fun arg -> (generate consts fvars arg env_size num_of_args) ^ "push rax ;; finish take care of arg\n")
                     (List.rev _args))) ^
    "push " ^ (string_of_int (List.length _args)) ^ "   ;;push arg count\n" ^
    (generate consts fvars _proc env_size num_of_args) ^ "\n" ^ "
    mov rdx, rax ;;save the closure on rdx
    CLOSURE_ENV rax, rdx ;;in rax we got env
    push rax ;;push rax->env
    CLOSURE_CODE r13, rdx ;;in r13 we got code

    ;; ------- change the stack for TP! -------\n
    push qword [rbp + WORD_SIZE]   ; old ret address
    mov r14, qword [rbp]
    SHIFT_STACK (" ^ (string_of_int ((List.length _args) + 5)) ^ ")
    mov rbp, r14
    jmp r13 ;;call rdx->code
    "
  | _ ->  "";;

end;;
