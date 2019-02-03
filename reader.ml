
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "pc.ml";;
 open PC;;
 exception X_not_yet_implemented;;
 exception X_this_should_not_happen;;
   
 type number =
   | Int of int
   | Float of float;;
   
 type sexpr =
   | Bool of bool
   | Nil
   | Number of number
   | Char of char
   | String of string
   | Symbol of string
   | Pair of sexpr * sexpr
   | Vector of sexpr list;;
 
 let rec sexpr_eq s1 s2 =
   match s1, s2 with
   | Bool(b1), Bool(b2) -> b1 = b2
   | Nil, Nil -> true
   | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
   | Number(Int n1), Number(Int n2) -> n1 = n2
   | Char(c1), Char(c2) -> c1 = c2
   | String(s1), String(s2) -> s1 = s2
   | Symbol(s1), Symbol(s2) -> s1 = s2
   | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
   | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
   | _ -> false;;
   
 module Reader: sig
   val read_sexpr : string -> sexpr
   val read_sexprs : string -> sexpr list
 end
 = struct
 let normalize_scheme_symbol str =
   let s = string_to_list str in
   if (andmap
   (fun ch -> (ch = (lowercase_ascii ch)))
   s) then str
   else Printf.sprintf "|%s|" str;;
 
 (* HELPER FUNCTIONS *)
  let caten_four nt1 nt2 nt3 nt4 s =
    let (e1, s) = (nt1 s) in
    let (e2, s) = (nt2 s) in
    let (e3, s) = (nt3 s) in
    let (e4, s) = (nt4 s) in
    ((e1, e2, e3, e4), s);;
  
  let caten_triple nt1 nt2 nt3 s =
    let (e1, s) = (nt1 s) in
    let (e2, s) = (nt2 s) in
    let (e3, s) = (nt3 s) in
    ((e1, e2, e3), s);;
  
  let caten_five nt1 nt2 nt3 nt4 nt5 s =
    let (e1, s) = (nt1 s) in
    let (e2, s) = (nt2 s) in
    let (e3, s) = (nt3 s) in
    let (e4, s) = (nt4 s) in
    let (e5, s) = (nt5 s) in
    ((e1, e2, e3, e4, e5), s);;
  
  
  (* HexPrefix support *)
  (* ⟨HexPrefix⟩::= #x *)
  let nt_hex_prefix =
    pack (word_ci "#x") (fun (l) -> (list_to_string l));;
  
  (* CharPrefix support *)
  (* ⟨CharPrefix⟩::= #\ *)
  let nt_char_prefix =
    pack (word "#\\") (fun (l) -> (list_to_string l));;
  
  (* support char semi-colon *)
  let nt_semi_colon= (char ';');;
  
  (* Digit support *)  
  (* ⟨ Digit ⟩ ::= ( 0 |...| 9 ) *)
  (* numeric value of a digit char *)
  let value_of_digit_char ch = 
    (int_of_char ch) - (int_of_char '0');;
  
  let nt_digit_char =
      range '0' '9';;
  
  let nt_digit = 
    pack nt_digit_char value_of_digit_char;;
  
  let nt_natural_chars = 
    plus nt_digit_char;;
  
  (* support natural number *)
  (* ⟨Natural⟩ ::= ⟨Digit⟩ + *)
  let nt_natural =
    let nt_digit_plus = plus nt_digit in
    pack nt_digit_plus 
         (fun digit_list ->(List.fold_left 
                           (fun d1 d2 -> 10 * d1 + d2)
                           0
                           digit_list
                           )
         );;
  
  (* support integers *)
  (* ⟨Integer⟩ ::= (+|-)?⟨Natural⟩  *)
  let nt_integer=
    let plus_sign = char '+' in           
    let minus_sign = char '-'  in
  
    (* (+ | -) and replace sign by value 1 or -1 respectively *)
    let plus_OR_minus = disj (pack plus_sign (fun _ -> 1)) (pack minus_sign (fun _ -> -1)) in
    let maybe_plus_OR_minus = maybe plus_OR_minus in
    
    let from_sign_to_val = pack maybe_plus_OR_minus (function 
                                              | None -> 1
                                              | (Some va) -> va 
                                          ) in
    let chain = caten from_sign_to_val nt_natural in
    let packed = pack chain
                      (fun (va, natural) -> (Int(va*natural)))
                      in
    packed;;
  
    
    
  (* support hex digit *)
  (* HexDigit ::= (0..9) | (a|...|f) | (A|...|F) *)
  let value_of_hex_digit_char ch =
    (int_of_char (lowercase_ascii ch)) - ((int_of_char 'a') - 10);;
  
  let nt_hex_digit_char =
      disj (range_ci 'a' 'f') nt_digit_char;;
  
  let nt_hex_natural_chars = 
    plus nt_hex_digit_char;;
  
  let nt_hex_digit = 
    let letter = range_ci 'a' 'f' in
    let nt_letter = pack letter value_of_hex_digit_char in
    let letter_or_digit = disj nt_letter nt_digit in
    letter_or_digit;;
  
  (* support hex natural *)
  (* ⟨HexNatural⟩ ::= ⟨HexDigit⟩ + *)
  let nt_hex_natural =
    let nt_hex_digit_plus = plus nt_hex_digit in
     pack nt_hex_digit_plus 
         (fun digit_list ->(List.fold_left 
                           (fun d1 d2 -> 16 * d1 + d2)
                           0
                           digit_list
                           )
         );;
    
  (* support HexIntegers *)
  (* ⟨HexInteger⟩ ::= ⟨HexPrefix⟩(+|-)?⟨HexNatural⟩  *)
  
  let nt_hex_without_prefix = 
    let nt_plus = char '+' in           
    let nt_minus = char '-'  in
    
    (* (+|-) and replace sign by value 1 or -1 respectively *)
    let plus_OR_minus = disj (pack nt_plus (fun _ -> 1)) (pack nt_minus (fun _ -> -1)) in
    
    (* (+|-)? *)
    let nt_maybe_plus_OR_minus = pack (maybe plus_OR_minus)
                                      (function 
                                      | None -> 1
                                      | (Some va) -> va 
                                      ) in
    (* (+|-)?⟨HexNatural⟩ *)
    let chain = pack (caten nt_maybe_plus_OR_minus nt_hex_natural_chars)
                     (fun (va, natural) -> natural) in
    
    chain;;
  
  let nt_hex_integer=  
    let nt_plus = char '+' in           
    let nt_minus = char '-'  in
    
    (* (+|-) and replace sign by value 1 or -1 respectively *)
    let plus_OR_minus = disj (pack nt_plus (fun _ -> 1)) (pack nt_minus (fun _ -> -1)) in
    
    (* (+|-)? *)
    let nt_maybe_plus_OR_minus = pack (maybe plus_OR_minus)
                                      (function 
                                      | None -> 1
                                      | (Some va) -> va 
                                      ) in
    (* (+|-)?⟨HexNatural⟩ *)
    let chain = pack (caten nt_maybe_plus_OR_minus nt_hex_natural)
                     (fun (va, natural) -> va * natural) in
    
    (* ⟨HexPrefix⟩(+|-)?⟨HexNatural⟩ *)
    pack (caten nt_hex_prefix chain)
         (fun (rm, hex_num) -> (Int (hex_num)));;
  
  (* support Float *)
  (* ⟨Float⟩::=⟨Integer⟩.⟨Natural⟩ *)
  let nt_float=
    let nt_maybe_minus = pack (maybe (char '-'))
                              (function
                              | None -> 1.0
                              | (Some minus) -> -1.0
                              ) in
    let get_integer = pack  nt_integer
                            (function
                            | (Int n) -> n
                            | (Float n) -> 5
                            ) in
  
    let chain = caten_four nt_maybe_minus get_integer (char '.') nt_natural_chars in
    pack  chain
          (fun (sign, integer, dot, natural_list) ->
          match integer with
          | 0 -> (
             let natural_string = (list_to_string natural_list) in
             let ff = float_of_string ((string_of_int integer) ^ (String.make 1 dot) ^ natural_string) in
           if ((sign = -1.0) && ((compare "0" natural_string) != 0)) then Float(-1.0 *. ff) else Float(ff) 
               )
          | _ ->
          (Float (sign *.  (float_of_string 
                        ((string_of_int integer) ^ (String.make 1 dot) ^ (list_to_string natural_list))
                        )
                ))
          );;
  
  
  (* support HexFloat *)
  (* ⟨HexFloat⟩::=⟨HexInteger⟩.⟨HexNatural⟩ *)
  let nt_hex_float=
    let nt_maybe_minus = pack (maybe (char '-'))
                              (function
                              | None -> 1.0
                              | (Some minus) -> -1.0
                              ) in
    
     let chain = caten_five nt_hex_prefix nt_maybe_minus nt_hex_without_prefix (char '.') nt_hex_natural_chars in
     (* let chain = caten_five nt_maybe_minus nt_hex_integer (char '.') nt_hex_natural_chars in *)
    pack  chain
          (fun (_, sign, integer_list, dot, natural_list) ->
          let integer = float_of_string ("0x" ^ (list_to_string integer_list)) in
          match integer with
          | 0. -> (
            let natural_string = (list_to_string natural_list) in
            let ff = (float_of_string ("0x" ^ (list_to_string integer_list) ^ (String.make 1 dot) ^ natural_string)) in
            if ((sign = -1.0) && ((compare "0" natural_string) != 0)) then Float(-1.0 *. ff) else Float(ff) 
          )
          | _ -> Float (sign *. (float_of_string ("0x" ^ (list_to_string integer_list) ^ (String.make 1 dot) ^ (list_to_string natural_list))))
          );;
  
  
  (* support NamedChar *)
  (* ⟨NamedChar⟩::=newline,nul,page,return,space,tab *)
  let nt_named_char=
    let nt_nul = pack (word_ci "nul") (fun (s) -> 0) in
    let nt_newline = pack (word_ci "newline") (fun (s) -> 10) in
    let nt_return = pack (word_ci "return") (fun (s) -> 13) in
    let nt_tab = pack (word_ci "tab") (fun (s) -> 9) in 
    let nt_formfeed = pack (word_ci "page") (fun (s) -> 12) in
    let nt_space = pack (word_ci "space") (fun (s) -> 32) in
    pack (disj (disj
                         (disj nt_nul nt_newline)
                         (disj nt_return nt_tab))
                         (disj nt_formfeed nt_space))
          (fun  r ->   Char(char_of_int r));;
  
  
  (* support ⟨VisibleSimpleChar⟩ *)
  (* ⟨VisibleSimpleChar⟩::= c > 32 *)
  let nt_visible_char = 
    pack 
    (const (fun x -> (int_of_char x) > 32))
    (fun ch -> Char(ch));;
  
  (* support ⟨HexChar⟩ *)
  (* ⟨HexChar⟩::=x⟨HexDigit⟩+ *)
  let nt_hex_char =
    (pack 
    (caten (char_ci 'x') nt_hex_natural)
    (fun (x,y) -> Char(char_of_int y)));;  
  
  (* support ⟨Char⟩ *)
  (* ⟨Char⟩::=⟨CharPrefix⟩(⟨VisibleSimpleChar⟩j ⟨NamedChar⟩ j ⟨HexChar⟩) *)
  let nt_char = 
    pack (caten nt_char_prefix (disj (disj nt_hex_char nt_named_char) nt_visible_char))
          (fun (pref, ch) -> ch);;
  (* support symbol char *)
  (* stuff *)
  let nt_symbol_char=
    let is_punctuation = const (fun x -> (List.mem x ['!';'$';'^';'*';'-';'_';'=';'+';'>';'<';'/';'?';':'])) in
    (pack (disj (disj nt_digit_char (range_ci 'a' 'z')) is_punctuation) lowercase_ascii);;
  
  let nt_symbol_char_without_e = 
   let is_punctuation = const (fun x -> (List.mem x ['!';'$';'^';'*';'-';'_';'=';'+';'>';'<';'/';'?';':'])) in
    (pack (disj_list [nt_digit_char; (range_ci 'a' 'd'); (range_ci 'f' 'z'); is_punctuation]) lowercase_ascii);;
 
  let symbol_with_e = 
     pack (plus nt_symbol_char_without_e) 
          (fun x -> Symbol(list_to_string x));;
 
  (* ⟨Symbol⟩::=⟨SymbolChar⟩+ *)
  let nt_symbol = 
    (* Symbol(pack (plus nt_symbol_char) list_to_string);; *)
    pack (plus nt_symbol_char) 
         (fun x -> Symbol(list_to_string x));;
  
  (* support Number *)
  (* ⟨Number⟩::=⟨Float⟩ | ⟨Integer⟩ | ⟨HexFloat⟩ | ⟨HexInteger⟩ *)
  let nt_number = 
    let number_p = pack  (disj (disj nt_float nt_integer) (disj nt_hex_float nt_hex_integer))
                         (fun x -> Number x) in
                        
    not_followed_by number_p nt_symbol;;
   let nt_number_e = 
   pack  (disj (disj nt_float nt_integer) (disj nt_hex_float nt_hex_integer))
                         (fun x -> Number x)
   
 
  (* Boolean support *)
  (* TODO whitespaces[!! ending of #t #f *)
  let nt_boolean =
    let nt_true = word_ci "#t" in
    let nt_false = word_ci "#f" in 
    let bool_p = pack  (disj nt_true nt_false)
                  (fun ls_chars ->
                  let x = list_to_string (List.map lowercase_ascii ls_chars) in
                  match x with
                  | "#t" -> Bool (true)
                  | "#f" -> Bool (false)
                  | _ -> raise X_no_match
                  ) in
    not_followed_by bool_p nt_symbol;;
  
  (* StringLiteralChar - any char except *)
  let nt_string_literal_char = 
    let dont_be = ["\\"; "\""] in 
    const (fun x -> not (List.mem (String.make 1 x) dont_be));;
  
  (* StringMetaChar *)
  let nt_string_meta_char =
    let slash = pack (word "\\\\") (fun c -> (char_of_int 92)) in
    let newline = pack (word "\\n") (fun c -> '\n') in
    let dquote = pack (word "\\\"") (fun c -> '"') in
    let tab = pack (word "\\t") (fun c -> '\t') in
    let r = pack (word "\\r") (fun c -> '\r') in
    let page = pack (word "\\f") (fun c -> (char_of_int 12)) in
    (disj (disj (disj (disj (disj newline page) dquote) tab) r) slash);;
  
  (* ⟨StringHexChar⟩::= \x⟨HexDigit⟩+; *)
  let nt_string_hex_char =
    let net_semi_colon_str = word ";" in
    pack 
    (caten_triple (word "\\") nt_hex_char net_semi_colon_str)
    (function
    | (_, (Char c), _) -> c
    | _ -> raise X_no_match);;
  
  (* StringChar *)
  let nt_string_char = 
   disj_list [nt_string_hex_char; nt_string_meta_char; nt_string_literal_char];;
    
  (* String *)
  let nt_string =
   let dq = word ("\"") in
   let chain = caten_triple dq (star nt_string_char) dq in
   pack chain
        (fun (d1, str_ls, d2) -> String(list_to_string str_ls));;
 
  (* scientific notation *)
  (* begin with either a valid integer / valid floating point number,
   followed by either the character e/E, followed by a valid integer *)
  (* aeb = aEb = a*(10**b) *)
  let nt_e_notation = 
   (* exp workd ONLY on float numbers *)
   let exp x y= x *. (10.**(float_of_int y)) in
   let nt_actual_number = pack nt_number_e
                            (function 
                             | (Number (Int a)) -> (float_of_int a)
                             | (Number (Float a)) -> a
                             | _ -> raise X_no_match
                            ) in
   let nt_e = pack (char_ci 'e') (fun _ -> 'e') in
   let nt_actual_integer = pack nt_integer
                           (function
                           | (Int a) ->  a
                           | _ -> raise X_no_match
                           ) in
   let notation_p = pack (caten_triple nt_actual_number nt_e nt_actual_integer)
        (fun (num, ch_e, integer) -> Number (Float (exp num integer))) in
   not_followed_by notation_p nt_symbol;;
 
  let nt_spaces_star = star (char ' ')
  let nt_lparen = 
    let open_paren =  char '(' in
    (*open parenthesis with optional spaces before and after*)
    let spaced_open = caten (caten nt_spaces_star open_paren) nt_spaces_star in
    pack spaced_open (fun ((left, par), right) -> par);;
 
  let nt_rparen = 
    let open_paren =  char ')' in
    (*open parenthesis with optional spaces bfefore and after*)
    let spaced_open = caten (caten nt_spaces_star open_paren) nt_spaces_star in
    pack spaced_open (fun ((left, par), right) -> par);;
 
  (* skips white spaces! *)
  let nt_whitespace =
    let nt_whitespace_char = const (fun x -> (int_of_char x) <= 32) in
    let func = fun _ -> () in
    let x = pack nt_whitespace_char func in
    let y = pack nt_none func in
    let x = disj x y in 
    let x = pack (star x) func in
    pack x (fun _ -> Nil);; 
   (* let nt_line_comment = 
     let semi_char = char ';' in
     let nt_comment_end = disj (char '\n') (char '\004') in
     let nt_all_but_semi = diff nt_any semi_char in
     let nt_commented_exp = pack
                             (caten semi_char
                                           (star (diff nt_any nt_comment_end)))
                             (fun _ ->  ()) in *)
     let nt_line_comment = 
       let semi_char = char ';' in
       let nt_comment_end = disj (char '\n') (char '\004') in
       (* let nt_commented_exp = pack
                               (caten semi_char
                               (star (diff nt_any nt_comment_end)))
                               (fun _ ->  []) in *)
       let nt_commented_exp = 
                               (caten semi_char
                               (star (diff nt_any nt_comment_end)))
                                in
        caten nt_commented_exp nt_comment_end;;
 
  let nt_nil =
    pack 
    (caten_triple (char '(' ) nt_whitespace (char ')' ))
    (fun _ -> Nil);; 
  
 
 
   (* try to make a string. if possible, forget about comments. else, remove comments (stupid solution) *)
  let rec nt_line_comment_whitespaces ls= 
     try
         let a1,b1 = nt_whitespace  ls in
         let a2,b2 = nt_line_comment   b1 in
         let a3,b3 = nt_whitespace b2 in
         nt_line_comment_whitespaces  b3
     with X_no_match -> let u,r = (nt_whitespace ls) in
                     (Nil, r);;
 
  (* ⟨List⟩::=(⟨Sexpr⟩) *)
  (* Pair depands on sexpr && sexpr depands on Pair *)
  let rec the_expr s =
      let skiip = caten_triple nt_whitespace nt_sexp_comment nt_whitespace in
      let chain = caten_five    
                                nt_line_comment_whitespaces
                                skiip
                                (disj_list [nt_ls; nt_dotted; nt_vector; atoms_compound]) 
                                skiip           
                                nt_line_comment_whitespaces 
                                in  
      let packed = pack chain
                   (fun (rm_c, sp1,expr,sp2,ws) -> expr) in
      packed s

      
 
 
     and nt_sexp_comment s = 
       let hs_semi = word "#;" in
       let packed = pack (caten_triple hs_semi (maybe (delayed (fun () -> nt_sexp_comment))) (delayed (fun () -> the_expr)))
                         (fun _ -> Nil) in
       (star packed) s
    
    and atoms_compound s =
    
    let skiip = caten_triple nt_whitespace nt_sexp_comment nt_whitespace in
    let chain = caten_five    
                                nt_line_comment_whitespaces
                                skiip
                                (disj_list [nt_boolean; nt_e_notation;
                                nt_number; nt_char; nt_string;
                                nt_symbol; reg_ls; reg_dotted; reg_vector; nt_quote; nt_qquote; nt_nil;
                                nt_unquote_spliced; nt_unquote]) 
                                skiip           
                                nt_line_comment_whitespaces 
                                in  
      let packed = pack chain
                   (fun (rm_c, sp1,expr,sp2,ws) -> expr) in
      packed s 

    (* unbal list unbal vector unbal dotted *)
    and netsted_sexpr s = 
    let skiip = caten_triple nt_whitespace nt_sexp_comment nt_whitespace in
    let chain = caten_five    
                                nt_line_comment_whitespaces
                                skiip
                                (disj_list [atoms_compound; nested_ls; nested_dotted; nested_vector]) 
                                skiip           
                                nt_line_comment_whitespaces 
                                in  
      let packed = pack chain
                   (fun (rm_c, sp1,expr,sp2,ws) -> expr) in
      packed s
      
    (* ⟨List⟩::=(⟨Sexpr⟩* *)
    and nested_ls s = 
    let chain = caten (disj (char '(') (char '[')) (star netsted_sexpr) in 
    pack chain (fun (_, sexpr_ls) -> (List.fold_right (fun a b -> Pair(a, b)) sexpr_ls Nil)) s

    and reg_ls s = 
    let chain1 = caten_triple (char '(') (star atoms_compound) (char ')') in
    let chain2 = caten_triple (char '[') (star atoms_compound) (char ']') in
    pack (disj chain1 chain2) (fun (_, sexpr_ls, _) -> (List.fold_right (fun a b -> Pair(a, b)) sexpr_ls Nil)) s
     
    and nt_ls s = 
    let ls_with_three_dots = caten_triple (disj (char '(') (char '[')) (star netsted_sexpr) (word "...") in
    let packed_three_dots = pack ls_with_three_dots 
    (fun (_, sexpr_ls, _) -> (List.fold_right (fun a b -> Pair(a, b)) sexpr_ls Nil)) in
    disj reg_ls packed_three_dots s

    (* ⟨DottedList⟩::=(⟨Sexpr⟩+.⟨Sexpr⟩) *)
    and nested_dotted s =
    let lparen = disj (char '(') (char '[') in
    let chain = caten_four lparen (plus netsted_sexpr) (char '.') netsted_sexpr in 
    pack chain (fun (_, sexpr_ls, _, sexpr) -> (List.fold_right (fun a b -> Pair(a, b)) sexpr_ls sexpr)) s
   
    and reg_dotted s = 
    let chain1 = caten_five (char '(') (plus atoms_compound) (char '.') atoms_compound (char ')') in
    let chain2 = caten_five (char '[') (plus atoms_compound) (char '.') atoms_compound (char ']') in 
    pack (disj chain1 chain2) (fun (_, sexpr_ls, _, sexpr, _) -> (List.fold_right (fun a b -> Pair(a, b)) sexpr_ls sexpr)) s
     
    and nt_dotted s =
    let lparen = disj (char '(') (char '[') in
    let dotted_with_three_dots = caten_five lparen (plus netsted_sexpr) (char '.') netsted_sexpr (word "...") in 
    let packed_three_dots = pack dotted_with_three_dots
    (fun (_, sexpr_ls, _, sexpr, _) -> (List.fold_right (fun a b -> Pair(a, b)) sexpr_ls sexpr)) in
    disj reg_dotted packed_three_dots s

    (* Vector *)
    and nested_vector s = 
    let lparen = disj (char '(') (char '[') in
    let chain = caten_triple (char '#') lparen (star netsted_sexpr) in
    pack chain (fun (_, _, sexpr_ls) -> Vector(sexpr_ls)) s

    and reg_vector s =
    let chain1 = caten_four (char '#') (char '(') (star atoms_compound) (char ')') in
    let chain2 = caten_four (char '#') (char '[') (star atoms_compound) (char ']') in
    pack (disj chain1 chain2) (fun (_, _, sexpr_ls, _) -> Vector(sexpr_ls)) s

    and nt_vector s = 
    let lparen = disj (char '(') (char '[') in
    let vector_with_three_dots = caten_four (char '#') lparen (star netsted_sexpr) (word "...") in
    let packed_three_dots = pack vector_with_three_dots 
    (fun (_, _, sexpr_ls, _) -> Vector(sexpr_ls)) in
    disj reg_vector packed_three_dots s
      
    (* Pair(Symbol(name), Pair(sexpr, Nil()) *) 
    and make_nt_quote tag name = 
    let chain = caten (word tag) the_expr in
    pack chain (fun (ch_unit, expr) -> Pair(Symbol(name),Pair(expr, Nil)))
    
    (* ⟨Quoted⟩::='⟨Sexpr⟩ *)
    and nt_quote s = 
      (make_nt_quote "\'" "quote") s
    (* QQuoted⟩::=‘⟨Sexpr⟩ *)
    and nt_qquote s = 
      (make_nt_quote "`" "quasiquote") s
    (* ⟨UnquotedSpliced⟩::=,@⟨Sexpr⟩ *)
    and nt_unquote_spliced s =
    (make_nt_quote ",@" "unquote-splicing") s
    (* ⟨Unquoted⟩::=;⟨Sexpr⟩ *)
    and nt_unquote s =
    (make_nt_quote "," "unquote") s;;    

 
 
  let read_sexpr string = 
     (* let no_comment = remove_comment (string_to_list string) in *)
     let e,s = (the_expr  (string_to_list string)) in
       e;;
 
  let read_sexprs string = 
    let e,s = (star (the_expr)) (string_to_list string) in
    e;;
  
   
 end;; (* struct Reader *)
 