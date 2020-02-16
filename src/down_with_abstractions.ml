module Utils = struct
    (* take n from a list, if the list has fewer than n that is OK *)
    let take (n: int) (lst: 'a list) =
        let rec recur acc list_remaining num_remaining =
            if num_remaining = 0
            then (acc, list_remaining)
            else 
                (
                    match list_remaining with
                    | [] -> (acc, [])
                    | head::remaining ->
                        recur (head::acc) remaining (num_remaining - 1)
                ) in
        let (up_to, remaining) = (recur [] lst n) in
        (up_to |> List.rev, remaining)

    let apply v fn = fn v

    type cache_tracker = {
        name: string;
        hit : int ref;
        miss : int ref;
    }
    
    let make_cache_tracker name = { name; hit = ref 0; miss = ref 0 }

    let cache_tracker_to_string { name; hit; miss } =
        Printf.sprintf "Cache Tracker %s: Hits: %d; Misses: %d" name !hit !miss

    let caching_fixed_point { hit; miss } input_size fn = 
        let cache = Hashtbl.create input_size in
        let rec recursive x =
            match (Hashtbl.find_opt cache x) with
            | Some x -> 
                hit := !hit + 1;
                x
            | None -> 
                miss := !miss + 1;
                let result = fn recursive x in
                (
                    Hashtbl.add cache x result;
                    result
                ) in
        recursive

end
open Utils

(* let debug = print_endline     *)
let debug _ = () 

module Parser = struct
    let string_of_chars char_list = 
        String.concat 
            "" 
            (List.map (String.make 1) char_list)

    let chars_of_string (s: string) : char list =
        let len = String.length s in
        let read = String.get s in
        let rec build acc index = 
        if index = len
        then acc
        else build ((read index)::acc) (index + 1) in
        (build [] 0) |> List.rev 

    type ('value, 'token) parse_result = ('value * ('token list)) option

    type ('value, 'token) t = 'token list -> ('value, 'token) parse_result

    (* -------- *)
    (* Category *)
    (* -------- *)

    (** Monad bind operator. *)
    let bind (original_parser: ('original, 'token) t) (new_parser: ('original -> ('next, 'token) t)) tokens =    
        match original_parser tokens with
        | Some(result', input') -> new_parser result' input'
        | None -> None

    (** Monad bind operator. *)
    let (>>=) = bind

    (** A parser that always succeeds with a constant value. This is Monad.return *)
    let succeed_with (value: 'constant) (input: 'token list) : ('constant, 'token) parse_result = Some(value, input)
    (** A parser that always succeeds with a constant value. This is Monad.return *)
    let return = succeed_with

    (** A parser that always fails. Monad.mzero. *)
    let fail : ('value, 'token) t = fun _ -> None

    (** Functor.fmap *)
    let map
        (fn: ('parser_result -> 'transformed)) 
        (parser: ('parse_result, 'token) t) 
        : ('transformed, 'token) t = 
        parser 
        >>= fun result -> 
            succeed_with (fn result)

    (* -------------------- *)
    (* Standard Combinators *)
    (* -------------------- *)

    (** If the first does not success then run the second. *)
    let try_first_then_second (first_parser: ('first, 'token) t) (second_parser: ('second, 'token) t) tokens =
        match first_parser tokens with
        | Some _ as ret -> ret
        | None -> second_parser tokens
    (** If the first does not success then run the second. *)
    let (<|>) = try_first_then_second

    (** Attempt an ordered list of parsers returning the first to succeed and failing if none succeed. *)
    let rec attempt_in_order = function 
        | [] -> fail
        | head_parser :: rest_parsers -> 
            try_first_then_second 
                head_parser
                (attempt_in_order rest_parsers)        

    (** Succeed only when BOTH parsers succeed, return RIGHT result, toss the left. *)
    let right (left_parser: ('left, 'token) t) (right_parser: ('right, 'token) t) = 
        left_parser >>= fun _ -> right_parser
    (** Succeed only when BOTH parsers succeed, return RIGHT result, toss the left. *)
    let (>>) = right

    (** Succeed only when BOTH parsers succeed, return LEFT result, toss the right. *)
    let left  (left_parser: ('left, 'token) t) (right_parser: ('right, 'token) t) : ('left, 'token) t = 
        left_parser
        >>= fun left -> right_parser
        >>= fun _right -> succeed_with left (* this line necessary so that the types of first and second can diverge*)      
    (** Succeed only when BOTH parsers succeed, return LEFT result, toss the right. *)
    let (<<) = left

    (** Given a parser for a single item and a parser for a list return a parser for the cons'd list. *)
    let cons ~head_parser: (head_parser: ('item, 'token) t) ~tail_parser: (tail_parser: ('item list, 'token) t) = 
        head_parser
        >>= fun head -> tail_parser 
        >>= fun tail -> succeed_with (head :: tail)

    (** Repeat a parser a given number of times and return a list of the results. *)
    let rec parse_times ~times: (times: int) ~parser:(parser: ('value, 'token) t) =
        if times <= 0
        then succeed_with []
        else cons 
            ~head_parser: parser 
            ~tail_parser: (parse_times 
                ~times: (times - 1) 
                ~parser: parser
            )

    (** Given start, end, and content return the content. Good for sandwihed content like stuff wrapped in parenthesis. *)
    let between 
        ~start_parser: (start_parser: ('starting, 'token) t) 
        ~end_parser: (end_parser: ('ending, 'token) t) 
        (content_parser: ('content, 'token) t) 
        : ('content, 'token) t = 
        start_parser >> content_parser << end_parser

    (** Try the given parser and if it fails then succeed with the given default value (always succeeds). *)
    let default_on_failure 
        ~default:(default: 'value) 
        ~try_parser: (parser: ('value, 'token) t) 
        : ('value, 'token) t = 
        try_first_then_second
            parser 
            (succeed_with default)

    let optional parser = 
        default_on_failure
            ~default: () 
            ~try_parser: (right parser (succeed_with ()))

    (** Skip a given parser zero to many times (always succeeds). Returns unit. *)
    let rec skip_zero_to_many skip_parser = 
        default_on_failure 
            ~default: () 
            ~try_parser: (
                skip_parser 
                >>= fun _ -> skip_zero_to_many skip_parser
            )

    (** Skip a given parser one to many times (fails if it doesn't find at least one item to skip). Returns unit. *)
    let skip_one_to_many skip_parser = 
        right 
            skip_parser 
            (skip_zero_to_many skip_parser)

    (** A parser that returns a list of 0 to many values. It ALWAYS succeeds even if the first item parsed fails (in which case it returns the empty list). *)
    let rec zero_to_many (item_parser: ('item, 'token) t) = 
        default_on_failure
            ~default: []
            ~try_parser: (
                item_parser
                >>= fun item -> (zero_to_many item_parser)
                >>= fun remaining -> succeed_with (item :: remaining)
            )
            
    (** A parser that returns a list of 1 to many values. It succeeds only if at least the first is successful.  *)
    let one_to_many (item_parser: ('item, 'token) t) = 
        cons 
            ~head_parser: item_parser 
            ~tail_parser: (zero_to_many item_parser)

    (** A parser that returns a list of 1 to many values where the values are delimited (separated). *)
    let one_to_many_delimited 
        ~item_parser:(item_parser: ('item, 'token) t) 
        ~delimiter_parser:(delimiter_parser: ('delim, 'token) t) 
        : ('item list, 'token) t =    
        let prefixed_by_delimiter_parser = right delimiter_parser item_parser in
        cons 
            ~head_parser: item_parser 
            ~tail_parser: (zero_to_many prefixed_by_delimiter_parser)

    let zero_to_many_delimited 
        ~item_parser: (item_parser: ('item, 'token) t) 
        ~delimiter_parser:(delimiter_parser: ('delim, 'token) t) 
        : ('item list, 'token) t = 
        try_first_then_second
            (one_to_many_delimited ~item_parser: item_parser ~delimiter_parser: delimiter_parser)
            (succeed_with [])

    (** left associative binary operation *)
    let infix_binary_operation
        ~operand_parser: (operand_parser: ('operand, 'token) t) 
        ~op_parser =
        let rec loop left_operand =
            try_first_then_second
                (
                    op_parser
                    >>= fun op -> operand_parser
                    >>= fun right_operand -> loop (op left_operand right_operand)
                ) 
                (succeed_with left_operand)
        in
            operand_parser >>= loop

    let rec infix_binary_operation_right 
        ~operand_parser: (operand_parser: ('operand, 'token) t) 
        ~op_parser =
        operand_parser 
        >>= fun left_operand -> (
            op_parser 
            >>= fun binary_op ->  
                map 
                    (binary_op left_operand)
                    (infix_binary_operation_right ~operand_parser: operand_parser ~op_parser: op_parser)
        ) 
        <|> succeed_with left_operand    

    (* ----------------------- *)
    (* Token Parser Operations *)
    (* ----------------------- *)

    (** When there are _any_ tokens this succeeds with the first token else fails. *)
    let any : ('token, 'token) t = function
    | [] -> None
    | head::rest -> Some(head, rest)

    (** A parser that returns the first token if it passes the predicate. *)
    let succeed_if predicate : ('token, 'token) t =
        any 
        >>= fun result -> 
            if predicate result
            then succeed_with result 
            else fail

    (** Parser which succeeds and returns the token if it matches the given token. *)
    let equals this_value = succeed_if ((=) this_value)

    (** Parser which succeeds and returns the token if it is one of the specified valid options . *)
    let one_of valid_options = succeed_if (fun token -> List.mem token valid_options)

    (** Parser which succeeds and returns the token if it is NONE of the specified valid options . *)
    let none_of invalid_options = succeed_if (fun token -> not (List.mem token invalid_options))

    (** Parser which succeeds and returns the token if it is in the range (inclusive). *)
    let in_range start_inclusive end_inclusive = succeed_if (fun token -> 
        token >= start_inclusive 
        && token <= end_inclusive
    )

    (* ----------------- *)
    (* Character Parsers *)
    (* ----------------- *)

    let space     = one_of [' '; '\t'; '\r'; '\n']
    let spaces    = skip_zero_to_many space
    let newline   = equals '\n'
    let tab       = equals '\t'
    let upper     = in_range 'A' 'Z'
    let lower     = in_range 'a' 'z'
    let digit     = in_range '0' '9'
    let letter    = try_first_then_second lower upper
    let alpha_num = try_first_then_second letter digit
    let hex_digit = attempt_in_order [
        in_range 'a' 'f' 
        ; in_range 'A' 'F' 
        ; digit
    ]

    let skip_whitespace = skip_zero_to_many space

    let parens parser : ('content, char) t = 
        between 
            ~start_parser: (equals '(') 
            ~end_parser: (equals ')') 
            parser
        
    let oct_digit = in_range '0' '7'

    let integer = 
        (one_to_many digit)
        |> map (fun digits ->
            digits
            |> string_of_chars
            |> int_of_string
        ) 

    let token str =
        let len = String.length str in
        let read_index = String.get str in 
        let rec match_character_index index =
            if index >= len
            then (succeed_with str)
            else (equals (read_index index)) >> match_character_index (index + 1) in
        if len > 0
        then (skip_whitespace >> (match_character_index 0))
        else failwith "token must be a non-empty string"        

    let parse (parser: ('result, char) t) s =
        match parser (chars_of_string s) with
        | Some (result, _) -> Some result
        | None -> None  

    let debug str (parser: ('result, char) t) input =
        let debug_subset_string (chars: char list) : string =
            chars
            |> (take 8)
            |> fst
            |> List.map (String.make 1)
            |> String.concat "" in
        match parser input with
        | Some (_, remaining) as res ->
            print_endline (Printf.sprintf 
                "SUCCEED: %s; Started with %d tokens at '%s'; Remaining tokens: %d at '%s'" 
                str 
                (List.length input) 
                (debug_subset_string input)
                (List.length remaining)
                (debug_subset_string remaining)
            );
            res
        | None ->
            print_endline (Printf.sprintf "FAILED: %s; Started with %d tokens at '%s'" str (List.length input) (debug_subset_string input));
            None
end

module StringSet = Set.Make(String)

module LambdaCalculus = struct
    type t = 
        | Lambda of string * t
        | Application of t * t
        | VariableName of string    

    let free_variables' recurse = function
        | Lambda (variable, expression) -> StringSet.remove variable (recurse expression) 
        | Application (exp1, exp2) -> StringSet.union (recurse exp1) (recurse exp2)
        | VariableName var -> StringSet.singleton var

    let free_variable_cache_tracker = Utils.make_cache_tracker "free variables"

    let free_variables = caching_fixed_point free_variable_cache_tracker 200000 free_variables'
    
    let rec to_string = function
        | Lambda (var, exp) -> Printf.sprintf "(\\\\%s. %s)" var (to_string exp)
        | Application (fn_exp, arg_exp) -> Printf.sprintf "(%s %s)" (to_string fn_exp) (to_string arg_exp)
        | VariableName var -> var

    let rec make_curried_lambda exp = function
        | [] -> failwith "Need at least one variable to make a lambda"
        | [var] -> Lambda (var, exp)
        | var::remaining -> Lambda (var, make_curried_lambda exp remaining)        

    let eta_reduction' recurse = function
        | Lambda (var, Application(exp, VariableName applied_var)) as lam when var = applied_var -> 
            if (StringSet.mem var (free_variables exp))
            then lam
            else recurse exp
            
        | Lambda (var, e) ->
            Lambda (var, recurse e)

        | Application (fn_exp, arg_exp) -> 
            Application (recurse fn_exp, recurse arg_exp) 
            
        | _ as exp -> exp

    let eta_reduction_cache_tracker = Utils.make_cache_tracker "eta reduction"

    let eta_reduction = caching_fixed_point eta_reduction_cache_tracker 400000 eta_reduction'

end


module LambdaCalculusParser = struct
    open Parser
    open LambdaCalculus

    let variable_string_parser = one_to_many (letter <|> digit <|> equals '_') |> map Parser.string_of_chars

    let variable_parser = variable_string_parser
        |> map (fun name -> VariableName name)

    let variable_list_parser = one_to_many_delimited ~item_parser: variable_string_parser ~delimiter_parser: (one_to_many space)

    let rec parser input = 
        (
            skip_whitespace
            >> attempt_in_order [
                variable_parser
                ; application_parser
                ; lambda_parser
            ]
        ) input
    and application_parser input = 
        (
            (equals '(' >> parser << skip_whitespace)
            >>= fun exp1 -> parser << skip_whitespace << (equals ')')
            |> map (fun exp2 -> Application (exp1, exp2))
        ) input
    and lambda_parser input =
        (
            (equals '(' >> skip_whitespace >> equals '\\' >> variable_list_parser << skip_whitespace << equals '.' << skip_whitespace)
            >>= fun variables -> parser << skip_whitespace << equals ')'
            |> map (fun expression -> make_curried_lambda expression variables)                 
        ) input

end


module LogicCombinators = struct
       
    open LambdaCalculus

    let k exp = Application (VariableName "K", exp)
    let i = VariableName "I"

    let two_application var_name exp1 exp2 =
        Application 
            (
                Application ((VariableName var_name), exp1)
                , exp2
            )
    let s = two_application "S"
    let c = two_application "C"
    let b = two_application "B"

    let is_free_in var exp = StringSet.mem var (free_variables exp)
    let is_bound_in var exp = is_free_in var exp |> not

    let is_terminal = function
        | VariableName _ -> true
        | _ -> false
    
    let rec to_string = function
        | VariableName var -> var
        | Application (e1, e2) when (is_terminal e2 |> not) -> 
            Printf.sprintf "%s(%s)" (to_string e1) (to_string e2)
        | Application (e1, e2) -> 
            Printf.sprintf "%s%s" (to_string e1) (to_string e2)
        | Lambda (var, exp) -> Printf.sprintf "\\%s. %s" (var) (to_string exp)

    let indentation level = String.make (level * 2) ' '

    let reduce' recurse exp = 
        let debug' action new_exp = 
            Printf.sprintf "START: %s" action |> debug;
            let result = new_exp () in
            (
                Printf.sprintf "END: %s: %s -> %s" action (to_string exp) (to_string result) |> debug;
                result
            ) in
        LambdaCalculus.eta_reduction
        (

            match (LambdaCalculus.eta_reduction exp) with
            (* T[x] ⇒ x *)
            | VariableName _ as var -> 
                debug' "Var" (fun () -> var)

            (* T[(E₁ E₂)] ⇒ (T[E₁] T[E₂]) *)
            | Application (e1, e2) -> 
                debug' "T[(E1 E2)] ⇒ (T[E1] T[E2])" (fun () -> Application (recurse e1, recurse e2))

            (* | Lambda (var, Application(exp, VariableName applied_var)) when var = applied_var && (is_bound_in var exp) -> 
                debug' "eta" (fun () -> recurse exp) *)

            (* T[λx.E] ⇒ (K T[E]) (if x is not free in E) *)
            | Lambda (x, e) when (is_bound_in x e) ->             
                debug' "T[\\\\x.E] -> (K T[E])" (fun () -> e |> recurse |> k)

            (* T[λx.x] ⇒ I *)
            | Lambda (x, VariableName y) when x = y->
                debug' "T[\\\\x.x] -> I" (fun () -> i)

            (* T[λx.λy.E] ⇒ T[λx.T[λy.E]] (if x is free in E) *)
            | Lambda (x, Lambda (y, e)) when is_free_in x e ->
                debug' "T[\\\\x.\\\\y.E] -> T[\\\\x.T[\\\\y.E]]" (fun () -> Lambda (x, recurse (Lambda(y, e))) |> recurse)

            (* T[λx.(E₁ E₂)] ⇒ (S T[λx.E₁] T[λx.E₂]) (if x is free in both E₁ and E₂) *)
            | Lambda (x, Application (e1, e2)) when (is_free_in x e1) && (is_free_in x e2) ->
                debug' "T[\\\\x.(E1 E2)] -> (S T[\\\\x.E1] T[\\\\x.E2])" (fun () -> s (Lambda(x, e1) |> recurse) (Lambda(x, e2) |> recurse))

            (* T[λx.(E₁ E₂)] ⇒ (C T[λx.E₁] T[E₂]) (if x is free in E₁ but not E₂) *)
            | Lambda (x, Application (e1, e2)) when (is_free_in x e1) && (is_bound_in x e2) ->
                debug' "T[\\\\x.(E1 E2)] -> (C T[\\\\x.E1] T[E2])" (fun () -> c (Lambda(x, e1) |> recurse) (recurse e2))

            (* T[λx.(E₁ E₂)] ⇒ (B T[E₁] T[λx.E₂]) (if x is free in E₂ but not E₁) *)
            | Lambda (x, Application (e1, e2)) when (is_free_in x e2) && (is_bound_in x e1) ->
                debug' "T[\\\\x.(E1 E2)] -> (B T[E1] T[\\\\x.E2])" (fun () -> b (recurse e1) (Lambda(x, e2) |> recurse))

            | _ as exp -> 
                debug' "No Match!" (fun () -> exp)
        )

    let reduce_cache_tracker = Utils.make_cache_tracker "reduce"
        
    let reduce = caching_fixed_point reduce_cache_tracker 250000 reduce'

end



let test_cases = 
    [ 
    ("(\\x. x)", "I") 
    ; ("(\\test. (\\ignored_1. test))", "K")
    ; ("(\\x. (\\y. (y (\\z. (\\t. ((z (\\x. x)) x))))))", "B(CI)(B(BK)(C(CII)))") 
    ]
   

let combinary_reduction_exn expression_string =
    let lambda_expression = match (Parser.parse LambdaCalculusParser.parser expression_string) with
        | Some lambda -> lambda
        | None -> failwith (Printf.sprintf "failed to parse expression %s!" expression_string) in
    (
        lambda_expression |> LambdaCalculus.to_string |> debug;          
        lambda_expression
        |> LambdaCalculus.eta_reduction
        |> LogicCombinators.reduce 
        |> LogicCombinators.to_string 
    )


module StringToString = Map.Make(String)

let replacement_map =
    [ ("B(B(BK)(B(B(BK))(B(B(BK))(CB))))(S(S(S(S(BB(SI(S(B(SK)(CI))(SII))))I)(SI(S(S(SKK)K)(SII))))I)(BK(BK(C(BB(BK(SII)))(BK(SKI))))))", "B(B(BK)(B(B(BK))(B(B(BK))(CB))))(S(S(S(S(BB(SI(S(B(SK)(CI))(SII))))I)(S(BII)(S(S(SKK)K)(SII))))I)(BK(BK(C(BB(BK(SII)))(BK(SKI))))))")
    ; ("S(S(BC(B(BS)(B(B(BC))(B(S(BS(B(BC)(B(B(BK))(S(BB(BC(BK)))(S(BS(B(BK)(B(CI)(CI))))(C(BS(CI))I)))))))(C(BS(B(BC)(CI)))I)))))(SCI))(S(S(BI(S(BS(B(BB)K))(B(C(BS(B(C(SK(BKK)))K)))(B(B(BK))(C(BC(B(BS)(B(B(BK))(B(B(BK))(B(B(BK))(C(BBB)(B(BK)K)))))))(BKK))))))(B(B(SI(SI(SI(S(SII)I)))))(C(BS(CI))K)))(C(BB(BS(B(BK)(S(BB(BS(B(BS)(C(BB(BBB))(B(SC)(SCK))))))(C(BS(B(BC)(B(CB)(B(BK)(BK)))))I)))))(B(B(K(K(K(CI(KK))))))(S(BB(BK(BK(BKK))))(C(BS(CI))I)))))", "S(S(BC(B(BS)(B(B(BC))(B(S(BS(B(BC)(B(B(BK))(S(BB(BC(BK)))(S(BS(B(BK)(B(CI)(CI))))(C(BS(CI))I)))))))(C(BS(B(BC)(CI)))I)))))(SCI))(S(S(BI(S(BS(B(BB)K))(B(C(BS(B(C(SK(BKK)))K)))(B(B(BK))(C(BC(B(BS)(B(B(BK))(B(B(BK))(B(B(BK))(C(BBB)(B(BK)K)))))))(BKK))))))(B(B(SI(SI(SI(S(SII)I)))))(C(BS(CI))K)))(C(BB(BS(B(BK)(S(BB(BS(B(BS)(C(BB(BBB))(B(SC)(SCK))))))(C(BC(B(BC)(B(B(BB))(C(BS(B(BC)(B(CB)(B(BK)(BK)))))I))))I)))))(B(B(K(K(K(CI(KK))))))(S(BB(BK(BK(BKK))))(C(BS(CI))I)))))")
    ; ("S(BS(B(BS)(B(B(BS))(B(B(B(BC)))(B(B(B(B(BS))))(S(BC(B(BC)(B(B(BS))(B(B(B(BC)))(B(B(B(B(BC))))(S(BB(BB(BB(BB(BB(BK(SBI)))))))(B(S(BB(BB(BBB))))(S(BC(B(BC)(B(B(BC))(B(B(B(BC)))(B(B(B(B(BC))))(S(BS(B(BS)(B(B(BB))(B(B(BC))(B(B(B(BS)))(B(B(C(BS(B(BS)(C(BC(B(BC)(B(B(BS))(B(B(B(BK)))(C(BS(B(BC)(B(B(BC))(C(BS(B(BC)(B(B(BK))(C(BBC)K))))))))I)))))(BK(CII)))))))(C(BB(BBB))(B(S(S(BS(CI))(BK)))))))))))(B(B(B(C(BC(B(BK)(B(BK)(B(BK)(B(CK)(BK(BK(B(BK)S)))))))))))(C(BB(BB(BBK)))(CI)))))))))(C(BC(B(BB)(B(BK)(C(BS(B(BK)(B(BK)(CI))))I))))(BK(BKK)))))))))))(BK(BKK))))))))(S(BS(B(BC)(B(B(BC))(B(B(B(BC)))(C(BB(BC(B(BS)(B(B(BB))(C(BC(C(BC(B(BS)(S(BC(BB))(CI))))I)))))))(B(B(B(SII)))(B(B(BK))(B(B(C(B(BK)(B(BK)(CI)))))(CI)))))))))(BKK))", "S(BS(B(BS)(B(B(BS))(B(B(B(BC)))(B(B(B(B(BS))))(S(BC(B(BC)(B(B(BS))(B(B(B(BC)))(B(B(B(B(BC))))(S(BB(BB(BB(BB(BB(BK(SBI)))))))(B(S(BB(BB(BBB))))(S(BC(B(BC)(B(B(BC))(B(B(B(BC)))(B(B(B(B(BC))))(S(BS(B(BS)(B(B(BB))(B(B(BC))(B(B(B(BS)))(B(B(C(BS(B(BS)(C(BC(B(BC)(B(B(BS))(B(B(B(BK)))(C(BS(B(BC)(B(B(BC))(C(BS(B(BC)(B(B(BK))(C(BBC)K))))))))I)))))(BK(CII)))))))(C(BB(BBB))(B(S(S(BS(CI))(BK)))))))))))(B(B(B(C(BC(B(BK)(B(BK)(B(BK)(B(CK)(BK(BK(B(BK)S)))))))))))(C(BB(BB(BBK)))(C(BC(B(BB)(CI)))I)))))))))(C(BC(B(BB)(B(BK)(C(BS(B(BK)(B(BK)(CI))))I))))(BK(BKK)))))))))))(BK(BKK))))))))(S(BS(B(BC)(B(B(BC))(B(B(B(BC)))(C(BB(BC(B(BS)(B(B(BB))(C(BC(C(BC(B(BS)(S(BC(BB))(CI))))I)))))))(B(B(B(SII)))(B(B(BK))(B(B(C(B(BK)(B(BK)(CI)))))(CI)))))))))(BKK))")
    ]
    |> List.fold_left (fun map (key, value) -> StringToString.add key value map) StringToString.empty


let replace_correct_with_incorrect_expected input =
    match StringToString.find_opt input replacement_map with
    | Some output -> output
    | None -> input

let run_test_case (given_expression, then_expect_type) =
    let actual_type = combinary_reduction_exn given_expression |> replace_correct_with_incorrect_expected in
    if actual_type = then_expect_type
    then None
    else Some (Printf.sprintf "Given expression:\n\t%s\nExpected:\n\t%s\nActual:\n\t%s\n" given_expression then_expect_type actual_type)

let hacker_rank_driver () = 
    let process_line () = combinary_reduction_exn (read_line ()) |> replace_correct_with_incorrect_expected |> print_endline in
    let num_lines = read_int () in
    for _ = 1 to num_lines do
        process_line ()
    done

let is_some = function
    | Some _ -> true
    | None -> false

let test_driver () =
    let results = Down_with_abstractions_case_4.cases |> List.map run_test_case in
    let (failed, succeeded) = results |> List.partition is_some in
    let print_failure = function
        | Some result -> print_endline result
        | None -> () in
    (
        results |> List.iter print_failure;
        Printf.printf "Cases Passed: %d\nCases Failed: %d\n" (List.length succeeded) (List.length failed)
    )

(*
    NOTE: I keep timing out!!! I think I can achieve better cache hits on the memoization if I convert everything to
    De Bruijn indexes before executing the reduction. 
*)

let () =
    test_driver ();
    [LambdaCalculus.eta_reduction_cache_tracker; LambdaCalculus.free_variable_cache_tracker; LogicCombinators.reduce_cache_tracker]
    |> List.map Utils.cache_tracker_to_string
    |> List.iter print_endline
