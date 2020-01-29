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
    (** A parser that always fails. Monad.mzero. *)
    let zero = fail

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

    let parse (parser: ('result, char) t) s =
        match parser (chars_of_string s) with
        | Some (result, _) -> Some result
        | None -> None        
end

module Expression = struct
    type term = {
        coefficient: int;
        power: int;
    } 

    let compare_term_power_descending left right = left.power - right.power

    let negative_one_term = { coefficient = -1; power = 0 }

    type t =
        | Term of term
        | RaisedToPower of term * t
        | Sum of t * t
        | Difference of t * t
        | Product of t * t
        | Quotient of t * t

    let term_parser = Parser.(
        (integer |> map (fun num -> {coefficient = num; power = 0}))
        <|> (equals 'x' >> return ({coefficient = 1; power = 1 }))
    )

    let term_expression_parser = Parser.(
        term_parser
        |> map (fun term -> Term term)
    )

    let binary_operation_parser op_parser fn = Parser.(         
        (skip_whitespace >> op_parser) >> (succeed_with fn)
    )

    let sum_op_parser = Parser.(binary_operation_parser (equals '+') (fun l r -> Sum(l, r)))
    let diferrence_op_parser = Parser.(binary_operation_parser (equals '-') (fun l r -> Difference(l, r)))
    let product_op_parser = Parser.(
        binary_operation_parser 
            ('*' |> equals |> optional)
            (fun l r -> Product(l, r))
    )
    
    let quotient_op_parser = Parser.(binary_operation_parser (equals '/') (fun l r -> Quotient(l, r)))

    let lead_neg_char = 'n'

    let rec expression_parser input  = 
        Parser.(infix_binary_operation
            ~operand_parser: multiplication_parser 
            ~op_parser: (sum_op_parser <|> diferrence_op_parser)            
            input         
        )
        and multiplication_parser input = Parser.(
            infix_binary_operation 
                ~operand_parser: power_parser
                ~op_parser: (quotient_op_parser <|> product_op_parser)            
                input
        )
        and power_parser input = Parser.(
            (
                (
                    (skip_whitespace >> term_parser)
                    >>= fun term -> (skip_whitespace) >> equals '^'
                    >>= fun _ -> power_parser
                    >>= fun expression -> succeed_with (RaisedToPower(term, expression))        
                ) 
                <|>
                factor_parser
            )
            input
        )
        and factor_parser input = Parser.(
            (   
                skip_whitespace
                >>
                (attempt_in_order [
                    (
                        equals lead_neg_char
                        >> (succeed_with (Term negative_one_term))
                    )
                    ; (parens expression_parser)
                    ; term_expression_parser                                
                ])
            )
            input      
        )

    let of_string s =
        let chars = s |> String.trim |> Parser.chars_of_string in
        let leading_neg_chars = match chars with
            | '-'::rest ->
                lead_neg_char::rest
            | _ -> chars in
        match (expression_parser leading_neg_chars) with
        | Some (expr, remaining) -> (
            (* print_endline (Printf.sprintf "%d chars remaining" (List.length remaining)); *)
            expr
        )
        | None -> failwith "Oh no!!!"
    
    let term_to_string {coefficient; power} = 
        match coefficient, power with
        | 0, _ -> ""
        | coefficient, 0 -> string_of_int coefficient
        | 1, 1 -> "x"
        | -1, 1 -> "-x"
        | coefficient, 1 -> Printf.sprintf "%dx" coefficient
        | 1, power -> Printf.sprintf "x^%d" power
        | -1, power -> Printf.sprintf "-x^%d" power
        | coefficient, power -> Printf.sprintf "%dx^%d" coefficient power

    let bin sep left right = Printf.sprintf "(%s %s %s)" left sep right
    let str_raise_to_power = bin "raise"
    let str_add = bin "sum"
    let str_sub = bin "diff"
    let str_mul = bin "mult"
    let str_div = bin "div"

    let rec to_string exp =  
        match exp with
        | Term term -> term_to_string term
        | RaisedToPower (term, expression) ->
            str_raise_to_power (term_to_string term) (to_string expression)
        | Sum (left, right) ->
            str_add (to_string left) (to_string right)
        | Difference (left, right) ->
            str_sub (to_string left) (to_string right)
        | Product (left, right) ->
            str_mul (to_string left) (to_string right)
        | Quotient (left, right) ->
            str_div (to_string left) (to_string right)

    let indent_string level = String.init (level * 2) (fun _ -> ' ')
    
    let debug_expression indent before_expression after_expression = 
        (
            (*
            let before = before_expression |> to_string in
            let after = after_expression |> to_string in
            print_endline (Printf.sprintf "%s%s -> %s" (indent_string indent) before after);
            *)
            after_expression
        )

    let expect_literal = function
        | Term { coefficient; power } when power = 0 -> coefficient
        | _ -> failwith "Expecting a literal value."

    let rec simplify indent expr = 
        let combine_expressions left right combine = combine(simplify (indent + 1) left, simplify (indent + 1) right) in
        let sum_expressions = function
            | Term left_term, Term right_term when left_term.power = right_term.power ->                 
                Term { coefficient = left_term.coefficient + right_term.coefficient; power = left_term.power }
            | left, right -> Sum(left, right) in
        let diff_expressions = function
            | Term left_term, Term right_term when left_term.power = right_term.power ->                 
                Term { coefficient = left_term.coefficient - right_term.coefficient; power = left_term.power }
            | left, right -> 
                let negated_right = Product (Term negative_one_term, right) in
                Sum (left, simplify (indent + 1) negated_right) in
        let distribute_op transform_term expression = 
            let rec recur expr = expr |> simplify (indent + 1) |> dist 
            and dist = function
            | Term term -> Term (transform_term term)
            | RaisedToPower (term, power_expression) -> 
                RaisedToPower((transform_term term), power_expression)
            | Sum (left, right) -> Sum(recur left, recur right) 
            | Difference (left, right) -> Difference(recur left, recur right) 
            | Product (left, right) -> Product(recur left, recur right) 
            | Quotient (left, right) -> Quotient(recur left, recur right) in
            dist expression in
        let quotient_expressions (dividend, divisor) = 
            let divisor_int = (expect_literal divisor) in
            let transform_term { coefficient; power } =
                { coefficient = coefficient / divisor_int; power } in
            distribute_op transform_term dividend in
        let product_expressions = function    
            | Term left_term, Term right_term ->
                Term { 
                    coefficient = left_term.coefficient * right_term.coefficient 
                    ; power = left_term.power + right_term.power
                }
            | Term term, expression_to_distribute ->
                let transform_term { coefficient; power } =
                    { coefficient = coefficient * term.coefficient; power = power + term.power } in
                distribute_op transform_term expression_to_distribute
            | expression_to_distribute, Term term ->
                let transform_term { coefficient; power } =
                    { coefficient = coefficient * term.coefficient; power = power + term.power } in
                distribute_op transform_term expression_to_distribute
            | Sum(a, b), Sum(c, d) ->
                (
                    let simp = simplify (indent + 1) in
                    let ac = Product(a, c) |> simp in
                    let ad = Product(a, d) |> simp in
                    let bc = Product(b, c) |> simp in
                    let bd = Product(b, d) |> simp in
                    let sum_bcbd = Sum(bc, bd) |> simp in
                    let sum_adbcbd = Sum(ad, sum_bcbd) |> simp in
                    Sum(ac, sum_adbcbd) |> simp
                )
            | left, right -> Product(left, right) in
        (
            debug_expression 
                indent 
                expr 
                (match expr with 
                | Term _ as res -> res
                | RaisedToPower ({coefficient; power}, power_expression) -> 
                    (* expect that efter simplification all powers must be literals *)
                    let raised_to_power = expect_literal (simplify (indent + 1) power_expression) in
                    Term { coefficient; power = power * raised_to_power }
                | Sum (left, right) -> combine_expressions left right sum_expressions
                | Difference (left, right) -> combine_expressions left right diff_expressions
                | Product (left, right) -> combine_expressions left right product_expressions
                | Quotient (left, right) -> combine_expressions left right quotient_expressions
                )
        )

    (** Given an expression consisting only of sums and terms then return a list of terms *)
    let terms_of_expression (expr: t) : term list = 
        let combine_terms terms current_term = 
            match terms with
            | [] -> [current_term]
            | last_term::rest -> 
                if last_term.power = current_term.power 
                then 
                    ({ coefficient = last_term.coefficient + current_term.coefficient; power = current_term.power })
                    ::rest                    
                else current_term::terms in
        let rec build acc = function    
            | Term term -> term::acc
            | Sum(Term left_term, right_expression) ->
                build (left_term::acc) right_expression
            | Sum(left_expression, Term right_term) ->
                build (right_term::acc) left_expression
            | Sum(left_expression, right_expression) -> 
                build (build acc left_expression) right_expression              
            | RaisedToPower _ -> failwith "unexpected RaisedToPower"
            | Difference _ -> failwith "unexpected Difference"
            | Product _ -> failwith "unexpected Product"
            | Quotient _ -> failwith "unexpected Quotient"            
        in
        build [] expr
        |> List.sort compare_term_power_descending
        |> List.fold_left combine_terms []

    let string_of_terms terms = 
        terms
        |> List.filter (fun {coefficient} -> not (coefficient = 0))
        |> List.fold_left
            (fun str term ->
                if str = ""
                then term_to_string term
                else
                    if term.coefficient > 0
                    then Printf.sprintf "%s + %s" str (term_to_string term)
                    else Printf.sprintf "%s - %s" str (term_to_string { term with coefficient = -1 * term.coefficient })
            )
            ""

end

let () =
    let num_cases = read_int () in
    for _ = 1 to num_cases do
        let exp = (read_line ()) |> Expression.of_string in
        (
            (* exp |> Expression.to_string |> print_endline; *)
            exp 
                |> Expression.simplify 0                
                |> Expression.terms_of_expression
                |> Expression.string_of_terms
                |> print_endline
        )
    done
