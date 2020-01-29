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

    let rec gcd a b =
        if a = 0 
        then b
        else gcd (b mod a) a

    let apply v fn = fn v
end
open Utils

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

module RationalNumber = struct
    type t = { numerator: int; denominator: int }

    let move_negative_to_denominator { numerator; denominator } =
        if denominator < 0 
        then { numerator = numerator * -1; denominator = denominator * -1 }
        else { numerator; denominator }

    let simplify { numerator; denominator } =
        let gcd' = gcd numerator denominator in 
        if gcd' = 1
        then move_negative_to_denominator { numerator; denominator }
        else move_negative_to_denominator { 
            numerator = numerator / gcd'; 
            denominator = denominator / gcd';
        }

    let (+/) left right = 
        if left.denominator = right.denominator
        then { numerator = left.numerator + right.numerator; denominator = left.denominator }
        else simplify {
            numerator = (left.numerator * right.denominator) + (right.numerator * left.denominator);
            denominator = left.denominator * right.denominator
        }

    let (-/) left right = 
        if left.denominator = right.denominator
        then { numerator = (left.numerator - right.numerator); denominator = left.denominator }
        else simplify {
            numerator = (left.numerator * right.denominator) - (right.numerator * left.denominator);
            denominator = left.denominator * right.denominator
        }

    let ( */ ) left right =
        simplify {
            numerator = (left.numerator * right.numerator);
            denominator = (left.denominator * right.denominator);
        }

    let invert { numerator; denominator } = 
        {
            numerator = denominator;
            denominator = numerator;
        }

    let (//) left right =
        simplify left */ (invert right)

    let of_string rational =
        let { numerator; denominator } = simplify rational in
        if denominator = 1
        then string_of_int numerator
        else Printf.sprintf "%d/%d" numerator denominator

    let get_integer_exn rational =
        let { numerator; denominator } = simplify rational in
        if (denominator = 1)
        then numerator
        else failwith "expected an integer by got a fraction with a denominator"
end

module IntuitiveRuntime = struct
    type function_value = {
        coefficients: RationalNumber.t list;
        constant: RationalNumber.t;
    }

    let list_of_function_value { coefficients; constant } =
        constant::(List.rev coefficients) |> List.rev

    let get_constant_opt { coefficients; constant } = match coefficients with
        | [] -> Some constant
        | _ -> None

    let get_constant_exn { coefficients; constant } = match coefficients with
        | [] -> constant
        | _ -> failwith "Expecting a constant but got a function."

    let is_constant fd = match get_constant_opt fd with
        | Some _ -> true
        | _ -> false

    let string_of_function_value fd =
        fd
        |> list_of_function_value 
        |> List.map RationalNumber.of_string
        |> String.concat ", "

    open RationalNumber

    let apply_to_function { coefficients; constant } (values: RationalNumber.t list) : function_value =    
        let len_values = List.length values in
        let len_coefficients = List.length coefficients in
        if (len_values > len_coefficients)
        then failwith (Printf.sprintf "Attempting to apply %d values to a function that accepts %d" len_values len_coefficients)
        else
            let (coefficients_to_apply, coefficients_remaining) = take len_values coefficients in
            let new_constant = (List.combine coefficients_to_apply values)
                |> List.fold_left
                    (fun total (coeff, value) -> total +/ (coeff */ value))
                    constant in
            {
                constant = new_constant;
                coefficients = coefficients_remaining
            }        

    module StackFrame = Map.Make(String)

    type stack_frame = function_value StackFrame.t

    type expression = stack_frame -> function_value

    type binary_expression = expression -> expression -> expression 

    let lift_binary_to_expression 
        fn
        (left_expression: expression) 
        (right_expression: expression) 
        (stack_frame: stack_frame)
        : function_value =
        let eval expr = stack_frame |> expr |> get_constant_exn in
        let (left, right) = (eval left_expression), (eval right_expression) in
        {
            constant = fn left right;
            coefficients = []
        } 

    let lift_unary_to_expression
        fn
        (expression: expression) 
        (stack_frame: stack_frame)
        : function_value =
        {
            constant = fn (stack_frame |> expression |> get_constant_exn);
            coefficients = []
        } 

    let sum_expression = lift_binary_to_expression (+/)
    let diff_expression = lift_binary_to_expression (-/)
    let product_expression = lift_binary_to_expression ( */ )
    let quotient_expression = lift_binary_to_expression (//)

    let positive_expression = lift_unary_to_expression (fun n -> n)
    let negative_expression = lift_unary_to_expression (fun {numerator; denominator} -> { numerator = numerator * -1; denominator })

    let function_value_expression function_value (_: stack_frame) : function_value = function_value
    let integer_constant_expression (numerator: int) (_: stack_frame) : function_value = { constant = { numerator; denominator = 1 }; coefficients = [] }
    let constant_expression (constant: RationalNumber.t) (_: stack_frame) : function_value = { constant; coefficients = [] }
    let read_variable_expression = StackFrame.find

    let apply_to_function_expression 
        (identifier: string)
        (argument_expressions: expression list)
        (stack_frame: stack_frame)
        : function_value =
        let function_to_apply = StackFrame.find identifier stack_frame in
        let argument_values = argument_expressions |> List.map (Utils.apply stack_frame) |> List.map get_constant_exn in 
        apply_to_function function_to_apply argument_values

    type run_time_state = 
        {
            stack_frame: stack_frame;
            output: string list;        
        }

    let run_time_state_init () : run_time_state = 
        {
            stack_frame = StackFrame.empty;
            output = []
        }

    type statement = run_time_state -> run_time_state

    let statement_list_statement 
        (statements: statement list) 
        (run_time_state: run_time_state)
        : run_time_state =
        List.fold_left
            (|>)
            run_time_state
            statements

    let assignment_statement 
        (identifier: string)
        (expression: expression)
        ({output; stack_frame}: run_time_state) 
        : run_time_state =
        {
            stack_frame = StackFrame.update identifier (fun _ -> Some (expression stack_frame)) stack_frame;
            output;
        }
        
    let do_statement 
        (repetitions: expression)
        (body: statement)
        (initial_state: run_time_state)
        : run_time_state =
        let repetitions' = initial_state.stack_frame |> repetitions |> get_constant_exn |> get_integer_exn in
        let rec repeat count_remaining current_state = 
            if count_remaining = 0
            then current_state
            else repeat (count_remaining - 1) (body current_state) in
        repeat repetitions' initial_state

    let what_is_statement
        (expr: expression)
        ({stack_frame; output}: run_time_state)
        : run_time_state =
        {
            stack_frame;
            output = (stack_frame |> expr |> string_of_function_value)::output
        }
end

module IntuitiveParser = struct
    open Parser
    open IntuitiveRuntime

    let binary_operation_parser op_parser fn = 
        skip_whitespace >> op_parser >> (succeed_with fn)

    let unary_operation_parser op_parser fn = 
        skip_whitespace >> op_parser >> (succeed_with fn)

    let sum_op_parser = binary_operation_parser (equals '+') sum_expression
    let diferrence_op_parser = binary_operation_parser (equals '-') diff_expression
    let product_op_parser = binary_operation_parser (equals '*') product_expression
    let quotient_op_parser = binary_operation_parser (equals '/') quotient_expression

    let positive_operation_parser = unary_operation_parser (equals '+') positive_expression
    let negative_operation_parser = unary_operation_parser (equals '-') negative_expression

    let identifier_parser = 
        one_to_many letter 
        |> map (fun char_list -> 
            char_list 
            |> List.map (String.make 1) 
            |> String.concat ""
        )
        >>= fun letter_part -> 
            (
                (integer |> map (fun num -> Printf.sprintf "%s%d" letter_part num))
                <|> (succeed_with letter_part)
            )

    let rec expression_parser input = infix_binary_operation
        ~operand_parser: mult_div_parser
        ~op_parser: (sum_op_parser <|> diferrence_op_parser)
        input
    and mult_div_parser input = infix_binary_operation
        ~operand_parser: term_parser
        ~op_parser: (product_op_parser <|> quotient_op_parser)
        input
    and argument_parser input = 
        (
            equals '['
            >> expression_parser
            << (skip_whitespace << equals ']')
        ) input
    and term_parser input =
        (
            skip_whitespace
            >>
            attempt_in_order [
                (
                    (positive_operation_parser <|> negative_operation_parser)
                    >>= fun unary_operation -> term_parser
                    >>= fun term -> succeed_with (unary_operation term)
                )
                ; integer |> map integer_constant_expression                
                ; (
                    identifier_parser 
                    >>= fun identifier -> zero_to_many argument_parser
                    >>= fun arguments ->
                        succeed_with (
                            match arguments with
                            | [] -> read_variable_expression identifier
                            | _ -> apply_to_function_expression identifier arguments
                        )
                )                
                ; parens (expression_parser << skip_whitespace)
            ]  
        ) input  

    let function_declaration_parser =
        skip_whitespace
        >> token "of"
        >> skip_whitespace
        >> integer
        >> skip_whitespace
        >> equals ':'
        >> skip_whitespace        
        >> (one_to_many_delimited ~item_parser: expression_parser ~delimiter_parser: (skip_whitespace >> equals ',' >> skip_whitespace))
        |> map (fun expressions -> 
            let (coefficients, constant_list) = 
                expressions 
                |> List.map (Utils.apply StackFrame.empty) 
                |> List.map get_constant_exn 
                |> take ((List.length expressions) - 1) in
            { coefficients; constant = List.hd constant_list } 
        )

    let declaration_statement_parser =
        identifier_parser
        >>= fun identifier -> 
            (skip_whitespace >> token "is" >> skip_whitespace)
            >> (
                (
                    token "function" 
                    >> function_declaration_parser |> map function_value_expression
                )
                <|>
                expression_parser                                   
            ) 
            >>= fun expression -> succeed_with (assignment_statement identifier expression)
            << (skip_whitespace >> equals '.')

    let single_assignment_parser =
        expression_parser
        >>= fun expr -> (skip_whitespace >> (token "to") >> skip_whitespace >> identifier_parser) 
        >>= fun identifier -> succeed_with (assignment_statement identifier expr)

    let assignment_parser =
        token "assign"
        >> skip_whitespace
        >> (
            one_to_many_delimited ~item_parser: single_assignment_parser ~delimiter_parser: (skip_whitespace >> (token "and") >> skip_whitespace)
            |> map statement_list_statement
        )
        << (skip_whitespace >> equals '!')

    let do_parser =
        (token "do" >> skip_whitespace >> equals '{' >> expression_parser)
        >>= fun expr -> (skip_whitespace >> (equals '}') >> skip_whitespace >> assignment_parser)
        >>= fun assignment -> succeed_with (do_statement expr assignment)

    let what_is_parser =
        token "what is"
        >> skip_whitespace
        >> one_to_many_delimited ~item_parser: (expression_parser |> map what_is_statement) ~delimiter_parser: (token "and")
        |> map statement_list_statement
        << (skip_whitespace >> equals '?')

    let statement_parser =
        skip_whitespace
        >> attempt_in_order [
            declaration_statement_parser
            ; assignment_parser
            ; do_parser
            ; what_is_parser
        ]

    let statement_list_parser = one_to_many statement_parser |> map statement_list_statement
end

let reversed_chars_of_string (s: string) : char list =
    let len = String.length s in
    let read = String.get s in
    let rec build acc index = 
    if index = len
    then acc
    else build ((read index)::acc) (index + 1) in
    (build [] 0) 

let chars_of_strings (strs: string list) : char list =
    strs 
    |> List.rev
    |> (List.map reversed_chars_of_string)
    |> List.flatten
    |> List.rev

let rec read_lines () =
    try
        let line = read_line () in
        line::(read_lines ())
    with
        _ -> []

let () =
    match (read_lines ()) |> chars_of_strings |> List.map Char.lowercase_ascii |> IntuitiveParser.statement_list_parser with
    | Some (program_statement, _) ->
        IntuitiveRuntime.run_time_state_init ()
        |> program_statement 
        |> (fun {output} ->
            output
            |> List.rev
            |> List.iter (Printf.printf "%s\n")
        )
    | _ -> print_endline "failed to parse program" 
