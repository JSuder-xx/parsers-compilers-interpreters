let take (n: int) (lst: 'a list) =
    let rec recur acc list_remaining num_remaining =
        if num_remaining = 0
        then acc 
        else 
            (
                match list_remaining with
                | [] -> acc
                | head::remaining ->
                    recur (head::acc) remaining (num_remaining - 1)
            ) in
    (recur [] lst n) |> List.rev

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

(* -------------------------------------------------
While Language Run-time 
---------------------------------------------------- *)
module StackFrame = Map.Make(String)

type stack_frame = int StackFrame.t

let strings_of_stack_frame (stack_frame: stack_frame) : string list =
    StackFrame.fold
        (fun key value list ->
            (Printf.sprintf "%s %d" key value)::list
        )
        stack_frame
        []
    |> List.sort (compare)

type 'a expression = stack_frame -> 'a

type int_expresion = int expression

type bool_expression = bool expression

type ('input, 'output) binary_expression = 'input expression -> 'input expression -> 'output expression

let lift_binary_to_expression 
    (fn: 'input -> 'input -> 'output) 
    (left_expression: 'input expression) 
    (right_expression: 'input expression) 
    (stack_frame: stack_frame) =
    fn (left_expression stack_frame) (right_expression stack_frame)

let sum_expression = lift_binary_to_expression (+)
let diff_expression = lift_binary_to_expression (-)
let product_expression = lift_binary_to_expression ( * )
let quotient_expression = lift_binary_to_expression (/)

let less_than_expression : (int, bool) binary_expression = lift_binary_to_expression (<)
let greater_than_expression : (int, bool) binary_expression = lift_binary_to_expression (>)

let and_expression = lift_binary_to_expression (&&)
let or_expression = lift_binary_to_expression (||)

let constant_expression n (_: stack_frame) = n
let read_variable_expression = StackFrame.find

type statement = stack_frame -> stack_frame

let statement_list_statement 
    (statements: statement list) 
    (stack_frame: stack_frame)
    : stack_frame =
    List.fold_left
        (|>)
        stack_frame
        statements

let assignment_statement 
    (identifier: string)
    (expression: int_expresion)
    (stack_frame: stack_frame) 
    : stack_frame =
    StackFrame.update identifier (fun _ -> Some (expression stack_frame)) stack_frame

let if_statement
    (condition_expression: bool_expression)
    (when_true_statement: statement)
    (when_false_statement: statement)    
    (stack_frame: stack_frame) 
    : stack_frame =    
        (
            if (condition_expression stack_frame)
            then when_true_statement
            else when_false_statement
        )
        stack_frame

let rec while_statement 
    (condition_expression: bool_expression)
    (body: statement)
    (stack_frame: stack_frame)
    : stack_frame =
    if (condition_expression stack_frame)
    then while_statement condition_expression body (body stack_frame)
    else stack_frame

(* -----------------------------------------------------------------------------
While Language Parser
-------------------------------------------------------------------------------- *)
open Parser

let binary_operation_parser op_parser fn = 
    skip_whitespace >> op_parser >> (succeed_with fn)

let sum_op_parser = binary_operation_parser (equals '+') sum_expression
let diferrence_op_parser = binary_operation_parser (equals '-') diff_expression
let product_op_parser = binary_operation_parser (equals '*') product_expression
let quotient_op_parser = binary_operation_parser (equals '/') quotient_expression

let less_than_op_parser = binary_operation_parser (equals '<') less_than_expression
let greater_than_op_parser = binary_operation_parser (equals '>') greater_than_expression

let and_op_parser = binary_operation_parser (token "and") and_expression
let or_op_parser = binary_operation_parser (token "or") or_expression

let identifier_parser = 
    one_to_many letter 
    |> map (fun char_list -> 
        char_list 
        |> List.map (String.make 1) 
        |> String.concat ""
    )

let rec int_expression_parser input = 
    infix_binary_operation
        ~operand_parser: mult_div_parser
        ~op_parser: (sum_op_parser <|> diferrence_op_parser)
    input
and mult_div_parser input = 
    infix_binary_operation
        ~operand_parser: int_term_parser
        ~op_parser: (product_op_parser <|> quotient_op_parser)
        input
and int_term_parser input =
    (
        skip_whitespace
        >>
        attempt_in_order [
            integer |> map constant_expression
            ; identifier_parser |> map read_variable_expression
            ; parens (int_expression_parser << skip_whitespace)
        ]  
    )
    input  
    
let rec bool_expression_parser input =
    (
        infix_binary_operation
            ~operand_parser: bool_term_parser
            ~op_parser: (and_op_parser <|> or_op_parser)
        <|>
        bool_term_parser
    )
        input
and relational_parser input =
    (
        int_expression_parser
        >>= fun left_expression -> (less_than_op_parser <|> greater_than_op_parser)
        >>= fun op -> int_expression_parser << skip_whitespace
        >>= fun right_expression -> 
            succeed_with (op left_expression right_expression)
    )
    input
and bool_term_parser input =
    (
        skip_whitespace
        >>
        attempt_in_order [
            (token "true" >> (succeed_with (constant_expression true)))
            ; (token "false" >> (succeed_with (constant_expression false)))
            ; relational_parser
            ; (parens bool_expression_parser)
        ]
    )
    input

let rec assignment_parser =
    identifier_parser
    >>= fun identifier -> (skip_whitespace >> (token ":=") >> int_expression_parser)
    >>= fun int_expression -> succeed_with (assignment_statement identifier int_expression)
and if_parser input =
    (
        (token "if")
        >> (
            bool_expression_parser
            >>= fun bool_expression -> 
                (
                    skip_whitespace 
                    >> token "then" 
                    >> bracketed_statement_list_parser
                )
            >>= fun when_true_statements -> (skip_whitespace >> token "else" >> bracketed_statement_list_parser)
            >>= fun when_false_statements -> 
                succeed_with (if_statement bool_expression when_true_statements when_false_statements)
        )
    )
    input
and while_parser input =
    (   
        (token "while")
        >> (
            bool_expression_parser
            >>= fun bool_expression ->                
                (
                    (token "do")
                    >> bracketed_statement_list_parser
                )
            >>= fun statement_list -> 
                succeed_with (while_statement bool_expression statement_list)
        )
    )
    input

and statement_parser input = 
    (
        skip_whitespace
        >> attempt_in_order [assignment_parser; if_parser; while_parser]
    ) 
    input
and bracketed_statement_list_parser input =
    (
        skip_whitespace
        >>
        between 
            ~start_parser: (equals '{')
            ~end_parser: (skip_whitespace >> (equals '}'))
            statement_list_parser
    )
    input
and statement_list_parser input = 
    (
        one_to_many_delimited 
           ~item_parser: statement_parser
            ~delimiter_parser: (skip_whitespace >> (equals ';'))
        |> map statement_list_statement
    )
    input

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
    match (read_lines ()) |> chars_of_strings |> statement_list_parser with
    | Some (program_statement, _) ->
        StackFrame.empty
        |> program_statement 
        |> strings_of_stack_frame
        |> List.iter (Printf.printf "%s\n")
    | _ -> print_endline "failed to parse program"
