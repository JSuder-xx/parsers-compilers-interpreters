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

module StateM = struct

    type ('state, 'result) state_computation_result = 
        {
            state: 'state;
            result: 'result;
        }
    type ('state, 'result) state_function = 'state -> ('state, 'result) state_computation_result
    type ('state, 'result) t = StateM of ('state, 'result) state_function

    let run (StateM f) s = f s

    let (>>=) (StateM state_function: ('state, 'original_result) t) (produce_new_state: 'original_result -> ('state, 'new_result) t) : ('state, 'new_result) t =
        StateM (
            fun (original_state: 'state) ->
            let {result; state} = state_function original_state in 
            let (StateM new_state_function) = produce_new_state result in
            new_state_function state
        )

    let return (result: 'result) : ('state, 'result) t = StateM (fun state -> { result; state })

    let map (fn: 'original_result -> 'new_result) state =
        state
        >>= fun result -> return (fn result)

    let void () = StateM (fun state -> { result = (); state })

    let read_state  = StateM (fun (state: 'state) -> { result = state; state })

    let write_state state : ('state, unit) t = StateM (fun _ -> { result = (); state })

    let execute (StateM state_function) (initial_state: 'state) : 'result =
        let {result} = state_function initial_state in
        result

    (** Turn a list of states into a state that produces a list of the given results. *)
    let sequence (states: ('state, 'result) t list) =
        let rec aux (states_remaining: ('state, 'result) t list) (results_accumulator: 'result list) =
            match states_remaining with
            | [] -> return (results_accumulator |> List.rev)
            | head_state :: states_remaining' ->
                head_state
                >>= fun result -> aux states_remaining' (result::results_accumulator)                   
        in
        aux states []

    let repeat (num_times: int) (state_monad: ('state, 'result) t) =
        let rec aux times_remaining acc =
            if times_remaining = 0
            then return acc 
            else state_monad >>= fun result -> aux (times_remaining - 1) (result::acc) in
        aux num_times []
end

module StringSet = Set.Make(String)

module MonoType = struct
    (* Type without a type variable generalization - though it may itself BE a type variable. *)
    type t = 
        | MultiParameterFunctionType of t list * t
        | TypeVariableName of string
        | ConcreteType of string * t list

    let rec free_type_variables = function
        | TypeVariableName type_variable_name ->
            StringSet.singleton type_variable_name
        | MultiParameterFunctionType (parameter_types, result_type) ->
            StringSet.union (free_type_variables_of_types parameter_types) (free_type_variables result_type)
        | ConcreteType (_, type_arguments) ->
            free_type_variables_of_types type_arguments
    and free_type_variables_of_types types =
        List.fold_left (fun acc_set current_type -> current_type |> free_type_variables |> (StringSet.union acc_set)) StringSet.empty types        

    let is_not_type_variable_of type_variable_name mono_type = 
        not (StringSet.mem type_variable_name (free_type_variables mono_type))

    let rec to_string = function
        | TypeVariableName type_variable_name ->
            type_variable_name
        | MultiParameterFunctionType (parameter_types, result_type) -> (
            match parameter_types with
            | [single_parameter_type] -> 
                (match single_parameter_type with
                | MultiParameterFunctionType _ -> Printf.sprintf "(%s) -> %s" (to_string single_parameter_type) (to_string result_type)                 
                | _ -> Printf.sprintf "%s -> %s" (to_string single_parameter_type) (to_string result_type)                 
                )
            | _ -> 
                Printf.sprintf "(%s) -> %s" (parameter_types |> List.map to_string |> String.concat ", ") (to_string result_type)
        )
        | ConcreteType (type_name, type_arguments) ->
            match type_arguments with
            | [] -> type_name
            | _ -> Printf.sprintf "%s[%s]" type_name (type_arguments |> List.map to_string |> String.concat ", ")
end

module TypeSubstitutionMapping = struct
    module Map = Map.Make(String)
    open MonoType

    type t = | TypeSubstitutionMap of MonoType.t Map.t

    let empty : t = TypeSubstitutionMap Map.empty

    let make tuple_list = 
        TypeSubstitutionMap (
            tuple_list
            |> List.fold_left 
                (fun map (name, mono_type) ->
                    Map.add name mono_type map
                )
                Map.empty            
        )

    let rec apply_substitution_to_mono_type (type_substitution_map: t) = function
        | TypeVariableName type_variable_name as this_type_variable ->
            let (TypeSubstitutionMap map) = type_substitution_map in
            (match Map.find_opt type_variable_name map with
            | Some substituted_type -> 
                Printf.sprintf "Substituting type variable %s with type %s found in map" type_variable_name (MonoType.to_string substituted_type) |> debug;
                apply_substitution_to_mono_type type_substitution_map substituted_type
            | None -> 
                this_type_variable
            )
        | MultiParameterFunctionType (parameter_types, result_type) ->
            let substitute_with_current_map = apply_substitution_to_mono_type type_substitution_map in
            MultiParameterFunctionType (
                parameter_types |> List.map substitute_with_current_map
                , substitute_with_current_map result_type            
            )
        | ConcreteType (type_name, type_arguments) ->
                ConcreteType (
                    type_name, 
                    type_arguments |> List.map (apply_substitution_to_mono_type type_substitution_map)
                ) 
    
    let rec make_type_substitution_unifying (type_substitution_map: t) left_type right_type =
        let sub = apply_substitution_to_mono_type type_substitution_map in
        match (sub left_type, sub right_type) with
        | TypeVariableName left_name, TypeVariableName right_name when left_name = right_name -> 
            type_substitution_map
        
        | TypeVariableName left_name, _ when MonoType.is_not_type_variable_of left_name right_type -> 
            Printf.sprintf "mgu: adding type variable %s to substitution map as %s" left_name (right_type |> MonoType.to_string) |> debug;  
            let (TypeSubstitutionMap map) = type_substitution_map in
            TypeSubstitutionMap (Map.add left_name right_type map)            
            
        | _, TypeVariableName _ -> 
            (* flip the arguments so we can always do case analysis on a left-side type variable *)
            make_type_substitution_unifying type_substitution_map right_type left_type
        
        | MultiParameterFunctionType (left_parameter_types, left_return_type), MultiParameterFunctionType (right_parameter_types, right_return_type) -> 
            make_type_substitution_unifying 
                (of_types type_substitution_map left_parameter_types right_parameter_types )
                left_return_type 
                right_return_type 

        | ConcreteType (left_type_name, left_type_arguments), ConcreteType (right_type_name, right_type_arguments) when left_type_name = right_type_name ->
            of_types type_substitution_map left_type_arguments right_type_arguments

        | left_type', right_type' -> 
            failwith (Printf.sprintf "Unable to unify type %s and %s" (MonoType.to_string left_type') (MonoType.to_string right_type'))            
    and of_types (type_substitution_map: t) left_types right_types =
        List.combine left_types right_types
        |> List.fold_left (fun current_substitution_map (left_param_type, right_param_type) -> make_type_substitution_unifying current_substitution_map left_param_type right_param_type) type_substitution_map
    
    let rename_type_variables t = StateM.(
        let get_name k = 
            let contains_key key = 
                read_state
                |> map (fun (map, _) -> Map.mem key map) in         
            let addName k = 
                read_state
                >>= fun (map, type_letter) ->
                    let next_type_letter = Char.chr ((Char.code type_letter) + 1) in
                    write_state (Map.add k type_letter map, next_type_letter) in
            contains_key k
            >>= fun success -> (
                if (not success) 
                then (addName k)
                else void ()
            )
            >>= fun _ -> read_state
            |> map (fun (map, _) -> Map.find k map) in
        MonoType.(
            let rec run = function
            | TypeVariableName variable_name ->
                get_name variable_name
                >>= fun new_name -> return (TypeVariableName (Printf.sprintf "%c" new_name))
            | ConcreteType (name, type_list) ->
                type_list
                |> List.map run
                |> StateM.sequence 
                |> map (fun list -> ConcreteType (name, list))
            | MultiParameterFunctionType (parameter_types, result_type) ->
                parameter_types
                |> List.map run
                |> StateM.sequence 
                >>= fun parameter_types_renamed -> (run result_type)
                >>= fun result_type_renamed -> return (MultiParameterFunctionType (parameter_types_renamed, result_type_renamed))
            in
            execute (run t) (Map.empty, 'a') 
        )
    )
end

(** Top level _Generalization_. Even if the type has no type variables this is always the top. *)
module TypeScheme = struct
    (** Top level _Type Generalization_. Even if the type has no type variables this is always the top. *)
    type t = | ForAll of StringSet.t * MonoType.t

    let no_generalization mono_type : t = ForAll (StringSet.empty, mono_type) 

    let extract_generalization mono_type : t =
        ForAll (
            MonoType.free_type_variables mono_type
            , mono_type
        )

    let instantiate_type_scheme_to_mono_type (ForAll (type_variable_set, mono_type): t) new_type_variable : (int, MonoType.t) StateM.t = StateM.(
        let original_type_variable_names = type_variable_set |> StringSet.elements in
        (StateM.repeat (original_type_variable_names |> List.length) new_type_variable)
        |> map (fun new_type_variables ->            
            TypeSubstitutionMapping.apply_substitution_to_mono_type
                (TypeSubstitutionMapping.make (List.combine original_type_variable_names new_type_variables))
                mono_type
        )
    )

    let free_type_variables (ForAll (variable_names_set, mono_type)) =
        StringSet.diff (MonoType.free_type_variables mono_type) variable_names_set        

    let to_string (ForAll (variable_names_set, mono_type)) =
        match (variable_names_set |> StringSet.elements |> String.concat  " ") with
        | "" -> MonoType.to_string mono_type
        | variables -> Printf.sprintf "forall[%s] %s" variables (MonoType.to_string mono_type)
end

module VariableTypingEnvironment = struct
    module Map = Map.Make(String)

    type t = | VariableTypingEnvironment of TypeScheme.t Map.t

    let make variable_type_scheme_list : t =
        VariableTypingEnvironment (
            List.fold_left 
                (fun map (variable, type_scheme) -> Map.add variable type_scheme map)
                Map.empty
                variable_type_scheme_list
        )

    let free_type_variables (VariableTypingEnvironment scheme_map) =
        scheme_map
        |> Map.bindings
        |> List.map snd
        |> List.fold_left (fun acc s -> StringSet.union acc (TypeScheme.free_type_variables s)) StringSet.empty

    let lookup_variable_opt name (VariableTypingEnvironment map) = Map.find_opt name map

    let bind_variable_to_type_scheme name scheme (VariableTypingEnvironment environment_map) = VariableTypingEnvironment (Map.add name scheme environment_map)

    let make_type_scheme_from_mono_type (environment: t) (mono_type: MonoType.t) =
        TypeScheme.ForAll (
            StringSet.diff (MonoType.free_type_variables mono_type) (free_type_variables environment)
            , mono_type
        )

    let to_variables_string (VariableTypingEnvironment map) =
        Map.bindings map
        |> List.map fst
        |> String.concat ", "

end

module Expression = struct
    type t =
        | Variable of string               
        | FunctionDefinition of function_definition         
        | FunctionApplication of function_application 
        | LetExpression of let_expression
    and let_expression =
        {
            variable_name: string;
            variable_expression: t;
            body_expression: t;
        }
    and function_definition = 
        {
            parameter_names: string list;
            function_body: t;
        }
    and function_application =
        {
            function_expression: t;
            argument_values: t list;            
        }

    let rec to_string = function
    | Variable (v) -> v
    | LetExpression {variable_name; variable_expression; body_expression} ->
        Printf.sprintf "let %s = %s in %s" variable_name (to_string variable_expression) (to_string body_expression)
    | FunctionDefinition { parameter_names; function_body } ->
        Printf.sprintf "(fun %s -> %s)" (parameter_names |> String.concat " ") (to_string function_body)
    | FunctionApplication { function_expression; argument_values } ->
        Printf.sprintf "%s(%s)" (to_string function_expression) (argument_values |> List.map to_string |> String.concat ",")
end


module ExpressionTyping = struct

    let new_type_variable = StateM.(
        read_state
        >>= fun type_variable_count -> write_state (type_variable_count + 1)
        >>= fun _ -> return (MonoType.TypeVariableName (Printf.sprintf "T%d" type_variable_count))
    )

    let rec solve 
        (typing_environment: VariableTypingEnvironment.t) 
        (type_substitution_map: TypeSubstitutionMapping.t) 
        (expression: Expression.t) 
        (expected_type: MonoType.t) 
        : (int, TypeSubstitutionMapping.t) StateM.t = StateM.(
        
        match expression with
        | Variable variable_name ->
            (match VariableTypingEnvironment.lookup_variable_opt variable_name typing_environment with
            | Some type_scheme ->
                TypeScheme.instantiate_type_scheme_to_mono_type type_scheme new_type_variable
                >>= fun mono_type_of_variable ->
                    let type_after_substitution = TypeSubstitutionMapping.apply_substitution_to_mono_type type_substitution_map mono_type_of_variable in
                    Printf.sprintf "Found variable %s of type %s which becomes %s after substitution" variable_name (MonoType.to_string mono_type_of_variable) (MonoType.to_string type_after_substitution) |> debug;  
                    return (
                        TypeSubstitutionMapping.make_type_substitution_unifying 
                            type_substitution_map 
                            expected_type 
                            type_after_substitution
                    )

            | None ->
                failwith (Printf.sprintf "Unable to find variable '%s' in environment with variables %s" variable_name (VariableTypingEnvironment.to_variables_string typing_environment))
            )
        | LetExpression {variable_name; variable_expression; body_expression} ->
            new_type_variable
            >>= fun new_type_variable_for_expression -> solve typing_environment type_substitution_map variable_expression new_type_variable_for_expression 
            >>= fun new_type_substition_map ->
                let local_type_for_expression = TypeSubstitutionMapping.apply_substitution_to_mono_type new_type_substition_map new_type_variable_for_expression in
                let new_environment = VariableTypingEnvironment.bind_variable_to_type_scheme 
                    variable_name 
                    (VariableTypingEnvironment.make_type_scheme_from_mono_type typing_environment local_type_for_expression)
                    typing_environment in
                solve new_environment new_type_substition_map body_expression expected_type 
        | FunctionDefinition { parameter_names; function_body } ->
            StateM.repeat (List.length parameter_names) new_type_variable 
            >>= fun parameter_type_variables -> new_type_variable            
            >>= fun return_type_type_variable -> 
                let new_substitution_map = 
                    TypeSubstitutionMapping.make_type_substitution_unifying 
                        type_substitution_map 
                        expected_type 
                        (MultiParameterFunctionType (parameter_type_variables, return_type_type_variable)) in
                let parameter_name_and_scheme_list = 
                    List.combine 
                        parameter_names 
                        (parameter_type_variables |> List.map TypeScheme.no_generalization) in
                let environment_with_function_parameters = 
                    parameter_name_and_scheme_list
                    |> (List.fold_left 
                        (fun env (name, scheme) -> 
                            Printf.sprintf "adding variable %s to environment" name |> debug; 
                            VariableTypingEnvironment.bind_variable_to_type_scheme name scheme env
                        ) 
                        typing_environment                       
                    ) in
                solve environment_with_function_parameters new_substitution_map function_body return_type_type_variable                  
        | FunctionApplication { function_expression; argument_values } -> 
            StateM.repeat (List.length argument_values) new_type_variable
            >>= fun parameter_type_variables -> 
                solve typing_environment type_substitution_map function_expression (MultiParameterFunctionType (parameter_type_variables, expected_type)) 
            >>= fun substitution_map_for_function_body -> 
                let parameter_type_and_variable_expressions = List.combine parameter_type_variables argument_values in
                let rec state_fold current_type_substition_map = function
                    | [] -> return current_type_substition_map
                    | (parameter_type, argument_value_expression)::remaining ->
                        solve typing_environment current_type_substition_map argument_value_expression parameter_type 
                        >>= fun new_type_substitution_map -> (state_fold new_type_substitution_map remaining) in
                state_fold substitution_map_for_function_body parameter_type_and_variable_expressions                                     
    )

    let type_of typing_environment expression = StateM.(
        let state_monad_of_typing exp =
            new_type_variable
            >>= fun expression_type_variable -> solve typing_environment TypeSubstitutionMapping.empty exp expression_type_variable
            >>= fun type_substitution_map -> 
                Printf.sprintf "Ready for final substitution!" |> debug; 
                return (TypeSubstitutionMapping.apply_substitution_to_mono_type type_substitution_map expression_type_variable)
        in
        execute (state_monad_of_typing expression) 0 
        |> TypeSubstitutionMapping.rename_type_variables  
    )
end


(** Parse a single identifier. *)
let identifier_parser = Parser.(
    (letter <|> equals '_')
    >>= fun first_letter -> zero_to_many (attempt_in_order [letter; digit; equals '_']) 
    |> map (fun char_list ->
        (first_letter::char_list)
        |> List.map (String.make 1)
        |> String.concat ""
    )
)
let variable_parser = identifier_parser |> Parser.map (fun variable_name -> Expression.Variable variable_name)                                    

let arrow_parser = Parser.(skip_whitespace >> token "->" >> skip_whitespace)

(** Parse a space delimited list of identifiers *)
let argument_identifiers_parser = Parser.(zero_to_many_delimited ~item_parser: identifier_parser ~delimiter_parser: (equals ' ' >> skip_whitespace))

module ExpressionParser = struct
    open Parser

    let rec expression_parser input =
        (attempt_in_order [
            let_expression_parser
            ; function_definition_expression_parser
            ; function_application_parser
            ; simple_expression_parser            
        ]) input
    and let_expression_parser input =
        (
            (token "let" >> skip_whitespace >> identifier_parser)
            >>= fun variable_name -> (skip_whitespace >> equals '=' >> skip_whitespace >> expression_parser)
            >>= fun variable_expression -> (skip_whitespace >> token "in" >> skip_whitespace >> expression_parser)
            |> map (fun body_expression -> Expression.LetExpression {variable_name; variable_expression; body_expression })
        ) input
    and function_definition_expression_parser input =
        (
            (token "fun" >> skip_whitespace >> argument_identifiers_parser)
            >>= fun parameter_names -> (arrow_parser >> expression_parser)
            |> map (fun function_body -> Expression.FunctionDefinition { parameter_names; function_body })
        ) input
    and parameter_list_parser input = 
        (
            parens (zero_to_many_delimited ~item_parser: expression_parser ~delimiter_parser: (skip_whitespace >> equals ',' >> skip_whitespace))
        ) input
    and function_parameters_parser function_expression input =
        (
            parameter_list_parser
            |> map (fun argument_values -> Expression.FunctionApplication { argument_values; function_expression })
        ) input
    and function_application_parser input =
        (
            (simple_expression_parser << skip_whitespace)
            >>= fun function_expression -> function_parameters_parser function_expression
        ) input
    and simple_expression_parser input = 
        (skip_whitespace >> attempt_in_order [
            (parens expression_parser)            
            ; (
                (identifier_parser << skip_whitespace)
                >>= fun variable_name -> 
                    let variable = Expression.Variable variable_name in
                    (
                        function_parameters_parser variable
                        <|> (succeed_with variable)
                    )
            )            
        ]) input

end

module TypeParser = struct
    open Parser
    let mono_type_parser (bound_type_variables: StringSet.t) =     
        let rec rec_mono_type_parser input = 
            (skip_whitespace >> attempt_in_order [
                function_without_arguments_parser
                ; function_with_arguments_parser
                ; arrow_function_parser
                ; simple_mono_type_parser            
            ]) input
        and function_body_parser argument_types input = 
            (
                (arrow_parser >> rec_mono_type_parser)
                |> map (fun result_type -> MonoType.MultiParameterFunctionType (argument_types, result_type))
            ) input
        and function_without_arguments_parser input = 
            (
                token "()" >> (function_body_parser [])
            ) input
        and function_with_arguments_parser input =
            (
                parens type_list_parser
                >>= fun parameter_types -> function_body_parser parameter_types
            ) input
        and arrow_function_parser input = 
            (
                simple_mono_type_parser >>= fun argument_type -> function_body_parser [argument_type]
            ) input
        and type_list_parser input = 
            (
                one_to_many_delimited ~item_parser: rec_mono_type_parser ~delimiter_parser: (skip_whitespace >> equals ',' >> skip_whitespace)
            ) input
        and type_application_list_parser input =
            (
                between 
                    ~start_parser: (equals '[' >> skip_whitespace) 
                    ~end_parser: (equals ']' >> skip_whitespace)
                    type_list_parser
            ) input
        and simple_mono_type_parser input = 
            (skip_whitespace >> attempt_in_order [
                (parens rec_mono_type_parser)
                ; (
                    (identifier_parser << skip_whitespace)
                    >>= fun type_name -> 
                        if (StringSet.mem type_name bound_type_variables)
                        then (succeed_with (MonoType.TypeVariableName type_name))
                        else (
                            (type_application_list_parser |> map (fun applied_types -> MonoType.ConcreteType (type_name, applied_types)))
                            <|> (succeed_with (MonoType.ConcreteType (type_name, [])))
                        )                
                ) 
            ]) input in
        rec_mono_type_parser

    let type_scheme_parser =
        (
            (token "forall[" >> skip_whitespace >> argument_identifiers_parser << (skip_whitespace >> equals ']'))
            >>= fun bound_type_variables -> 
                let bound_type_variables_set = StringSet.of_list bound_type_variables in
                (mono_type_parser bound_type_variables_set)
                |> map (fun mono_type -> TypeScheme.ForAll(bound_type_variables_set, mono_type))
        )
        <|>
        (
            (mono_type_parser StringSet.empty)
            |> map (fun mono_type -> TypeScheme.ForAll(StringSet.empty, mono_type))
        )

    let variable_type_scheme_parser =
        (identifier_parser << skip_whitespace << equals ':' << skip_whitespace) 
        >>= fun variable_name -> type_scheme_parser
        |> map (fun type_scheme -> (variable_name, type_scheme))
    
    let variable_typing_environment_parser =
        zero_to_many (skip_whitespace >> variable_type_scheme_parser)
        |> map VariableTypingEnvironment.make

end

let prelude = 
    [ "head: forall[a] list[a] -> a"
    ; "tail: forall[a] list[a] -> list[a]"
    ; "nil: forall[a] list[a]"
    ; "cons: forall[a] (a, list[a]) -> list[a]"
    ; "cons_curry: forall[a] a -> list[a] -> list[a]"
    ; "map: forall[a b] (a -> b, list[a]) -> list[b]"
    ; "map_curry: forall[a b] (a -> b) -> list[a] -> list[b]"
    ; "one: int"
    ; "zero: int"
    ; "succ: int -> int"
    ; "plus: (int, int) -> int"
    ; "eq: forall[a] (a, a) -> bool"
    ; "eq_curry: forall[a] a -> a -> bool"
    ; "not: bool -> bool"
    ; "true: bool"
    ; "false: bool"
    ; "pair: forall[a b] (a, b) -> pair[a, b]"
    ; "pair_curry: forall[a b] a -> b -> pair[a, b]"
    ; "first: forall[a b] pair[a, b] -> a"
    ; "second: forall[a b] pair[a, b] -> b"
    ; "id: forall[a] a -> a"
    ; "const: forall[a b] a -> b -> a"
    ; "apply: forall[a b] (a -> b, a) -> b"
    ; "apply_curry: forall[a b] (a -> b) -> a -> b"
    ; "choose: forall[a] (a, a) -> a"
    ; "choose_curry: forall[a] a -> a -> a"
    ]
    |> String.concat " "

let prelude_typing_environment = match (Parser.parse TypeParser.variable_typing_environment_parser prelude) with
    | Some e -> e
    | None -> failwith "prelude failed to parse!!!"


let test_case_3 = ("fun f -> let x = fun g y -> let _ = g(y) in eq(f, g) in x", "forall[a b] (a -> b) -> (a -> b, a) -> bool")
let test_case_11 = ("let f = fun x -> x in pair(f(one), f(true))", "pair[int, bool]")
let test_case_15 = ("id(id)", "forall[a] a -> a")
let test_case_17 = ("let x = id in let y = let z = x(id) in z in y", "forall[a] a -> a")
let test_case_18 = ("cons(id, nil)", "forall[a] list[a -> a]")
let test_case_23 = ("fun x -> let y = let z = x(fun x -> x) in z in y", "forall[a b] ((a -> a) -> b) -> b")
let test_case_24 = ("fun x -> fun y -> let x = x(y) in x(y)", "forall[a b] (a -> a -> b) -> a -> b")
let test_cases = 
    [ test_case_3
    ; test_case_11
    ; test_case_15
    ; test_case_17
    ; test_case_18
    ; test_case_23
    ; test_case_24
    ]

let type_string_of_expression_string expression_string =
    let expression = match (Parser.parse ExpressionParser.expression_parser expression_string) with
        | Some expression -> expression
        | None -> failwith "failed to parse expression!" in
    (
        expression |> Expression.to_string |> debug;  
        ExpressionTyping.type_of prelude_typing_environment expression 
        |> TypeScheme.extract_generalization 
        |> TypeScheme.to_string 
    )

let run_test_case (given_expression, then_expect_type) =
    let actual_type = type_string_of_expression_string given_expression in
    if actual_type = then_expect_type
    then None
    else Some (Printf.sprintf "Given expression:\n\t%s\nExpected type:\n\t%s\nActual type:\n\t%s\n" given_expression then_expect_type actual_type)

let hacker_rank_driver () = 
    type_string_of_expression_string (read_line ())
    |> print_endline

let test_driver () =
    test_cases
    |> List.map run_test_case
    |> List.iter (fun result_option ->
        match result_option with
        | Some result -> print_endline result
        | None -> ()
    )

let () =
    test_driver ()
    (* hacker_rank_driver () *)
 
(*
https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system
http://dev.stephendiehl.com/fun/006_hindley_milner.html
*)
