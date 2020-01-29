module Zipper = struct
    type 'a t = {
        before: 'a list;
        current: 'a;
        after: 'a list;
    }

    let init current = { before = []; current; after = []; }
   
    let current zipper = zipper.current

    let update zipper value = { zipper with current = value }
    
    let move_left zipper = 
        match zipper.before with
        | before_item::before_remaining ->
            {
                before = before_remaining;
                current = before_item;
                after = zipper.current::zipper.after
            }
        | _ -> failwith "attempted to navigate too far to the left"

    let move_right default_value zipper = 
        match zipper.after with
        | after_item::after_remaining ->
            {
                before = zipper.current::zipper.before;
                current = after_item;
                after = after_remaining;
            }
        | _ -> 
            {
                before = zipper.current::zipper.before;
                current = default_value;
                after = [];
            }

end

type state = {
    memory_zipper : int Zipper.t;
    count_of_instructions_executed: int;
    input : char list;
    output : char list;
}

let initial_state input =
    {
        input;
        output = [];
        count_of_instructions_executed = 0;
        memory_zipper = Zipper.init 0
    }

let max_instructions = 100000

let can_execute_instruction { count_of_instructions_executed } = count_of_instructions_executed < max_instructions
let was_killed { count_of_instructions_executed } = count_of_instructions_executed > max_instructions

type instruction = state -> state

let increment_instruction_count_by by state = 
    { state with count_of_instructions_executed = state.count_of_instructions_executed + by }

let increment_instruction_count = increment_instruction_count_by 1

let run_instruction (state: state) (instruction: instruction) =
    if can_execute_instruction state
    then instruction state 
    else increment_instruction_count state 

let run_instructions instructions initial_state =
    instructions 
    |> List.fold_left run_instruction initial_state

let read_value_at_data_pointer state = Zipper.current state.memory_zipper

let write_value_at_data_pointer state value = 
    { state with memory_zipper = Zipper.update state.memory_zipper value }

let decrement_data_pointer state = 
    { state with memory_zipper = Zipper.move_left state.memory_zipper }
    |> increment_instruction_count
    
let increment_data_pointer state = 
    { state with memory_zipper = Zipper.move_right 0 state.memory_zipper }
    |> increment_instruction_count

let increment_value state =     
    let current_value = read_value_at_data_pointer state in
    write_value_at_data_pointer state ((current_value + 1) mod 256)
    |> increment_instruction_count

let decrement_value state = 
    let current_value = read_value_at_data_pointer state in
    write_value_at_data_pointer 
        state 
        (
            let value = current_value -1 in
            if value < 0 then value + 256 else value
        )
    |> increment_instruction_count

let read_input_into_data_pointer state =
    match state.input with
    | current_input::remaining_input ->
        let input_written_state = write_value_at_data_pointer state (Char.code current_input) in
        { input_written_state with input = remaining_input }
        |> increment_instruction_count
    | _ -> failwith "ran out of input"    

let output_value_at_data_pointer state = 
    let value = read_value_at_data_pointer state in
    { state with output = (Char.chr value)::state.output }
    |> increment_instruction_count

let loop fns =
    let rec recurse state =
        let start_value = read_value_at_data_pointer state in
        let state_after_condition_check = increment_instruction_count state in
        if start_value = 0
        then 
            (increment_instruction_count state_after_condition_check)
        else (              
            let new_state = (run_instructions fns state_after_condition_check) |> increment_instruction_count in
            if (can_execute_instruction new_state) && ((read_value_at_data_pointer new_state) > 0)
            then recurse new_state
            else new_state                
        ) in
    recurse

let parse (chars: char list) : (instruction list * char list) =
    let rec recurse acc_instructions remaining_chars =
        (            
            match remaining_chars with
            | '<'::remaining -> recurse (decrement_data_pointer::acc_instructions) remaining
            | '>'::remaining -> recurse (increment_data_pointer::acc_instructions) remaining
            | '+'::remaining -> recurse (increment_value::acc_instructions) remaining
            | '-'::remaining -> recurse (decrement_value::acc_instructions) remaining
            | ','::remaining -> recurse (read_input_into_data_pointer::acc_instructions) remaining
            | '.'::remaining -> recurse (output_value_at_data_pointer::acc_instructions) remaining
            | '['::remaining ->
                let (child_instructions, remaining') = recurse [] remaining in
                recurse ((loop child_instructions)::acc_instructions) remaining'
            | ']'::remaining -> (acc_instructions |> List.rev, remaining)
            | _::remaining -> recurse acc_instructions remaining
            | [] -> (acc_instructions |> List.rev, [])
        ) in
    recurse [] chars           

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

let string_of_chars chars =
    chars 
    |> List.map (String.make 1)
    |> String.concat ""

let () =
    let _ = read_line () in
    let program_input = (
        let line = read_line () in 
        String.sub line 0 ((String.length line) - 1)
        |> reversed_chars_of_string
        |> List.rev
    ) in
    let program_chars = (read_lines ()) |> chars_of_strings in 
    let (instructions, _) = program_chars |> parse in
    let final_state = run_instructions instructions (initial_state program_input) in
    (
        final_state.output
            |> List.rev
            |> string_of_chars
            |> print_endline;
        if (was_killed final_state)
        then print_endline "PROCESS TIME OUT. KILLED!!!"
        else ()
    )
