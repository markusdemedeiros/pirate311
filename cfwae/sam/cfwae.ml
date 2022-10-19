open Interpreter

let string_of_err = function
  | E_ArgNum -> "wrong number of arguments"
  | E_ExpectedFun -> "expected a function"
  | E_ExpectedNum -> "expected a number"
  | E_Unbound v -> "variable '" ^ v ^ "' is unbound"
  | E_DuplicateBinding -> "duplicate binding"
  | E_Div0 -> "division by zero"

let string_of_val = function
  | RV_Num n -> Uint63.to_string n
  | RV_Closure _ -> "<closure>"

let rec run t =
  match Lazy.force t with
  | Ret r -> print_endline (string_of_val r)
  | Tau t -> run t
  | Vis (err, _) -> print_endline ("error: " ^ string_of_err err)

let usage_msg = "cfwae <source>"
let source_paths = ref []

let () =
  let anon_handler arg = source_paths := arg :: !source_paths in
  Arg.parse [] anon_handler usage_msg;
  let source_path =
    match !source_paths with
    | [ p ] -> p
    | _ ->
       print_endline usage_msg;
       exit 1
  in
  let source_chan = open_in source_path in
  let lexbuf = Lexing.from_channel source_chan in
  try
    let parse_tree = Parser.prog Lexer.token lexbuf in
    run (eval parse_tree);
    close_in source_chan
  with e ->
    let pos = lexbuf.lex_curr_p in
    Printf.eprintf "%s:%d:%d: parse error\n" source_path pos.pos_lnum
      (pos.pos_cnum - pos.pos_bol);
    close_in source_chan;
    raise e
