{
open Parser
}

let digit = ['0'-'9']
let initial = ['a'-'z' 'A'-'Z' '!'-'/' ':' '<'-'@' '\\' '^'-'_' '|' '~']
let identc = initial | digit

rule token = parse
    [' ' '\t']             { token lexbuf }
  | '\n'                   { Lexing.new_line lexbuf; token lexbuf }
  | eof                    { EOF }
  | '{'                    { LBRACE }
  | '}'                    { RBRACE }
  | "with"                 { WITH }
  | "fun"                  { FUN }
  | "if0"                  { IF0 }
  | '+'                    { ADD }
  | '-'                    { SUB }
  | '*'                    { MUL }
  | '/'                    { DIV }
  | '-'? digit+ as lxm     { INT (Uint63.of_int (int_of_string lxm)) }
  | initial identc* as lxm { IDENT lxm }
