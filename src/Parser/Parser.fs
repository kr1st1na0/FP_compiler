module Parser

open System

type Token =
    | OPERATOR of string
    | NUMBER of float
    | STRING of string
    | ID of string
    | DOT
    | COMMA
    | SEMICOLON
    | LEFT_CURLY
    | RIGHT_CURLY
    | LEFT_BRACKET
    | RIGHT_BRACKET
    | LEFT_PARENTHESIS
    | RIGHT_PARENTHESIS

type Expr =
    | OPERATOR of string * Expr list
    | NUMBER of float
    | STRING of string
    | ID of string
    | BOOL of bool
    | COND of Expr * Expr * Expr               
    | VARIABLE of string * Expr                                       
    | FUNC of string * Expr * Expr * env * int 
    | CALL of string * Expr * int
    | PRINT of Expr
    | READ_FILE of string
    | WRITE_FILE of string * string
    | FOR_LOOP of string * Expr * Expr * Expr
    | WHILE of Expr * Expr
    | CONTINUE
    | KILL
    | BASE of string
    | BASEOP of string
    | BASELIST of Expr list
    | BASEARGLIST of Expr list
    
and env = Map<string, Expr>

let toString = (function x -> (x |> List.toArray |> String))

let tokens source =
    let lit_tokens = Map [
        ('.', Token.DOT);
        (';', Token.SEMICOLON);
        (',', Token.COMMA);
        ('{', Token.LEFT_CURLY);
        ('}', Token.RIGHT_CURLY);
        ('(', Token.LEFT_PARENTHESIS);
        (')', Token.RIGHT_PARENTHESIS);
        ('[', Token.LEFT_BRACKET);
        (']', Token.RIGHT_BRACKET);
    ]

    let arithm_tokens = Map [
        ('+', Token.OPERATOR("+"));
        ('-', Token.OPERATOR("-"));
        ('*', Token.OPERATOR("*"));
        ('/', Token.OPERATOR("/"));
        ('=', Token.OPERATOR("="));
        ('>', Token.OPERATOR(">"));
        ('<', Token.OPERATOR("<"));
        ('|', Token.OPERATOR("|"));
        ('&', Token.OPERATOR("&"));
        (':', Token.OPERATOR(":"));
    ]

    let rec read_str acc = function
    | '\\'::'"'::t -> (toString (List.rev acc)), t
    | '"'::t -> (toString (List.rev acc)), t
    | h::t -> read_str (h::acc) t
    | [] -> failwith "read_str ERROR: EOF before closing"

    let rec read_comm = function
    | '#'::t -> t
    | _::t -> read_comm t
    | [] -> failwith "read_comm ERROR: EOF before closing comment"


    let rec read_id acc = function
    | h::t when Char.IsWhiteSpace(h) -> (toString (List.rev acc)), t
    | h::t when Char.IsLetter(h) || Char.IsDigit(h) || h = '_' -> read_id (h::acc) t
    | h::t when h = '(' || h = ')' || h = '{' || h = '}' || h = '[' || h = ']' -> (toString (List.rev acc)), (h::t)
    | [] -> (toString (List.rev acc)), []
    | h::_ -> failwith ("read_id ERROR: Unexpected symbol was found: " + (string h))


    let rec read_num acc = function
    | h::t when Char.IsWhiteSpace(h) -> (toString (List.rev acc)), t
    | h::t when Char.IsDigit(h) -> read_num (h::acc) t
    | '.'::t -> read_num ('.'::acc) t
    | h::t when h = '(' || h = ')' || h = '[' || h = ']' -> (toString (List.rev acc)), (h::t)
    | [] -> (toString (List.rev acc)), []
    | h::_ -> failwith ("read_num ERROR: Unexpected symbol was found: " + (string h))


    let rec tokens_implem acc = function
    | '.'::'.'::t -> tokens_implem (Token.OPERATOR("..")::acc) t
    | '>'::'='::t -> tokens_implem (Token.OPERATOR(">=")::acc) t
    | '<'::'='::t -> tokens_implem (Token.OPERATOR("<=")::acc) t
    | '='::'='::t -> tokens_implem (Token.OPERATOR("==")::acc) t
    | h::t when Char.IsWhiteSpace(h) -> tokens_implem acc t
    | h::t when lit_tokens |> Map.containsKey h -> 
        let token = lit_tokens |> Map.find h
        tokens_implem (token::acc) t
    | '"'::t | '\\'::'"'::t -> 
        let read_str, remainder = read_str [] t
        tokens_implem (Token.STRING(read_str)::acc) remainder
    | '#'::t -> 
        let remainder = read_comm t
        tokens_implem acc remainder
    | h::t when Char.IsLetter(h) ->
        let read_id, remainder = read_id [] (h::t)
        tokens_implem (Token.ID(read_id)::acc) remainder
    | h::t when Char.IsDigit(h) ->
        let read_num, remainder = read_num [] (h::t)
        try 
            let parsed_number = System.Double.Parse(read_num, System.Globalization.CultureInfo.InvariantCulture)
            tokens_implem (Token.NUMBER(parsed_number)::acc) remainder
        with
            _ -> failwith ("tokens_implem ERROR: Unexpected symbol was found " + read_num)
    | '-'::h::t when Char.IsDigit(h) ->
        let read_num, remainder = read_num [] (h::t)
        try 
            let parsed_number = System.Double.Parse("-" + read_num, System.Globalization.CultureInfo.InvariantCulture)
            tokens_implem (Token.NUMBER(parsed_number)::acc) remainder
        with
            _ -> failwith ("tokens_implem ERROR: Unexpected symbol was found " + read_num)
    | h::' '::t when (arithm_tokens |> Map.tryFind h).IsSome ->
         tokens_implem ((arithm_tokens |> Map.find h)::acc) t
    | [] -> List.rev acc, []
    | _ -> failwith "tokens_implem ERROR: Unexpected symbol was found or wrong structure"

    tokens_implem [] source

let parse tokens = 
    let rec parse_ids acc = function
        | Token.ID(id)::t -> parse_ids (id::acc) t
        | Token.RIGHT_CURLY::t -> List.rev acc, t
        | _ -> failwith "parse_ids ERROR: id was not found"

    let keywords = ["var"; "func"; "print"; "if"; "else"; "for"; "while"; "read"; "write"]

    let rec token_parser acc = function
        | [] -> List.rev acc, []

        | Token.ID(expr)::t when (List.tryFind (fun x -> x = expr) keywords).IsSome ->
            token_parser (Expr.BASE(expr)::acc) t

        | Token.NUMBER(n)::t -> token_parser (Expr.BASELIST([Expr.NUMBER(n)])::acc) t
        | Token.ID("true")::t -> token_parser (Expr.BASELIST([Expr.BOOL(true)])::acc) t
        | Token.ID("false")::t -> token_parser (Expr.BASELIST([Expr.BOOL(false)])::acc) t
        | Token.ID("continue")::t -> token_parser (Expr.CONTINUE::acc) t
        | Token.ID("kill")::t -> token_parser (Expr.KILL::acc) t
        | Token.ID(id)::t -> token_parser (Expr.BASELIST([Expr.ID(id)])::acc) t
        | Token.STRING(s)::t -> token_parser (Expr.BASELIST([Expr.STRING(s)])::acc) t
        | Token.OPERATOR("=")::t -> token_parser (Expr.BASE("=")::acc) t
        | Token.OPERATOR("..")::t -> token_parser (Expr.BASE("..")::acc) t
        | Token.OPERATOR(":")::t -> token_parser (Expr.BASE(":")::acc) t

        | Token.LEFT_BRACKET::t -> token_parser (Expr.BASE("[")::acc) t
        | Token.RIGHT_BRACKET::t -> token_parser (Expr.BASE("]")::acc) t
        | Token.RIGHT_CURLY::t -> List.rev acc, t
        | Token.LEFT_CURLY::t ->
            let read_args, remaining_part = token_parser [] t
            if List.forall (fun x -> match x with | Expr.BASELIST([Expr.ID(_)]) -> true | _ -> false) read_args 
            then token_parser (Expr.BASEARGLIST(read_args)::acc) remaining_part
            else failwith ("token_parser ERROR: non ids inside function args: " + (sprintf "%A" read_args))

        | Token.RIGHT_PARENTHESIS::t -> List.rev acc, t
        | Token.LEFT_PARENTHESIS::t ->
            let read_exprs, remaining_part = token_parser [] t

            match read_exprs with
            | Expr.BASEOP(op)::t -> token_parser (Expr.BASELIST([Expr.OPERATOR(op, t)])::acc) remaining_part
            | Expr.BASE("var")::Expr.BASELIST([Expr.ID(id)])::Expr.BASE("=")::Expr.BASELIST(list)::[] ->
                token_parser (Expr.BASELIST([Expr.VARIABLE(id, Expr.BASELIST(list))])::acc) remaining_part

            | Expr.BASE("func")::Expr.BASELIST([Expr.ID(id)])::(Expr.BASEARGLIST(args_list) as args)
                ::Expr.BASE(":")::(Expr.BASELIST(_) as body)::[] -> 
                token_parser (BASELIST([Expr.FUNC(id, args, body, Map<string, Expr>[], List.length args_list)])::acc) remaining_part

            | Expr.BASE("read")::Expr.BASELIST([Expr.STRING(path)])::t ->
                token_parser (BASELIST([Expr.READ_FILE(path)])::acc) remaining_part
            
            | Expr.BASE("write")::Expr.BASELIST([Expr.STRING(path)])::Expr.BASELIST([Expr.STRING(data)])::t ->
                token_parser (BASELIST([Expr.WRITE_FILE(path, data)])::acc) remaining_part
            
            | Expr.BASELIST([Expr.ID(id)])::t ->
                if List.forall (fun x -> match x with | Expr.BASELIST(_) -> true | _ -> false) t
                then token_parser (BASELIST([Expr.CALL(id, Expr.BASELIST(t), List.length t)])::acc) remaining_part
                else failwith ("token_parser ERROR: wrong function syntax" + (sprintf "%A" t)) 

            | Expr.BASELIST(list)::t -> 
                let rec gather_base_lists acc = function
                | (Expr.BASELIST(_) as list)::t' -> gather_base_lists (list::acc) t'
                | Expr.CONTINUE::t' -> gather_base_lists (Expr.KILL::acc) t'
                | Expr.KILL::t' -> gather_base_lists (Expr.KILL::acc) t'
                | [] -> List.rev acc, []
                | waste -> 
                    printfn "unmatched expr: %A" waste
                    failwith "gather_base_lists ERROR: misformat expression"

                let lists, _ = gather_base_lists [] (BASELIST(list)::t)
                token_parser (Expr.BASELIST(lists)::acc) remaining_part
            | Expr.BASE("if")::(Expr.BASELIST(_) as cond)
                ::Expr.BASE(":")::(Expr.BASELIST(_) as expr1)
                ::Expr.BASE("else")::Expr.BASE(":")::(Expr.BASELIST(_) as expr2)::[] -> 
                    token_parser (Expr.BASELIST([Expr.COND(cond, expr1, expr2)])::acc) remaining_part

            | Expr.BASE("if")::(Expr.BASELIST(_) as cond)
                ::Expr.BASE(":")::(Expr.BASELIST(_) as expr1)::[] ->
                    token_parser (Expr.BASELIST([Expr.COND(cond, expr1, BASE(""))])::acc) remaining_part

            | Expr.BASE("for")::Expr.BASELIST([Expr.ID(var)])
                ::Expr.BASE("[")::(Expr.BASELIST(_) as start)
                ::Expr.BASE("..")::(Expr.BASELIST(_) as endValue)
                ::Expr.BASE("]")::Expr.BASE(":")::(Expr.BASELIST(_) as body)::[] ->
                    token_parser (Expr.BASELIST([Expr.FOR_LOOP(var, start, endValue, body)])::acc) remaining_part

            | Expr.BASE("while")::(Expr.BASELIST(_) as cond)::
                Expr.BASE(":")::(Expr.BASELIST(_) as body)::[] ->
                    token_parser (Expr.BASELIST([Expr.WHILE(cond, body)])::acc) remaining_part

            | Expr.BASE("print")::(Expr.BASELIST(_) as body)::[] -> token_parser (Expr.BASELIST([Expr.PRINT(body)])::acc) remaining_part

            | (Expr.NUMBER(_) as num_expr)::[] -> token_parser (BASELIST([num_expr])::acc) remaining_part
            | (Expr.STRING(_) as str_expr)::[] -> token_parser (BASELIST([str_expr])::acc) remaining_part
            | waste -> failwith ("token_parser ERROR: wrong parenthesis structure: " + (sprintf "%A" waste))

        | Token.OPERATOR(op)::t -> token_parser (Expr.BASEOP(op)::acc) t
        | waste -> 
            printfn "unexpected token: %A" waste
            failwith "token_parser ERROR: unexpected token"

    let parsed_expr, remaining_part = token_parser [] tokens
    if remaining_part <> [] then 
        printfn "could not parse: %A" remaining_part
        failwith "token_parser ERROR: wrong expression"
    Expr.BASELIST(parsed_expr)

