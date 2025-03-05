module Interpreter
#nowarn "25"
open System
open Parser
exception ControlFlow of string

let eval env expr = 
    let find name env = env |> Map.find name

    let numeric_op = Map [
        ("+", ((function x -> x), (function (Expr.NUMBER(x), Expr.NUMBER(y)) -> Expr.NUMBER(x + y))));
        ("-", ((function Expr.NUMBER(x) -> Expr.NUMBER(-x)), (function (Expr.NUMBER(x), Expr.NUMBER(y)) -> Expr.NUMBER(x - y))));
        ("*", ((function x -> x), (function (Expr.NUMBER(x), Expr.NUMBER(y)) -> Expr.NUMBER(x * y))));
        ("/", ((function Expr.NUMBER(x) -> Expr.NUMBER(1. / x)), (function (Expr.NUMBER(x), Expr.NUMBER(y)) -> Expr.NUMBER(x / y))));
    ]
    let bool_op = Map [
        ("&", ((function x -> x), (function (Expr.BOOL(x), Expr.BOOL(y)) -> Expr.BOOL(x && y))));
        ("|", ((function x -> x), (function (Expr.BOOL(x), Expr.BOOL(y)) -> Expr.BOOL(x || y))));
    ]
    let binary_op = Map [
        (">", (function (Expr.NUMBER(x), Expr.NUMBER(y)) -> Expr.BOOL(x > y)));
        ("<", (function (Expr.NUMBER(x), Expr.NUMBER(y)) -> Expr.BOOL(x < y)));
        (">=", (function (Expr.NUMBER(x), Expr.NUMBER(y)) -> Expr.BOOL(x >= y)));
        ("<=", (function (Expr.NUMBER(x), Expr.NUMBER(y)) -> Expr.BOOL(x <= y)));
    ]

    let rec eval_args_bool eval_fn env acc = fun x ->
        match x with
        | h::t -> 
            let evaluated, new_env = eval_fn env h
            match evaluated with
            | Expr.BOOL(_) -> 
                eval_args_bool eval_fn new_env (evaluated::acc) t
            | Expr.BASELIST([Expr.BOOL(_) as boolean]) ->
                eval_args_bool eval_fn new_env (boolean::acc) t
            | Expr.NUMBER(n) -> 
                eval_args_bool eval_fn new_env (Expr.BOOL(Convert.ToBoolean n)::acc) t
            | Expr.BASELIST([Expr.NUMBER(n)]) ->
                eval_args_bool eval_fn new_env (Expr.BOOL(Convert.ToBoolean n)::acc) t
            | waste -> failwith ("check_bool ERROR: unexpected bool expression: " + (sprintf "%A" waste))
        | [] -> List.rev acc, env

    let rec eval_args_num eval_fn env acc = fun x ->
        match x with
        | h::t -> 
            let evaluated, new_env = eval_fn env h
            match evaluated with
            | Expr.NUMBER(_) -> 
                eval_args_num eval_fn new_env (evaluated::acc) t
            | Expr.BASELIST([Expr.NUMBER(_) as number]) ->
                eval_args_num eval_fn new_env (number::acc) t
            | waste -> failwith ("check_number ERROR: unexpected numeric expression: " + (sprintf "%A" waste))
        | [] -> List.rev acc, env

    let rec eval_implem env = function
        | Expr.NUMBER(_) as number -> number, env
        | Expr.STRING(_) as string -> string, env
        | Expr.BOOL(_) as boolean -> boolean, env
        | Expr.ID(id) -> eval_implem env (find id env)

        | Expr.BASELIST([Expr.NUMBER(_) as number]) -> number, env
        | Expr.BASELIST([Expr.STRING(_) as string]) -> string, env
        | Expr.BASELIST([Expr.BOOL(_) as boolean]) -> boolean, env
        | Expr.BASELIST([Expr.ID(id)]) -> find id env, env

        | Expr.BASELIST([Expr.OPERATOR(_) as op]) -> eval_implem env op

        | Expr.OPERATOR(op, t) when (Map.tryFind op numeric_op).IsSome ->
            let (single_lambda, multiple_lambda) = Map.find op numeric_op
            let eval_list, new_env = eval_args_num eval_implem env [] t
            match List.length eval_list with
            | 0 -> failwith "eval_implem ERROR: operator + can't have 0 args"
            | 1 -> single_lambda (List.head eval_list), new_env
            | _ -> List.reduce (fun x y -> multiple_lambda (x, y)) eval_list, new_env
        | Expr.OPERATOR(op, t) when (Map.tryFind op bool_op).IsSome ->
            let (single_lambda, multiple_lambda) = Map.find op bool_op
            let eval_list, new_env = eval_args_bool eval_implem env [] t
            match List.length eval_list with
            | 0 -> failwith "eval_implem ERROR: operator + can't have 0 args"
            | 1 -> single_lambda (List.head eval_list), new_env
            | _ -> List.reduce (fun x y -> multiple_lambda (x, y)) eval_list, new_env

        | Expr.OPERATOR("==", t) ->
            match List.length t with
            | 2 ->
                let first::second::[] = t
                let eval_first, new_env = eval_implem env first
                let eval_second, new_env' = eval_implem new_env second
                (function 
                    | (Expr.NUMBER(x), Expr.NUMBER(y)) -> Expr.BOOL(x = y)
                    | (Expr.BOOL(x), Expr.BOOL(y)) -> Expr.BOOL(x = y)
                    | (Expr.STRING(x), Expr.STRING(y)) -> Expr.BOOL(x = y)
                    | _ -> failwith ("eval_implem ERROR: given unsupported args: " + (sprintf "%A %A" eval_first eval_second))
                ) (eval_first, eval_second), new_env'
            | _ -> failwith ("eval_implem ERROR: operator " + (sprintf "%s" "=") + " can't have not 2 args")
        | Expr.OPERATOR(op, t) when (Map.tryFind op binary_op).IsSome ->
            let eval_list, new_env = eval_args_num eval_implem env [] t
            let functor = Map.find op binary_op
            match List.length eval_list with
            | 2 -> 
                let first::second::[] = eval_list
                functor (first, second), new_env
            | _ -> failwith ("eval_implem ERROR: operator " + (sprintf "%s" op) + " can't have not 2 args")

        | Expr.VARIABLE(id, list) -> Expr.BASE (""), (Map.add id list env)
        | Expr.COND(cond, expr1, expr2) ->
            let eval_cond, new_env = eval_implem env cond
            match eval_cond with 
            | Expr.NUMBER(n) -> if Convert.ToBoolean n then (expr1, new_env) else (expr2, new_env)
            | Expr.BOOL(b) -> if b then (expr1, new_env) else (expr2, new_env)
            | waste -> failwith ("eval_implem ERROR: unevaluatable cond expression: " + (sprintf "%A" waste))

        | Expr.FOR_LOOP(var, start, endValue, body) ->
            let start_val, start_env = eval_implem env start
            let end_val, end_env = eval_implem start_env endValue
            let rec loop current_env current_val end_val =
                if current_val >= end_val then
                    Expr.BASE(""), current_env
                else
                    try
                        let _, body_env = eval_implem (Map.add var (Expr.NUMBER(current_val)) current_env) body
                        loop body_env (current_val + 1.) end_val
                    with
                    | ControlFlow "Break" -> Expr.BASE(""), current_env 
                    | ControlFlow "Continue" -> loop current_env (current_val + 1.) end_val
            match (start_val, end_val) with
            | (Expr.NUMBER(start_num), Expr.NUMBER(end_num)) ->
                loop env start_num end_num
            | _ -> failwith "FOR_LOOP ERROR: Start and end values must be numbers"


        | Expr.WHILE(cond, body) ->
            let rec loop current_env =
                try
                    let cond_val, new_env = eval_implem current_env cond
                    match cond_val with
                    | Expr.BOOL(true) ->
                        let _, body_env = eval_implem new_env body
                        loop body_env
                    | Expr.BOOL(false) -> Expr.BASE(""), current_env
                    | _ -> failwith "While condition must be a boolean"
                with
                | ControlFlow "Continue" -> loop current_env
                | ControlFlow "Break" -> Expr.BASE(""), current_env
            loop env

        | Expr.CONTINUE -> raise (ControlFlow "Continue")
        | Expr.KILL -> raise (ControlFlow "Break")

        | Expr.BASELIST(list) -> 
            let rec eval_lists env = function
                | h::t -> 
                    let evaluated_first, new_env = eval_implem env h
                    match evaluated_first with
                    | Expr.BASE(_) as simple -> eval_lists new_env t
                    | _ ->
                        let evaluated, new_env' = eval_implem new_env evaluated_first 
                        match evaluated with
                        | Expr.NUMBER(_) | Expr.STRING(_) | Expr.BOOL(_)-> 
                            if List.length t <> 0 then printfn "eval_base_lists warning useless members at the end of list"
                            evaluated, new_env' 
                        | _ -> eval_lists new_env' t
                | [] ->
                    Expr.BASE(""), env
            eval_lists env list
        | Expr.FUNC(id, args, body, _, arity) ->
            Expr.BASE(""), (Map.add id (Expr.FUNC(id, args, body, env, arity)) env)
        | Expr.CALL(id, Expr.BASELIST(args), arity) ->
            let env_function = Map.tryFind id env
            if env_function.IsNone then failwith ("eval_implem ERROR: use of undeclared function " + id)
            else 
                let (Expr.FUNC(_, Expr.BASEARGLIST(env_args), body, env_env, env_arity)) = env_function.Value
                if arity <> env_arity 
                then failwith ("eval_implem ERROR: function use with different args: expected " + (sprintf "%A" env_arity) + " got: " + (sprintf "%A" arity))
                else
                    let rec add_env_args env = function
                    | (Expr.BASELIST([Expr.ID(h1)])::t1), (h2::t2) -> 
                        let eval_h2, new_env =  eval_implem env h2
                        add_env_args (Map.add h1 eval_h2 new_env) (t1, t2)
                    | ([], []) -> env
                    | waste -> failwith ("eval_implem ERROR: Some bad things happened: " + (sprintf "%A" waste))

                    let new_env = add_env_args env (env_args, args) 
                    let merged_env = Map.fold (fun acc key value -> Map.add key value acc) env new_env
                    let merged_env2 = Map.fold (fun acc key value -> Map.add key value acc) merged_env env_env

                    eval_implem merged_env2 body
        | Expr.PRINT(body) ->
            let evaludated_body, new_env = eval_implem env body
            match evaludated_body with
            | Expr.BASE(_) -> failwith ("eval_implem.print ERROR: unexpected base value\n")
            | _ ->
                let evaluated_eval, new_env' = eval_implem new_env evaludated_body
                match evaluated_eval with
                | Expr.NUMBER(num) -> 
                    printfn "%f" num
                    BASE(""), new_env
                | Expr.STRING(str) -> 
                    printfn "%s" str
                    BASE(""), new_env
                | Expr.BOOL(boolean) ->
                    if boolean then
                        printfn "true"
                        BASE(""), new_env
                    else
                        printfn "false"
                        BASE(""), new_env
                | Expr.ID(id_val) as id ->
                    let evaluated_id, new_env'' = eval_implem new_env' id
                    printfn "id: %s = %A" id_val evaluated_id
                    BASE(""), new_env''
        | Expr.READ_FILE path ->
            try
                let text = System.IO.File.ReadAllText(path)
                Expr.STRING text, env
            with
            | ex -> failwith ("Error reading file: " + ex.Message)

        | Expr.WRITE_FILE(path_expr, data_expr) ->
            try
                System.IO.File.AppendAllText(path_expr, data_expr)
                Expr.STRING "Data written successfully", env
            with
            | ex -> failwith ("Error writing to file: " + ex.Message)
        
        | Expr.BASE(_) -> failwith ("eval_implem ERROR: base value is unexpected\n")
        | waste -> failwith ("eval_implem ERROR: wrong structure to process" + (sprintf "%A\n" waste))

    match expr with
    | h -> eval_implem env h