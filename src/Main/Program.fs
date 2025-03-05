open System
open System.IO
open Parser
open Interpreter

open System.Text.RegularExpressions

let env = Map<String, Expr> []


let rec repl env =
    printf "> "
    let source = Console.ReadLine()
    try
        printfn "Source: %s" source
        let tokens, _ = tokens (source |> Seq.toList)
        let expr = parse tokens
        printfn "Parsed: %A" expr
        let eval, new_env = eval env expr
        printfn "Evaluated: %A\n" eval
        repl new_env
    with ex ->
        printfn "Error: %s" ex.Message
        repl env

let rec execute env (filename: string) =
    if (not(Regex.IsMatch(filename, "^.*[.]gg$"))) then
        printf("ERROR. Wrong extension\n")
    else
        let lines = File.ReadAllLines(filename)
        let source = String.concat "" lines
        try
            let tokens, _ = tokens (source |> Seq.toList)
            let expr = parse tokens
            let eval, new_env = eval env expr
            printfn "\nGOOD"
        with ex ->
            printfn "ERROR: %s" ex.Message


let main =
    let args = Environment.GetCommandLineArgs()
    if args.Length <> 2 then
        printfn "For start: dotnet run [name of file].gg\n"
        1
    else
        execute env args[1]
        0