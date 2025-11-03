module ExprEvaluator
open System

// Tokens
type Token =
  | Plus | Minus | Mul | Div | Mod | Pow
  | Lpar | Rpar | Assign
  | Number of float * bool
  | Ident of string

exception LexError of string
exception ParseError of string
exception EvalError of string

//BNF
//<program>      ::= <statement>
//<statement>    ::= <functiondef> | <assignment> | <expression>
//<functiondef>  ::= <identifier> "(" <identifier> ")" "=" <expression>
//<assignment>   ::= <identifier> "=" <expression>
//<expression>   ::= <term> { ("+" | "-") <term> }
//<term>         ::= <factor> { ("*" | "/" | "%") <factor> }
//<factor>       ::= <primary> [ "^" <factor> ]
//<primary>      ::= <number> | <identifier> | <identifier> "(" <expression> ")" | "(" <expression> ")"
//<number>       ::= <digit> { <digit> } [ "." <digit> { <digit> } ]
//<identifier>   ::= <letter> { <letter> | <digit> | "_" }


// Lexer

let isDigit c = Char.IsDigit c
let isLetter c = Char.IsLetter c
let isWhite c = Char.IsWhiteSpace c
let isIdentChar c = Char.IsLetterOrDigit c || c = '_'

let rec scanNumber chars acc =
  match chars with
  | c :: tail when isDigit c -> scanNumber tail (acc + string c)
  | '.' :: tail when not (acc.Contains "." ) -> scanNumber tail (acc + ".")
  | _ -> chars, acc

let rec scanIdent chars acc =
  match chars with
  | c :: tail when isIdentChar c -> scanIdent tail (acc + string c)
  | _ -> chars, acc

let lexer (input: string) : Token list =
  let rec scan cs =
    match cs with
    | [] -> []
    | c :: tail when isWhite c -> scan tail
    | '+' :: tail -> Plus :: scan tail
    | '-' :: tail -> Minus :: scan tail
    | '*' :: tail -> Mul :: scan tail
    | '/' :: tail -> Div :: scan tail
    | '%' :: tail -> Mod :: scan tail
    | '^' :: tail -> Pow :: scan tail
    | '(' :: tail -> Lpar :: scan tail
    | ')' :: tail -> Rpar :: scan tail
    | '=' :: tail -> Assign :: scan tail
    | c :: _ when isLetter c ->
        let (rest, idStr) = scanIdent cs ""
        Ident idStr :: scan rest
    | c :: _ when isDigit c ->
        let (rest, numStr) = scanNumber cs ""
        match System.Double.TryParse numStr with
        | true, v ->
            let hadDot = numStr.Contains "."
            Number (v, hadDot) :: scan rest
        | _ -> raise (LexError $"Invalid number: {numStr}")
    | other :: _ -> raise (LexError $"Unknown character: '{other}'")
  scan (List.ofSeq input)

let mutable symbolTable = Map.empty<string, float>
let mutable functionTable = Map.empty<string, string * Token list>

let rec pow baseF expF =
  if expF = 0.0 then 1.0
  elif expF = 1.0 then baseF
  elif expF > 1.0 then
    let rec loop acc n =
      if n <= 0 then acc else loop (acc * baseF) (n - 1)
    loop 1.0 (int expF)
  elif expF < 0.0 then 1.0 / pow baseF (-expF)
  else
    raise (EvalError "Fractional powers not supported without Math library")

let isClose a b = 
  let diff = if a > b then a - b else b - a
  diff < 1e-10

let isIntLike f =
  let n = int f
  isClose f (float n)

let intDiv a b =
  if b = 0.0 then raise (EvalError "Division by zero")
  else
    let q = a / b
    if q >= 0.0 then float (int q)
    else float (int q + 1)

let intMod a b =
  if b = 0.0 then raise (EvalError "Modulo by zero")
  else a - b * intDiv a b

// Parser
let rec parseE tokens =
  let (tokens2, v1, hasFloat1) = parseT tokens
  parseEopt tokens2 v1 hasFloat1

and parseEopt tokens acc hasFloat =
  match tokens with
  | Plus :: tail ->
      let (t2, v2, f2) = parseT tail
      parseEopt t2 (acc + v2) (hasFloat || f2)
  | Minus :: tail ->
      let (t2, v2, f2) = parseT tail
      parseEopt t2 (acc - v2) (hasFloat || f2)
  | _ -> tokens, acc, hasFloat

and parseT tokens =
  let (tokens2, v1, f1) = parseF tokens
  parseTopt tokens2 v1 f1

and parseTopt tokens acc hasFloat =
  match tokens with
  | Mul :: tail ->
      let (t2, v2, f2) = parseF tail
      parseTopt t2 (acc * v2) (hasFloat || f2)
  | Div :: tail ->
      let (t2, v2, f2) = parseF tail
      if v2 = 0.0 then raise (EvalError "Division by zero")
      let result =
        if (not hasFloat) && (isIntLike acc) && (isIntLike v2) then intDiv acc v2
        else acc / v2
      parseTopt t2 result (hasFloat || f2 || not (isIntLike acc && isIntLike v2))
  | Mod :: tail ->
      let (t2, v2, f2) = parseF tail
      let result = intMod acc v2
      parseTopt t2 result (hasFloat || f2)
  | _ -> tokens, acc, hasFloat

and parseF tokens =
  let (t2, v1, f1) = parseU tokens
  match t2 with
  | Pow :: tail ->
      let (t3, v2, f2) = parseF tail
      let res = pow v1 v2
      let resFloat = (not (isIntLike res)) || f1 || f2
      t3, res, resFloat
  | _ -> t2, v1, f1

and parseU tokens =
  match tokens with
  | Minus :: tail ->
      let (ts2, v, f) = parseU tail
      ts2, -v, f
  | Plus :: tail -> parseU tail
  | _ -> parseP tokens

and parseP tokens =
  match tokens with
  | Number (n, hadDot) :: tail -> tail, n, (hadDot || not (isIntLike n))
  | Ident name :: Lpar :: tail ->
      let (afterArg, argVal, argFloat) = parseE tail
      match afterArg with
      | Rpar :: rest ->
          match functionTable.TryFind name with
          | Some (param, body) ->
              let oldBinding = symbolTable.TryFind param
              symbolTable <- symbolTable.Add(param, argVal)
              let (afterBody, result, resFloat) = parseE body
              if afterBody <> [] then
                  match oldBinding with
                  | Some v -> symbolTable <- symbolTable.Add(param, v)
                  | None -> symbolTable <- symbolTable.Remove param
                  raise (ParseError $"Extra tokens in function body of {name}")
              match oldBinding with
              | Some v -> symbolTable <- symbolTable.Add(param, v)
              | None -> symbolTable <- symbolTable.Remove param
              rest, result, (argFloat || resFloat)
          | None -> raise (EvalError $"Undefined function: {name}")
      | _ -> raise (ParseError "Missing closing parenthesis")
  | Ident name :: tail ->
      match symbolTable.TryFind name with
      | Some v -> tail, v, (not (isIntLike v))
      | None -> raise (EvalError $"Undefined variable: {name}")
  | Lpar :: tail ->
      let (t2, v, f) = parseE tail
      match t2 with
      | Rpar :: rest -> rest, v, f
      | _ -> raise (ParseError "Missing closing parenthesis")
  | _ -> raise (ParseError "Unexpected token")

// Evaluation
let parseAndEval tokens =
  let rec parseStatement toks =
    match toks with
    | Ident fname :: Lpar :: Ident param :: Rpar :: Assign :: rest ->
        functionTable <- functionTable.Add(fname, (param, rest))
        [], 0.0, false
    | Ident name :: Assign :: rest ->
        let (afterExpr, value, _) = parseE rest
        symbolTable <- symbolTable.Add(name, value)
        afterExpr, value, false
    | _ -> parseE toks
  let (rest, value, isFloat) = parseStatement tokens
  if rest <> [] then raise (ParseError "Extra tokens after expression")
  value, isFloat

let EvaluateExpression (input: string) =
    try
        if obj.ReferenceEquals(symbolTable, null) then
            symbolTable <- Map.empty
        if obj.ReferenceEquals(functionTable, null) then
            functionTable <- Map.empty

        let lines = 
            input.Split([|'\n'; ';'|], StringSplitOptions.RemoveEmptyEntries)
            |> Array.map (fun s -> s.Trim())
            |> Array.filter (fun s -> s <> "")

        let mutable lastResult = 0.0
        let mutable isFloat = false

        for line in lines do
            let tokens = lexer line
            let (result, f) = parseAndEval tokens
            lastResult <- result
            isFloat <- f

        if isFloat then lastResult.ToString("0.0###", System.Globalization.CultureInfo.InvariantCulture)
        else lastResult.ToString("0", System.Globalization.CultureInfo.InvariantCulture)

    with
    | LexError msg -> $"Lexer error: {msg}"
    | ParseError msg -> $"Parser error: {msg}"
    | EvalError msg -> $"Runtime error: {msg}"
    | ex -> $"Error: {ex.Message}"

let ResetState () =
    symbolTable <- Map.empty
    functionTable <- Map.empty

let EvaluateExprForX (expr: string) (x: float) =
    try
        if obj.ReferenceEquals(symbolTable, null) then
            symbolTable <- Map.empty
        if obj.ReferenceEquals(functionTable, null) then
            functionTable <- Map.empty
        let oldX = symbolTable.TryFind "x"
        symbolTable <- symbolTable.Add("x", x)
        let tokens = lexer expr
        let (value, _) = parseAndEval tokens
        match oldX with
        | Some v -> symbolTable <- symbolTable.Add("x", v)
        | None -> symbolTable <- symbolTable.Remove "x"
        value.ToString(System.Globalization.CultureInfo.InvariantCulture)
    with
    | LexError msg -> $"Lexer error: {msg}"
    | ParseError msg -> $"Parser error: {msg}"
    | EvalError msg -> $"Runtime error: {msg}"
    | ex -> $"Error: {ex.Message}"
