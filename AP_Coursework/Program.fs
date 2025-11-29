module ExprEvaluator
open System

// Tokens
type Token =
  | Plus | Minus | Mul | Div | Mod | Pow
  | Lpar | Rpar | Assign | Comma
  | LBracket | RBracket | Semicolon
  | Number of float * bool
  | Ident of string

exception LexError of string
exception ParseError of string
exception EvalError of string

//BNF (extended)
//<program>      ::= <statement>
//<statement>    ::= <functiondef> | <assignment> | <forloop> | <expression>
//<functiondef>  ::= <identifier> "(" <identifier> ")" "=" <expression>
//<assignment>   ::= <identifier> "=" <expression>
//<forloop>      ::= "for" <identifier> "=" <expression> "to" <expression> ["step" <expression>] "do" <expression>
//<expression>   ::= <term> { ("+" | "-") <term> }
//<term>         ::= <factor> { ("*" | "/" | "%") <factor> }
//<factor>       ::= <unary> [ "^" <factor> ]
//<unary>        ::= ["+"|"-"] <unary> | <primary>
//<primary>      ::= <number>
//                 | <identifier>
//                 | <identifier> "(" <arglist> ")"   // user funcs (1 arg) and built-ins (var-args)
//                 | "(" <expression> ")"
//<arglist>      ::= <expression> { "," <expression> }
//<number>       ::= <digit> { <digit> } [ "." <digit> { <digit> } ]
//<identifier>   ::= <letter> { <letter> | <digit> | "_" }
//
//Built-ins (operate on current y(x)):
//  plot(x, dx, mode)
//  diff(x0[, h])
//  tangent(x0, halfWidth[, mode])
//  integrate(a, b[, n])
//  root_bisect(a, b[, tol][, maxIter])
//  root_newton(x0[, tol][, maxIter])
//  root_secant(x0, x1[, tol][, maxIter])
//
//Vector/Matrix helpers (scalar results):
//  dot(a1,b1[, a2,b2, ...])
//  norm(a1[, a2, ...])
//  det(a,b,c,d)                 // 2x2 determinant |a b; c d|
//  det(a11,a12,...,a33)         // 3x3 determinant (row-major)


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
    | ',' :: tail -> Comma :: scan tail
    | '[' :: tail -> LBracket :: scan tail
    | ']' :: tail -> RBracket :: scan tail
    | ';' :: tail -> Semicolon :: scan tail
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

// Plotting state for GUI integration
let mutable plotPoints : (float * float) list = []
let mutable plotMode : string option = None
let mutable plotRange : (float * float) option = None

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

let absf x = if x >= 0.0 then x else -x

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
  // Helpers for new built-ins
  let evalYAt xVal =
    match functionTable.TryFind "y" with
    | Some (param, body) ->
        let oldBinding = symbolTable.TryFind param
        symbolTable <- symbolTable.Add(param, xVal)
        let (afterBody, result, resFloat) = parseE body
        // Body should fully consume tokens
        if afterBody <> [] then
            match oldBinding with
            | Some v -> symbolTable <- symbolTable.Add(param, v)
            | None -> symbolTable <- symbolTable.Remove param
            raise (ParseError "Extra tokens in function body of y")
        // restore
        match oldBinding with
        | Some v -> symbolTable <- symbolTable.Add(param, v)
        | None -> symbolTable <- symbolTable.Remove param
        result
    | None -> raise (EvalError "Undefined function: y(x) not defined")
  match tokens with
  | Number (n, hadDot) :: tail -> tail, n, (hadDot || not (isIntLike n))
  | Ident "plot" :: Lpar :: tail ->
      // parse plot(x, dx, mode)
      let (t1, xVal, _) = parseE tail
      match t1 with
      | Comma :: t2 ->
          let (t3, _dxVal, _) = parseE t2
          match t3 with
          | Comma :: Ident mode :: Rpar :: rest ->
              // side-effect: compute y at current xVal and record point
              let yVal = evalYAt xVal
              plotPoints <- (xVal, yVal) :: plotPoints
              plotMode <- Some(mode.ToLowerInvariant())
              rest, yVal, (not (isIntLike yVal))
          | _ -> raise (ParseError "Expected: plot(x, dx, mode)")
      | _ -> raise (ParseError "Expected comma in plot arguments")
  | Ident "diff" :: Lpar :: tail ->
      // diff(x0[, h]) numeric derivative of y at x0 (central difference)
      let (t1, x0, _) = parseE tail
      let h, rest =
        match t1 with
        | Rpar :: rest -> 1e-5, rest
        | Comma :: t2 ->
            let (t3, hVal, _) = parseE t2
            match t3 with
            | Rpar :: rest -> hVal, rest
            | _ -> raise (ParseError "Expected closing ')' in diff")
        | _ -> raise (ParseError "Expected ',' or ')' in diff")
      let yph = evalYAt (x0 + h)
      let ymh = evalYAt (x0 - h)
      let d = (yph - ymh) / (2.0 * h)
      rest, d, true
  | Ident "integrate" :: Lpar :: tail ->
      // integrate(a, b[, n]) trapezoidal rule on y(x)
      let (t1, a, _) = parseE tail
      match t1 with
      | Comma :: t2 ->
          let (t3, b, _) = parseE t2
          let n, rest =
            match t3 with
            | Rpar :: rest -> 100, rest
            | Comma :: t4 ->
                let (t5, nVal, _) = parseE t4
                match t5 with
                | Rpar :: rest -> max 1 (int (absf nVal)) , rest
                | _ -> raise (ParseError "Expected closing ')' in integrate")
            | _ -> raise (ParseError "Expected ',' or ')' in integrate")
          let aa, bb = if a <= b then a, b else b, a
          let nn = max 1 n
          let h = (bb - aa) / float nn
          let mutable sum = 0.0
          let mutable i = 1
          while i < nn do
            let x = aa + float i * h
            sum <- sum + evalYAt x
            i <- i + 1
          let area = (h/2.0) * (evalYAt aa + 2.0*sum + evalYAt bb)
          rest, area, true
      | _ -> raise (ParseError "Expected comma in integrate arguments")
  | Ident "root_bisect" :: Lpar :: tail ->
      // root_bisect(a, b[, tol][, maxIter])
      let (t1, a, _) = parseE tail
      match t1 with
      | Comma :: t2 ->
          let (t3, b, _) = parseE t2
          let tol, maxIter, rest =
            match t3 with
            | Rpar :: rest -> 1e-6, 100, rest
            | Comma :: t4 ->
                let (t5, tolV, _) = parseE t4
                match t5 with
                | Rpar :: rest -> tolV, 100, rest
                | Comma :: t6 ->
                    let (t7, itV, _) = parseE t6
                    match t7 with
                    | Rpar :: rest -> tolV, max 1 (int (absf itV)), rest
                    | _ -> raise (ParseError "Expected ')' after maxIter")
                | _ -> raise (ParseError "Expected ')' or ',' after tol")
            | _ -> raise (ParseError "Expected ',' or ')' in root_bisect")
          let fa = evalYAt a
          let fb = evalYAt b
          // If an endpoint is exactly a root, nudge it inward so we search for an interior root
          let bumpTowards a b =
            let step = if tol > 0.0 then tol else 1e-12
            if a < b then a + step else a - step
          let mutable aa = a
          let mutable bb = b
          let mutable fa1 = fa
          let mutable fb1 = fb
          if fa1 = 0.0 then
            aa <- bumpTowards a b
            fa1 <- evalYAt aa
          if fb1 = 0.0 then
            bb <- bumpTowards b a
            fb1 <- evalYAt bb
          if fa1 * fb1 > 0.0 then raise (EvalError "Bisection requires f(a)*f(b) <= 0")
          let mutable lo = aa
          let mutable hi = bb
          let mutable flo = fa1
          let mutable fhi = fb1
          let mutable mid = (lo + hi) / 2.0
          let mutable fmid = evalYAt mid
          let mutable iter = 0
          while (absf (hi - lo) > tol) && iter < maxIter do
            mid <- (lo + hi) / 2.0
            fmid <- evalYAt mid
            if flo * fmid <= 0.0 then
              hi <- mid
              fhi <- fmid
            else
              lo <- mid
              flo <- fmid
            iter <- iter + 1
          rest, mid, true
      | _ -> raise (ParseError "Expected comma in root_bisect arguments")
  | Ident "root_newton" :: Lpar :: tail ->
      // root_newton(x0[, tol][, maxIter]) using numeric derivative
      let (t1, x0, _) = parseE tail
      let tol, maxIter, rest =
        match t1 with
        | Rpar :: rest -> 1e-6, 50, rest
        | Comma :: t2 ->
            let (t3, tolV, _) = parseE t2
            match t3 with
            | Rpar :: rest -> tolV, 50, rest
            | Comma :: t4 ->
                let (t5, itV, _) = parseE t4
                match t5 with
                | Rpar :: rest -> tolV, max 1 (int (absf itV)), rest
                | _ -> raise (ParseError "Expected ')' after maxIter")
            | _ -> raise (ParseError "Expected ')' or ',' after tol")
        | _ -> raise (ParseError "Expected ',' or ')' in root_newton")
      let mutable x = x0
      let h = 1e-5
      let mutable i = 0
      while i < maxIter do
        let fx = evalYAt x
        if absf fx < tol then i <- maxIter else
        let d = (evalYAt (x + h) - evalYAt (x - h)) / (2.0*h)
        if d = 0.0 then raise (EvalError "Zero derivative in Newton method")
        x <- x - fx / d
        i <- i + 1
      rest, x, true
  | Ident "root_secant" :: Lpar :: tail ->
      // root_secant(x0, x1[, tol][, maxIter])
      let (t1, x0, _) = parseE tail
      match t1 with
      | Comma :: t2 ->
          let (t3, x1, _) = parseE t2
          let tol, maxIter, rest =
            match t3 with
            | Rpar :: rest -> 1e-6, 50, rest
            | Comma :: t4 ->
                let (t5, tolV, _) = parseE t4
                match t5 with
                | Rpar :: rest -> tolV, 50, rest
                | Comma :: t6 ->
                    let (t7, itV, _) = parseE t6
                    match t7 with
                    | Rpar :: rest -> tolV, max 1 (int (absf itV)), rest
                    | _ -> raise (ParseError "Expected ')' after maxIter")
                | _ -> raise (ParseError "Expected ')' or ',' after tol")
            | _ -> raise (ParseError "Expected ',' or ')' in root_secant")
          let mutable xPrev = x0
          let mutable xCurr = x1
          let mutable fPrev = evalYAt xPrev
          let mutable fCurr = evalYAt xCurr
          let mutable i = 0
          while i < maxIter && absf fCurr > tol do
            let denom = (fCurr - fPrev)
            if denom = 0.0 then raise (EvalError "Zero slope in Secant method")
            let xNext = xCurr - fCurr * (xCurr - xPrev) / denom
            xPrev <- xCurr
            fPrev <- fCurr
            xCurr <- xNext
            fCurr <- evalYAt xCurr
            i <- i + 1
          rest, xCurr, true
      | _ -> raise (ParseError "Expected comma in root_secant arguments")
  | Ident "tangent" :: Lpar :: tail ->
      // tangent(x0, halfWidth[, mode]) – buffers a short tangent segment for plotting
      let (t1, x0, _) = parseE tail
      match t1 with
      | Comma :: t2 ->
          let (t3, halfW, _) = parseE t2
          let modeStr, rest =
            match t3 with
            | Rpar :: rest -> "linear", rest
            | Comma :: Ident m :: Rpar :: rest -> m.ToLowerInvariant(), rest
            | _ -> raise (ParseError "Expected ')' or ', mode' in tangent")
          let y0 = evalYAt x0
          let h = 1e-5
          let d = (evalYAt (x0 + h) - evalYAt (x0 - h)) / (2.0*h)
          let xL = x0 - halfW
          let xR = x0 + halfW
          let yL = y0 + d * (xL - x0)
          let yR = y0 + d * (xR - x0)
          plotPoints <- (xL, yL) :: (xR, yR) :: plotPoints
          plotMode <- Some(modeStr)
          plotRange <- Some (xL, xR)
          rest, y0, true
      | _ -> raise (ParseError "Expected comma in tangent arguments")
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
          | None ->
              // Built-in unary math functions (radians)
              let low = name.ToLowerInvariant()
              let applyBuiltin (f: float -> float) =
                  let r = f argVal
                  rest, r, true
              match low with
              | "sin" -> applyBuiltin Math.Sin
              | "cos" -> applyBuiltin Math.Cos
              | "tan" -> applyBuiltin Math.Tan
              | "exp" -> applyBuiltin Math.Exp
              | "log" -> if argVal <= 0.0 then raise (EvalError "log domain error") else applyBuiltin Math.Log
              | "sqrt" -> if argVal < 0.0 then raise (EvalError "sqrt domain error") else applyBuiltin Math.Sqrt
              | "abs" -> applyBuiltin absf
              | _ -> raise (EvalError $"Undefined function: {name}")
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
    // function definition: f(x) = <expr>
    | Ident fname :: Lpar :: Ident param :: Rpar :: Assign :: rest ->
        functionTable <- functionTable.Add(fname, (param, rest))
        [], 0.0, false
    // for-loop: for x = a to b step s do <expr>
    | Ident "for" :: Ident var :: Assign :: rest ->
        let (tA, a, _) = parseE rest
        match tA with
        | Ident "to" :: tB ->
            let (tS, b, _) = parseE tB
            let (tBodyStart, stepVal) =
              match tS with
              | Ident "step" :: tStep ->
                  let (tBody, s, _) = parseE tStep
                  tBody, s
              | _ -> tS, 1.0
            match tBodyStart with
            | Ident "do" :: body ->
                if stepVal = 0.0 then raise (EvalError "Step must be non-zero")
                plotRange <- Some (a, b)
                let compare = if stepVal > 0.0 then (fun x -> x <= b + 1e-12) else (fun x -> x >= b - 1e-12)
                let mutable x = a
                let mutable lastRes = 0.0
                let oldBinding = symbolTable.TryFind var
                try
                    while compare x do
                        symbolTable <- symbolTable.Add(var, x)
                        let (restAfter, v, f) = parseE body
                        if restAfter <> [] then raise (ParseError "Extra tokens after for body expression")
                        lastRes <- v
                        x <- x + stepVal
                    // restore
                    match oldBinding with
                    | Some vOld -> symbolTable <- symbolTable.Add(var, vOld)
                    | None -> symbolTable <- symbolTable.Remove var
                    [], lastRes, not (isIntLike lastRes)
                with ex ->
                    // restore then rethrow
                    match oldBinding with
                    | Some vOld -> symbolTable <- symbolTable.Add(var, vOld)
                    | None -> symbolTable <- symbolTable.Remove var
                    raise ex
            | _ -> raise (ParseError "Expected 'do' in for-loop")
        | _ -> raise (ParseError "Expected 'to' in for-loop")
    // assignment: x = <expr>
    | Ident name :: Assign :: rest ->
        let (afterExpr, value, _) = parseE rest
        symbolTable <- symbolTable.Add(name, value)
        afterExpr, value, false
    // expression
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

        // Normalize tiny values to +0.0 to avoid "-0" in output
        if absf lastResult < 5e-13 then lastResult <- 0.0

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
    plotPoints <- []
    plotMode <- None
    plotRange <- None

let HasPlotData () = plotPoints <> []
let GetPlotData () = plotPoints |> List.rev |> List.toArray
let GetPlotMode () = match plotMode with | Some m -> m | None -> "linear"
let GetPlotRange () = match plotRange with | Some (a,b) -> (a,b) | None -> (0.0,1.0)
let ClearPlotData () = plotPoints <- []; plotMode <- None; plotRange <- None

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
