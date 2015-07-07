#I "packages/FParsec.1.0.1/lib/net40-client/"

#r "FParsecCS.dll"
#r "FParsec.dll"

open FParsec



//Types
type Expr = | Variable of int
            | Constant of int
            | Function of int * Expr list
            | Predicate of int * Expr list            
            | Equality of Expr * Expr
            | Not of Expr
            | And of Expr * Expr
            | Or of Expr * Expr
            | Impl of Expr * Expr
            | Bicond of Expr * Expr
            | ForAll of int list * Expr
            | Exists of int list * Expr

type State = { 
    varStack: (string * int) list list
    nonVarMap: (string * int) list    
    nextId: int    
}

let newState = { 
    varStack = []
    nonVarMap = []   
    nextId = 0
}

let varId st n = 
    let rec findMap f l = 
        match l with
        | [] -> None
        | fst::rst -> 
            match f(fst) with
            | None -> findMap f rst
            | Some r -> Some r

    let p = findMap (List.tryFind (fun (sn, _) -> sn = n)) st.varStack            

    match p with
    | Some (_,i) -> Some i
    | None -> None

let pushVars st ns =
    let frame, nextId = ns |> List.mapFold (fun i n -> (n,i), i + 1) st.nextId 
    {st with varStack = frame::st.varStack; nextId = nextId }, List.map snd frame

let popVars st =     
    {st with varStack = List.tail st.varStack }

let addNonVar st n = 
    match st.nonVarMap |> List.tryFind (fun (sn, _) -> sn = n) with
    | Some (_,i) -> st,i
    | None -> {st with nonVarMap = (n, st.nextId)::st.nonVarMap; nextId = st.nextId + 1; }, st.nextId

//Parsing
let ws = spaces
let str_ws s = pstring s .>> ws

type IdentifierType = Var | NotVar

module UpdState = 
    type Result<'a> = | SuccessUpdate of State * 'a 
                      | Success of 'a
                      | Failure of string

let updateState f p = 
    p .>>. getUserState >>= (fun (r,st) -> 
        match f st r with
        | UpdState.Success r' -> preturn r'
        | UpdState.SuccessUpdate (st',r') -> preturn r' .>> setUserState st'        
        | UpdState.Failure msg -> failFatally msg
    )

//gn - get name from parser result
//c - construct new result from old result and index
let nonVarToIdThroughState gn c = 
    updateState (fun st r ->
        let st',i = gn r |> addNonVar st
        UpdState.SuccessUpdate (st', (c r i))
    )

let varToIdThroughState = 
    updateState (fun st n ->
        let i = varId st n
        match i with
        | None -> UpdState.Failure (sprintf "unknown variable %A" n)
        | Some i -> UpdState.Success (Variable i)
    )

let identifier t = 
    let fl, err = match t with
                  | Var -> isLower, "variable"
                  | NotVar -> isUpper, "non-variable identifier"    
    let isChar c = isLetter c || isDigit c || c = '_'    
    many1Satisfy2L fl isChar err .>> ws 


let term, pRefTerm = createParserForwardedToRef()

let func =     
    //NOTE: Second part fails immediately if there is no opening bracket,
    //so backtracking occurs and we can check other choices (constant)
    identifier NotVar .>>.? (between (str_ws "(") (str_ws ")") (sepBy1 term (str_ws ",")))
        |> nonVarToIdThroughState fst (fun r i -> Function (i, snd r))     

do pRefTerm := choice [
        identifier Var |> varToIdThroughState
        func
        identifier NotVar |> nonVarToIdThroughState id (fun _ i -> Constant i)        
    ]

let termEquality = 
    term .>>? str_ws "=" .>>. term |>> Equality

let predicate = 
    choice [
        termEquality

        identifier NotVar .>>.? (between (str_ws "(") (str_ws ")") (sepBy1 term (str_ws ","))) 
            |> nonVarToIdThroughState fst (fun r i -> Predicate (i, snd r)) 
                
        identifier NotVar 
            |> nonVarToIdThroughState id (fun _ i -> Predicate (i, [])) 
    ]
       
let opp = new OperatorPrecedenceParser<Expr,unit,State>()
let expr = opp.ExpressionParser

let updateStatePushVars = 
    updateState (fun st r ->      
        UpdState.SuccessUpdate (pushVars st r)
    )     

let quantifiedExpr isForAll =
    let l,ctor = match isForAll with
                 | true -> "A", ForAll
                 | false -> "E", Exists
    str_ws ("@" + l) >>. sepBy1 (identifier Var) (str_ws ",") 
        |> updateStatePushVars .>>. expr .>> updateUserState (fun st -> popVars st) |>> ctor

opp.TermParser <- choice [
   quantifiedExpr true
   quantifiedExpr false
   predicate
   between (str_ws "(") (str_ws ")") expr
]   
opp.AddOperator(PrefixOperator("!", ws, 5, true, fun x -> Not x))
opp.AddOperator(InfixOperator("&", ws, 4, Associativity.Left, fun x y -> And (x,y)))
opp.AddOperator(InfixOperator("|", ws, 3, Associativity.Left, fun x y -> Or (x,y)))
opp.AddOperator(InfixOperator("=>", ws, 2, Associativity.Left, fun x y -> Impl (x,y)))
opp.AddOperator(InfixOperator("<=>", ws, 1, Associativity.Left, fun x y -> Bicond (x,y)))

let test p str =    
    match runParserOnString p newState "" str with
    | Success(result, st, _)   -> printfn "Success: %A, state: %A" result st
    | Failure(errorMsg, _, _) -> printfn "Failure: %s" errorMsg

//test expr "@A x,y (@E x P1(x) & F1(x) = F2(x)) & P2(x) & P3(y)"

let rec exprToString (expr, st) = 
    let getName id = 
        fst (List.find (fun (_,i) -> i = id) st.nonVarMap)

    let funcOrPredToString (i, ts, st) = 
        sprintf "%s(%s)" (getName i) ((ts |> List.fold (fun s t -> s + (exprToString (t,st)) + ",") "").TrimEnd(','))

    match expr with
    | Variable i -> sprintf "x%d" i
    | Constant i -> getName i
    | Function (i,ts) -> funcOrPredToString (i,ts,st)
    | Predicate (i,ts) -> funcOrPredToString (i,ts,st)
    | Equality (t1,t2) -> sprintf "%s = %s" (exprToString (t1,st)) (exprToString (t2, st))
    | _ -> failwith "Not implemented yet"

//Theorem proving
let getExpr st s = 
    match runParserOnString expr st "" s with
    | Success(result, st, _)   -> (result, st)
    | Failure(errorMsg, _, _) -> failwith errorMsg

let getPredForAll st s = 
    let (e, st) = getExpr st ("@A x,y,z,w " + s)
    match e with
    | ForAll (_, pred) -> (pred, st)
    | _ -> failwith ""

module Unify =   
    type CompExprOp = | Function of int
                      | Predicate of int
                      | Equality

    type UniExpr = | Constant of int
                   | CompExprOp of CompExprOp
                   | Variable of int                   
                   | List of UniExpr list
                   | CompExpr of CompExprOp * UniExpr list

    //Converters Expr <-> UniExpr for unification
    let rec getUniExpr expr = 
        match expr with
        | Expr.Variable i -> Variable i
        | Expr.Constant i -> Constant i
        | Expr.Function (i,ts) -> CompExpr (CompExprOp.Function i, ts |> List.map getUniExpr)
        | Expr.Predicate (i,ts) -> CompExpr (CompExprOp.Predicate i, ts |> List.map getUniExpr)
        | Expr.Equality (t1,t2) -> CompExpr (CompExprOp.Equality, [getUniExpr t1; getUniExpr t2])
        | _ -> failwith "Can't get unification expression from given expression"

    let rec getExpr uniExpr = 
        match uniExpr with
        | Constant i -> Expr.Constant i
        | Variable i -> Expr.Variable i
        | CompExpr (op, args) -> 
            match op with
            | Function i -> Expr.Function (i, args |> List.map getExpr)
            | Predicate i -> Expr.Predicate (i, args |> List.map getExpr)
            | Equality -> Expr.Equality (getExpr args.[0], getExpr args.[1])
        | _ -> failwith ""

    let mapTillNone f l =
        let rec map lo li = 
            match li with
            | [] -> Some lo
            | x::xs -> 
                match f x with
                | Some y -> map (y::lo) xs
                | None -> None

        map [] l

   
    ///<summary>Fixes one subst expression in subst list</summary>
    ///<param name="su">Subst list</param>
    ///<param name="e">Subst expression</param>
    ///<param name="uv">Used variables list to detect hopeless loops</param>
    ///<returns>Some fixed expression or None if substitution is impossible</returns>
    let rec fixVarsInSubstExpr su uv e  =
        //printfn "%A %A %A" su uv e

        match e with
        | Variable i -> 
            if uv |> List.contains i then None else

            match su |> List.tryFind (fun (id, _) -> id = i) with
            | None -> Some (Variable i)
            | Some (_,s) -> fixVarsInSubstExpr su (i::uv) s 
        | CompExpr (op, args) ->            
            match args |> mapTillNone (fixVarsInSubstExpr su uv) with
            | None -> None
            | Some args' -> Some (CompExpr (op, args'))            
        | x -> Some x

    ///<summary>Fixes incomplete subst, ex. {x / Mother(y); y / John} -> {x / Mother(John); y / John}
    ///Also finds loops that make substitution impossible like {x / F(y); y / F(x)}</summary>
    ///<param name="su">Subst list</param>
    ///<returns>Some fixed subst list or None if substitution is impossible</returns>
    let rec fixVarsInSubst su =
        su |> mapTillNone (fun (i, se) ->
            let se' = se |> fixVarsInSubstExpr su []
            match se' with
            | None -> None
            | Some se' -> Some (i,se')
        )

    let rec unify x y su = 
        if Option.isNone su then None else

        match (x,y) with
        | (Constant xi, Constant yi) -> if xi = yi then su else None
        | (CompExprOp xo, CompExprOp yo) -> if xo = yo then su else None        
        | (Variable i, _) -> unifyVar i y (Option.get su)
        | (_, Variable i) -> unifyVar i x (Option.get su)
        | (List [], List []) -> su
        | (List (xf::xr), List (yf::yr)) -> unify (List xr) (List yr) (unify xf yf su)
        | (CompExpr (xo, xargs), CompExpr (yo, yargs)) -> unify (List xargs) (List yargs) (unify (CompExprOp xo) (CompExprOp yo) su)
        | _ -> None

    and unifyVar var x su = 
        //Executes f1 if subst is already there and f2 if not
        let tryFind i f1 f2 = 
            match su |> List.tryFind (fun (li, _) -> li = i) with
            | Some (_,e) -> f1 e
            | None -> f2 ()

        //Adds new subst
        let add () = Some ((var, x)::su)

        //If var is found in subst replace it and unify again
        tryFind var (fun e -> unify e x (Some su)) (fun () ->
        
        //else
        match x with
        //if x is Variable too
        | Variable xi -> 
            //And x is found in subst replace it and unify again
            tryFind xi (fun e -> unify (Variable var) x (Some su))  (fun () ->            
                //else if variables are the same
                if xi = var then Some su else
                //else
                add()
            )
        | _ -> add()        
        )  
        
let unify x y = 
    match Unify.unify (Unify.getUniExpr x) (Unify.getUniExpr y) (Some []) with
    | None -> None
    | Some su -> 
        match su |> Unify.fixVarsInSubst with
        | None -> None
        | Some su' -> Some (su' |> List.map (fun (i, se) -> (i, se |> Unify.getExpr)))

let substToString st s = 
    match s with
    | None -> "No substitution"
    | Some l -> l 
                |> List.map (fun (i, su) -> sprintf "x%d / %s" i (exprToString (su,st))) 
                |> List.reduce (fun s1 s2 -> s1 + "; " + s2)

let testUnify st x y =
    sprintf "(%s) unifying with (%s) gives {%s}"
        (exprToString (x,st))
        (exprToString (y,st))
        (substToString st (unify x y))

let strs = [ 
    "Test(x, F(x))"
    "Test(F(x), x)"
    "Knows(John, x)"
    "Knows(John, Jane)"
    "Knows(y, Bill)"
    "Knows(y, Mother(y))"
    "Knows(x, Elisabeth)"
    "Knows(y, z)"
]

let (es, st) = List.mapFold getPredForAll newState strs
     





    