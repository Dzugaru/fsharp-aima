#I "packages/FParsec.1.0.1/lib/net40-client/"

#r "FParsecCS.dll"
#r "FParsec.dll"

open FParsec



//Types
type Term = | Function of int * Term list
            | Constant of int
            | Variable of int

type Predicate = | Predicate of int * Term list
                 | Equality of Term * Term

type Expr = | Atom of Predicate
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
   predicate |>> Atom
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

test expr "@A x,y (@E x P1(x) & F1(x) = F2(x)) & P2(x) & P3(y)"