type ide = string;;
type exp = Eint of int | Ebool of bool | Estring of string | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp | Dict of (ide * exp) list | Select of exp * ide | Insert of exp * ide * exp |
	Remove of exp * ide | Clear of exp | ApplyOver of exp * exp;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | String of string | Unbound | FunVal of evFun | RecFunVal of ide * evFun | DictVal of (ide * evT) list
and evFun = ide * exp * evT env;;

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	Estring s -> String s |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
        Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
            		_ -> failwith("non functional def"))  
    (* 2° Progetto intermedio PR2 *)
    |Dict(dictlist) -> DictVal(evalList dictlist r)
    |Select(dictlist, name) -> 
    	let v1 = eval dictlist r in
			(match v1 with
			DictVal(dict) -> research dict name
			|_ -> failwith("wrong argument"))
	|Insert(dictlist,name,expToAdd) -> 
		let v1 = eval expToAdd r in
			let v2 = eval dictlist r in
				(match v2 with
					DictVal(dict) -> DictVal(add dict name v1)
					|_ -> failwith("wrong argument"))
	|Remove(dictlist,name) -> 
		(match (eval dictlist r) with
			DictVal(dict) -> DictVal(remove dict name)
			|_ -> failwith("wrong expression"))
	|Clear(dictlist) -> 
		(match (eval dictlist r) with
			DictVal(dict) -> DictVal([])
			|_ -> failwith("wrong expression"))
	|ApplyOver(f,dictlist) -> 
		let fClosure = eval f r in
		(match (fClosure, eval dictlist r) with
			(FunVal(arg,fBody,fEnv),DictVal(dict)) -> DictVal(apply arg fBody fEnv dict)
			|(RecFunVal(g,(arg,fBody,fEnv)),DictVal(dict)) -> DictVal(applyRec arg fBody fEnv dict g fClosure)
			|(_,_) -> failwith("wrong expression: Fun , Dict required"))
and evalList (l : (ide * exp) list ) (env : evT env) : (ide * evT) list = 
		match l with
		[] -> []
		|(ide,e)::xs -> (ide,eval e env)::(evalList xs env)
and research (l : (ide * evT) list) (name : ide) : evT = 
		match l with
		[] -> failwith("no such elements")
		|(ide,v)::xs -> if (name = ide) then v else (research xs name)
and add (l : (ide * evT) list) (name : ide) (value : evT) : (ide * evT) list = 
		match l with
		[] -> (name,value)::[]
		|(ide,v)::xs -> if (ide = name) then (ide,value)::xs else (ide,v)::(add xs name value)
and remove (l : (ide * evT) list) (name : ide) : (ide * evT) list = 
		match l with
		[] -> []
		|(ide,v)::xs -> if (name = ide) then xs else (ide,v)::(remove xs name)
and apply (arg : ide) (body : exp) (env : evT env) (l : (ide * evT) list) : (ide * evT) list = 
		match l with
		[] -> []
		|(ide,v)::xs -> 
			let env1 = bind env arg v in
			try (ide,eval body env1)::(apply arg body env xs)
				with 
				Failure explanation -> (ide,v)::(apply arg body env xs)
and applyRec (arg : ide) (body : exp) (env : evT env) (l : (ide * evT) list) (g : ide) (f : evT) : (ide * evT) list =
		match l with
		[] -> []
		|(ide,v)::xs -> 
			let rEnv = bind env g f in
				let aEnv = bind rEnv arg v in
					try (ide,eval body aEnv)::(applyRec arg body env xs g f)
						with
						Failure explanation -> (ide,v)::(applyRec arg body env xs g f)
;;
		
(* =================  TESTS  ================= *)

(* ambiente vuoto *)
let env0 = emptyenv Unbound;;

(* alcune funzioni per il test *)
let plusOne = Fun("x",Sum(Den "x",Eint(1)));;
let plusOnCondition = Fun("x",Ifthenelse(IsZero(Den "x"),Sum(Den "x",Eint(5)),Diff(Den "x",Eint(3))));;
let notBool = Fun("x",Not(Den "x"));;

(* dichiarazione dizionari *)
let emptyDict = Dict [];; (* dizionario vuoto *)
eval emptyDict env0;; (* risultato atteso: Dict [] *)

let dict1 = Dict [("a",Eint(1));("b",Ebool(true));("c",Ebool(false));("d",Eint(0));("e",Eint(2))];;
eval dict1 env0;; (* risultato atteso: Dict [("a",Int 1);("b",Bool true);("c",Bool false);("d",Int 0);("e",Int 2)] *)

(* dichiarazione di funzione ricorsiva *)
let fun1 = Ifthenelse(IsZero(Den "x"),Eint(0),Sum(Den "x",FunCall(Den "f",Diff(Den "x",Eint 1))));;
let fun2 = Letrec("f",Fun("x",fun1),ApplyOver(Den "f",dict1));;

(* selezione del valore del parametro "a" da dict1 *)
let v1 = Select(dict1,"a");;
eval v1 env0;; (* risultato atteso: Int (1) *)
 
let v2 = Select(dict1,"d");;
eval v2 env0;; (* risultato atteso: Int (0) *)

(* dizionario risultate dall' inserimento di "f" nel dict1 *)
let dict2 = Insert(dict1,"f",Eint(3));;
eval dict2 env0;; (* risultato atteso: Dict [("a",Int 1);("b",Bool true);("c",Bool false);("d",Int 0);("e",Int 2);("f",Int 3)] *)

(* rimozione di "f" da dict2 *)
let dict3 = Remove(dict2,"f");;
eval dict3 env0;; (* risultato atteso: Dict [("a",Int 1);("b",Bool true);("c",Bool false);("d",Int 0);("e",Int 2)] *)

(* eliminazione elementi nel dizionario *)
let dict4 = Clear(dict3);;
eval dict4 env0;; (* risultato atteso: Dict [] *)

(* applicazione della funzione che incrementa di uno i valori interi *)
let res1 = ApplyOver(plusOne,dict1);;
eval res1 env0;; (* risultato atteso: Dict [("a",Int 2);("b",Bool true);("c",Bool false);("d",Int 1);("e",Int 3)] *)

(* applicazione di una funzione sotto una determinata condizione *)
let res2 = ApplyOver(plusOnCondition,dict1);;
eval res2 env0;; (* risultato atteso: Dict [("a",Int (-2));("b",Bool true);("c",Bool false);("d",Int (5));("e",Int (-1))] *)

(* applicazione di una funzione che nega i booleani *)
let res3 = ApplyOver(notBool,dict1);;
eval res3 env0;; (* risultato atteso: Dict [("a",Int 1);("b",Bool false);("c",Bool true);("d",Int 0);("e",Int 2] *)

(* TEST su casi limite *)

(* proviamo a selezionare un elemento che non è presente nel dizionario *)
let d1 = Select(dict1,"h");;
eval d1 env0;; (* risultato atteso: Eccezione: no such elements, lanciata dalla funzione research *)

(* proviamo a selezionare un elemento da un dizionario vuoto *)
let d2 = Select(emptyDict,"a");;
eval d2 env0;; (* risultato atteso: Eccezione: no such elements, lanciata dalla funzione research *)

(* proviamo ad inserire un elemento già presente in un dizionario. Il caso è stato gestito con la modifica del valore già presente*)
let d3 = Insert(dict1,"e",Ebool(true));;
eval d3 env0;; (* risultato atteso: Dict [("a",Int 1);("b",Bool true);("c",Bool false);("d",Int 0);("e",Bool true)] *)

(* proviamo a rimuovere un elemento da un dizionario vuoto. Se un elemento non è presente, la remove semplicemente non fa nulla *)
let d4 = Remove(emptyDict,"a");;
eval d4 env0;; (* risultato atteso: Dict [] *)

(* proviamo a pulire un dizionario già vuoto *)
let d5 = Clear(emptyDict);;
eval d5 env0;; (* risultato atteso: Dict [] *)

(* l'applicazione di una funzione su un dizionario vuoto semplicemente restituisce un dizionario vuoto *)
let d6 = ApplyOver(plusOne,emptyDict);;
eval d6 env0;; (* risultato atteso: Dict [] *)

(* applicazione della funzione ricorsiva sul dizionario dict1 *)
eval fun2 env0;; (* risultato atteso: Dict [("a",Int 1);("b",Bool true);("c",Bool false);("d",Int 0);("e",Int 3] *)