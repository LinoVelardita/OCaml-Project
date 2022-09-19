type ide = string;;

type op = Sum | Sub | Mul;;

type bool_op = And | Or;;

type eq_op = Equal | Greater | Lower | GEq | LEq;;

type exp =
    | EInt of int
    | EBool of bool
    | EString of string
    | Not of exp
    | Ide of ide
    | Op of exp * op * exp
    | BoolOp of exp * bool_op * exp
    | EqOp of exp * eq_op * exp
    | IfThenElse of exp * exp * exp
    | Let of ide * exp * exp
    | Fun of ide * exp
    | RecFun of ide * ide * exp
    | FunCall of exp * exp
    | EDict of (ide * exp) list
    | Insert of ide * exp * exp
    | Delete of ide * exp
    | Has_Key of ide * exp
    | Iterate of exp * exp
    | Filter of (ide list) * exp
    | FunAcc of ide * ide * exp (*parametro, accumulatore, body*)
    | FunCallAcc of exp * exp * exp (*FunAcc * param * accumulatore*)
    | Fold of exp * exp (*FunAcc * Dict*)
    ;;


type evT =
    | Int of int
    | Bool of bool
    | String of string
    | FunClosure of ide * exp * env
    | RecClosure of ide * ide * exp * env
    | FunAccClosure of ide * ide * exp * env
    | FunDClosure of ide * ide * exp * env (*param, acc, body, ambiente*)
    | Dict of (ide * evT) list
    | Unbound
and env = (ide * evT) list;;

let emptyEnv = [("",Unbound)];;

let bind (var : ide) (v : evT) (e : env) : env = (var, v) :: e;;

let two_bind (var : ide) (var2 : ide) (v : evT) (v2 : evT) (e : env) : env =
    (var, v) :: (var2, v2) :: e;;

let rec lookup (id : ide) (r : env) : evT = match r with
    | [] -> Unbound
    | (x, value) :: l -> if(id = x) then value else lookup id l;;

let typecheck (s : string) (e : evT) : bool = match s with
    | "int" -> (match e with
              | Int(_) -> true
              | _ -> false)
    | "bool" -> (match e with
              | Bool(_) -> true
              | _ -> false)
    | "string" -> (match e with
              | String(_) -> true
              | _ -> false)
    | "dictionary" -> (match e with
              | Dict(_) -> true
              | _ -> false)
    | _ -> failwith("Invalid Type");;

let type_dict (e : (ide * evT) list) : string = match e with
    | [] -> failwith("FATAL ERROR")
    | (k, value) :: xs -> (match value with
                            | Int(_) -> "int"
                            | Bool(_) -> "bool"
                            | String(_) -> "string"
                            | _ -> failwith("Type Not Allowed"));;

let eval_not (e : evT) : evT = match e with
         | Bool(true) -> Bool(false)
         | Bool(false) -> Bool(true)
         | _ -> failwith("Invalid Type(required boolean)");;


let eval_op (e1 : evT) (o : op) (e2 : evT) : evT = match e1, o, e2 with
    | Int(x), op, Int(y) -> (match op with
                            |Sum -> Int(x+y)
                            |Sub -> Int(x-y)
                            |Mul -> Int(x*y))
    | _ -> failwith("Invalid Type");;

let eval_bool (a : evT) (o : bool_op) (b : evT) : evT = match a, o, b with
    | Bool(a), op, Bool(b) -> (match op with
                               |And -> Bool(a && b)
                               |Or -> Bool(a || b))
    | _ -> failwith("Invalid Type");;

let eval_eq (x : evT) (o : eq_op) (y : evT) : evT = match x, o, y with
    | Bool(x), op, Bool(y) -> (match op with
                               Equal -> if(x = y) then Bool(true)
                                        else Bool(false)
                               | _ -> failwith("Invalid Operation for boolean"))
    | Int(x), op, Int(y) -> (match op with
                             Equal -> if(x = y) then Bool(true)
                                      else Bool(false)
                             | Greater -> if(x > y) then Bool(true)
                                        else Bool(false)
                             | Lower -> if(x < y) then Bool(true)
                                      else Bool(false)
                             | GEq -> if (x >= y) then Bool(true)
                                    else Bool(false)
                             | LEq -> if (x <= y) then Bool(true)
                                    else Bool(false))
    | _ -> failwith("Invalid Type");;


let rec member (dict : (ide * evT) list) (a : ide) = match dict with
    | [] -> false
    | (key, value) :: xs -> if(key = a) then true else member xs a;;

let eval_insert (k : ide) (v : evT) (l : (ide * evT) list) : (ide * evT) list = match l with
    | [] -> [(k, v)]
    | (x, y) :: xs -> if(typecheck (type_dict l) v && (member l k)=false)
                            then (k, v) :: l
                      else failwith("Invalid Type: type must be unique(dictionary)");;

let rec delete_key (id : ide) (l : (ide * evT) list) : (ide * evT) list = match l with
    | [] -> []
    | (key, value) :: xs -> if(key = id) then xs
                            else (key, value) :: delete_key id xs;;

let rec member_k a l = match l with
    | [] -> false
    | x :: xs -> if(x = a) then true else member_k a xs;;

let rec eval_filter (l : (ide * evT) list) (k : ide list) : (ide * evT) list = match l with
    | [] -> []
    | (key, value) :: xs -> if(member_k key k) then (key, value) :: eval_filter xs k
                            else eval_filter xs k;;



let rec eval (e : exp) (r : env) : evT = match e with
    | EInt(x) -> Int(x)
    | EBool(b) -> Bool(b)
    | EString(s) -> String(s)
    | Not(b) -> eval_not (eval b r)
    | Ide(x) -> lookup x r
    | Op(x, o, y) -> eval_op (eval x r) o (eval y r)
    | BoolOp(a, o, b) -> eval_bool (eval a r) o (eval b r)
    | EqOp(x, o, y) -> eval_eq (eval x r) o (eval y r)
    | IfThenElse(cond, a, b) -> (match eval cond r with
                                   | Bool(true) -> eval a r
                                   | Bool(false) -> eval b r
                                   | _ -> failwith("Non-Boolean Condition"))
    | Let(id, e1, e2) -> eval e2 (bind id (eval e1 r) r)
    | Fun(param, body) -> FunClosure(param, body, r)
    | RecFun(id, param, body) -> RecClosure(id, param, body, r)
    | FunCall(f, e) -> let evalue = eval e r in
                           let fclose = eval f r in
                               (match fclose with
                                | FunClosure(idparam, body, env) ->
                                    eval body (bind idparam evalue env)
                                | RecClosure(fid, idparam, body, env) ->
                                    let recEnv = bind fid fclose env in
                                        eval body (bind idparam evalue recEnv)
                                | _ -> failwith("Invalid function"))
    | EDict(l) -> Dict(eval_dict l r)
    | Insert(id, v, dict) -> let dict_val = eval dict r in
                             let vv = eval v r in
                             (match dict_val with
                             | Dict(l) -> Dict(eval_insert id vv l)
                             | _ -> failwith("Invalid Type(dictionary)"))
    | Delete(id, dict) -> let dict_val = eval dict r in
                          (match dict_val with
                           | Dict(l) -> Dict(delete_key id l)
                           | _ -> failwith("Invalide Type(dictionary)"))
    | Has_Key(id, dict) -> let dict_val = eval dict r in
                           (match dict_val with
                           | Dict(l) -> if(member l id) then Bool(true)
                                        else Bool(false)
                           | _ -> failwith("Innvalid Type(dictionary)"))
    | Iterate(f, dict) ->  (match dict, f with
                           | EDict(l), Fun(param, body) -> Dict(eval_iterate l f r)
                           | EDict(l), RecFun(id, param, body) -> Dict(eval_iterate l f r)
                           | _ -> failwith("Invalid Type(dictionary)"))
    | Filter(k, dict) -> let dict_val = eval dict r in
                         (match dict_val with
                          | Dict(l) -> Dict(eval_filter l k)
                          | _ -> failwith("Invalid Type(dictionary)"))
    | FunAcc(param, acc, body) -> FunAccClosure(param, acc, body, r)
    | FunCallAcc(f, e, a) -> let evalue = eval e r in
                             let avalue = eval a r in
                             let fclose = eval f r in
                                (match fclose with
                                 | FunAccClosure(param, acc, body, env) ->
                                    eval body (two_bind param acc evalue avalue env)
                                 | _ -> failwith("Invalid funcall"))
    | Fold(f, d) -> let a = EInt(0) in
                        (match d, f with
                        | EDict(l), FunAcc(param, acc, body) -> apply_dict l f a r
                        | _ -> failwith("Invalid Type(Fold : dictionary)"))

and eval_dict (l : (ide * exp) list) (r : env) : (ide * evT) list = match l with
    | [] -> []
    | (key, value) :: xs -> (key, (eval value r)) :: eval_dict xs r

and eval_iterate (l : (ide * exp) list) (f : exp) (r : env) : (ide * evT) list = match l with
    | [] -> []
    | (key, value) :: xs -> let call = FunCall(f, value) in
                            (key, eval call r) :: eval_iterate xs f r

and apply_dict (l : (ide * exp) list) (f : exp) (acc : exp) (r : env) : evT = match l with
        | [] -> failwith("Iteration Error")
        | (key, value) :: [] -> let last_it = FunCallAcc(f, value, acc) in
                                    eval last_it r
        | (key, value) :: xs -> apply_dict xs f (FunCallAcc(f, value, acc)) r
    ;;





    (*________________Test dell'interprete base___________________*)

    let env0 = emptyEnv;;

    let e1 = FunCall(Fun("y", Op(Ide "y", Sum, EInt 1)), EInt 3);;

    eval e1 env0;;

    let fattoriale = RecFun("fact", "n", IfThenElse(EqOp(Ide "n", Equal, EInt 1), EInt 1, Op(Ide "n", Mul, FunCall(Ide "fact", Op(Ide "n", Sub, EInt 1)))));;

    let call_fattoriale = FunCall(fattoriale, EInt 4);;

    eval call_fattoriale env0;;

    let abs = FunAcc("x", "y", IfThenElse(EqOp(Ide "x", Greater, Ide "y"), Op(Ide "x", Sub, Ide "y"), Op(Ide "y", Sub, Ide "x")));;

    let call_abs = FunCallAcc(abs, EInt 3, EInt 10);;

    eval call_abs env0;;

    (*____________Test Dizionario & Funzioni Primitive_____________*)

    let d = EDict([]);;

    let d = Insert("a", EInt 1, d);;
    let d = Insert("b", EInt 2, d);;
    let haskey = Has_Key("b", d);;

    eval d env0;;
    eval haskey env0;;

    let d = Delete("b", d);;
    let haskey = Has_Key("b", d);;

    eval d env0;;
    eval haskey env0;;

    let magazzino = EDict( [ ("mele", EInt 430); ("banane", EInt 312); ("arance", EInt 525); ("pere", EInt 217) ] ) ;;

    let filter_m = Filter(["mele"; "pere"], magazzino);;

    eval filter_m env0;;

    let uno = Fun("x", Op(Ide "x", Sum, EInt 1));;

    let it_dict = Iterate(uno, magazzino);;

    eval it_dict env0;;

    let addone = FunAcc("x", "acc", Op(Ide "acc", Sum, Op(Ide "x", Sum, EInt 1)));;

    let fold_m = Fold(addone, magazzino);;

    eval fold_m env0;;
