(* 
   UNIVERSIDADE FEDERAL DO RIO GRANDE DO SUL  - Semestre 2022/01
   
   Curso de Ciência da Computação
   
   Trabalho de Implementação - Semântica Formal - Turma B

   Andrei Pochmann Koenich     Cartão: 00308680
   Pedro Company Beck          Cartão: 00324055
   Pietro Benati Carrara       Cartão: 00318995

   Referências:
   https://www.youtube.com/watch?v=Zukb_gsW1RU
   https://www.youtube.com/watch?v=jSrt_1FR7YI
   https://www.youtube.com/watch?v=TFUBQXhT5gw
*)

(*++++++++++++++++++++++++++++++++++++++*)
(*     Interpretador para L1            *)
(*   - inferência de tipos              *)
(*   - avaliador big step com ambientes *)
(*   - construções imperativas          *)
(*++++++++++++++++++++++++++++++++++++++*)

(**+++++++++++++++++++++++++++++++++++++++++*)
(*  SINTAXE, AMBIENTE de TIPOS e de VALORES *)
(*++++++++++++++++++++++++++++++++++++++++++*)

type tipo =
    TyInt
  | TyBool
  | TyFn of tipo * tipo
  | TyPair of tipo * tipo
  | TyRef of tipo (* Adicao do novo tipo Tref *)
  | TyUnit(* Adicao do novo tipo Unit *)

type ident = string

type op = Sum | Sub | Mult | Eq | Gt | Lt | Geq | Leq

type expr =
  | Num of int
  | Var of ident
  | True
  | False
  | Binop of op * expr * expr
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | If of expr * expr * expr
  | Fn of ident * tipo * expr
  | App of expr * expr
  | Let of ident * tipo * expr * expr
  | LetRec of ident * tipo * expr  * expr 
              
  (* Daqui para baixo, adições das novas expressões *)

  | Asg of expr * expr 
  | Dref of expr
  | New of expr
  | Seq of expr * expr
  | Whl of expr * expr
  | Skip

type tenv = (ident * tipo) list

type valor =
    VNum of int
  | VTrue
  | VFalse
  | VPair of valor * valor
  | VClos  of ident * expr * renv
  | VRclos of ident * ident * expr * renv
              
  (* Daqui para baixo, adições dos novos valores *)

  | VRef  (* Adição do novo valor que representa uma posição de memória *)
  | VSkip (* Adicao do valor skip, que é o único do tipo unit *)
and
  renv = (ident * valor) list

(* Representação dos endereços de memória com valores inteiros *)    
type address = int
  
(* Representação da memória como uma lista de pares ordenados de endereços e valores *)
type mem = (address * valor) list

(* Adição do tipo que representa um par, contendo um valor e uma memória *)
type valorMem = (valor * mem)

(* Funções polimórficas para ambientes *)

let rec lookup a k =
  match a with
    [] -> None
  | (y,i) :: tl -> if (y=k) then Some i else lookup tl k

let rec update a k i =
  (k,i) :: a

(* Exceções que não devem ocorrer *)

exception BugParser

exception BugTypeInfer

(**+++++++++++++++++++++++++++++++++++++++++*)
(*         INFERÊNCIA DE TIPOS              *)
(*++++++++++++++++++++++++++++++++++++++++++*)

exception TypeError of string

let rec typeinfer (tenv:tenv) (e:expr) : tipo =
  match e with

  (* TInt  *)
  | Num _ -> TyInt 
                   
  (* TVar *)
  | Var x ->
      (match lookup tenv x with
         Some t -> t
       | None -> raise (TypeError ("Erro: variável não declarada:" ^ x)))

  (* TBool *)
  | True  -> TyBool
  | False -> TyBool

  (*TOP+  e outras para demais peradores binários *)
  | Binop(oper,e1,e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      if t1 = TyInt && t2 = TyInt then
        (match oper with
           Sum | Sub | Mult -> TyInt
         | Eq | Lt | Gt | Geq | Leq -> TyBool)
      else raise (TypeError "Erro: operando nao é do tipo int.")

  (* TPair *)
  | Pair(e1,e2) -> TyPair(typeinfer tenv e1, typeinfer tenv e2)
                     
  (* TFst *)
  | Fst e1 ->
      (match typeinfer tenv e1 with
         TyPair(t1,_) -> t1
       | _ -> raise (TypeError "Erro: fst espera tipo par.")) 
                                                              
  (* TSnd  *)
  | Snd e1 ->
      (match typeinfer tenv e1 with
         TyPair(_,t2) -> t2
       | _ -> raise (TypeError "Erro: fst espera tipo par."))

  (* TIf  *)
  | If(e1,e2,e3) ->
      (match typeinfer tenv e1 with
         TyBool ->
           let t2 = typeinfer tenv e2 in
           let t3 = typeinfer tenv e3
           in if t2 = t3 then t2
           else raise (TypeError "Erro: then/else com tipos diferentes.")
       | _ -> raise (TypeError "Erro: condição de IF não é do tipo bool."))

  (* TFn *)
  | Fn(x,t,e1) ->
      let t1 = typeinfer (update tenv x t) e1
      in TyFn(t,t1)

  (* TApp *)
  | App(e1,e2) ->
      (match typeinfer tenv e1 with
         TyFn(t, t') ->  if (typeinfer tenv e2) = t then t'
           else raise (TypeError "Erro: tipo do argumento está errado." )
       | _ -> raise (TypeError "Erro: tipo função era esperado."))

  (* TLet *)
  | Let(x,t,e1,e2) ->
      if (typeinfer tenv e1) = t then typeinfer (update tenv x t) e2
      else raise (TypeError "Erro: expressão não é do tipo declarado em let." )

  (* TLetRec *)
  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) ->
      let tenv_com_tf = update tenv f tf in
      let tenv_com_tf_tx = update tenv_com_tf x tx in
      if (typeinfer tenv_com_tf_tx e1) = t2
      then typeinfer tenv_com_tf e2
      else raise (TypeError "Erro: tipo da função diferente do declarado.")
  | LetRec _ -> raise BugParser

  (* TAtr *)
  | Asg(e1,e2) ->
      (match typeinfer tenv e1 with
         TyRef(t) -> if (typeinfer tenv e2) = t then TyUnit
           else raise (TypeError "Erro: tipo do argumento está errado." )
       | _ -> raise (TypeError "Erro: tipo referencia era esperado."))
      
  (* Novas regras do sistema de tipos são adicionadas a partir desse ponto *)      

  (* Regra TSkip *)
  | Skip -> TyUnit

  (* Regra TDeref *)
  | Dref(e) ->
      (match typeinfer tenv e with
         TyRef(t) -> t
       | _ -> raise (TypeError "Erro: tipo referencia era esperado."))

  (* Regra TWhile *)
  | Whl(e1,e2) ->
      (match typeinfer tenv e1 with
         TyBool -> if (typeinfer tenv e2) = TyUnit then TyUnit
           else raise (TypeError "Erro: tipo unit era esperado como segundo argumento.")
       | _ -> raise (TypeError "Erro: tipo bool era esperado como primeiro argumento."))

  (* Regra TNew *)
  | New(e) ->
      (match typeinfer tenv e with
         t -> TyRef(t)) 

  (* Regra TSeq *)
  | Seq(e1,e2) ->
      (match typeinfer tenv e1 with
         TyUnit -> (typeinfer tenv e2)
       | _ -> raise (TypeError "Erro: tipo unit era esperado como primeiro argumento."))

(**+++++++++++++++++++++++++++++++++++++++++*)
(*   FUNÇÕES PARA MANIPULAÇÃO DE MEMÓRIA    *)
(*++++++++++++++++++++++++++++++++++++++++++*)
       
exception MemoryError of string

(* Função para inserir um novo valor em uma nova posição de memória *)
let insere_mem (mem:mem) (v: valor) : mem =
  (List.length mem, v) :: mem
  

(* Função para encontrar um valor em uma posição de memória específica *)
let rec lookup_mem (mem:mem) (address: address) : valor =
  (match mem with
     [] -> raise (MemoryError ("Erro: posição de memória inválida."))
   | _ -> if (fst(List.hd mem)) = address then (snd(List.hd mem)) else lookup_mem (List.tl mem) address)


(* Função para substituir um valor em uma determinada posição de memória já ocupada *)
let rec mem_set (mem:mem) (key:address) value =
  match mem with
    [] -> raise (MemoryError "Erro: atribuição em posição de memória não existente.")
  | (pos, old_val) :: rest -> if (pos = key) then (pos, value) :: rest else (pos, old_val) :: mem_set rest key value

(* Função para retornar o próximo endereço da memória que deve ser ocupado *)                                                                              
let nova_posicao (mem:mem) : address = List.length mem

(**+++++++++++++++++++++++++++++++++++++++++*)
(*                 AVALIADOR                *)
(*++++++++++++++++++++++++++++++++++++++++++*)

let compute (oper: op) (v1: valorMem) (v2 : valorMem) (mem: mem) : valorMem =
  match (oper, fst v1, fst v2) with
    (Sum, VNum(n1), VNum(n2)) -> (VNum (n1 + n2), mem)
  | (Sub, VNum(n1), VNum(n2)) -> (VNum (n1 - n2), mem)
  | (Mult, VNum(n1),VNum(n2)) -> (VNum (n1 * n2), mem)
  | (Eq, VNum(n1), VNum(n2))  -> if (n1 = n2)  then (VTrue,mem) else (VFalse,mem)
  | (Gt, VNum(n1), VNum(n2))  -> if (n1 > n2)  then (VTrue,mem) else (VFalse,mem)
  | (Lt, VNum(n1), VNum(n2))  -> if (n1 < n2)  then (VTrue,mem) else (VFalse,mem)
  | (Geq, VNum(n1), VNum(n2)) -> if (n1 >= n2) then (VTrue,mem) else (VFalse,mem)
  | (Leq, VNum(n1), VNum(n2)) -> if (n1 <= n2) then (VTrue,mem) else (VFalse,mem)
  | _ -> raise BugTypeInfer


let rec eval (renv:renv) (e:expr) (mem:mem) : valorMem =
  match e with
    Num n -> (VNum n,mem)
  | True -> (VTrue,mem)
  | False -> (VFalse,mem)
  | Skip -> (VSkip,mem) (* Adição da avaliação para o valor Skip *)

  | Var x ->
      (match lookup renv x with
         Some v -> (v,mem)
       | None -> raise BugTypeInfer)

  | Binop(oper,e1,e2) ->
      let v1 = eval renv e1 mem in
      let v2 = eval renv e2 (snd v1) in
      compute oper v1 v2 mem

  | Pair(e1,e2) ->
      let v1 = eval renv e1 mem in
      let v2 = eval renv e2 (snd v1) in
      VPair(fst v1,fst v2), snd v2

  | Fst e ->
      (match fst (eval renv e mem) with
       | VPair(v1,_) -> (v1, mem)
       | _ -> raise BugTypeInfer)

  | Snd e ->
      (match fst (eval renv e mem) with
       | VPair(_,v2) -> (v2,mem)
       | _ -> raise BugTypeInfer)

  | If(e1,e2,e3) ->
      let v1 = eval renv e1 mem in
      (match fst(v1) with
         VTrue  -> eval renv e2 (snd v1)
       | VFalse -> eval renv e3 (snd v1)
       | _ -> raise BugTypeInfer)

  | Fn (x,_,e1) ->  VClos(x,e1,renv), mem

  | App(e1,e2) ->
      let v1 = eval renv e1 mem in
      let mem' = snd v1 in
      let v2 = eval renv e2 (mem') in
      (match fst v1 with
         VClos(x,ebdy,renv') ->
           let renv'' = update renv' x (fst v2)
           in eval renv'' ebdy mem'

       | VRclos(f,x,ebdy,renv') ->
           let renv''  = update renv' x (fst v2) in
           let renv''' = update renv'' f (fst v1)
           in eval renv''' ebdy mem'
       | _ -> raise BugTypeInfer)

  | Let(x,_,e1,e2) ->
      let v1 = eval renv e1 mem
      in eval (update renv x (fst v1)) e2 (snd v1)

  | LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let renv'= update renv f (VRclos(f,x,e1,renv))
      in eval renv' e2 mem

  | LetRec _ -> raise BugParser

  (* Novas regras da semântica operacional big step são adicionadas a partir desse ponto *)

  (* Regra Deref *)
  | Dref(e) ->
      let v = eval renv e mem in
      (match fst v with
         VNum(n) -> (lookup_mem mem n, mem)
       | _ -> raise (TypeError "Erro: as posicoes de memoria devem ser endereçadas por números inteiros."))

  (* Regra Seq *)
  | Seq(e1,e2) ->
      let v1 = eval renv e1 mem in
      (match fst v1 with
         VSkip -> eval renv e2 (snd v1)
       | _ -> raise (TypeError "Erro: operação intermediária não possui o tipo unit."))

  (* Regra New *)
  | New(e) ->
      let v = eval renv e mem in
      let mem' = snd v in
      (VNum(nova_posicao mem')), (insere_mem mem' (fst v))

  (* Regra Atr *)                               
  | Asg(evar, evalue) ->
      let addressVal, mem' = eval renv evar mem in
      let value, mem'' = eval renv evalue mem' in
      (match addressVal with
         VNum(address) -> VSkip, (mem_set mem'' address value)
       | _ -> raise (TypeError "Erro: tentativa de atribuição em endereço não-inteiro da memória."))

  (* Regra E-While *)    
  | Whl(econd, eloop) ->
      eval renv (If(econd, Seq(eloop, Whl(econd, eloop)), Skip)) mem

(* Função auxiliar para conversão de tipos em strings *)

let rec ttos (t:tipo) : string =
  match t with
    TyInt  -> "int"
  | TyBool -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
  | TyPair(t1,t2) ->  "("  ^ (ttos t1) ^ " * "   ^ (ttos t2) ^ ")"
  | TyRef(n) -> "&" ^ (ttos n)
  | TyUnit -> "void"

(* Função auxiliar para conversão de valores em strings *)

let rec vtos (v: valor) : string =
  match v with
    VNum n -> string_of_int n
  | VTrue -> "true"
  | VFalse -> "false"
  | VPair(v1, v2) ->
      "(" ^ vtos v1 ^ "," ^ vtos v1 ^ ")"
  | VClos _ ->  "fn"
  | VRclos _ -> "fn"
  | VRef -> "&"
  | VSkip -> "null"

(* Função principal do interpretador *)

let int_bse (e:expr) (mem:mem) : unit =
  try
    let t = typeinfer [] e in
    let v = eval [] e mem
    in  print_string ((vtos (fst v)) ^ " : " ^ (ttos t))
  with
    TypeError msg ->  print_string ("erro de tipo - " ^ msg)

 (* As exceções abaixo não podem ocorrer *)
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"
  | BugParser     ->  print_string "corrigir bug no parser para let rec"
  
(**+++++++++++++++++++++++++++++++++++++++++*)
(*            CASOS DE TESTE                *)
(*++++++++++++++++++++++++++++++++++++++++++*) 

  (* Casos de teste para TypeInfer *)

let teste1 = New(Num 3301)
let teste2 = New(True)
let teste3 = Whl(True,Skip)
let teste4 = Dref(teste1)
let teste5 = Dref(teste2)
let teste6 = Seq(Skip,Num 3301)
let teste7 = Seq(Skip,True)
let teste8 = Asg(teste1,Num 42)
let teste9 = Asg(teste2,True)
  
(* typeinfer [] Skip;; *)
(* typeinfer [] teste1;; *)
(* typeinfer [] teste2;; *)
(* typeinfer [] teste3;; *)
(* typeinfer [] teste4;; *)
(* typeinfer [] teste5;; *)
(* typeinfer [] teste6;; *)
(* typeinfer [] teste7;; *)
(* typeinfer [] teste8;; *)
(* typeinfer [] teste9;; *)

   (* Casos de teste para semântica operacional big step *)

(*
Valor esperado: 16
let a = new 5 in
let b = !a + 1 in
a := 10;
!a + b
     *)
let testeSomaRefDeref =
  Let("a", TyRef TyInt, New(Num 5),
      Let("b", TyInt, Binop(Sum, Dref(Var "a"), Num 1),
          Seq(
            Asg(Var "a", Num 10),
            Binop(Sum, Dref(Var "a"), Var "b")
          )))

(*
  let x = new input in
  let y = new 1 in
  let z = new 1 in
  while (!z <= !x) {
    y := !y * !z;
    z = !z + 1
  };
  !y
  *)
  
let testFatorial input =
  Let("x", TyRef TyInt, New(Num input),
      Let("y", TyRef TyInt, New(Num 1),
          Let("z", TyRef TyInt, New(Num 1),
              Seq(Whl(Binop(Leq, Dref(Var "z"), Dref(Var "x")),
                      Seq(Asg(Var "y", Binop(Mult, Dref(Var "y"), Dref(Var "z"))),
                          Asg(Var "z", Binop(Sum, Dref(Var "z"), Num 1)))),
                  Dref(Var "y")))))

(*Valor esperado: 6*)
let testFat3 = testFatorial 3
(*Valor esperado: 120*)
let testFat4 = testFatorial 5 
