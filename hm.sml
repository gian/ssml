structure HM =
struct
    structure A = Ast

(*
    datatype ty =
        TyId of id
      | TyVar of id
      | TyPoly of id
      | TyCon of ty * ty
      | TySig of ty list * dec list
    and exp =
        Fn of id * exp * ty option
      | Var of id * ty option
      | App of exp * exp * ty option
      | Ann of exp * ty
      | Let of dec list * exp * ty option
      | Literal of ty
    and dec =
        ValBind of id * ty option * exp
      | ValRecBind of id * ty option * exp
      | TyDef of id * ty
      | TyDec of id
      | ValDec of id * ty
      | Struct of dec list * ty option
      | StructDec of id * dec * ty option
      | SigDec of id * ty *)

    val tyvarCounter = ref 0
    fun freshTy () = 
        A.TyVar (!tyvarCounter) before tyvarCounter := (!tyvarCounter) + 1

    val constraints : (Ast.ty * Ast.ty) list ref = ref []

    fun addConstr (t,t') = constraints := (t,t') :: (!constraints)

    fun constrExp (A.Fn (i,e,NONE)) =
    let
        val t = freshTy ()
        val t' = freshTy ()
        val (t'',e') = constrExp e
        val _ = addConstr (t',t'')
        val tx = freshTy ()
        val _ = addConstr (tx,A.TyArrow (t,t'))
    in
        (tx, A.Fn (i, e', SOME tx))
    end
      | constrExp (A.Var (i,NONE)) =
    let
        val t = Symtab.lookup i handle _ => 
            let
                val t' = freshTy ()
                val _ = Symtab.insert i t'
            in
                t'
            end
    in
        (t, A.Var (i, SOME t))
    end
      | constrExp (A.App (e1,e2,NONE)) =
    let
        val (t1,e1') = constrExp e1
        val (t2,e2') = constrExp e2
        val tx = freshTy ()
        val tx' = freshTy ()
        val _ = addConstr (tx,t2)
        val _ = addConstr (A.TyArrow (tx,tx'), t1)
    in
        (tx', A.App (e1,e2,SOME tx'))
    end
      | constrExp (A.Ann (e,t)) =
    let
        val (t',e') = constrExp e
        val _ = addConstr (t',t)
    in
        (t,e')
    end
      | constrExp (A.Let (l,e,NONE)) =
    let
        val l' = constrDec l
    in
        constrExp e
    end
      | constrExp (A.Literal t) = (t, A.Literal t)
      | constrExp e = 
        raise (Fail ("Unhandled expression in constrExp: " ^ A.ppexp e))

    and constrDec _ = raise (Fail "Not implemented")

    fun printConstr' l = 
            String.concatWith "\n" 
                (map (fn (t1,t2) => A.ppty t1 ^ " = " ^ A.ppty t2) l)

    fun printConstr () = printConstr' (!constraints)
 end

