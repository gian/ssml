structure HM =
struct
    structure A = Ast

    val tyvarCounter = ref 0
    fun freshTy () = 
        A.TyVar (!tyvarCounter) before tyvarCounter := (!tyvarCounter) + 1

    val constraints : (Ast.ty * Ast.ty) list ref = ref []

    fun addConstr (t,t') = constraints := (t,t') :: (!constraints) 

    fun constrExp (A.Fn (i,e,NONE)) =
    let
        val t = freshTy ()
        val _ = Symtab.insert i t
        val (t',e') = constrExp e
        val tx = A.TyArrow (t,t') 
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
        val tx' = freshTy ()
        val _ = addConstr (t1, A.TyArrow (t2,tx'))
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
        val l' = List.map constrDec l
    in
        constrExp e
    end
      | constrExp (A.Literal t) = (t, A.Literal t)
      | constrExp e = 
        raise (Fail ("Unhandled expression in constrExp: " ^ A.ppexp e))

    and constrDec (A.ValBind (i,NONE,e)) =
    let
        val (t,e') = constrExp e
        val _ = Symtab.insert i t
    in
        A.ValBind (i, SOME t, e')
    end
      | constrDec (A.ValRecBind (i,NONE,e)) =
    let
        val t = freshTy ()
        val _ = Symtab.insert i t
        val (t',e') = constrExp e
        val _ = addConstr (t,t')
    in
        A.ValRecBind (i, SOME t, e')
    end
      | constrDec _ = raise (Fail "Not implemented")


    fun substinconstr tn th l =
        map (fn (x,y) => (A.substinty tn th x, A.substinty tn th y)) l

    fun unify [] = []
      | unify ((A.TyVar x, t2) :: rest) =
            if t2 = A.TyVar x then unify rest
            else if A.occursin (A.TyVar x) t2 then
                raise Fail "Circular type constraints"
            else (unify (substinconstr (A.TyVar x) t2 rest)) @ [(A.TyVar x, t2)]
      | unify ((t1, A.TyVar x) :: rest) =
            if t1 = A.TyVar x then unify rest
            else if A.occursin (A.TyVar x) t1 then
                raise Fail "Circular type constraints"
            else (unify (substinconstr (A.TyVar x) t1 rest)) @ [(A.TyVar x, t1)]
      | unify ((t1 as A.TyId a, t2 as A.TyId b) :: rest) =
            if a = b then unify rest
            else raise Fail ("Type error: " ^ A.ppty t1 ^ " =/= " ^ A.ppty t2)
      | unify ((A.TyPoly a, A.TyPoly b) :: rest) =
            if a = b then unify rest
            else raise Fail ("Polymorphic unification")
      | unify ((A.TyCon (t1,c1), A.TyCon (t2,c2)) :: rest) =
            unify ((t1,t2) :: (c1,c2) :: rest)
      | unify ((A.TyArrow (t1,t2), A.TyArrow (t3,t4)) :: rest) =
            unify ((t1,t3) :: (t2,t4) :: rest)
      | unify ((t1,t2) :: rest) =
            raise Fail ("Type error: " ^ A.ppty t1 ^ " =/= " ^ A.ppty t2)

    fun printConstr' l = 
            String.concatWith "\n" 
                (map (fn (t1,t2) => A.ppty t1 ^ " = " ^ A.ppty t2) l)

    fun printConstr () = printConstr' (!constraints)

    fun reset () = constraints := []
 end

