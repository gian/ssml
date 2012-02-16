structure HM =
struct
    structure A = Ast

    val tyvarCounter = ref 0
    fun freshTy () = 
        A.TyVar (!tyvarCounter) before tyvarCounter := (!tyvarCounter) + 1

    val constraints : (Ast.ty * Ast.ty) list ref = ref []

    fun addConstr (t,t') = constraints := (t,t') :: (!constraints) 

    structure UF = IUnionFind

    val tysets : (A.id * (A.ty UF.set)) list ref = ref []

    fun getSet i = (case List.find (fn (i', _) => i = i') (!tysets) of
			SOME (_, s) => s
		      | NONE => let val ns = UF.new (A.TyVar i)
				in ns before tysets := (i, ns) :: (!tysets)
				end)
    fun lookup xs k = (case List.find (fn (j, _) => j = k) xs of
			   SOME (_, v) => v
			 | NONE => raise Fail ("Unbound variable " ^ A.ppty (A.TyVar k)))

    fun force (A.TyVar x) = UF.find (getSet x)
      | force t = t

    fun forceAll t =
	let fun aux (A.TyCon (t1, t2)) = A.TyCon (forceAll t1, forceAll t2)
	      | aux (A.TyArrow (t1, t2)) = A.TyArrow (forceAll t1, forceAll t2)
	      | aux t = t
	in aux (force t)
	end

    fun occursUF i t =
	(case t of
	     A.TyArrow (t1, t2) => occursUF i (force t1) orelse occursUF i (force t2)
	   | A.TyCon   (t1, t2) => occursUF i (force t1) orelse occursUF i (force t2)
	   | A.TyVar j => i = j
	   | _ => false)

    fun pickCanon (A.TyVar _, t) = t
      | pickCanon (t, A.TyVar _) = t
      | pickCanon (t1, t2) =
	if t1 = t2 then t1
	else raise Fail ("Non-substitution union called on " ^ A.ppty t1 ^ " and " ^ A.ppty t2)

    fun solve (A.TyVar x, A.TyVar y) =
	UF.union pickCanon (getSet x) (getSet y)
      | solve (A.TyVar x, tr) =
	if occursUF x tr then
	    raise Fail ("Circular type constraints: " ^ A.ppty (A.TyVar x) ^ " in " ^ A.ppty tr)
	else UF.union pickCanon (getSet x) (UF.new tr)
      | solve (tl, tr as A.TyVar x) = solve (tr, tl)
      | solve (t1 as A.TyId a, t2 as A.TyId b) =
        if a = b then () else raise Fail ("Type error: " ^ A.ppty t1 ^ " =/= " ^ A.ppty t2)
      | solve (A.TyPoly a, A.TyPoly b) =
        if a = b then () else raise Fail ("Polymorphic unification")
      | solve (A.TyCon (t1, c1), A.TyCon (t2, c2)) =
	(solve (force t1, force t2); solve (force c1, force c2))
      | solve (A.TyArrow (t1, t2), A.TyArrow (t3, t4)) =
        (solve (force t1, force t3); solve (force t2, force t4))
      | solve (t1, t2) = raise Fail ("Type error: " ^ A.ppty t1 ^ " =/= " ^ A.ppty t2)

    fun solveList xs = List.foldl (fn (c, ()) => solve c) () xs

    fun mkPoly k (t as A.TyVar x) = if k > x then t else A.TyPoly x
      | mkPoly k (A.TyCon (t1, t2)) = A.TyCon (mkPoly k (force t1), mkPoly k (force t2))
      | mkPoly k (A.TyArrow (t1, t2)) = A.TyArrow (mkPoly k (force t1), mkPoly k (force t2))
      | mkPoly k t = t
	
	(*let fun aux P (t as A.TyVar x) =
		if k > x then (P, t)
		else ((P, lookup P x)
		      handle _ => let val tv = freshTy ()
				  in ((x, tv) :: P, tv)
				  end)
	      | aux P (t as A.TyId x) = (P, t)
	      | aux P (A.TyPoly (x, t)) =
		raise Fail ("Impossible: non-instantiated polymorphic type")
	      | aux P (A.TyCon (t1, t2)) =
		let val (P', t1') = aux P (force t1)
		    val (P'', t2') = aux P' (force t2)
		in (P'', A.TyCon (t1', t2'))
		end
	      | aux P (A.TySig _) = raise Fail ("Type error: signature as a return type")
	      | aux P (A.TyArrow (t1, t2)) =
		let val (P', t1') = aux P (force t1)
		    val (P'', t2') = aux P' (force t2)
		in (P'', A.TyArrow (t1', t2'))
		end
	    val (P, t') = aux [] t
	in List.foldl (fn ((_, A.TyVar x), t) => A.TyPoly (x, t)) t' P
	end*)

    fun instantiate P (A.TyPoly x) =
	((P, lookup P x) handle _ => let val t = freshTy () in ((x, t) :: P, t) end)
      | instantiate P (A.TyCon (t1, t2)) =
	let val (P1, t1') = instantiate P  (force t1)
	    val (P2, t2') = instantiate P1 (force t2)
	in (P2, A.TyCon (t1', t2'))
	end
      | instantiate P (A.TyArrow (t1, t2)) =
	let val (P1, t1') = instantiate P  (force t1)
	    val (P2, t2') = instantiate P1 (force t2)
	in (P2, A.TyArrow (t1', t2'))
	end
      | instantiate P t = (P, t)

    fun tyinfExp G (A.Fn (i, e, NONE)) =
	let val t = freshTy ()
	    val (t', e') = tyinfExp ((i, t) :: G) e
	    val tx = A.TyArrow (t, t')
	in (tx, A.Fn (i, e', SOME tx))
	end
      | tyinfExp G (A.App (e1, e2, NONE)) =
	let val (t1, e1') = tyinfExp G e1
	    val (t2, e2') = tyinfExp G e2
	    val tr = freshTy ()
	    val _  = (print ("Solving " ^ A.ppty (force t1) ^ " = " ^ A.ppty (A.TyArrow (t2, tr)) ^ "\n");
		      solve (force t1, A.TyArrow (t2, tr)))
	in (tr, A.App (e1', e2', SOME (forceAll tr)))
	end
      | tyinfExp G (A.Var (x, NONE)) =
	let val (_, t) = instantiate [] (lookup G x)
	in (t, A.Var (x, SOME t))
	end
      | tyinfExp G (A.Let (ds, e, NONE)) =
	let val (G', ds') = tyinfDecList G ds
	    val (t, e') = tyinfExp G' e
	in (t, A.Let (ds', e', SOME t))
	end
      | tyinfExp G (A.Ann (e, t)) =
	let val (t', e') = tyinfExp G e
	    val _ = solve (t', t)
	in (t, e')
	end
      | tyinfExp G e =
        raise (Fail ("Unhandled expression in tyinfExp: " ^ A.ppexp e))

    and tyinfDec G (A.ValBind (i, NONE, e)) =
	let val k = !tyvarCounter
	    val (t, e') = tyinfExp G e
	    val t' = mkPoly k (force t)
	in ((i, t') :: G, A.ValBind (i, SOME t', e'))
	end
      | tyinfDec G (A.ValRecBind (i, NONE, e)) =
	let val k = !tyvarCounter
	    val t = freshTy ()
	    val (t', e') = tyinfExp ((i, t) :: G) e
	    val _ = solve (t, t')
	    val t'' = mkPoly k (force t')
	in ((i, t'') :: G, A.ValRecBind (i, SOME t'', e'))
	end
      | tyinfDec G d =
	raise Fail ("Unhandled declaration in tyinfDec: " ^ A.ppdec d)

    and tyinfDecList G ds =
	List.foldl (fn (d, (G, ds)) =>
		       let val (G', d') = tyinfDec G d
		       in (G', d'::ds) end) (G, []) ds

(*    fun constrExp (A.Fn (i,e,NONE)) =
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
            raise Fail ("Type error: " ^ A.ppty t1 ^ " =/= " ^ A.ppty t2)*)

    fun printConstr' l = 
            String.concatWith "\n" 
                (map (fn (t1,t2) => A.ppty t1 ^ " = " ^ A.ppty t2) l)

    fun printConstr () = printConstr' (!constraints)

    fun reset () = constraints := []
 end

