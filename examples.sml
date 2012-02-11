structure Examples =
struct
    val a = 0
    val x = 1


    val example1
        = Ast.ValRecBind (a, NONE, 
            Ast.Fn (x, Ast.Var (x, NONE), NONE))

    fun run' e =
        let
            val s = HM.reset ()
            val e' = HM.constrDec e
        in
            (print "===========================================\n";
             print ("Pre-constr: " ^ (Ast.ppdec e) ^ "\n");
             HM.constrDec e;
             print ((HM.printConstr ()) ^ "\n");
             print ("Post-constr: " ^ (Ast.ppdec e') ^ "\n");
             print "===========================================\n";
             ())
         end

    fun run () = 
        (run' example1;
         ())
end


