structure Symtab =
struct
    val tab : (Ast.id * Ast.ty) list ref = ref []

    exception UnknownSymbol

    fun insert i t = tab := (i,t) :: (!tab)
    
    fun lookup i = 
        (case List.find (fn (i',_) => i = i') (!tab) of
            NONE => raise UnknownSymbol
          | SOME (_,t) => t)
end
