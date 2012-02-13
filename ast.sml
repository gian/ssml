structure Ast =
struct
    type id = int

    datatype ty =
        TyId of id
      | TyVar of id
      | TyPoly of id
      | TyCon of ty * ty
      | TySig of ty list * dec list
      | TyArrow of ty * ty
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
      | SigDec of id * ty
    
    val ppid = Int.toString


    fun substinty (TyId n) th (TyId t) =
            if n = t then th else TyId t
      | substinty (TyVar n) th (TyVar t) =
            if n = t then th else TyVar t
      | substinty tn th (TyCon (t1,t2)) = 
            TyCon (substinty tn th t1, substinty tn th t2)
      | substinty tn th (TyArrow (t1,t2)) =
            TyArrow (substinty tn th t1, substinty tn th t2)
      | substinty tn th t = t

    fun occursin (tx as TyVar t1) t2 =
           (case t2 of 
                TyArrow (t1',t2') => occursin tx t1' orelse occursin tx t2'
              | TyCon (t1',t2') => occursin tx t1' orelse occursin tx t2'
              | TyVar t2' => t1 = t2'
              | _ => false)
      | occursin _ _ = raise Fail ("Invalid argument to occursin")

    fun ppty (TyId i) = "t" ^ ppid i
      | ppty (TyVar i) = "?X" ^ ppid i
      | ppty (TyPoly i) = String.str (Char.chr ((Char.ord #"a") + i))
      | ppty (TyCon (a,b)) = ppty a ^ " " ^ ppty b
      | ppty (TySig ([],l)) = 
            "sig\n   " ^ String.concatWith "\n   " (map ppdec l) ^ "\nend\n"
      | ppty (TySig (p,l)) =
            "(" ^ String.concatWith " * " (map ppty p) ^ ") -> " ^ 
            "sig\n   " ^ String.concatWith "\n   " (map ppdec l) ^ "\nend\n"
      | ppty (TyArrow (t1,t2)) = ppty t1 ^ " -> " ^ ppty t2
    and ppann NONE = ""
      | ppann (SOME t) = " : " ^ ppty t
    and ppexp (Fn (i,e,t)) = "(fn v" ^ ppid i ^ " => " ^ ppexp e ^ ")" ^ ppann t
      | ppexp (Var (i,t)) = "v" ^ ppid i ^ ppann t
      | ppexp (App (e1,e2,t)) = ppexp e1 ^ " " ^ ppexp e2 ^ ppann t
      | ppexp (Ann (e,t)) = "(" ^ ppexp e ^ " : " ^ ppty t ^ ")"
      | ppexp (Let (l,e,t)) = 
        "let\n   " ^
            String.concatWith "\n   " (map ppdec l) ^
        "\nin\n   " ^ ppexp e ^ "\nend"
      | ppexp (Literal t) = "#" ^ ppty t
    and ppdec (ValBind (i,t,e)) = "val v" ^ ppid i ^ ppann t ^ " = " ^ ppexp e
      | ppdec (ValRecBind (i,t,e)) = 
            "val rec v" ^ ppid i ^ ppann t ^ " = " ^ ppexp e
      | ppdec (TyDef (i,t)) = "type t" ^ ppid i ^ " = " ^ ppty t
      | ppdec (TyDec i) = "type t" ^ ppid i
      | ppdec (ValDec (i,t)) = "val v" ^ ppid i ^ " : " ^ ppty t
      | ppdec (Struct (l,t)) = 
            "struct\n   " ^ 
                String.concatWith "\n   " (map ppdec l) ^
            "\nend"
      | ppdec (StructDec (i,d,t)) =
        "structure s" ^ ppid i ^ ppann t ^ " = " ^ ppdec d
      | ppdec (SigDec (i,t)) =
        "signature S" ^ ppid i ^ " = " ^ ppty t

end

