structure Env :> ENV = 
struct

structure Sy = Symbol
structure Ty = Types

type access = unit ref
type ty = Ty.ty

datatype enventry = VarEntry of {ty: ty}
                  | FunEntry of {formals: ty list, result: ty}

fun enter ((symbol, entry), env) = Sy.enter (env, symbol, entry)

val baseTenv =
    foldl enter Sy.empty 
          [ (Sy.symbol "int", Ty.INT)
          , (Sy.symbol "string", Ty.STRING)]

val baseVenv = foldl enter Sy.empty [

  (Sy.symbol "print",       FunEntry { formals = [Ty.STRING]
                                     , result = Ty.UNIT}),

  (Sy.symbol "flush",       FunEntry { formals = []
                                     , result = Ty.UNIT})

  (* TODO: remaining entries *)
]

end (* Env *)

