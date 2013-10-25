signature SEMANT =
sig
  val transProg: Absyn.exp -> Types.ty
end

structure Semant :> SEMANT =
struct

structure S = Symbol
structure A = Absyn
structure E = Env
structure Ty = Types
structure PT = PrintTypes

val err = ErrorMsg.error

fun lookupTy tenv sym pos =
    let
        val tyOpt = S.look (tenv, sym)
    in
        Ty.ERROR (* TODO *)
    end

(* NB: Some function names adjusted to use CamelCase more consistently.
 * For example: 'actual_ty' was renamed to 'actualTy' *)

fun actualTy (Ty.NAME (s, ty)) pos =
    Ty.ERROR (* TODO *)
  | actualTy t _ = t

fun checkInt ({exp, ty}, pos) =
    case ty of
        Ty.INT => ()
      | Ty.ERROR => ()
      | _ => err pos ("INT required" ^ ", " ^
                      PT.asString ty ^ " provided")

fun checkString ({exp, ty}, pos) = 
    case ty of Ty.STRING => ()
                  | Ty.ERROR =>() 
                  | _ => err pos ("String required" ^ ", " ^
                                 PT.asString ty^ "provided")

fun checkUnit (ty, pos, msg) = err pos "TODO"

fun checkAssignable (declared: Ty.ty, assigned: Ty.ty, pos, msg) =
    let
        val aDeclared = actualTy declared pos
        val aAssigned = actualTy assigned pos
    in
        () (* TODO *)
    end

fun transTy (tenv, t) = Ty.ERROR (* TODO *)

fun transExp (venv, tenv) =
    let
        val TODO = {exp = (), ty = Ty.ERROR}

        fun trexp (A.NilExp) = {exp = (), ty = Ty.NIL}
          | trexp (A.VarExp var) = trvar var
          | trexp (A.IntExp i) = {exp = (), ty = Ty.INT}
          | trexp (A.StringExp (str, pos)) = {exp = (), ty = Ty.STRING}
          | trexp (A.OpExp {left, oper, right, pos}) = 
 if oper = A.PlusOp 
               orelse oper = A.MinusOp
               orelse oper = A.TimesOp
               orelse oper = A.DivideOp
            then
                let
                    val left' = trexp left
                    val right' = trexp right
                in
                    (checkInt (left', pos); 
                     checkInt(right', pos);
                     {exp = (), ty=Ty.INT})
                end
            else if oper = A.EqOp
                    orelse oper = A.NeqOp
                    orelse oper = A.LtOp
                    orelse oper = A.LeOp
                    orelse oper = A.GtOp
                    orelse oper = A.GeOp
            then
                let 
                    val left' = trexp left
                    val right' = trexp right
                in
                    (*Her er der redundans*)
                    case #ty left' of Ty.INT => (checkInt (left', pos);
                                                 checkInt (right', pos);
                                                 {exp = (), ty = Ty.INT})
                                    | Ty.STRING => (checkString (left', pos);
                                                    checkString(right', pos);
                                                    {exp = (), ty = Ty.STRING})
                                    | _ => {exp = (), ty = Ty.ERROR}  
                end
            else {exp = (), ty = Ty.ERROR}
          | trexp (A.CallExp {func, args, pos}) = TODO
          | trexp (A.IfExp {test, thn, els, pos}) =
	    (case els of NONE=> 
                         let
                             val test' = trexp test
                             val thn' = trexp thn
                         in
                             (checkInt(test', pos);
                              {exp = (), ty = #ty thn'})
                         end
		       | SOME els=> 
			 let
			     val test' = trexp test
			     val thn' = trexp thn
			     val els' = trexp els
			 in
			     (checkInt(test', pos);
			      if (# ty thn' = #ty els')
			      then {exp = (), ty = #ty thn'}
			      else {exp = (), ty = Ty.ERROR})
			 end)
          | trexp (A.WhileExp {test, body, pos}) = TODO
          | trexp (A.RecordExp {fields, typ, pos}) = TODO
(*Jeg tænkte at hvis den er tom er det vel en unit?? Eller skal det være NIL?*)
          | trexp (A.SeqExp []) = {exp = (), ty = Ty.UNIT}
(*Se godt på mærkerne, tækte om det skal være noget andet end '' i val*)
          | trexp (A.SeqExp (aexps as (aexp'::aexps'))) = 
	   let
(*Fordi aexp' er en exp og en pos er bliver man nødt til at dele den op fordi vi kun vil tilgå expressionen. Ved ikke om det giver mening for jer? *)
	       val (e, p) = aexp'
		val aexp'' = trexp e
	    in
		if aexps' = []
		then {exp = (), ty = #ty aexp''}
		else trexp (A.SeqExp aexps')
	    end
          | trexp (A.AssignExp {var, exp, pos}) = TODO
          | trexp (A.ForExp {var, escape, lo, hi, body, pos}) = TODO
          | trexp (A.BreakExp pos) = TODO
          | trexp (A.LetExp {decls, body, pos}) =
	    let
                val {venv=venv', tenv=tenv'} = transDecs (venv, tenv, decls)
            in
                transExp (venv', tenv') body
            end
          | trexp (A.ArrayExp {typ, size, init, pos}) = TODO

        and trvar (A.SimpleVar (id, pos)) = TODO
          | trvar (A.FieldVar (var, id, pos)) = TODO
          | trvar (A.SubscriptVar (var, exp, pos)) = TODO
    in
        trexp
    end

and transDec ( venv, tenv
             , A.VarDec {name, escape, typ = NONE, init, pos}) =
    {tenv = tenv, venv = venv} (* TODO *)

  | transDec ( venv, tenv
             , A.VarDec {name, escape, typ = SOME (s, pos), init, pos=pos1}) =
    {tenv = tenv, venv = venv} (* TODO *)

  | transDec (venv, tenv, A.TypeDec tydecls) =
    {tenv = tenv, venv = venv} (* TODO *)

  | transDec (venv, tenv, A.FunctionDec fundecls) =
    {tenv = tenv, venv = venv} (* TODO *)

and transDecs (venv, tenv, decls) =
    case decls 
     of [] => {venv = venv, tenv = tenv}
      | (d::ds) =>
        let
            val {venv = venv', tenv = tenv'} = transDec (venv, tenv, d)
        in
            transDecs (venv', tenv', ds)
        end

fun transProg absyn =
    let
        val {exp=_,ty} = transExp (Env.baseVenv, Env.baseTenv) absyn
    in
        ty
    end

end (* Semant *)

