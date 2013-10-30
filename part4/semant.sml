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

(* Nesting of while- and for- loops, so we know if a break is allowed. *)
val nesting = ref 0
fun incNesting() = nesting := !nesting + 1
fun decNesting() = nesting := !nesting - 1
					     
(*Search the look table for the sym parameter*)
fun lookupTy tenv sym pos =
    let
        val tyOpt = S.look (tenv, sym)
    in
        case tyOpt of
	     SOME someType => someType
	   (* returns a type error so we can move on *)
	   | NONE => (err pos ("type is not defined in the enviroment: " ^ S.name sym) ; Ty.ERROR)
    end
	
(* NB: Some function names adjusted to use CamelCase more consistently.
 * For example: 'actual_ty' was renamed to 'actualTy' *)
	
fun actualTy (Ty.NAME (s, ty)) pos =
    (case !ty of
	NONE => (err pos "The type is undeclared" ; Ty.ERROR)
(* why should this be pos????? *)
      | SOME t => actualTy t pos)
  | actualTy t _ = t
		       
fun checkInt ({exp, ty}, pos) =
    case ty of
        Ty.INT => ()
      | Ty.ERROR => ()
      | _ => err pos ("INT required" ^ ", " ^
                      PT.asString ty ^ " provided")

fun checkString ({exp, ty}, pos) = 
    case ty of 
	Ty.STRING => ()
      | Ty.ERROR =>() 
      | _ => err pos ("String required" ^ ", " ^
                                 PT.asString ty^ "provided")

fun checkUnit ({exp, ty}, pos) = 
    case ty of 
	Ty.UNIT => ()
      | Ty.ERROR => ()
      | _  => err pos ("Unit required, " ^ PT.asString ty ^ " provided")  

		  
fun checkAssignable (declared: Ty.ty, assigned: Ty.ty, pos, msg) =
    let
	(* get the type of aDec and aAss so we can use this in 'in' *)
        val aDeclared = actualTy declared pos
        val aAssigned = actualTy assigned pos
    in
	(*INSANE! Make sure the unique is the same ref in records and arrays*)
        case aDeclared of
	    Ty.RECORD (_, u1) =>
	    (case aAssigned of
		 Ty.NIL => true
	       | Ty.RECORD (_, u2) =>
		 if (u1=u2)
		 then true
		 else (err pos ("Mismatch of the record unique ref in: " ^ msg) ; false)
	       | _ => (err pos ("Mismatch of the types in: " ^ msg) ; false))
	  | Ty.ARRAY(_, u1) =>
	    (case aAssigned of
		 Ty.ARRAY(_, u2) => 
		 if (u1=u2)
		 then true
		 else (err pos ("Mismatch of the array unique ref in: " ^ msg) ; false)
	       | _ => (err pos ("Mismatch of the types in: " ^ msg) ; false)) 
	  | x => 
	    (*Check all other cases*)
	    if (x= aAssigned) 
	    then true 
	    else (err pos ("Mismatch of the types in: " ^ msg) ; false)
    end
	
fun transTy (tenv, t) =
    let 
	(*Translate Absyn recorddata to Type recorddata*)
	fun transRecordData [] = []
	  | transRecordData ({name, escape, typ, pos} :: fieldList) = 
	  (name, lookupTy tenv name pos):: transRecordData fieldList
    in
	case t of
	    (*ref (), is a unique ref*)
	    A.RecordTy(fielddata) => Ty.RECORD (transRecordData fielddata, ref ())
	  | A.ArrayTy(sym, pos) => Ty.ARRAY (lookupTy tenv sym pos, ref ())
	  | A.NameTy(sym, pos) => lookupTy tenv sym pos
    end
				      
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
                    case #ty left' of 
			Ty.INT => (checkInt (left', pos);
                                   checkInt (right', pos);
                                   {exp = (), ty = Ty.INT})
                      | Ty.STRING => (checkString (left', pos);
                                      checkString(right', pos);
                                      {exp = (), ty = Ty.STRING})
                      | _ => {exp = (), ty = Ty.ERROR}  
                end
            else {exp = (), ty = Ty.ERROR}
          | trexp (A.CallExp {func, args, pos}) =TODO
          | trexp (A.IfExp {test, thn, els, pos}) =
	    (case els of 
		 NONE=> 
                 let
                     val test' = trexp test
                     val thn' = trexp thn
                 in
                     (checkInt(test', pos);
		      checkUnit(thn', pos);
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
          | trexp (A.WhileExp {test, body, pos}) = 
	    let 
		val _ = incNesting()
		val test' = trexp test
		val body' = trexp body
		val _ = decNesting()
	    in
		(checkInt(test', pos);
		 checkUnit(body', pos);
		 {exp = (), ty = Ty.UNIT})
	    end

          | trexp (A.RecordExp {fields, typ, pos}) = TODO
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
          | trexp (A.AssignExp {var, exp, pos}) = 
	    let 
		val var' = trvar var
		val exp' = trexp exp
	    in
		if #ty var' = #ty exp'
		then
		    {exp = (), ty = Ty.UNIT}
		else
		    (err pos "mismatch of types in assignment"; {exp = (), ty = Ty.ERROR})
	    end
          | trexp (A.ForExp {var, escape, lo, hi, body, pos}) = TODO (*
	    let
		val lo' = trexp lo
		val hi' = trexp hi
		val body' = trexp body
	    in
		(* vi mangler evt. at checke id *)
		(checkInt(lo', pos);
		 checkInt(hi', pos);
		 checkUnit(body', pos);
		 {exp = (), ty = Ty.UNIT})
	    end *)
          | trexp (A.BreakExp pos) = 
	    if !nesting > 0
	    then 
		{exp = (), ty = Ty.UNIT}
	    else
		(err pos "break expression not inside while/for loop"; {exp = (), ty = Ty.UNIT})
		    
          | trexp (A.LetExp {decls, body, pos}) =
	    let
                val {venv=venv', tenv=tenv'} = transDecs (venv, tenv, decls)
            in
		transExp (venv', tenv') body
            end
          | trexp (A.ArrayExp {typ, size, init, pos}) = 
	    let
		val init' = trexp init
	    in
 		(checkInt (trexp size, pos);
		 {exp = (), ty = #ty init'})
	    (* Jeg ved ikke om man skal checke om vi skal checke typ med et eller andet?
	    Det er jo et symbol så det vidte jeg ikke lige hvad jeg skulle gøre ved*)
	    end
		
        and trvar (A.SimpleVar (id, pos)) =
	    (case S.look(venv, id) of 
		 SOME(E.VarEntry{ty}) => {exp = (), ty = actualTy ty pos}
	       | SOME(E.FunEntry _) => (err pos "not a simple var"; 
					 {exp = (), ty =Ty.ERROR}) 
	       | NONE => ((err pos ("undefined variable " ^S.name id));
			  {exp = (), ty = Ty.INT}))
          | trvar (A.FieldVar (var, id, pos)) = 
	    (case S.look(venv, id) of 
		 SOME(E.VarEntry {ty}) => TODO
		(* case ty of
		     Ty.RECORD (fields, _) => {exp = (), ty = ty}
		   | _ => ((err pos "Variable is not a record");
			   {exp =(), ty = Ty.UNIT}) *)
	  | SOME(E.FunEntry {formals, result}) => TODO
	       | NONE => ((err pos ("undefined variable " ^S.name id));
			  {exp = (), ty = Ty.INT}))

          | trvar (A.SubscriptVar (var, exp, pos)) = 
	    let
		val exp' = trexp exp
	    in
		(checkInt(exp', pos);
		 {exp = (), ty = Ty.INT})
	    end
    in
        trexp
    end
	
and transDec ( venv, tenv, A.VarDec {name, escape, typ = NONE, init, pos}) =
    let 
	val {exp,ty} = (transExp(venv,tenv)) init
	val venv' = S.enter(venv, name, E.VarEntry{ty=ty})
    in 
	{tenv=tenv, venv=venv'}
    end
	
  | transDec ( venv, tenv, A.VarDec {name, escape, typ = SOME (s, pos), init, pos=pos1}) =
    let
	val {exp, ty} = (transExp(venv, tenv)) init
	val typ' = S.look(tenv, s)
	val venv' = S.enter(venv, name, E.VarEntry{ty = ty})
    in
	((case typ' of 
	     NONE => err pos "type is not defined in enviroment"
	  | SOME ty1 => (checkAssignable(ty1, ty, pos1, "type in var dec should be the same"); ()));
	 {tenv = tenv, venv = venv'})
    end
	
  | transDec (venv, tenv, A.TypeDec tydecls) =
    let 
	val [{name, ty, pos}] = tydecls
	val tenv' = S.enter(tenv, name, transTy(tenv, ty))
    in
	{tenv = tenv', venv = venv}
    end
	
  | transDec (venv, tenv, A.FunctionDec fundecls) = {tenv = tenv, venv = venv} (* TO DO *)
	 
and transDecs (venv, tenv, decls) =
    case decls of 
	[] => {venv = venv, tenv = tenv}
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
