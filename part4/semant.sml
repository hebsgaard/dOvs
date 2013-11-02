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
	   | NONE => (err pos ("type is not defined in the enviroment: " ^ S.name sym) ; Ty.ERROR)
    end
	
(* NB: Some function names adjusted to use CamelCase more consistently.
 * For example: 'actual_ty' was renamed to 'actualTy' *)

fun lookUpFields(id:S.symbol, fields:(S.symbol*Ty.ty) list) =
    let
	fun luf (id:S.symbol, []:(S.symbol*Ty.ty) list) = Ty.ERROR
	  | luf (id, x::xs:(S.symbol*Ty.ty) list) = 
	    if (id = (#1 x))
	    then (#2 x)
	    else luf(id, xs)
    in
	luf(id, fields)
    end
	
fun actualTy (Ty.NAME (s, ty)) pos =
    (case !ty of
	NONE => (err pos "The type is undeclared" ; Ty.ERROR)
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
	       | _ => (err pos ("RECORDMismatch of the types in: " ^ msg) ; false))
	  | Ty.ARRAY(_, u1) =>
	    (case aAssigned of
		 Ty.ARRAY(_, u2) => 
		 if (u1=u2)
		 then true
		 else (err pos ("Mismatch of the array unique ref in: " ^ msg) ; false)
	       | _ => (err pos ("ARRAYMismatch of the types in: " ^ msg) ; false)) 
	  | x => 
	    (*Check all other cases*)
	    if (x= aAssigned) 
	    then true 
	    else (err pos ("ERRORMismatch of the types in: " ^ msg) ; false)
    end
	
fun transTy (tenv, t) =
    let 
	(*Translate Absyn fielddata to Type recorddata*)
	fun transRecordData [] = []
	  | transRecordData ({name, escape, typ, pos} :: fieldList) =
	    let
		val (sym, pos1) = typ
	    in 
		(name, lookupTy tenv sym pos1):: transRecordData fieldList
	    end
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
          | trexp (A.CallExp {func, args, pos}) =
	    let
		val  args' = map #1 args
		fun argsMatch (formals, argsExp) = 
		    let 
			fun argsTy (formalTy, exp) = 
			    let
				val {exp, ty} = trexp exp
			    in
				if (formalTy = ty)
				then ()
				else err pos ("argument has incorrct type")
			    end
		    in
			if (length (formals) = length(argsExp))
			then ((map argsTy (ListPair.zip(formals, argsExp)));())
			else err pos ("Number of arguments in declaration and given is different in: " 
				      ^ S.name func)
		    end
	    in
		(case S.look (venv, func) of 
		     NONE =>( err pos ("Function doesn't exist in environment: " ^ S.name func); 
			      {exp =(), ty = Ty.ERROR})
		   | SOME(Env.VarEntry _)  => (err pos "Variable is provided, should call a function"; {exp =(), ty = Ty.ERROR}) 
		   | SOME (E.FunEntry{formals=formals, result=resultTy}) => 
		     (argsMatch (formals, args');
		     {exp = (), ty = resultTy}))
	    end
          | trexp (A.IfExp {test, thn, els, pos}) =
	    (case els of 
		 NONE=> 
                 let
                     val test' = trexp test
                     val thn' = trexp thn
                 in
                     (checkInt(test', pos)
		     ; checkUnit(thn', pos)
		     ; {exp = (), ty = #ty thn'})
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

          | trexp (A.RecordExp {fields, typ, pos}) = 
	    let
		val typ' = S.look(tenv, typ)
		val fieldNames = map #1 fields
		val fieldTypes = map #ty (map trexp (map #2 fields))
	    in
		(case typ' of
		     NONE => (err pos "The type is not defined in environment" ; {exp =(), ty=Ty.ERROR})
		   | SOME ty => 
		     case ty of 
			 Ty.RECORD(rfields, u) =>
			 let
			     val rFieldNames = map #1 rfields
			     val rFieldTypes = map (fn t => actualTy t pos) (map #2 rfields)
			 in
			     if fieldNames = rFieldNames
			     then
				 if fieldTypes = rFieldTypes
				 then {exp = (), ty = Ty.RECORD(rfields, u)}
				 else (err pos "The fieldtypes aren't equal" ; {exp = (), ty=Ty.RECORD(rfields, u)})
			     else (err pos "The ids don't match in record" ; {exp = (), ty=Ty.RECORD(rfields, u)})
			 end
		       | _ =>  (err pos ("not a record type" ^ S.name typ); {exp = (), ty = Ty.ERROR}))
	    end
          | trexp (A.SeqExp []) = {exp = (), ty = Ty.UNIT}
          | trexp (A.SeqExp (aexps as (aexp'::aexps'))) = 
	    let
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
		if checkAssignable(#ty var', #ty exp', pos, "assignable")
		then
		    {exp = (), ty = Ty.UNIT}
		else
		   {exp = (), ty = Ty.ERROR}
	    end
          | trexp (A.ForExp {var, escape, lo, hi, body, pos}) =
	    let
		val _ = incNesting()
		val venv' = S.enter(venv, var, E.VarEntry{ty = Ty.INT})
		val lo' =trexp lo 
		val hi' =trexp hi
		val body' = transExp (venv', tenv) body
		val _ = decNesting()
	    in
		(checkInt(lo', pos);
		 checkInt(hi', pos);
		 checkUnit(body', pos);
		 {exp = (), ty = Ty.UNIT})
	    end 
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
		val size' = trexp size
		val typ' = S.look(tenv, typ)
	    in
 		(checkInt (size', pos);
		 case typ' of
		    NONE => (err pos ("type is not defined for array" ^S.name typ)
			    ; {exp = (), ty = Ty.UNIT})
		  | SOME ty1 => {exp = (), ty = ty1})
	    end
		
        and trvar (A.SimpleVar (id, pos)) =
	    (case S.look(venv, id) of 
		 SOME(E.VarEntry{ty}) => {exp = (), ty = actualTy ty pos}
	       | SOME(E.FunEntry _) => (err pos "not a simple var but a function"; 
					 {exp = (), ty =Ty.ERROR}) 
	       | NONE => ((err pos ("undefined variable " ^S.name id));
			  {exp = (), ty = Ty.UNIT}))

          | trvar (A.FieldVar (var, id, pos)) =
	    let
		val var' = trvar var
	    in
		(case #ty var' of
		     Ty.RECORD(fields, _) =>
		     let 
			 val luf' = lookUpFields(id, fields)
		     in
			 (case luf' of
			      Ty.ERROR => (err pos "The symbol isn't in the record" ; {exp = (), ty=Ty.ERROR })
			    | ty1 => {exp = (), ty = ty1})
		     end
		   | _ => (err pos "The fieldvar has to be a recordtype" ; {exp = (), ty = Ty.ERROR})) 
	    end
		    
          | trvar (A.SubscriptVar (var, exp, pos)) = 
	    let
		val exp' = trexp exp
		val var' = trvar var
	    in
		(checkInt(exp', pos)
		; (case #ty var' of
		       Ty.ARRAY (ty1, _) => {exp = (), ty = ty1}
		    | _ => (err pos "SubscriptVar isn't an array" ; {exp = (), ty = Ty.ERROR}))) 
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
	
  | transDec (venv, tenv, A.FunctionDec fundecls) = 
   let 
       val  [{ name: S.symbol
                       , params: A.fielddata list
                       , result = SOME (sym, pos1)
                       , body: A.exp
                       , pos: A.pos}] = fundecls
       val resTy = case S.look(tenv, sym) of 
		       NONE => Ty.UNIT
		     | SOME ty  => ty 
       fun paramsTy ({ name: S.symbol
                       , escape: bool ref
                       , typ: (S.symbol * A.pos)
                       , pos: A.pos})= 
	   let
	       val typ' = #1 typ
	   in
	       case S.look (tenv, typ') of 
	       NONE => (err pos ("type is not in envirnment: " ^S.name typ'); 
			{name = name, ty = Ty.ERROR})
	     | SOME ty=> {name = name, ty = ty}
	   end
       val params' = map paramsTy params
       val venv' = Symbol.enter(venv, name, 
			  E.FunEntry{formals = map #ty params', result = resTy})
       fun enterParam ({name, ty}, venv) = 
           Symbol.enter (venv, name, E.VarEntry{ty=ty})
       val venv'' = foldr enterParam venv' params'
   in
       (transExp (venv'', tenv) body;  
       {tenv = tenv, venv = venv'})
   end
	 
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
