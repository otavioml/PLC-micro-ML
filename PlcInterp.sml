exception Impossible
exception HDEmptySeq
exception TLEmptySeq
exception ValueNotFoundInMatch
exception NotAFunc

(* fun getV(v:plcVal) = 
	case v of IntV(a) => a
			| BoolV(a) => a
			| _ => raise Impossible *)

fun getV(n:plcVal) = 
	case n of IntV(a) => a
		| _ => raise Impossible 

fun getBoolV(v:plcVal) = 
	case v of BoolV(a) => a
		| _ => raise Impossible 


fun eval (e:expr,env:((string * plcVal) list)) = 
	(case e of 
		ConI n => IntV(n)
		| ConB b => BoolV(b)
		| Var x => 
			let val v = (lookup env x) 
			in v
			end
		| If(exp1,v1,v2) => 
			let val eExp1 = eval(exp1,env)
			in
				if (getBoolV(eExp1)) 
				then eval(v1,env)
				else eval(v2,env)
			end		
		| Let(var, value, pg) => 
			let val evar = eval(value,env)
			in eval(pg,(var,evar)::env)
			end
		| ESeq(t) => SeqV([])
		| List([]) => ListV([])
		| List(l) => 
			if (List.length l) > 1 
			then ListV((List.map (fn (x) => eval (x,env)) l))
			else raise Impossible
		| Prim1(ope,expr) => 
			if ope = "!" then
				let val eExp = eval(expr,env)
				in BoolV(not (getBoolV(eExp)))
				end
			else if ope = "-" then
				let val eExp = eval(expr,env)
				in IntV(~(getV(eExp)))
				end
			else if ope = "tl" then
				let
					val eExpr = (eval (expr,env))
				in
					case eExpr of 
						SeqV([]) => raise TLEmptySeq
						| SeqV(l) => SeqV(tl(l))
						| _ => raise Impossible
				end
			else if ope = "hd" then
				let val eExpr = (eval (expr,env))
				in
					case eExpr of 
						SeqV([]) => raise HDEmptySeq
						| SeqV(l) => hd(l)
						| _ => raise Impossible
				end
			else if ope = "print" then
				let val eExpr = (eval (expr,env))
				in
					print(val2string(eExpr)^"\n");
					ListV([])
				end
			else if ope = "ise" then
				let
					val eExpr = (eval (expr,env))
				in
					case eExpr of 
						SeqV(l) => BoolV(List.null l)
						| _ => raise Impossible
				end
			else raise Impossible
		| Prim2(ope,expr1,expr2) =>
			(
				if ope = "=" orelse ope = "!=" then 
					let
						val eExp1 = (eval (expr1,env))
						val eExp2 = (eval (expr2,env))
					in
						if ope = "!=" 
						then BoolV(not (eExp1 = eExp2))
						else BoolV(eExp1 = eExp2)
					end
				else if ope = "+" orelse ope = "-" orelse ope = "*" orelse ope = "/" then
					let
						val eExp1 = (eval (expr1,env))
						val eExp2 = (eval (expr2,env))
					in
						if ope = "+" then IntV(getV(eExp1)+getV(eExp2))
						else if ope = "-" then IntV(getV(eExp1)-getV(eExp2))
						else if ope = "*" then IntV(getV(eExp1)*getV(eExp2))
						else if ope = "/" then IntV(getV(eExp1) div getV(eExp2))
						else raise Impossible
					end
				else if ope = "<" orelse ope = "<=" then
					let
						val eExp1 = (eval (expr1,env))
						val eExp2 = (eval (expr2,env))
					in
						if ope = "<" 
						then BoolV(getV(eExp1) < getV(eExp2)) 
						else BoolV(getV(eExp1) <= getV(eExp2))
					end
				else if ope = "&&" then
						let
							val eExp1 = (eval (expr1,env))
							val eExp2 = (eval (expr2,env))
						in BoolV(getBoolV(eExp1) andalso getBoolV(eExp2))
						end
				else if ope = "::" then
					let
						val eExp1 = (eval (expr1,env))
						val eExp2 = (eval (expr2,env))
					in
						case eExp1 of SeqV(a) => 
							(case eExp2 of SeqV(b) => 
								SeqV(a@b)
								| _ => SeqV(eExp2::a)
							)
							| _ => (case eExp2 of SeqV([]) => 
										SeqV(eExp1::[]) 
										| SeqV(b) => SeqV(eExp1::b)
									)
					end
				else if ope = ";" then
					let
						val eExp1 = (eval (expr1,env))
						val eExp2 = (eval (expr2,env))
					in eExp2
					end
				else raise Impossible
			)
		| Item(n,expr) =>
			let val eExpr = eval (expr,env)
			in
				case eExpr of
					ListV(l) => List.nth (l, n-1)
					| _ => raise Impossible
			end
		| Match(expComp, lOp) => 
			let
				val eExprComp = eval(expComp,env)
				val validOpt = List.filter (fn((opt,ret)) => 
													case opt of 
														SOME(tp) => (eval (tp,env)) = eExprComp
														| NONE => true
												) lOp
			in
				if(List.null validOpt) 
				then raise ValueNotFoundInMatch
				else eval(#2((List.nth (validOpt, 0))),env)
			end
		| Letrec(name, tps, l, tret, b, pg) => eval(pg,(name,Clos(name,l,b,env))::env)
		| Call(f,pr) =>
			let
				val vf = eval(f,env);
			    val prEv = eval(pr,env);
			in
				case vf of 
					(Clos("", l, b, envP)) =>
						let val NewEnv = (l, prEv)::envP
			            in eval(b,NewEnv)
			            end
		            | (Clos(f, l, b, envP)) =>
						let val NewEnv = (l, prEv)::(f,vf)::envP
			            in eval(b,NewEnv)
			            end
			        | _ => raise NotAFunc
			end
		| Anon(tps, l, b) => Clos("",l, b, env)
	)