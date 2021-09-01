(* PlcChecker *)

exception EmptySeq
exception UnknownType
exception NotEqTypes
exception WrongRetType
exception DiffBrTypes
exception IfCondNotBool
exception NoMatchResults
exception MatchResTypeDiff
exception MatchCondTypesDiff
exception CallTypeMisM
exception NotFunc
exception ListOutOfRange
exception OpNonList
	 
fun checkEqType (t:plcType):bool = 
	case t of BoolT => true
		| IntT => true
		| ListT([]) => true
		| SeqT (t2) => (checkEqType (t2))
		| ListT(l) => (List.all (checkEqType) l)
		| FunT(_) => false;

fun checkIsSeqType (t:plcType):bool = case t 
	of SeqT(_) => true
	| _ => false; 

fun teval (e:expr,env:((string * plcType) list)) = 
	case e of 
		 ConI(_) => IntT
		| ConB(_) => BoolT
		| Var(x) => lookup env x
		| If(exp1,v1,v2) => 
			if (teval (exp1,env)) = BoolT 
			then 
				let
					val teval1 = (teval (v1,env))
					val teval2 = (teval (v2,env))
				in
					if  teval1 = teval2
					then teval1
					else raise DiffBrTypes
				end
			else
				raise IfCondNotBool
		| Let(var, v, p) => 
			let val tvar = teval(v,env)
			in teval(p,(var,tvar)::env)
			end
		| ESeq(t) => 
			if (checkIsSeqType (t)) 
			then t 
			else raise EmptySeq
		| List([]) => ListT([])
		| List(l) => 
			if (List.length l) > 1 
			then ListT((List.map (fn (x) => teval (x,env)) l))
			else raise UnknownType
		| Prim1(ope,expr) => 
			if ope = "!" then
				if (teval (expr,env)) = BoolT
				then BoolT
				else raise UnknownType
			else if ope = "-" then
				if (teval (expr,env)) = IntT
				then IntT
				else raise UnknownType
			else if ope = "tl" then
				let val texpr = (teval (expr,env))
				in
					case texpr of 
						SeqT(ListT []) => raise EmptySeq
						| SeqT(_) => texpr
						| _ => raise UnknownType
				end
			else if ope = "hd" then
				let val texpr = (teval (expr,env))
				in
					case texpr of 
						SeqT(IntT) => IntT
						| SeqT(BoolT) => BoolT
						| SeqT(ListT []) => raise EmptySeq
						| SeqT(ListT(l)) => ListT(l)
						| SeqT(FunT(a,b)) => FunT(a,b)
						| SeqT(SeqT(a)) => SeqT(a)
						| _ => raise UnknownType
				end
			else if ope = "print" then
				let val texpr = (teval (expr,env))
				in ListT([])
				end
			else if ope = "ise" then
				let val texpr = (teval (expr,env))
				in
					case texpr of 
						SeqT(_) => BoolT
						| _ => raise UnknownType
				end
			else raise UnknownType
		| Prim2(ope,expr1,expr2) =>
			(
				if ope = "=" orelse ope = "!=" then 
					let
						val teval1 = (teval (expr1,env))
						val teval2 = (teval (expr2,env))
					in
						if teval1 = teval2
						then 
							if checkEqType teval1
							then BoolT
							else raise UnknownType
						else raise NotEqTypes
					end 
				else if ope = "+" orelse ope = "-" orelse ope = "*" orelse ope = "/" then
					let
						val teval1 = (teval (expr1,env))
						val teval2 = (teval (expr2,env))
					in
						if teval1 = teval2 andalso teval1 = IntT
						then IntT
						else raise UnknownType
					end
				else if ope = "<" orelse ope = "<=" then
					let
						val teval1 = (teval (expr1,env))
						val teval2 = (teval (expr2,env))
					in
						if teval1 = teval2 andalso teval1 = IntT
						then BoolT
						else raise UnknownType 
					end
				else if ope = "&&" then
					let
						val teval1 = (teval (expr1,env))
						val teval2 = (teval (expr2,env))
					in
						if teval1 = teval2 andalso teval1 = BoolT
						then BoolT
						else raise UnknownType
					end
				else if ope = "::" then
					let
						val teval1 = (teval (expr1,env))
						val teval2 = (teval (expr2,env))
					in
						if teval2 = SeqT(teval1)
						then SeqT(teval1)
						else raise UnknownType
					end
				else if ope = ";" then
					let val teval2 = (teval (expr2,env))
					in teval2
					end
				else raise UnknownType
			)
		| Item(n,expr) =>
			let val texpr = teval (expr,env)
			in
				case texpr of 
					ListT([]) => raise ListOutOfRange 
					| ListT(h::t) => 
						if n > ((List.length (h::t))) orelse n < 1
						then raise ListOutOfRange
						else List.nth ((h::t),n-1)
					| _ => raise OpNonList
			end
		| Match(expComp, lOp) => 
			let val texprComp = teval(expComp,env)
			in
				if List.null lOp 
				then
					raise NoMatchResults
				else
					if List.all (fn((opt,ret)) => 
									case opt of 
										SOME(tp) => (teval (tp,env)) = texprComp
										| NONE => true
								) lOp
					then
						let
							val PrimRet = teval((#2 (hd(lOp))),env)
						in
							if List.all (fn((opt,ret)) => (teval(ret,env)) = PrimRet) lOp
							then PrimRet
							else raise MatchResTypeDiff
						end
					else raise MatchCondTypesDiff
			end
		| Letrec(name, tp, l, tr, corpo, prog) => 
			let
				val tc = teval(corpo,(name,FunT(tp,tr))::(l, tp)::env)
				val tprog = teval(prog, (name,FunT(tp,tr))::env)
			in
				if tc = tr 
				then
					tprog
				else
					raise WrongRetType
			end
		| Call(f,pr) => 
			let
				val tpr = teval(pr, env)
				val ftp = teval(f,env)
			in
				case ftp of 
					FunT(tp,texpr) => 
						if tpr = tp then texpr else raise CallTypeMisM
					| _ => raise NotFunc
			end
		| Anon(tp, l, expr) => 
			let val texpr = teval(expr, (l,tp)::env)
			in FunT(tp, texpr)
			end
