%%

%name PlcParser

%pos int


%term VAR
    | AND
    | IF | THEN | ELSE
    | PLUS | MINUS | MULT | DIV | EQ | LESS | LESSEQUAL | NEGATION
    | LPAR | RPAR | LSBRACKET | RSBRACKET | LCBRACES | RCBRACES
    | CONCAT
    | MATCH | WITH | END
    | PRINT
    | SEMIC | ARROW | PIPE | UNDERLINE | COLON | COMMA
    | NAME of string | CINT of int | CBOOL of bool
    | NIL | BOOL | INT
    | FUN | REC | FN | ARROWFUN
    | EOF
    | HD | TL | ISE
    

%nonterm Prog of expr 
    | Decl of expr
    | Expr of expr 
    | AtomExpr of expr 
    | Const of expr 
    | AppExpr of expr
    | Comps of expr list
    | MatchExpr of (expr option * expr) list 
    | CondExpr of expr option
    | Args of (plcType * string) list
    | Params of (plcType * string) list
    | TypedVar of plcType * string
    | Type of plcType
    | AtomType of plcType
    | Types of plcType list


%right SEMIC ARROW
%nonassoc IF
%left ELSE
%left AND
%left EQ
%left LESS LESSEQUAL
%right CONCAT
%left PLUS MINUS
%left MULT DIV
%nonassoc NEGATION PRINT HD TL ISE
%left LSBRACKET

%eop EOF

%noshift EOF

%start Prog

%%

Prog: Expr (Expr) 
    | Decl (Decl)

Decl: VAR NAME EQ Expr SEMIC Prog (Let(NAME, Expr, Prog))
    | FUN NAME Args EQ Expr SEMIC Prog (Let(NAME, makeAnon(Args, Expr), Prog))
    | FUN REC NAME Args COLON Type EQ Expr SEMIC Prog (makeFun(NAME, Args, Type, Expr, Prog))

Expr : AtomExpr (AtomExpr)
    | AppExpr (AppExpr)
    | IF Expr THEN Expr ELSE Expr (If(Expr1, Expr2, Expr3))
    | Expr PLUS Expr (Prim2("+", Expr1, Expr2))
    | Expr MINUS Expr (Prim2("-", Expr1, Expr2))
    | Expr MULT Expr (Prim2("*", Expr1, Expr2))
    | Expr DIV Expr (Prim2("/", Expr1, Expr2))
    | Expr EQ Expr (Prim2("=", Expr1, Expr2))
    | Expr LESS Expr (Prim2("<", Expr1, Expr2))
    | Expr LESSEQUAL Expr (Prim2("<=", Expr1, Expr2))
    | Expr SEMIC Expr (Prim2(";", Expr1, Expr2))
    | MINUS Expr (Prim1("-", Expr))
    | NEGATION Expr (Prim1("!", Expr1))
    | Expr AND Expr (Prim2("&&", Expr1, Expr2))
    | MATCH Expr WITH MatchExpr (Match(Expr, MatchExpr))
    | Expr LSBRACKET CINT RSBRACKET (Item(CINT, Expr))
    | Expr CONCAT Expr (Prim2("::", Expr1, Expr2))
    | PRINT Expr (Prim1("print", Expr))
    | HD Expr (Prim1("hd", Expr1))
    | TL Expr (Prim1("tl", Expr1))
    | ISE Expr (Prim1("ise", Expr1))

AtomExpr : Const (Const)
    | NAME (Var(NAME))
    | LCBRACES Prog RCBRACES (Prog)
    | LPAR Comps RPAR (List(Comps))
    | LPAR Expr RPAR (Expr)
    | FN Args ARROWFUN Expr END (makeAnon(Args, Expr))

Const : CINT (ConI(CINT))
    | CBOOL (ConB(CBOOL))
    | LPAR RPAR (List [])
    | LPAR Type LSBRACKET RSBRACKET RPAR (ESeq(Type))

AppExpr: AtomExpr AtomExpr (Call(AtomExpr1, AtomExpr2))
    | AppExpr AtomExpr (Call(AppExpr, AtomExpr))

MatchExpr : END ([])
	| PIPE CondExpr ARROW Expr MatchExpr ((CondExpr, Expr)::MatchExpr)

CondExpr : Expr (SOME(Expr))
	| UNDERLINE (NONE)

Args: LPAR RPAR ([])
    | LPAR Params RPAR (Params)
    
Params: TypedVar (TypedVar::[])
    | TypedVar COMMA Params (TypedVar::Params)

Comps: Expr COMMA Expr (Expr1::Expr2::[])
    | Expr COMMA Comps (Expr::Comps)

TypedVar: Type NAME ((Type, NAME))

Type: AtomType (AtomType)
    | LPAR Types RPAR (ListT(Types))
    | LSBRACKET Type RSBRACKET (SeqT(Type))
    | Type ARROW Type (FunT (Type1, Type2))

AtomType: NIL (ListT [])
    | BOOL (BoolT)
    | INT (IntT)
    | LPAR Type RPAR (Type)

Types: Type COMMA Type (Type1::Type2::[])
    | Type COMMA Types (Type::Types)
