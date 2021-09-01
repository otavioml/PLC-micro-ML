(* Plc interpreter main file *)
CM.make("$/basis.cm");
CM.make("$/ml-yacc-lib.cm");
use "Environ.sml";
use "Absyn.sml";
use "PlcChecker.sml";
use "PlcInterp.sml";
use "PlcParserAux.sml";
use "PlcParser.yacc.sig";
use "PlcParser.yacc.sml";
use "PlcLexer.lex.sml";
use "Parse.sml";
use "testParserCases.sml";

open PlcFrontEnd;

fun run (e:expr) =

	let 
		val TypeCheck = teval(e,[])
		val Evaluation = eval(e,[])
	in
		(val2string Evaluation) ^ " : " ^ (type2string TypeCheck)
	end
	handle SymbolNotFound => "Undefined Symbol detected."
            |  EmptySeq => "Empty sequence as input."
            |  UnknownType => "Unknown Type."
            |  NotEqTypes => "Types not Equal."
            |  WrongRetType => "Wrong Return Type."
            |  DiffBrTypes => "Conditional branches have different type."
            |  IfCondNotBool => "If conditional is not Boolean."
            |  NoMatchResults => "No match results."
            |  MatchResTypeDiff => "Match result with wrong type."
            |  MatchCondTypesDiff => "Match is with different type."
            |  CallTypeMisM => "Function call with wrong Type."
            |  NotFunc => "Not a function."
            |  ListOutOfRange => "Trying to access invalid value from List."
            |  OpNonList => "Expression is not a List."
            |  HDEmptySeq => "Head from empty sequence is empty."
            |  TLEmptySeq => "Tail from empty sequence is empty"
            |  ValueNotFoundInMatch => "Value not found."
            |  NotAFunc => "Value is not a function."
            |  Impossible => "Operation can't be executed."
            |  _ => "Unexpected exeption."