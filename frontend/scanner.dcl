definition module scanner

import StdEnv, general

::	SearchPaths	:== [String]

::	* ScanState

::	FilePosition = {fp_line :: !Int, fp_col :: !Int}

instance <<< FilePosition

::	Token
	= 	IdentToken !.String		//		an identifier
	|	IntToken !.String		//		an integer
	|	RealToken !.String		//		a real
	|	StringToken !.String	//		a string
	|	CharToken !.String		//		a character
	|	CharListToken !.String	//		a character list '{char}*'
	|	BoolToken !Bool			//		a boolean
	|	OpenToken				//		(
	|	CloseToken				//		)
	|	CurlyOpenToken			//		{
	|	CurlyCloseToken			//		}
	|	SquareOpenToken			//		[
	|	SquareCloseToken		//		]

	|	DotToken				//		.
	|	SemicolonToken			//		;
	|	ColonToken				//		:
	|	DoubleColonToken		//		::
	|	CommaToken				//		,
	|	ExclamationToken		//		!
	|	BarToken				//		|
	|	ArrowToken				//		->
	|	DoubleArrowToken		//		=>
	|	EqualToken				//		=
	|	DefinesColonToken		//		=:
	|	ColonDefinesToken		//		:==
	|	WildCardToken			//		_
	|	BackSlashToken			//		\
	|	DoubleBackSlashToken	//		\\
	|	LeftArrowToken			//		<-
	|	LeftArrowColonToken		//		<-:
	|	DotDotToken				//		..
	|	AndToken				//		&
	|	HashToken				//		#
	|	AsteriskToken			//		*
	|	LessThanOrEqualToken	//		<=

	|	ModuleToken				//		module
	|	ImpModuleToken			//		implementation
	|	DefModuleToken			//		definition
	|	SysModuleToken			//		system

	|	ImportToken				//		import
	|	FromToken				//		from
	|	SpecialToken			//		special

	|	IntTypeToken			//		Int
	|	CharTypeToken			//		Char
	|	RealTypeToken			//		Real
	|	BoolTypeToken			//		Bool
	|	StringTypeToken			//		String
	|	FileTypeToken			//		File
	|	WorldTypeToken			//		World
	|	VoidTypeToken			//		Void
	|	LeftAssocToken			//		left
	|	RightAssocToken			//		right
	|	ClassToken				//		class
	|	InstanceToken			//		instance
	|	OtherwiseToken			//		otherwise

	|	IfToken					//		if
	|	WhereToken				//		where
	|	WithToken				//		with
	|	CaseToken				//		case
	|	OfToken					//		of
	|	LetToken Bool			//		let!, let
	|	SeqLetToken Bool		//		Let!, Let
	|	InToken					//		in
	
	|	DynamicToken			//		dynamic
	|	DynamicTypeToken		//		Dynamic

	
	|	PriorityToken Priority	//		infixX N

	|	CodeToken				//		code
	|	InlineToken				//		inline
	|	CodeBlockToken [String]	//		{...}

	|	NewDefinitionToken		//		generated automatically
	|	EndGroupToken			//		generated automatically
	|	EndOfFileToken			//		end of file
	|	ErrorToken String		//		if an error occured
	
:: Context
	=	GeneralContext
	|	TypeContext
	|	FunctionContext
	|	CodeContext

::	Assoc	= LeftAssoc | RightAssoc | NoAssoc

::	Priority = Prio Assoc Int | NoPrio
    
class getFilename state :: !*state -> (!String,!*state)
instance getFilename ScanState

class tokenBack state :: !*state -> !*state
instance tokenBack ScanState

class nextToken state :: !Context !*state -> (!Token, !*state)
instance nextToken ScanState

class currentToken state :: !*state -> (!Token, !*state)
instance currentToken ScanState

class insertToken state :: !Token !Context !*state -> *state
instance insertToken ScanState

class replaceToken state :: !Token !*state -> *state
instance replaceToken ScanState

class getPosition state :: !*state -> (!FilePosition,!*state)  // Position of current Token (or Char)
instance getPosition ScanState

openScanner :: !String !SearchPaths !*Files -> (!Optional ScanState, !*Files)
closeScanner :: !ScanState !*Files -> *Files

setUseLayout :: !Bool !ScanState -> ScanState
UseLayout :: !ScanState -> (!Bool, !ScanState)
dropOffsidePosition :: !ScanState -> ScanState

isLhsStartToken :: ! Token -> Bool
isOffsideToken :: ! Token -> Bool
isEndGroupToken :: ! Token -> Bool

instance == Token

instance <<< Token

instance toString Token, Priority


/* Sjaak ... */

// instance < Priority

determinePriority :: !Priority !Priority -> Optional Bool

/* ... Sjaak */


