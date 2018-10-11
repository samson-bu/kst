module ST-SYNTAX
	// control program
	syntax Pgm ::= Libraries
	syntax Libraries ::= List{Library, ""}                              [klabel('POUDecls)]

	// declaration of POUs
	syntax Library ::= FunctionDeclaration
					 | FunctionBlockDeclaration
					 | ProgramDeclaration

	syntax FunctionBlockDeclaration ::= "FunctionBlockDeclaration"
	syntax ProgramDeclaration ::= "ProgramDeclaration"
	syntax StatementList ::= "StatementList"
	// declaration of function
	syntax FunctionDeclaration ::= "FUNCTION" ID ":" ElementaryTypeName FcVarDeclsList StatementList "END_FUNCTION"
	syntax FcVarDeclsList ::= List{FcVarDecl, ""}       [klabel('FcVarDeclsList)]
	syntax FcVarDecl ::= InputDeclarations
					   | OutputDeclarations
					   | InOutDeclarations
					   | FunctionVarDeclarations

	// declaration of function block
	syntax FunctionBlockDeclaration ::= "FUNCTION_BLOCK" ID FbVarDeclList StatementList "END_FUNCTION_BLOCK"
	syntax FbVarDeclList ::= List{FbVarDecl, ""}        [klabel('FbVarDeclList)]
	syntax FbVarDecl ::= InputDeclarations
					   | OutputDeclarations
					   | InOutDeclarations
					   | TempVarDeclarations
					   | InternalDeclarations
	// declaration of program
	syntax ProgramDeclaration ::= "PROGRAM" ID FbVarDeclList StatementList "END_PROGRAM"

	// declaration of varaibles
	syntax InputDeclarations ::= "VAR_INPUT" InputDeclarationList "END_VAR"
							   | "VAR_INPUT" "RETAIN" InputDeclarationList "END_VAR"
							   | "VAR_INPUT" "NON_RETAIN" InputDeclarationList "END_VAR"
	syntax InputDeclarationList ::= List{InputDeclaration, ""}
	syntax InputDeclaration ::= VarInitDecl
                              | Var1List ":" "BOOL" "R_EDGE" ";"
                              | Var1List ":" "BOOL" "F_EDGE" ";"

	syntax OutputDeclarations ::= "VAR_OUTPUT" VarInitDeclList "END_VAR"
								| "VAR_OUTPUT" "RETAIN" VarInitDeclList "END_VAR"
								| "VAR_OUTPUT" "NON_RETAIN" VarInitDeclList "END_VAR"

	syntax InOutDeclarations ::= "VAR_IN_OUT" VarDeclarationList "END_VAR"
	syntax VarDeclarationList ::= List{VarDeclaration, ""}
	syntax VarDeclaration ::= TempVarDecl
							| FbNameDecl ";"
	syntax FbNameDecl ::= Var1List ":" FunctionBlockTypeName
						| Var1List ":" FunctionBlockTypeName ":=" StructureInitialization
	syntax FunctionBlockTypeName ::= ID
	syntax StructureInitialization ::= "(" StructureElementInitializationList ")"
	syntax StructureElementInitializationList ::= List{StructureElementInitialization, ","}
	syntax StructureElementInitialization ::= ID ":=" Constant
                                            | ID ":=" EnumeratedValue
                                            | ID ":=" StructureInitialization

	syntax FunctionVarDeclarations ::= "VAR" "CONSTANT" Var1InitDeclList "END_VAR"
							         | "VAR" Var1InitDeclList "END_VAR"
	syntax Var1InitDeclList ::= List{Var1InitDecl, ""}                  [klabel('FcVars)]
	syntax Var1InitDecl ::= Var1List ":" SimpleSpecInit ";"             [strict(2)]
						  | Var1List ":" SubrangeSpecInit ";"           [strict(2)]
						  | Var1List ":" EnumeratedSpecInit ";"         [strict(2)]

	syntax TempVarDeclarations ::= "VAR_TEMP" TempVarDeclsList "END_VAR"
	syntax TempVarDeclsList ::= List{TempVarDecl, ""}
	syntax TempVarDecl ::= Var1List ":" ElementaryTypeName ";"
                         | Var1List ":" IntegerTypeName "(" SignedInteger ".." SignedInteger ")" ";"
                         | Var1List ":" "(" EnumeratedValueList ")" ";"

	syntax InternalDeclarations ::= "VAR" VarInitDeclList "END_VAR"
							      | "VAR" "CONSTANT" VarInitDeclList "END_VAR"
							      | "VAR" "RETAIN" VarInitDeclList "END_VAR"
							      | "VAR" "NON_RETAIN " VarInitDeclList "END_VAR"
	syntax VarInitDeclList ::= List{VarInitDecl, ""}
	syntax VarInitDecl ::= Var1InitDecl
                         | FbNameDecl ";"

	syntax SimpleSpecInit ::= ElementaryTypeName
							| ElementaryTypeName ":=" Constant          [strict(2)]

	syntax SubrangeSpecInit ::= IntegerTypeName "(" SignedInteger ".." SignedInteger ")"
							  | IntegerTypeName "(" SignedInteger ".." SignedInteger ")" ":=" SignedInteger
	syntax EnumeratedSpecInit ::= "(" EnumeratedValueList ")"
								| "(" EnumeratedValueList ")" ":=" EnumeratedValue

	syntax Var1List ::= List{Var1ListItem, ","}                     [klabel('Var1List)]
	syntax Var1ListItem ::= ID
						  | ID DecimalInteger ".."


    syntax EnumeratedValueList ::= List{EnumeratedValue, ","}
    syntax EnumeratedValue ::= ID
                             | ID "#" ID

	syntax StatementList ::= List{Statement, ""}            [klabel('Stmts)]
	syntax Statement ::= AssignmentStatement
					   | SubprogramControlStatement
					   | SelectionStatement
					   | IterationStatement
					   | FunctionInvocation ";"
					   | "@debug"

	syntax AssignmentStatement ::= Variable ":=" Expression ";"     [strict(2), klabel('AssignStmt)]

	syntax SubprogramControlStatement ::= FbInvocation ";"          [klabel('FbInvocationStmt)]
										| "RETURN" ";"              [klabel('ReturnStmt)]

	syntax FbInvocation ::= FbiName "(" ")"
						  | FbiName  "(" ParamAssignmentFormalList ")"
						  | FbiName  "(" ParamAssignmentNonformalList ")"
	syntax FbiName ::= ID

	syntax SelectionStatement ::= IfStatement ";"
								| CaseStatement ";"
	syntax IfStatement ::= "IF" Expression "THEN" StatementList ElseifStatementList "END_IF"                        [klabel('If1), strict(1)]
						 | "IF" Expression "THEN" StatementList ElseifStatementList "ELSE" StatementList "END_IF"   [klabel('If2), strict(1)]
	syntax ElseifStatementList ::= List{ElseifStatement, ""}
	syntax ElseifStatement ::= "ELSIF" Expression "THEN" StatementList

	syntax CaseStatement ::= "CASE" Expression "OF" CaseElementList "END_CASE"                                  [klabel('Case1)]
						   | "CASE" Expression "OF" CaseElementList "ELSE" StatementList "END_CASE"             [klabel('Case2)]
	syntax CaseElementList ::= List{CaseElement, ""}
	syntax CaseElement ::= CaseList ":" StatementList
	syntax CaseList ::= List{CaseListElement, ","}
	syntax CaseListElement ::= SignedInteger
							 |  SignedInteger ".." SignedInteger
							 | EnumeratedValue

	syntax IterationStatement ::= ForStatement ";"
								| WhileStatement ";"
								| RepeatStatement ";"
								| "EXIT" ";"
	syntax ForStatement ::= "FOR" ID ":=" Expression "TO" Expression "BY" Expression "DO" StatementList "END_FOR"   [klabel('For1)]
						  | "FOR" ID ":=" Expression "TO" Expression "DO" StatementList "END_FOR"                   [klabel('For2)]

	syntax WhileStatement ::= "WHILE" Expression "DO" StatementList "END_WHILE"             [klabel('While), strict(1)]

	syntax RepeatStatement ::= "REPEAT" StatementList "UNTIL" Expression "END_REPEAT"       [klabel('Repeat)]

	// expression
	syntax Expression ::= XorExpression
                        | Expression "OR" XorExpression             [left, strict(1), klabel('Or)]
	syntax XorExpression ::= AndExpression
						   | XorExpression "XOR" AndExpression      [left, seqstrict, klabel('Xor)]
	syntax AndExpression ::= Comparison
						   | AndExpression "&" Comparison           [left, strict(1), klabel('And)]
						   | AndExpression "AND" Comparison         [left, strict(1), klabel('And)]
	syntax Comparison ::= EquExpression
						| Comparison "=" EquExpression              [left, strict, klabel('EQ)]
	syntax EquExpression ::= AddExpression
						   | EquExpression "<" AddExpression        [left, strict, klabel('LT)]
						   | EquExpression ">" AddExpression        [left, strict, klabel('GT)]
						   | EquExpression "<=" AddExpression       [left, strict, klabel('LE)]
						   | EquExpression ">=" AddExpression       [left, strict, klabel('GE)]
	syntax AddExpression ::= Term
						   | AddExpression "+" Term                 [left, strict, klabel('Add)]
						   | AddExpression "-" Term                 [left, strict, klabel('Sub)]
	syntax Term ::= PowerExpression
				  | Term "*" PowerExpression                        [left, strict, klabel('Mul)]
				  | Term "/" PowerExpression                        [left, strict, klabel('Div)]
				  | Term "MOD" PowerExpression                      [left, strict, klabel('Mod)]
	syntax PowerExpression ::= UnaryExpression
							 | PowerExpression "**" UnaryExpression         [left, strict, klabel('Pow)]
	syntax UnaryExpression ::= PrimaryExpression
							 | "-" PrimaryExpression                [klabel('Minus), prefer, strict]
							 | "NOT" PrimaryExpression              [klabel('Complement), strict]
	syntax PrimaryExpression ::= Constant                           [klabel('PriConstant)]
							   | Variable                           [klabel('PriVariable)]
							   | "(" Expression ")"                 [klabel('Bracket)]
							   | FunctionInvocation                 [klabel('PriFcInvocation)]

	syntax FunctionInvocation ::= FunctionName "(" ParamAssignmentFormalList ")"    [strict(2)]
								| FunctionName "(" ParamAssignmentNonformalList ")" [strict(2)]
								| FunctionName "(" ")"                              [prefer]
	syntax FunctionName ::= ID
	syntax ParamAssignmentFormalList ::= List{ParamAssignmentFormal, ","}
	syntax ParamAssignmentFormal ::= ID ":=" Expression                         [klabel('ParamIns)]
								   | Variable "=>" ID                           [klabel('ParamOuts), strict(1)]
								   | "NOT" Variable "=>" ID                     [klabel('NParamOuts)]
	syntax ParamAssignmentNonformalList ::= List{Expression, ","}

	// expressions tests
//	syntax TestExpressions ::= Expressions ";"
//	syntax Expressions ::= List{Expression, ""}

	// variable
	syntax Id ::= ID                                [klabel('Id)]
	syntax ID ::= Token{[A-Za-z\_][A-Za-z0-9\_]*}   [onlyLabel]
	syntax Variable ::= ID                          [klabel('Simp)]
					  | ID "." ID                   [klabel('Fbs)]
	// constant
	syntax Constant ::= BitStringLiteral            [klabel('Lit)]
					  | BooleanLiteral              [klabel('Lit)]
					  | NumericLiteral              [klabel('Lit)]

	syntax BitStringLiteral ::= BitStringTypeName "#" IntegerLiteral    [strict(2), klabel('Bitstring)]
	syntax BooleanLiteral ::= "TRUE"            [klabel('True)]
							| "FALSE"           [klabel('False)]
							| "BOOL#1"          [klabel('True)]
							| "BOOL#0"          [klabel('False)]
	syntax NumericLiteral ::= IntegerLiteral                        [klabel('Int)]
							| IntegerTypeName "#" IntegerLiteral    [klabel('SharpInt)]
							| Float                                 [klabel('Real)]
							| RealTypeName "#" Float                [klabel('SharpReal)]
							| SignedInteger                         [klabel('SInt)]
							| IntegerTypeName "#" SignedInteger     [klabel('SharpSInt)]

	syntax IntegerLiteral ::= BinaryInteger             [klabel('Bina)]
						    | OctalInteger              [klabel('Octa)]
						    | DecimalInteger            [klabel('Deci)]
						    | HexInteger                [klabel('Hexa)]
	syntax BinaryInteger ::= Token{"2#" [0-1][0-1\_]*}
	syntax OctalInteger ::= Token{"8#" [0-7][0-7\_]*}
	syntax DecimalInteger ::= Token{[0-9][0-9\_]*}
	syntax HexInteger ::= Token{"16#" [0-9A-F][0-9A-F\_]*}

	syntax SignedInteger ::= "+" DecimalInteger                     [klabel('PIntger)]
						   | "-" DecimalInteger                     [klabel('NIntger)]
	// constants tests
//	syntax TestConstants ::= Constants ";"
//	syntax Constants ::= List{Constant, ""}

	// data types
	syntax ElementaryTypeName ::= IntegerTypeName
								| RealTypeName
								| "BOOL"
								| BitStringTypeName
	syntax IntegerTypeName ::= "SINT"
							 | "INT"
							 | "DINT"
							 | "LINT"
						     | "USINT"
							 | "UINT"
							 | "UDINT"
							 | "ULINT"
	syntax RealTypeName ::= "REAL"
						  | "LREAL"
	syntax BitStringTypeName ::= "BYTE"
							   | "WORD"
							   | "DWORD"
							   | "LWORD"
	// data type tests
//	syntax TestDataTypes ::= DataTypes ";"
//	syntax DataTypes ::= List{ElementaryTypeName, ""}
endmodule
