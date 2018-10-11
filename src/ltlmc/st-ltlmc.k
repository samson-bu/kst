require "../syntax/st-syntax.k"
require "builtins/model-checker.k"

module ST-LTLMC
	imports ST-SYNTAX
	imports MODEL-CHECKER-HOOKS
	imports LTL-HOOKS

//    syntax Id::= "n" [token]
//			| "sum" [token]
//
//    syntax Int ::="states""(" Bag "," Id ")" [function]
//    syntax Prop ::= "equal""(" Id "," Int ")"  [function]
//				| Id
//				| Int
//
//    rule states(<generatedTop> ...<T>...<store> ...(I:Id |-> N:Int)... </store>...</T>... </generatedTop>, I) => N [structural]
//
//    rule B:Bag |=Ltl X:Id => true  requires states(B, X) =/=Int 0 [ltl, anywhere]
//    rule B:Bag |=Ltl I:Int => true requires I =/=Int 0 [ltl, anywhere]
//    rule B:Bag |=Ltl equal(I, N) =>true requires states(B, I) ==Int N [ltl, anywhere]
	// ltl-support

	syntax Pgm ::= LtlFormula

	syntax Statement ::= "@ltlmc" ":" ID

	syntax Prop ::= VarInstance
                  | "eqToSum" "(" VarInstance "," VarInstance ")"
                  | "eqTo" "(" VarInstance "," Int ")"
                  |  "lt" "(" VarInstance "," Int ")"
                  |  "leq" "(" VarInstance "," Int ")"
                  |  "gt" "(" VarInstance "," Int ")"
                  |  "geq" "(" VarInstance "," Int ")"
                  |  "neqTo" "(" VarInstance "," Int ")"
                  |  "eq" "(" VarInstance "," VarInstance ")"


	rule @ltlmc : L:ID => . [lbldstmt]


	syntax Int ::= "val" "(" Bag "," VarInstance ")"         [function]
    rule val(<generatedTop>... <T>...
                 <state>... VI:VarInstance |-> L:Int ...</state>
                 <store>... L |-> I:Int ...</store>
           ...</T> ...</generatedTop>, VI)
       => I

  syntax Int ::= "sumFirstN" "(" Int ")" [function]
  rule sumFirstN(0) => 0 [anywhere]
  rule sumFirstN(N:Int) => sumFirstN(N -Int 1) +Int N requires N >Int 0 [anywhere]

  syntax Int ::= "pow" "(" Int "," Int ")" [function]
  rule pow(X:Int, 0) => 1
  rule pow(X:Int, Y:Int) => X *Int pow(X, Y -Int 1) requires Y >Int 0

  rule B:Bag |=Ltl eqTo(X:VarInstance, I:Int) => true requires val(B, X) ==Int I [ltl, anywhere]

  rule B:Bag |=Ltl neqTo(X:VarInstance, I:Int) => true requires val(B, X) =/=Int I [ltl, anywhere]

  rule B:Bag |=Ltl lt(X:VarInstance, I:Int) => true requires val(B, X) <Int I [ltl, anywhere]

  rule B:Bag |=Ltl leq(X:VarInstance, I:Int) => true requires val(B, X) <=Int I [ltl, anywhere]

  rule B:Bag |=Ltl gt(X:VarInstance, I:Int) => true requires val(B, X) >Int I [ltl, anywhere]

  rule B:Bag |=Ltl geq(X:VarInstance, I:Int) => true requires val(B, X) >=Int I [ltl, anywhere]

  rule B:Bag |=Ltl eq(X:VarInstance, Y:VarInstance) => true requires val(B, X) ==Int val(B, Y) [ltl, anywhere]

  rule B:Bag |=Ltl eqToSum(X:VarInstance, Y:VarInstance) => true
       requires val(B, X) ==Int sumFirstN(val(B, Y))
       [ltl, anywhere]

  rule <generatedTop>...
         <T>...
         <k> @ltlmc : L:ID ... </k>
         ...</T>
       ...</generatedTop>
       |=Ltl L
       =>
       true
       [anywhere]

	// exection

	syntax KItem ::= "@preprocessing"
				   | "@initializing"
				   | "@updatingInputs"
				   | "@executingPrograms"
				   | "@writingOutputs"

	configuration
	<T>
		<k> $PGM:Pgm</k>                        // computations
		<stack> .List </stack>                  // run-time stack
		<env> .Map </env>                       // the local environment of <pid>
		<store> .Map </store>                   // a map from locations to values, representing the memory
		<nLoc> 0 </nLoc>                        // the next available location
		<type> .Map </type>                     // a map from locations to data types
		<catg> .Map </catg>                     // a map from locations to variable catetories, e.g., input, output
		<cnst> .Map </cnst>                     // a map from locations to (0, or 1), where 1 indicates a constant
		<rete> .Map </rete>                     // a map from locations to (0, or 1), where 1 indicates retentive value
		<pid> 0 </pid>                          // currently executing/processing instance
		<pgs> .K </pgs>                         // list of program instances
		<phase> @preprocessing </phase>         // the currently executing phase
		<in stream="stdin"> .List </in>         // input signals
		<out stream="stdout"> .List </out>      // output signals

		// POUs
		<pous color="blue">
			<pou multiplicity="*">
				<pName> .K </pName>             // the name of POU
				<pRet> .K </pRet>               // the data type of return value, if the POU is a function
				<pVars> .K </pVars>             // delcaration of variables
				<pStmts> .K </pStmts>           // statements list
			</pou>
		</pous>

		// instances
		<inss color="green">
			<ins multiplicity="*">
				<iEnv> .Map </iEnv>             // local environment of the instance
				<iIns> .Map </iIns>             // from variables to function block instances
				<iType> .K </iType>             // the POU type of the instance
				<iId> 0 </iId>                  // the unique identieri of the instance
			</ins>
			<nId> 0 </nId>                      // the next available identifer
		</inss>

		// debug only
		<debug> .K </debug>

		// LTL-model checking
		<state> .Map </state>                   // map from variables (of the form *.*.*.V) to their locations
												// VarInstance |-> L
		<nameSpace> .K </nameSpace>
	</T>

	syntax VarInstance ::= ID
						 | VarInstance ":::" ID           [left]

	// semantic rules
	rule P:Library Ps:Libraries => P~>Ps                [structural]
	rule <k> .K => Pgs </k>
		 <phase> @preprocessing => @initializing </phase>
		 <pgs> Pgs </pgs>                               [structural]

	// 1. preprocessing phase
	// function
	rule <k> FUNCTION Name:ID : Ret:ElementaryTypeName Vars:FcVarDeclsList Stmts:StatementList END_FUNCTION
			=> allocL(I, Vars) // ~> store()
			...
	     </k>
		 <phase> @preprocessing </phase>
		(.Bag =>
 		    <pou>
 				<pName> Name </pName>
 				<pRet> Ret </pRet>
 				<pVars> Vars </pVars>
 				<pStmts> Stmts </pStmts>
 		    </pou>
		 )
		 (.Bag =>
			<ins>
                <iEnv> Name |-> L </iEnv>
                <iIns> .Map </iIns>
                <iType> Name </iType>
                <iId> I </iId>
            </ins>
		 )
		 <store> Store:Map (. => L |-> default(Ret)) ...</store>
		 <type> Type:Map (. => L |-> Ret) ...</type>
		 <catg> Catg:Map (. => L |-> FcVar) ...</catg>
		 <cnst> Cnst:Map (. => L |-> 0) ...</cnst>
		 <rete> Rete:Map (. => L |-> 0) ...</rete>
		 <nId> I => I +Int 1 </nId>
		 <nLoc> L => L +Int 1 </nLoc>
		 // ltlmc only
		 <state> State:Map (. => Name ::: Name |-> L) ...</state>
		 <nameSpace> _ => Name </nameSpace>         [structural]

	// function block
	rule <k> FUNCTION_BLOCK Name:ID Vars:FbVarDeclList Stmts:StatementList END_FUNCTION_BLOCK => . ... </k>
		 <phase> @preprocessing </phase>
		 (.Bag =>
		    <pou>
				<pName> Name </pName>
				<pVars> Vars </pVars>
				<pStmts> Stmts </pStmts>
				...
		    </pou>
		 )                      [structural]
	// program
	rule <k> PROGRAM Name:ID Vars:FbVarDeclList Stmts:StatementList END_PROGRAM => . ... </k>
		 <phase> @preprocessing </phase>
		 (.Bag =>
		    <pou>
				<pName> Name </pName>
				<pVars> Vars </pVars>
				<pStmts> Stmts </pStmts>
				...
		    </pou>
		 )
		( .Bag =>
			<ins>
				<iEnv> .Map </iEnv>
				<iIns> .Map </iIns>
				<iType> Name </iType>
				<iId> I </iId>
			</ins>
		)
		<nId> I => I +Int 1 </nId>
		<pgs> Pgs => I ~> Pgs </pgs>            [structural]

	// 2. initializing phase
	rule <k> I:Int => allocL(I, Vars) ... </k>
		 <phase> @initializing </phase>
		 <ins>
		    <iId> I </iId>
		    <iType> T </iType>
		    ...
		 </ins>
		 <pou>
			<pName> T </pName>
			<pVars> Vars:FbVarDeclList </pVars>
			...
		 </pou>
		 // ltlmc only
		 <nameSpace> _ => T </nameSpace>            [structural]
	rule <k> .K => Pgs </k>
		 <phase> @initializing => @updatingInputs</phase>
		 <pgs> Pgs </pgs>                           [structural]

	// 3. scanning cycle
	// 3.1 updating inputs
	rule <k> I:Int => . ...</k> //updatingInputs(I, Vars) ... </k>
		 <phase> @updatingInputs </phase>
		 <ins>
		    <iId> I </iId>
		    <iType> T </iType>
		    ...
		 </ins>
		 <pou>
			<pName> T </pName>
			<pVars> Vars:FbVarDeclList </pVars>
			...
		 </pou>                                 [structural]
	rule <k> .K => Pgs </k>
		 <phase> @updatingInputs => @executingPrograms</phase>
		 <pgs> Pgs </pgs>                       [structural]

	syntax KItem ::= updatingInputs(Int, FbVarDeclList)
	rule updatingInputs(I:Int, V:FbVarDecl Vs:FbVarDeclList) => updateInput(I, V) ~> updatingInputs(I, Vs)      [structural]
	rule updatingInputs(I:Int, .FbVarDeclList) => .             [structural]

	syntax KItem ::= updateInput(Int, FbVarDecl)
	rule updateInput(I:Int, VAR_INPUT V:InputDeclaration Vs:InputDeclarationList END_VAR )
			=> update(I, V) ~> updateInput(I, VAR_INPUT Vs END_VAR)         [structural]
	rule updateInput(I:Int, VAR_INPUT .InputDeclarationList END_VAR ) =>.   [structural]

	rule updateInput(I:Int, VAR_INPUT RETAIN V:InputDeclaration Vs:InputDeclarationList END_VAR )
			=> update(I, V) ~> updateInput(I, VAR_INPUT RETAIN Vs END_VAR)      [structural]
	rule updateInput(I:Int, VAR_INPUT RETAIN .InputDeclarationList END_VAR ) =>.        [structural]

	rule updateInput(I:Int, VAR_INPUT NON_RETAIN V:InputDeclaration Vs:InputDeclarationList END_VAR )
			=> update(I, V) ~> updateInput(I, VAR_INPUT NON_RETAIN Vs END_VAR)          [structural]
	rule updateInput(I:Int, VAR_INPUT NON_RETAIN .InputDeclarationList END_VAR ) =>.    [structural]

	rule updateInput(I:Int, O:OutputDeclarations) => .          [structural]
	rule updateInput(I:Int, O:TempVarDeclarations) => .         [structural]
	rule updateInput(I:Int, O:InternalDeclarations) => .        [structural]

	syntax KItem ::= update(Int, InputDeclaration)
	// Var1List ":" SimpleSpecInit ";"             [strict(2)]
	// 整型和布尔型
	rule <k> update(I:Int, X:ID, Xs:Var1List : SSI:SimpleSpecInit ;)
			=> update(I, Xs : SSI ;)
			...
		 </k>
		 <in> ListItem(V:Int) => . ... </in>
		 <store> L |-> (_ => inSig(V, T)) ... </store>
		 <ins>
			<iId> I </iId>
			<iEnv> X |-> L ... </iEnv>
			...
		 </ins>
		 <type> L |-> T ...</type>      [structural]
	// todo: 实数型

	rule update(I:Int, .Var1List : _:SimpleSpecInit ;) => .     [structural]
	// todo: Var1List ":" SubrangeSpecInit ";"           [strict(2)]
	// todo: Var1List ":" EnumeratedSpecInit ";"         [strict(2)]
	// todo: FbNameDecl ";"
	// 未初始化
	rule  update(I:Int, X:ID, Xs:Var1List : Name:ID ;) => .     [structural]
	// todo: 初始化

	// helpers
	syntax KItem ::= inSig(Int, ElementaryTypeName)             [function]
	rule inSig(I:Int, IT:IntegerTypeName) => I                  [structural]
	rule inSig(I:Int, BOOL) => false
		 when I ==Int 0     [structural]
	rule inSig(I:Int, BOOL) => true
		 when I =/=Int 0        [structural]

	// 3.2 executing programs
	rule <k> I:Int => executeL(Stmts) ... </k>
		 <pid> _ => I </pid>
		 <env> _ => IEnv </env>
		 <phase> @executingPrograms </phase>
		 <ins>
		    <iId> I </iId>
		    <iEnv> IEnv:Map </iEnv>
		    <iType> T </iType>
		    ...
		 </ins>
		 <pou>
			<pName> T </pName>
			<pStmts> Stmts:StatementList </pStmts>
			...
		 </pou>     [structural]
	rule <k> .K => Pgs </k>
		 <phase> @executingPrograms => @writingOutputs</phase>
		 <pgs> Pgs </pgs>       [structural]

	syntax KItem ::= executeL(StatementList)
	rule executeL(S:Statement Ss:StatementList) => S ~> executeL(Ss)        [structural]
	rule executeL(.StatementList) => .      [structural]

	// 赋值语句
	rule <k> 'AssignStmt('Simp(X:ID),, RV:RawVal :: ET:ElementaryTypeName) => . ... </k>
		 <store> L |-> (_ => RV) ... </store>
		 <pid> I </pid>
		 <ins>
		    <iId> I </iId>
		    <iEnv> X |-> L ...</iEnv>
		    ...
		 </ins>
		 <type> L |-> T ... </type>
		 when subtype(ET, T)
	// todo: FBInvoation
	// selection statement
	// ifstatement
	// if1
	rule IF E:Expression THEN Stmts:StatementList ESL:ElseifStatementList END_IF ; => ifAux(E, Stmts, ESL)  [structural]

	syntax Expression ::= TypedVal
	syntax KItem ::= ifAux(Expression, StatementList, ElseifStatementList)          [strict(1)]
	rule ifAux(true :: BOOL , Ss:StatementList , _:ElseifStatementList) => executeL(Ss)
	rule ifAux(false :: BOOL , SL:StatementList , ESL:ElseifStatementList) => ESL

	rule ES:ElseifStatement ESL:ElseifStatementList => ES ~> ESL        [structural]
	rule .ElseifStatementList => .      [structural]
	// elsif
	rule ELSIF E:Expression THEN Stmts:StatementList => ifAux(E, Stmts, .ElseifStatementList)
	// if2
	rule IF E:Expression THEN Stmts:StatementList ESL:ElseifStatementList ELSE Stmts2:StatementList END_IF ;
		=> ifAux(E, Stmts, ESL, Stmts2)     [structural]
	syntax KItem ::= ifAux(Expression, StatementList, ElseifStatementList, StatementList)   [strict(1)]
	rule ifAux(true :: BOOL , Ss:StatementList , _:ElseifStatementList, _:StatementList) => executeL(Ss)
	rule ifAux(false :: BOOL , SL:StatementList , ES:ElseifStatement ESL:ElseifStatementList, SL2:StatementList) => ESL
	rule ifAux(false :: BOOL , _:StatementList , .ElseifStatementList, SL:StatementList) => executeL(SL)

	// fix me: 如果ESL非空，即使是没有一个条件满足，也会漏掉ELSE

	// todo: case statement

	// iteration statement

	// for statement

	// while statement
	rule WHILE E:Expression DO SL:StatementList END_WHILE ; => whileAux(E, SL) ~> WHILE E DO SL END_WHILE ;     [structural]
	syntax KItem ::= whileAux(Expression, StatementList)            [strict(1)]
	rule whileAux(true::BOOL, SL:StatementList) => executeL(SL)
	rule whileAux(false::BOOL, _:StatementList) ~> WHILE E:Expression DO SL:StatementList END_WHILE ; => .

	// repeat statement



	// 3.3 writing outputs
	rule <k> I:Int => . ...</k>
		 <phase> @writingOutputs </phase>       [structural]


	// allocate memory for function's variables
	syntax KItem ::= allocL(Int, FcVarDeclsList)
	rule allocL(I:Int, V:FcVarDecl Vs:FcVarDeclsList) => allocC(I, V) ~> allocL(I, Vs)      [structural]
	rule <k> allocL(I:Int, .FcVarDeclsList) => . ...</k>        [structural]

	// allocate memory for input (output, in_out, func) variable
	syntax KItem ::= allocC(Int, FcVarDecl)
	// input
	rule allocC(I:Int, VAR_INPUT V:InputDeclaration Vs:InputDeclarationList END_VAR)
			=> storeIn(I, V, 0) ~> allocC(I:Int, VAR_INPUT Vs END_VAR)      [structural]
	rule allocC(I:Int, VAR_INPUT .InputDeclarationList END_VAR) => .        [structural]

	rule allocC(I:Int, VAR_INPUT RETAIN V:InputDeclaration Vs:InputDeclarationList END_VAR)
			=> storeIn(I, V, 1) ~> allocC(I:Int, VAR_INPUT RETAIN Vs END_VAR)       [structural]
	rule allocC(I:Int, VAR_INPUT RETAIN .InputDeclarationList END_VAR) => .         [structural]

	rule allocC(I:Int, VAR_INPUT NON_RETAIN V:InputDeclaration Vs:InputDeclarationList END_VAR)
			=> storeIn(I, V, 0) ~> allocC(I:Int, VAR_INPUT NON_RETAIN Vs END_VAR)   [structural]
	rule allocC(I:Int, VAR_INPUT NON_RETAIN .InputDeclarationList END_VAR) => .     [structural]

	// output
	rule allocC(I:Int, VAR_OUTPUT V:VarInitDecl Vs:VarInitDeclList END_VAR)
			=> storeOut(I, V, 0) ~> allocC(I:Int, VAR_OUTPUT Vs END_VAR)    [structural]
	rule allocC(I:Int, VAR_OUTPUT .VarInitDeclList END_VAR) => .            [structural]

	rule allocC(I:Int, VAR_OUTPUT RETAIN V:VarInitDecl Vs:VarInitDeclList END_VAR)
			=> storeOut(I, V, 1) ~> allocC(I:Int, VAR_OUTPUT RETAIN Vs END_VAR) [structural]
	rule allocC(I:Int, VAR_OUTPUT RETAIN .VarInitDeclList END_VAR) => .         [structural]

	rule allocC(I:Int, VAR_OUTPUT NON_RETAIN V:VarInitDecl Vs:VarInitDeclList END_VAR)
			=> storeOut(I, V, 0) ~> allocC(I:Int, VAR_OUTPUT NON_RETAIN Vs END_VAR) [structural]
	rule allocC(I:Int, VAR_OUTPUT NON_RETAIN .VarInitDeclList END_VAR) => .         [structural]

	// in_out
	rule allocC(I:Int, VAR_IN_OUT V:VarDeclaration Vs:VarDeclarationList END_VAR)
			=> storeIO(I, V) ~> allocC(I:Int, VAR_IN_OUT Vs END_VAR)            [structural]
	rule allocC(I:Int, VAR_IN_OUT .VarDeclarationList END_VAR) => .             [structural]

	// func
	rule allocC(I:Int, VAR V:Var1InitDecl Vs:Var1InitDeclList END_VAR)
			=> storeFC(I, V, 0) ~> allocC(I:Int, VAR Vs:Var1InitDeclList END_VAR)   [structural]
	rule allocC(I:Int, VAR .Var1InitDeclList END_VAR) => .      [structural]
	rule allocC(I:Int, VAR CONSTANT V:Var1InitDecl Vs:Var1InitDeclList END_VAR)
			=> storeFC(I, V, 1) ~> allocC(I:Int, VAR CONSTANT Vs:Var1InitDeclList END_VAR)      [structural]
	rule allocC(I:Int, VAR CONSTANT .Var1InitDeclList END_VAR) => .     [structural]

	// allocate memory for function block's (and program's) variables
	syntax KItem ::= allocL(Int, FbVarDeclList)
	rule allocL(I:Int, V:FbVarDecl Vs:FbVarDeclList) => allocB(I, V) ~> allocL(I, Vs)       [structural]
	rule <k> allocL(I:Int, .FbVarDeclList) => . ...</k>     [structural]

	// allocate memory for input (output, in_out, temp, internal) variable
	syntax KItem ::= allocB(Int, FbVarDecl)
	// input
	rule allocB(I:Int, VAR_INPUT V:InputDeclaration Vs:InputDeclarationList END_VAR)
			=> allocC(I, VAR_INPUT V Vs END_VAR )       [structural]

	rule allocB(I:Int, VAR_INPUT RETAIN V:InputDeclaration Vs:InputDeclarationList END_VAR)
			=> allocC(I, VAR_INPUT RETAIN V Vs END_VAR )        [structural]

	rule allocB(I:Int, VAR_INPUT NON_RETAIN V:InputDeclaration Vs:InputDeclarationList END_VAR)
			=> allocC(I, VAR_INPUT NON_RETAIN V Vs END_VAR )        [structural]

	// output
	rule allocB(I:Int, VAR_OUTPUT V:VarInitDecl Vs:VarInitDeclList END_VAR)
			=> allocC(I, VAR_OUTPUT V Vs END_VAR )      [structural]

	rule allocB(I:Int, VAR_OUTPUT RETAIN V:VarInitDecl Vs:VarInitDeclList END_VAR)
			=> allocC(I, VAR_OUTPUT RETAIN V Vs END_VAR )       [structural]

	rule allocB(I:Int, VAR_OUTPUT NON_RETAIN V:VarInitDecl Vs:VarInitDeclList END_VAR)
			=> allocC(I, VAR_OUTPUT NON_RETAIN V Vs END_VAR )       [structural]

	// in_out
	rule allocB(I:Int, VAR_IN_OUT V:VarDeclaration Vs:VarDeclarationList END_VAR)
			=> allocC(I, VAR_IN_OUT V Vs END_VAR)       [structural]

	// temp
	rule allocB(I:Int, VAR_TEMP V:TempVarDecl Vs:TempVarDeclsList END_VAR)
			=> storeTemp(I, V) ~> allocB(I, VAR_TEMP Vs END_VAR)        [structural]
	rule allocB(I:Int, VAR_TEMP .TempVarDeclsList END_VAR) => .         [structural]

	// internal
	rule allocB(I:Int, VAR V:VarInitDecl Vs:VarInitDeclList END_VAR)
			=> storeInte(I, V, 0, 0) ~> allocB(I, VAR Vs END_VAR)       [structural]
	rule allocB(I:Int, VAR .VarInitDeclList END_VAR) => .               [structural]

	rule allocB(I:Int, VAR CONSTANT V:VarInitDecl Vs:VarInitDeclList END_VAR)
			=> storeInte(I, V, 1, 0) ~> allocB(I, VAR CONSTANT Vs END_VAR)      [structural]
	rule allocB(I:Int, VAR CONSTANT .VarInitDeclList END_VAR) => .              [structural]

	rule allocB(I:Int, VAR RETAIN V:VarInitDecl Vs:VarInitDeclList END_VAR)
			=> storeInte(I, V, 0, 1) ~> allocB(I, VAR RETAIN Vs END_VAR)        [structural]
	rule allocB(I:Int, VAR RETAIN .VarInitDeclList END_VAR) => .                [structural]

	rule allocB(I:Int, VAR NON_RETAIN V:VarInitDecl Vs:VarInitDeclList END_VAR)
			=> storeInte(I, V, 0, 0) ~> allocB(I, VAR NON_RETAIN Vs END_VAR)    [structural]
	rule allocB(I:Int, VAR NON_RETAIN .VarInitDeclList END_VAR) => .            [structural]


	syntax Catg ::= "Input"
				  | "Output"
				  | "InOut"
				  | "Temp"
				  | "Internal"
				  | "FcVar"
	// stroe variables
	// store input variable
	syntax KItem ::= storeIn(Int, InputDeclaration, Int)
	rule storeIn(I:Int, VI:VarInitDecl , J:Int) => storeIn1(I, VI, J)           [structural]
	// 有初值
	syntax KItem ::= storeIn1(Int, VarInitDecl, Int)
	rule <k> storeIn1(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName := C:Constant ;, F:Int)
			=> storeIn1(I, Xs : ET := C ;, F)
			...
		 </k>
		 <ins>
			<iEnv> IEnv:Map (. => X |-> L) </iEnv>
			<iId> I </iId>
			...
		 </ins>
		 <nLoc> L => L +Int 1 </nLoc>
		 <store> Store:Map (. => L |-> toVal(C)) </store>
		 <type> Type:Map (. => L |-> ET) </type>
		 <catg> Catg:Map (. => L |-> Input) </catg>
		 <cnst> Cnst:Map (. => L |-> 0) </cnst>
		 <rete> Rete:Map (. => L |-> F) </rete>
		 // ltlmc only
		 <state> State:Map (. => NS ::: X |-> L) ...</state>
		 <nameSpace> NS:VarInstance </nameSpace>        [structural]
	rule storeIn1(I:Int, .Var1List : _:ElementaryTypeName := _;, _) => .        [structural]
	// 无初值
	rule <k> storeIn1(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName ;, F:Int)
			=> storeIn1(I, Xs : ET ;, F)
			...
		 </k>
		 <ins>
			<iEnv> IEnv:Map (. => X |-> L) </iEnv>
			<iId> I </iId>
			...
		 </ins>
		 <nLoc> L => L +Int 1 </nLoc>
		 <store> Store:Map (. => L |-> default(ET)) </store>
		 <type> Type:Map (. => L |-> ET) </type>
		 <catg> Catg:Map (. => L |-> Input) </catg>
		 <cnst> Cnst:Map (. => L |-> 0) </cnst>
		 <rete> Rete:Map (. => L |-> F) </rete>
		 // ltlmc only
		 <state> State:Map (. => NS ::: X |-> L) ...</state>
		 <nameSpace> NS:VarInstance </nameSpace>        [structural]
	rule storeIn1(I:Int, .Var1List : _:ElementaryTypeName ;, _) => .        [structural]

	syntax KItem ::= "@restoreNameSpace"
	rule <k> @restoreNameSpace => . ...</k>
		 <nameSpace> NS:VarInstance ::: V:ID => NS </nameSpace>     [structural]

	// 未初始化
	rule <k> storeIn1(I:Int, X:ID , Xs:Var1List : Name:ID ;, F:Int)
			=> allocL(J, Vars) ~> @restoreNameSpace ~> storeIn1(I, Xs : Name ;, F)
			...
		 </k>
		 (.Bag =>
			<ins>
				<iEnv> .Map </iEnv>
				<iIns> .Map </iIns>
				<iType> Name </iType>
				<iId> J </iId>
			</ins>
		 )
		 <nId> J => J +Int 1 </nId>
		 <ins>
			<iId> I </iId>
			<iIns> IIns:Map (. => X |-> J) </iIns>
			...
		 </ins>
		 <pou>
		    <pName> Name </pName>
		    <pVars> Vars:FbVarDeclList </pVars>
		    ...
		 </pou>
		 // ltlmc only
		 <nameSpace> NS => NS ::: X </nameSpace>            [structural]
	rule storeIn1(I:Int, .Var1List : _:FunctionBlockTypeName ;, _) => .     [structural]
	// todo: FbNameDecl ";"
	// 初始化
	// todo: BOOL R_EDGE
	// todo: BOOL F_EDGE

	// store output variable
	syntax KItem ::= storeOut(Int, VarInitDecl, Int)

	// 带初值
	rule <k> storeOut(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName := C:Constant ;, F:Int )
			=> storeOut(I, Xs : ET := C ;, F )
			...
		 </k>
		 <ins>
			<iEnv> IEnv:Map (. => X |-> L) </iEnv>
			<iId> I </iId>
			...
		 </ins>
		 <nLoc> L => L +Int 1 </nLoc>
		 <store> Store:Map (. => L |-> toVal(C)) </store>
		 <type> Type:Map (. => L |-> ET) </type>
		 <catg> Catg:Map (. => L |-> Output) </catg>
		 <cnst> Cnst:Map (. => L |-> 0) </cnst>
		 <rete> Rete:Map (. => L |-> F) </rete>
		 // ltlmc only
		 <state> State:Map (. => NS ::: X |-> L) ...</state>
         <nameSpace> NS:VarInstance </nameSpace>            [structural]
	rule storeOut(I:Int, .Var1List : _:ElementaryTypeName := _;, _) => .    [structural]
	// 不带初值
	rule <k> storeOut(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName ;, F:Int )
			=> storeOut(I, Xs : ET ;, F )
			...
		 </k>
		 <ins>
			<iEnv> IEnv:Map (. => X |-> L) </iEnv>
			<iId> I </iId>
			...
		 </ins>
		 <nLoc> L => L +Int 1 </nLoc>
		 <store> Store:Map (. => L |-> default(ET)) </store>
		 <type> Type:Map (. => L |-> ET) </type>
		 <catg> Catg:Map (. => L |-> Output) </catg>
		 <cnst> Cnst:Map (. => L |-> 0) </cnst>
		 <rete> Rete:Map (. => L |-> F) </rete>
		 // ltlmc only
		 <state> State:Map (. => NS ::: X |-> L) ...</state>
         <nameSpace> NS:VarInstance </nameSpace>        [structural]
	rule storeOut(I:Int, .Var1List : ET:ElementaryTypeName ;, F:Int ) => .      [structural]
	// FbNameDecl ";"
	// 未初始化
	rule <k> storeOut(I:Int, X:ID , Xs:Var1List : Name:ID ;, F:Int )
         	=> allocL(J, Vars) ~> @restoreNameSpace ~> storeOut(I, Xs : Name ;, F )
        	...
         </k>
		 (.Bag =>
			<ins>
				<iEnv> .Map </iEnv>
				<iIns> .Map </iIns>
				<iType> Name </iType>
				<iId> J </iId>
			</ins>
		 )
		 <nId> J => J +Int 1 </nId>
		 <ins>
			<iId> I </iId>
			<iIns> IIns:Map (. => X |-> J) </iIns>
			...
		 </ins>
		 <pou>
		    <pName> Name </pName>
		    <pVars> Vars:FbVarDeclList </pVars>
		    ...
		 </pou>
		 // ltlmc only
		 <nameSpace> NS => NS ::: X </nameSpace>            [structural]
	rule storeOut(I:Int, .Var1List : _:FunctionBlockTypeName ;, _) => .     [structural]
	// todo: FbNameDecl ";"
	// 初始化

	// store in_out variable
	syntax KItem ::= storeIO(Int, VarDeclaration)
	// TempVarDecl
	rule <k> storeIO(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName ;)
			=> storeIO(I, Xs : ET ;)
			...
		 </k>
		 <ins>
			<iEnv> IEnv:Map (. => X |-> L) </iEnv>
			<iId> I </iId>
			...
		 </ins>
		 <nLoc> L => L +Int 1 </nLoc>
		 <store> Store:Map (. => L |-> default(ET)) </store>
		 <type> Type:Map (. => L |-> ET) </type>
		 <catg> Catg:Map (. => L |-> InOut) </catg>
		 <cnst> Cnst:Map (. => L |-> 0) </cnst>
		 <rete> Rete:Map (. => L |-> 0) </rete>
		 // ltlmc only
		 <state> State:Map (. => NS ::: X |-> L) ...</state>
         <nameSpace> NS:VarInstance </nameSpace>            [structural]
	rule storeIO(I:Int, .Var1List : ET:ElementaryTypeName ;) => .       [structural]
	// todo: Var1List ":" IntegerTypeName "(" SignedInteger ".." SignedInteger ")" ";"
	// todo: Var1List ":" "(" EnumeratedValueList ")" ";"
	// FbNameDecl ";"
	// 未初始化
	rule <k> storeIO(I:Int, X:ID , Xs:Var1List : Name:ID ;)
			=> allocL(J, Vars) ~> @restoreNameSpace ~> storeIO(I, Xs : Name ;)
			...
		 </k>
		 (.Bag =>
			<ins>
				<iEnv> .Map </iEnv>
				<iIns> .Map </iIns>
				<iType> Name </iType>
				<iId> J </iId>
			</ins>
		 )
		 <nId> J => J +Int 1 </nId>
		 <ins>
			<iId> I </iId>
			<iIns> IIns:Map (. => X |-> J) </iIns>
			...
		 </ins>
		 <pou>
		    <pName> Name </pName>
		    <pVars> Vars:FbVarDeclList </pVars>
		    ...
		 </pou>
		 // ltlmc only
		 <nameSpace> NS => NS ::: X </nameSpace>        [structural]
	rule storeIO(I:Int, .Var1List : _:FunctionBlockTypeName ;) => .     [structural]
	// todo: 初始化

	// store func_var variable
	// todo: SubrangeSpecInit, EnumeratedSpecInit
	syntax KItem ::= storeFC(Int, Var1InitDecl, Int)
	// 有初始值
	rule <k> storeFC(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName := C:Constant ;, F:Int)
			=> storeFC(I, Xs : ET := C ;, F)
			...
		 </k>
		 <ins>
			<iEnv> IEnv:Map (. => X |-> L) </iEnv>
			<iId> I </iId>
			...
		 </ins>
		 <nLoc> L => L +Int 1 </nLoc>
		 <store> Store:Map (. => L |-> toVal(C)) </store>
		 <type> Type:Map (. => L |-> ET) </type>
		 <catg> Catg:Map (. => L |-> FcVar) </catg>
		 <cnst> Cnst:Map (. => L |-> F) </cnst>
		 <rete> Rete:Map (. => L |-> 0) </rete>
		 // ltlmc only
		 <state> State:Map (. => NS ::: X |-> L) ...</state>
         <nameSpace> NS:VarInstance </nameSpace>        [structural]
	rule storeFC(I:Int, .Var1List : _ := _ ;, _) => .   [structural]
	// 无初始值
	rule <k> storeFC(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName ;, F:Int)
			=> storeFC(I, Xs : ET ;, F)
			...
		 </k>
		 <ins>
			<iEnv> IEnv:Map (. => X |-> L) </iEnv>
			<iId> I </iId>
			...
		 </ins>
		 <nLoc> L => L +Int 1 </nLoc>
		 <store> Store:Map (. => L |-> default(ET)) </store>
		 <type> Type:Map (. => L |-> ET) </type>
		 <catg> Catg:Map (. => L |-> FcVar) </catg>
		 <cnst> Cnst:Map (. => L |-> F) </cnst>
		 <rete> Rete:Map (. => L |-> 0) </rete>
		 // ltlmc only
		 <state> State:Map (. => NS ::: X |-> L) ...</state>
         <nameSpace> NS:VarInstance </nameSpace>        [structural]
	rule storeFC(I:Int, .Var1List : _:ElementaryTypeName ;, _) => .     [structural]

	// store temp variable
	syntax KItem ::= storeTemp(Int, TempVarDecl)
	rule <k> storeTemp(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName ;)
			=> storeTemp(I, Xs : ET ;)
			...
		 </k>
		 <ins>
			<iEnv> IEnv:Map (. => X |-> L) </iEnv>
			<iId> I </iId>
			...
		 </ins>
		 <nLoc> L => L +Int 1 </nLoc>
		 <store> Store:Map (. => L |-> default(ET)) </store>
		 <type> Type:Map (. => L |-> ET) </type>
		 <catg> Catg:Map (. => L |-> Temp) </catg>
		 <cnst> Cnst:Map (. => L |-> 0) </cnst>
		 <rete> Rete:Map (. => L |-> 0) </rete>
		 // ltlmc only
		 <state> State:Map (. => NS ::: X |-> L) ...</state>
         <nameSpace> NS:VarInstance </nameSpace>        [structural]
	rule storeTemp(I:Int, .Var1List : _ ;) => .         [structural]
	// todo: Var1List ":" IntegerTypeName "(" SignedInteger ".." SignedInteger ")" ";"
	// todo: Var1List ":" "(" EnumeratedValueList ")" ";"

	// store internal variable
	syntax KItem ::= storeInte(Int, VarInitDecl, Int, Int)
	// 带初始值
	rule <k> storeInte(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName := C:Constant ;, F1:Int, F2:Int)
			=> storeInte(I, Xs : ET := C ;, F1, F2)
			...
		 </k>
		 <ins>
			<iEnv> IEnv:Map (. => X |-> L) </iEnv>
			<iId> I </iId>
			...
		 </ins>
		 <nLoc> L => L +Int 1 </nLoc>
		 <store> Store:Map (. => L |-> toVal(C)) </store>
		 <type> Type:Map (. => L |-> ET) </type>
		 <catg> Catg:Map (. => L |-> Internal) </catg>
		 <cnst> Cnst:Map (. => L |-> F1) </cnst>
		 <rete> Rete:Map (. => L |-> F2) </rete>
		 // ltlmc only
		 <state> State:Map (. => NS ::: X |-> L) ...</state>
         <nameSpace> NS:VarInstance </nameSpace>            [structural]
	rule storeInte(I:Int, .Var1List : _ := C:Constant ;, _, _) => .     [structural]
	// 不带初值
	rule <k> storeInte(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName ;, F1:Int, F2:Int)
			=> storeInte(I, Xs : ET ;, F1, F2)
			...
		 </k>
		 <ins>
			<iEnv> IEnv:Map (. => X |-> L) </iEnv>
			<iId> I </iId>
			...
		 </ins>
		 <nLoc> L => L +Int 1 </nLoc>
		 <store> Store:Map (. => L |-> default(ET)) </store>
		 <type> Type:Map (. => L |-> ET) </type>
		 <catg> Catg:Map (. => L |-> Internal) </catg>
		 <cnst> Cnst:Map (. => L |-> F1) </cnst>
		 <rete> Rete:Map (. => L |-> F2) </rete>
		 // ltlmc only
		 <state> State:Map (. => NS ::: X |-> L) ...</state>
         <nameSpace> NS:VarInstance </nameSpace>            [structural]
	rule storeInte(I:Int, .Var1List : _:ElementaryTypeName ;, _, _) => .        [structural]
	// todo: Var1List ":" SubrangeSpecInit ";"
	// todo: Var1List ":" EnumeratedSpecInit ";"
	// todo: FbNameDecl ";"
	// 未初始化
	rule <k> storeInte(I:Int, X:ID , Xs:Var1List : Name:ID ;, F1:Int, F2:Int)
			=>  allocL(J, Vars) ~> @restoreNameSpace ~> storeInte(I, Xs : Name ;, F1, F2)
			...
		 </k>
		( .Bag =>
			<ins>
				<iEnv> .Map </iEnv>
				<iIns> .Map </iIns>
				<iType> Name </iType>
				<iId> J </iId>
			</ins>
		)
		 <nId> J => J +Int 1 </nId>
		 <ins>
		    <iId> I </iId>
			<iIns> IIns:Map (. => X |-> J) </iIns>
			...
		 </ins>
		 <pou>
			<pName> Name </pName>
			<pVars> Vars:FbVarDeclList </pVars>
			...
		 </pou>
		 // ltlmc only
		 <nameSpace> NS => NS ::: X </nameSpace>        [structural]
	rule storeInte(I:Int, .Var1List : _:FunctionBlockTypeName ;, _, _) => .     [structural]
	// todo: 初始化


	// helpers for store
	syntax KItem ::= toVal( Constant )              [function]
	// bool
	rule toVal('Lit('True(.KList))) => true             [structural]
	rule toVal('Lit('False(.KList))) => false           [structural]
	// Numeric
	// integer
	rule toVal('Lit('Int(X:IntegerLiteral))) => toInt(X)        [structural]
	rule toVal('Lit('SharpInt(T:IntegerTypeName,, X:IntegerLiteral))) => toInt(X)       [structural]
	syntax KItem ::= toInt(IntegerLiteral)          [function]
	rule toInt('Bina(X)) => binToInt(substrString(#tokenToString(X), 2, lengthString(#tokenToString(X))))   [structural]
	rule toInt('Octa(X)) => octToInt(substrString(#tokenToString(X), 2, lengthString(#tokenToString(X))))   [structural]
	rule toInt('Deci(X)) => String2Int(#tokenToString(X))       [structural]
	rule toInt('Hexa(X)) => hexToInt(substrString(#tokenToString(X), 3, lengthString(#tokenToString(X))))   [structural]
	// real
	rule toVal('Lit('Real(X))) => X     [structural]
	rule toVal('Lit('SharpReal(RT:RealTypeName,, X:Float))) => X        [structural]
	// todo: signed integer


	// 16进制
	syntax KItem ::= hexToInt (String)                                                  [function]
	rule hexToInt(Str:String) => hexToInt (0, Str)

	syntax KItem ::= hexToInt (Int, String)                                             [function]
	rule hexToInt(I:Int, Str:String) => hexToInt( I, retainHead(Str, 1), trimHead(Str, 1) )
    when Str =/=String ""        [structural]
    rule hexToInt(I:Int, "") => I       [structural]

    syntax KItem ::=  hexToInt (
                    Int,    //upper digits already converted
                    String, //one char - current digit
                    String  //next digits
                  )
                  [function]
    rule hexToInt(I:Int, Digit:String, Str:String)
         => hexToInt( (I *Int 16) +Int hexDigitToInt(Digit), Str )      [structural]

	syntax KItem ::= hexDigitToInt ( String )                             [function]
    rule hexDigitToInt(Digit:String) => ordChar(Digit) -Int ordChar("0")
    when        (ordChar(Digit) >=Int ordChar("0"))
        andBool (ordChar(Digit) <=Int ordChar("9"))     [structural]
    rule hexDigitToInt(Digit:String) => ordChar(Digit) -Int ordChar("A") +Int 10
    when        (ordChar(Digit) >=Int ordChar("A"))
        andBool (ordChar(Digit) <=Int ordChar("F"))     [structural]

	// 8进制
	syntax KItem ::= octToInt ( String )                                   [function]
    rule octToInt(Str:String) => octToInt(0, Str)       [structural]
    syntax KItem ::= octToInt ( Int, String )                              [function]
    rule octToInt(I:Int, Str:String) => octToInt( I, retainHead(Str, 1), trimHead(Str, 1) )
    when
        Str =/=String ""        [structural]
    rule octToInt(I:Int, "") => I       [structural]

    syntax KItem ::=  octToInt (
                    Int,    //upper digits already converted
                    String, //one char - current digit
                    String  //next digits
                  )
                  [function]
    rule octToInt(I:Int, Digit:String, Str:String) =>
        octToInt( (I *Int 8) +Int octDigitToInt(Digit), Str )               [structural]

    syntax KItem ::= octDigitToInt ( String )                              [function]
    rule octDigitToInt(Digit:String) => hexDigitToInt(Digit)            [structural]

	// 2进制
	syntax KItem ::= binToInt (String)                                      [function]
	rule binToInt(Str:String) => binToInt (0, Str)          [structural]

	syntax KItem ::= binToInt (Int, String)                                 [function]
	rule binToInt(I:Int, Str:String) => binToInt (I, retainHead(Str, 1), trimHead(Str, 1))
	when
		Str =/=String ""            [structural]
	rule binToInt(I:Int, "") => I           [structural]

	syntax KItem ::= binToInt (
					Int,    // upper digits already converted
					String, // one char - current digit
					String  // next digits
				  )                                                         [function]
	rule binToInt(I:Int, Digit:String, Str:String) =>
		 binToInt((I *Int 2) +Int binDigitToInt(Digit), Str)        [structural]
	syntax KItem ::= binDigitToInt (String)                                 [function]
	rule binDigitToInt(Digit:String)
		=> #if Digit ==String "1"
		     #then 1
		     #else #if  Digit ==String "0"
		             #then 0
		             #else .
		           #fi
		   #fi      [structural]
	// helpers of constant
	//@Retain the first Count chars in the string
	syntax String ::= retainHead ( String, Int )                         [function]
	rule retainHead(Str:String, Count:Int) => substrString(Str, 0, Count)   [structural]

	//@Retain the last Count chars in the string
	syntax String ::= retainTail ( String, Int )                         [function]
	rule retainTail(Str:String, Count:Int) => substrString(Str, lengthString(Str) -Int Count, lengthString(Str))    [structural]

	//@Trim the first Count chars in the string
	syntax String ::= trimHead ( String, Int )                           [function]
	rule trimHead(Str:String, Count:Int) => substrString(Str, Count, lengthString(Str))     [structural]

	//@Trim the last Count chars in the string
	syntax String ::= trimTail ( String, Int )                           [function]
	rule trimTail(Str:String, Count:Int) => substrString(Str, 0, lengthString(Str) -Int Count)      [structural]

	syntax String ::= lastChar ( String )                                [function]
	rule lastChar(Str:String) => retainTail(Str, 1)     [structural]


	// data types
	syntax RawVal ::= Int | Float | Bool
	syntax TypedVal ::=  RawVal "::" ElementaryTypeName

	syntax KItem ::= subtype(ElementaryTypeName, ElementaryTypeName)        [function]
	rule subtype( ET:ElementaryTypeName, ET ) => true                       [structural]
	rule subtype( SINT, ET:ElementaryTypeName ) => (ET ==K INT) orBool (ET ==K DINT) orBool (ET ==K LINT) orBool (ET ==K REAL) orBool (ET ==K LREAL)
         when ET =/=K SINT                                                  [structural]
	rule subtype( INT, ET:ElementaryTypeName ) => (ET ==K DINT) orBool (ET ==K LINT) orBool (ET ==K REAL) orBool (ET ==K LREAL)
         when ET =/=K INT                                                   [structural]
	rule subtype( DINT, ET:ElementaryTypeName ) => (ET ==K LINT) orBool (ET ==K REAL) orBool (ET ==K LREAL)
         when ET =/=K SINT                                                  [structural]
	rule subtype( LINT, ET:ElementaryTypeName ) => (ET ==K REAL) orBool (ET ==K LREAL)
         when ET =/=K LINT                                                  [structural]
	rule subtype( USINT, ET:ElementaryTypeName ) => (ET ==K UINT) orBool (ET ==K UDINT) orBool (ET ==K ULINT) orBool (ET ==K REAL) orBool (ET ==K LREAL)
         when ET =/=K USINT                                                 [structural]
	rule subtype( UINT, ET:ElementaryTypeName ) => (ET ==K UDINT) orBool (ET ==K ULINT) orBool (ET ==K REAL) orBool (ET ==K LREAL)
         when ET =/=K UINT                                                  [structural]
	rule subtype( UDINT, ET:ElementaryTypeName ) => (ET ==K ULINT) orBool (ET ==K REAL) orBool (ET ==K LREAL)
         when ET =/=K UDINT                                                 [structural]
	rule subtype( ULINT, ET:ElementaryTypeName ) => (ET ==K REAL) orBool (ET ==K LREAL)
         when ET =/=K ULINT                                                 [structural]
	rule subtype( REAL, ET:ElementaryTypeName ) => (ET ==K LREAL)
         when ET =/=K REAL                                                  [structural]

	syntax KItem ::= default ( ElementaryTypeName )         [function]
	rule default(IT:IntegerTypeName) => 0           [structural]
	rule default(RT:RealTypeName) => 0.0            [structural]
	rule default(BOOL) => false                     [structural]


	syntax KResult ::= TypedVal | ElementaryTypeName | Catg

	// E: expression
	// E.1 constant
	// E.1.1 bool
	rule 'PriConstant('Lit('True(.KList))) => true :: BOOL      [structural]
	rule 'PriConstant('Lit('False(.KList))) => false :: BOOL    [structural]
	// todo: E.1.2 bitstring
	// E.1.3 numeric
	rule 'PriConstant('Lit('Int(IL:IntegerLiteral))) => toInt(IL) :: INT            [structural]
	rule 'PriConstant('Lit('SharpInt(IT:IntegerTypeName,, IL:IntegerLiteral))) => toInt(IL) :: IT       [structural]

	rule 'PriConstant('Lit('Real(RL:Float))) => RL :: REAL      [structural]
	rule 'PriConstant('Lit('SharpReal(RT:RealTypeName,, RL:Float))) => RL :: RT     [structural]
	// todo: signinteger

	// E.2 variable look up
	// 'PriVariable
	rule <k> 'PriVariable('Simp(X:ID)) => V :: T ...</k>
		 <env> X |-> L ...</env>
		 <store> L |-> V ...</store>
		 <type> L |-> T ... </type>     [structural]
	rule <k> 'PriVariable('Fbs(X1:ID,, X2:ID)) => V :: T ...</k>
		 <pid> I </pid>
		 <debug> _ => I </debug>
		 <ins>
			<iId> I </iId>
			<iIns> X1 |-> J ...</iIns>
			...
		 </ins>
		 <ins>
		    <iId> J </iId>
		    <iEnv> X2 |-> L ...</iEnv>
		    ...
		 </ins>
		 <store> L |-> V ...</store>
		 <type> L |-> T ...</type>      [structural]
	rule 'Bracket(E:Expression) => E        [structural]

	// todo: E.3 'PriFcInvocation
	rule <k> 'PriFcInvocation(FN:FunctionName () ) ~> Rest:K
			=> initL(J, Vars) ~> executeL(Stmts) ~> popStack(J)
		 </k>
		 <stack>... . => ListItem(stackFrame(Rest, I)) </stack>
		 <env> _ => IEnv </env>
		 <pid> I => J </pid>
		 <ins>
		    <iId> J </iId>
		    <iType> FN </iType>
		    <iEnv> IEnv </iEnv>
		    ...
		 </ins>
		 <pou>
			<pName> FN </pName>
			<pStmts> Stmts </pStmts>
			<pVars> Vars </pVars>
			...
		 </pou>     [structural]
	// todo: ParamAssignmentNonformalList
	rule <k> 'PriFcInvocation(FN:FunctionName (PANs:ParamAssignmentNonformalList) ) ~> Rest:K
			=> initL(J, Vars) ~> "here" ~> executeL(Stmts) ~> popStack(J)
		 </k>
		 <stack>... . => ListItem(stackFrame(Rest, I)) </stack>
		 <env> _ => IEnv </env>
		 <pid> I => J </pid>
		 <ins>
		    <iId> J </iId>
		    <iType> FN </iType>
		    <iEnv> IEnv </iEnv>
		    ...
		 </ins>
		 <pou>
			<pName> FN </pName>
			<pStmts> Stmts </pStmts>
			<pVars> Vars </pVars>
			...
		 </pou> [structural]
	rule <k> 'PriFcInvocation(FN:FunctionName (PAs:ParamAssignmentFormalList) ) ~> Rest:K
			=> initL(J, Vars) ~> paramAssignInL(PAs) ~> switchContext(J) ~> executeL(Stmts) ~> paramAssignOutL(PAs) ~> popStack(J)
		 </k>
		 <stack>... . => ListItem(stackFrame(Rest, I)) </stack>
		 <pid> I => J </pid>
		 <ins>
		    <iId> J </iId>
		    <iType> FN </iType>
		    ...
		 </ins>
		 <pou>
			<pName> FN </pName>
			<pStmts> Stmts </pStmts>
			<pVars> Vars </pVars>
			...
		 </pou> [structural]

	// helper of 'PriFcInvocation
	syntax KItem ::= stackFrame( K, Int )

	syntax KItem ::= popStack( Int )
	rule <k> popStack( J:Int) => V::T ~> Rest ...</k>
		 <stack> ... ListItem(stackFrame(Rest, I)) => . </stack>
		 <env> _ => IEnv </env>
		 <pid> J => I </pid>
		 <ins>
			<iId> I </iId>
			<iEnv> IEnv </iEnv>
			...
		 </ins>
		 <ins>
		    <iId> J </iId>
			<iType> FN </iType>
			<iEnv> FN |-> L ... </iEnv>
			...
		 </ins>
		 <store> L |-> V ...</store>
		 <type> L |-> T ...</type>      [structural]
	syntax KItem ::= initL(Int, FcVarDeclsList)
	rule initL(I:Int, V:FcVarDecl Vs:FcVarDeclsList) => initC(I, V) ~> initL(I, Vs) [structural]
	rule initL(I:Int, .FcVarDeclsList) => .     [structural]

	syntax KItem ::= initC(Int, FcVarDecl)
	// input
	rule initC(I:Int, VAR_INPUT V:InputDeclaration Vs:InputDeclarationList END_VAR)
			=> initIn(I, V) ~> initC(I:Int, VAR_INPUT Vs END_VAR)       [structural]
	rule initC(I:Int, VAR_INPUT .InputDeclarationList END_VAR) => .     [structural]

	rule initC(I:Int, VAR_INPUT RETAIN V:InputDeclaration Vs:InputDeclarationList END_VAR)
			=> initIn(I, V) ~> initC(I:Int, VAR_INPUT RETAIN Vs END_VAR)        [structural]
	rule initC(I:Int, VAR_INPUT RETAIN .InputDeclarationList END_VAR) => .      [structural]

	rule initC(I:Int, VAR_INPUT NON_RETAIN V:InputDeclaration Vs:InputDeclarationList END_VAR)
			=> initIn(I, V) ~> initC(I:Int, VAR_INPUT NON_RETAIN Vs END_VAR)        [structural]
	rule initC(I:Int, VAR_INPUT NON_RETAIN .InputDeclarationList END_VAR) => .      [structural]

	// output
	rule initC(I:Int, VAR_OUTPUT V:VarInitDecl Vs:VarInitDeclList END_VAR)
			=> initOut(I, V) ~> initC(I:Int, VAR_OUTPUT Vs END_VAR)     [structural]
	rule initC(I:Int, VAR_OUTPUT .VarInitDeclList END_VAR) => .         [structural]

	rule initC(I:Int, VAR_OUTPUT RETAIN V:VarInitDecl Vs:VarInitDeclList END_VAR)
			=> initOut(I, V) ~> initC(I:Int, VAR_OUTPUT RETAIN Vs END_VAR)      [structural]
	rule initC(I:Int, VAR_OUTPUT RETAIN .VarInitDeclList END_VAR) => .          [structural]

	rule initC(I:Int, VAR_OUTPUT NON_RETAIN V:VarInitDecl Vs:VarInitDeclList END_VAR)
			=> initOut(I, V) ~> initC(I:Int, VAR_OUTPUT NON_RETAIN Vs END_VAR)  [structural]
	rule initC(I:Int, VAR_OUTPUT NON_RETAIN .VarInitDeclList END_VAR) => .      [structural]

	// in_out
	rule initC(I:Int, VAR_IN_OUT V:VarDeclaration Vs:VarDeclarationList END_VAR)
			=> initIO(I, V) ~> initC(I:Int, VAR_IN_OUT Vs END_VAR)          [structural]
	rule initC(I:Int, VAR_IN_OUT .VarDeclarationList END_VAR) => .          [structural]

	// func
	rule initC(I:Int, VAR V:Var1InitDecl Vs:Var1InitDeclList END_VAR)
			=> initFC(I, V) ~> initC(I:Int, VAR Vs:Var1InitDeclList END_VAR)        [structural]
	rule initC(I:Int, VAR .Var1InitDeclList END_VAR) => .                       [structural]
	rule initC(I:Int, VAR CONSTANT V:Var1InitDecl Vs:Var1InitDeclList END_VAR)
			=> initFC(I, V) ~> initC(I:Int, VAR CONSTANT Vs:Var1InitDeclList END_VAR)   [structural]
	rule initC(I:Int, VAR CONSTANT .Var1InitDeclList END_VAR) => .              [structural]

	syntax KItem ::= initIn(Int, InputDeclaration)
	rule initIn(I:Int, VI:VarInitDecl) => initIn1(I, VI)        [structural]
	// 有初值
	syntax KItem ::= initIn1(Int, VarInitDecl)
	rule <k> initIn1(I:Int, (X:ID , Xs:Var1List => Xs) : ET:ElementaryTypeName := C:Constant ;)
			...
		 </k>
		 <ins>
			<iId> I </iId>
			<iEnv> X |-> L ...</iEnv>
			...
		 </ins>
		 <store> L |-> (_ => toVal(C)) ...</store>      [structural]
	rule initIn1(I:Int, .Var1List : _:ElementaryTypeName := _;) => .        [structural]
	// 无初值
	rule <k> initIn1(I:Int, (X:ID , Xs:Var1List => Xs) : ET:ElementaryTypeName ;)
			...
		 </k>
		 <ins>
			<iId> I </iId>
			<iEnv> X |-> L ...</iEnv>
			...
		 </ins>
		 <store> L |-> (_ => default(ET)) ...</store>       [structural]
	rule initIn1(I:Int, .Var1List : _:ElementaryTypeName ;) => .        [structural]

	syntax KItem ::= initOut(Int, VarInitDecl)
	// 带初值
	rule <k> initOut(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName := C:Constant ; )
			=> initOut(I, Xs : ET := C ;)
			...
		 </k>
		 <ins>
			<iId> I </iId>
			<iEnv> X |-> L ...</iEnv>
			...
		 </ins>
		 <store> L |-> (_ => toVal(C)) ...</store>          [structural]
	rule initOut(I:Int, .Var1List : _:ElementaryTypeName := _;) => .        [structural]
	// 不带初值
	rule <k> initOut(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName ;)
			=> initOut(I, Xs : ET ; )
			...
		 </k>
		 <ins>
			<iId> I </iId>
			<iEnv> X |-> L ...</iEnv>
			...
		 </ins>
		 <store> L |-> (_ => default(ET)) ...</store>               [structural]
	rule initOut(I:Int, .Var1List : ET:ElementaryTypeName ;) => .   [structural]

	syntax KItem ::= initIO(Int, VarDeclaration)
	rule <k> initIO(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName ;)
			=> initIO(I, Xs : ET ;)
			...
		 </k>
		 <ins>
			<iId> I </iId>
			<iEnv> X |-> L ...</iEnv>
			...
		 </ins>
		 <store> L |-> (_ => default(ET)) ...</store>               [structural]
	rule initIO(I:Int, .Var1List : ET:ElementaryTypeName ;) => .    [structural]

	syntax KItem ::= initFC(Int, Var1InitDecl)
	// 有初始值
	rule <k> initFC(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName := C:Constant ;)
			=> initFC(I, Xs : ET := C ;)
			...
		 </k>
		 <ins>
			<iId> I </iId>
			<iEnv> X |-> L ...</iEnv>
			...
		 </ins>
		 <store> L |-> (_ => toVal(C)) ...</store>      [structural]
	rule initFC(I:Int, .Var1List : _ := _ ;) => .       [structural]
	// 无初始值
	rule <k> initFC(I:Int, X:ID , Xs:Var1List : ET:ElementaryTypeName ;)
			=> initFC(I, Xs : ET ;)
			...
		 </k>
		 <ins>
			<iId> I </iId>
			<iEnv> X |-> L ...</iEnv>
			...
		 </ins>
		 <store> L |-> (_ => default(ET)) ...</store>       [structural]
	rule initFC(I:Int, .Var1List : _:ElementaryTypeName ;) => . [structural]

	syntax KItem ::= paramAssignInL ( ParamAssignmentFormalList )
	rule paramAssignInL(PAF:ParamAssignmentFormal , PAFL:ParamAssignmentFormalList) => paramAssignIn(PAF) ~> paramAssignInL(PAFL)   [structural]
	rule paramAssignInL(.ParamAssignmentFormalList) => .    [structural]

	syntax KItem ::= paramAssignIn(ParamAssignmentFormal)
	rule paramAssignIn('ParamIns(X:ID,, E:Expression ) ) => 'AssignStmt('Simp(X),, E)       [structural]
	rule paramAssignIn('ParamOuts(_,, _)) => .      [structural]
	rule paramAssignIn('NParamOuts(_,, _)) => .     [structural]

	syntax KItem ::= paramAssignOutL(ParamAssignmentFormalList)
	rule paramAssignOutL(PAF:ParamAssignmentFormal, PAFL:ParamAssignmentFormalList) => paramAssignOut(PAF) ~> paramAssignOutL(PAFL)     [structural]
	rule paramAssignOutL(.ParamAssignmentFormalList) => .       [structural]

	syntax KItem ::= paramAssignOut(ParamAssignmentFormal)
	rule paramAssignOut('ParamIns(_,, _)) => .          [structural]
	rule <k> paramAssignOut('ParamOuts('Simp(Y:ID),, X:ID)) => . ...</k>
		 <stack> ListItem(stackFrame(Rest:K, I))  ... </stack>
		 <env> Y |-> L ...</env>
		 <store> Store:Map (L2|-> (_ => Store(L))) </store>
		 <type> L |-> T ...</type>
		 <ins>
			<iId> I </iId>
			<iEnv> X |-> L2 ...</iEnv>
			...
		 </ins>     [structural]
	rule <k> paramAssignOut('NParamOuts('Simp(Y:ID),, X:ID)) => . ...</k>
		 <stack> ListItem(stackFrame(Rest:K, I))  ... </stack>
		 <env> Y |-> L ...</env>
		 <store> Store:Map (L2|-> (_
		        => #if subtype(T, BOOL)
		             #then notBool Store(L)
		             #else ~Int Store(L)
		           #fi
		        )) </store>
		 <type> L |-> T ...</type>
		 <ins>
			<iId> I </iId>
			<iEnv> X |-> L2 ...</iEnv>
			...
		 </ins>     [structural]

	syntax KItem ::= switchContext(Int)
	rule <k> switchContext(I:Int) => . ...</k>
		 <env> _ => IEnv </env>
		 <ins>
			<iId> I </iId>
			<iEnv> IEnv </iEnv>
			...
		 </ins>     [structural]


	// E.4 expression
	rule 'Minus(F:Float :: RT:RealTypeName) => (0.0 -Float F) :: RT     [structural]
	rule 'Minus(I:Int :: IT:IntegerTypeName) => (0 -Int I) :: IT        [structural]

	rule 'Complement(B:Bool :: BOOL) => (notBool B) :: BOOL             [structural]
	rule 'Complement(I:Int :: IT:IntegerTypeName) => (~Int I) :: IT     [structural]

	rule 'Pow(I1:Int :: IT1:IntegerTypeName,, I2:Int :: IT2:IntegerTypeName) => (I1 ^Int I2) :: INT     [structural]
	rule 'Pow(F1:Float :: RT1:RealTypeName,, F2:Float :: RT2:RealTypeName) => (F1 ^Float F2) :: REAL    [structural]

	rule 'Mod(I1:Int :: IT1:IntegerTypeName,, I2:Int :: IT2:IntegerTypeName) => (I1 %Int I2) :: INT
		 when I2 =/=Int 0       [structural]
	// F % F
	rule 'Mod(F1:Float :: RT1:RealTypeName,, F2:Float :: RT2:RealTypeName) =>
		#if (F1 %Float F2) >=Float 0.0
		  #then (F1 %Float F2) :: REAL
		  #else (F1 %Float F2 +Float F2) :: REAL
		#fi     [structural]
	// I * I
	rule 'Mul(I1:Int :: IT1:IntegerTypeName,, I2:Int :: IT2:IntegerTypeName) => (I1 *Int I2) :: INT     [structural]
	// F * F
	rule 'Mul(F1:Float :: RT1:RealTypeName,, F2:Float :: RT2:RealTypeName) => (F1 *Float F2) :: REAL    [structural]

	// I / I
	rule 'Div(I1:Int :: IT1:IntegerTypeName,, I2:Int :: IT2:IntegerTypeName) => (I1 /Int I2) :: INT
		 when I2 =/=Int 0       [structural]
	// F / F
	rule 'Div(F1:Float :: RT1:RealTypeName,, F2:Float :: RT2:RealTypeName) => (F1 /Float F2) :: REAL    [structural]

	// I + I
	rule 'Add(I1:Int :: IT1:IntegerTypeName,, I2:Int :: IT2:IntegerTypeName) => (I1 +Int I2) :: INT     [structural]
	// F + F
	rule 'Add(F1:Float :: RT1:RealTypeName,, F2:Float :: RT2:RealTypeName) => (F1 +Float F2) :: REAL    [structural]

	// I - I
	rule 'Sub(I1:Int :: IT1:IntegerTypeName,, I2:Int :: IT2:IntegerTypeName) => (I1 -Int I2) :: INT     [structural]
	// I - I
	rule 'Sub(F1:Float :: RT1:RealTypeName,, F2:Float :: RT2:RealTypeName) => (F1 -Float F2) :: REAL    [structural]

	// I > I
	rule 'GT(I1:Int :: IT1:IntegerTypeName,, I2:Int :: IT2:IntegerTypeName) => (I1 >Int I2) :: BOOL     [structural]
	// F > F
	rule 'GT(F1:Float :: RT1:RealTypeName,, F2:Float :: RT2:RealTypeName) => (F1 >Float F2) :: BOOL     [structural]

	// I < I
	rule 'LT(I1:Int :: IT1:IntegerTypeName,, I2:Int :: IT2:IntegerTypeName) => (I1 <Int I2) :: BOOL     [structural]
	// F < F
	rule 'LT(F1:Float :: RT1:RealTypeName,, F2:Float :: RT2:RealTypeName) => (F1 <Float F2) :: BOOL     [structural]

	// I >= I
	rule 'GE(I1:Int :: IT1:IntegerTypeName,, I2:Int :: IT2:IntegerTypeName) => (I1 >=Int I2) :: BOOL    [structural]
	// F >= F
	rule 'GE(F1:Float :: RT1:RealTypeName,, F2:Float :: RT2:RealTypeName) => (F1 >=Float F2) :: BOOL    [structural]

	// I <= I
	rule 'LE(I1:Int :: IT1:IntegerTypeName,, I2:Int :: IT2:IntegerTypeName) => (I1 <=Int I2) :: BOOL    [structural]
	// F <= F
	rule 'LE(F1:Float :: RT1:RealTypeName,, F2:Float :: RT2:RealTypeName) => (F1 <=Float F2) :: BOOL    [structural]

	// I = I
	rule 'EQ(I1:Int :: IT1:IntegerTypeName,, I2:Int :: IT2:IntegerTypeName) => (I1 ==Int I2) :: BOOL    [structural]
	// F = F
	rule 'EQ(F1:Float :: RT1:RealTypeName,, F2:Float :: RT2:RealTypeName) => (F1 ==Float F2) :: BOOL    [structural]
	// B = B
	rule 'EQ(B1:Bool,, B2:Bool) => (B1 ==Bool B2) :: BOOL       [structural]

	// B & B
	rule 'And(B1:Bool,, B2:Bool) => (B1 andBool B2) :: BOOL     [structural]
	rule 'And(false,, _) => false :: BOOL           [structural]
	rule 'And(true,, B) => B :: BOOL            [structural]

	// B XOR B
	rule 'Xor(B1:Bool,, B2:Bool) => (B1 xorBool B2) :: BOOL     [structural]

	// B Or B
	rule 'Or(B1:Bool,, B2:Bool) => (B1 orBool B2) :: BOOL       [structural]
	rule 'Or(true,, _) => true :: BOOL      [structural]
	rule 'Or(false,, B) => B :: BOOL        [structural]
endmodule