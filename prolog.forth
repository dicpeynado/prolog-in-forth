\ Defining words
: ATOM: CREATE 0 , ;

\ Stack Definitions
\ ^ARG.STACK is used for argument pointers
\ pushed by FUNCTOR, popped by POP
DEFER PRINT.TERM

CREATE STRUCTURE.STACK	12000 ALLOT	\ structure stack
CREATE CONTROL.STACK	12000 ALLOT	\ control stack
CREATE TRAIL		2000 ALLOT	\ trail stack
CREATE ^ARG.STACK	2000 ALLOT	\ arg pointer stack

\ Prolog Machine Register
\ VALUE is multiple cfa word
\ access value by name (i.e. X vs. X @)

0 VALUE CF	\ Current Frame
0 VALUE NF	\ Next Frame
0 VALUE BF	\ Backtrack Frame
0 VALUE SS	\ Structure Stack
0 VALUE TS	\ Trail Stack

\ Register to Register Operations
: BF>CF  BF IS CF ;
: NF>CF  NF IS CF ;
: NF>BF  NF IS BF ;
: CF>NF  CF IS NF ;

\ Context Save Operations

\ :M RP>Stack ( -- )	R> NF		! ;M
:  BP>Stack ( n -- )   NF 1 cells+ 	! ;
:  CF>Stack ( -- )	CF NF 2 cells+	! ;
:  BF>Stack ( -- )	BF NF 3 cells+	! ;
:  SS>Stack ( -- )	SS NF 4 cells+	! ;
:  TS>Stack ( -- )	TS NF 5 cells+	! ;

\ Context Restore Operations
\ :M StackNF>RP ( -- ) R> DROP NF @ >R	;M \ ret from unit
\ :M Stack>RP ( -- ) R> DROP CF @ >R	;M
:  Stack>BP ( -- n ) CF 1 cells+	@	;
:  Stack>CF ( -- )	 CF 2 cells+	@ IS CF	;
:  Stack>BF ( -- )	 BF 3 cells+	@ IS BF	;
:  Stack>GS ( -- )	 CF 4 cells+	@ IS SS	;
:  Stack>TS ( -- )	 CF 5 cells+	@ IS TS	;

\ Temporaries, Equates, Tags
\ Temporary Variables
0 VALUE ARG
0 VALUE NVARS
0 VALUE ARITY
  VARIABLE ARG.FLG
  VARIABLE COPY.FLG
\ Equates
2 cells	CONSTANT BYTES/CELL
6 cells	CONSTANT BYTES/FRAME
\ Tags - Here the tag is the high order 16 bits
1 CONSTANT VAR.TYPE
2 CONSTANT CONST.TYPE
3 CONSTANT FUNCT.TYPE

\ Record Manipulation
\ Code records
: CODE>ARITY ( ^code -- n ) 	1 cells+ @ 256 / ;	\ in second byte
: CODE>NVARS ( ^code -- n ) 	1 cells+ @ 255 and ;	\ in first byte
: CODE>PROC  ( ^code -- addr )  2 cells+    ;

\ Procedure Records
: PROC>CODE  ( ^clause -- ^code ) 2 cells + @ ;	\ procedure > code
: PROC>ARITY ( ^clause -- n ) 1 cells+ @ ;	\ procedure > arity

\ Record Manipulation
\ Structure Records
: STRUC>FUNCTOR ( ^functor -- ^atom )	 @ ;	\ func > name
: STRUC>ARITY	( ^functor -- arity ) 1 cells+ @ ;
: STRUC>ARGS	( ^functor -- ^args ) 2 cells+  ;


\ Term References
: >TYPE 	( term.ref -- type )	 @ ;
: >POINT	( term.ref -- ^term ) 1 cells+ @ ;

\ Procedure Search
: FIND.PROC ( n pfa -- ^code | flag )
\ Find a procedure of given arity and functor
\ arity = n, functor = pfa
\ Return FALSE if not found
\ Return pointer to first code record if found
	BEGIN
	@ DUP					\ get pointer to clause records
	IF 2DUP PROC>ARITY =			\ compare arity
		IF TRUE ELSE FALSE THEN 	\ IF = then we're done
	ELSE   TRUE THEN			\ if link = 0 then we're done
	UNTIL SWAP DROP DUP			\ clean stack
	IF PROC>CODE TRUE THEN ;	 	\ convert to code record pointer

\ Variable Manipulation
: CREATE.UNBOUND.VAR ( addr -- )
\ Create an unbound variable at addr
	VAR.TYPE OVER 2! ; \ store
: INIT.VARS ( -- )
\ create unbound variables in the control frame
	NVARS ?DUP
	IF	NF BYTES/FRAME +
		ARITY BYTES/CELL * + DUP ROT BYTES/CELL * + SWAP
		DO I CREATE.UNBOUND.VAR BYTES/CELL +LOOP THEN ;
: RESET.VARS ( top.TS bottom.TS -- )
\ reset the variables on the trail stack
	2DUP = IF 2DROP ELSE DO I @ VAR.TYPE OVER 2! 1 cells +LOOP THEN ;

\ Saving State
\ :M RESET.RP ( ^code -- )
\ Reset the return stack pointer
\ R> DROP CODE>PROC >R ;M
: SAVE.BACKTRACK ( ^code -- ^code )
\ Save appropriate information at a backtrack pointer
	DUP @ DUP BP>Stack		\ get  link to next code record
	IF BF>Stack			\ if a choice point, save old BF
		NF>BF			\ current frame is new backtrack frame
		SS>Stack TS>Stack 	\ save stack pointers
	THEN ;

\ Adjust Pointer to Next FRAME
: SET.NF ( ^code -- ^code )
\ reset NF register
	CODE>ARITY BYTES/CELL * BYTES/FRAME + CF + IS BF ;
: RESET.NF ( -- )
\ reset NF pointer
	NF BYTES/FRAME +
	ARITY NVARS + BYTES/CELL * +
	IS NF ;							\ adjust next frame pointer
: INIT.^ARG ( -- )
\ init ARG register
	NF BYTES/FRAME + IS ARG ;

\ General Backtracking
: BACKTRACK ( -- )
\ Restore context
\ BF>CF					\ make the BF current
\ Stack>BP DUP R> DROP CODE>PROC >R	\ get pointer to code record
\ @ DUP BP>Stack 0=			\ get link to next code record
\ IF Stack>BF THEN			\ reset BF if this not choice pt
 \ Stack>PF Stack>SS			\ restore PF and SS pointers
\ Stack>BF Stack>SS
\ TS Stack>TS				\ restore TS
\ TS RESET.VARS				\ reset vars on the trail
\ INIT.^ARG
\ SET.NF ;				\ reset NF
 ." not implemented " ;

\ Backtracking on Unification Failure
: RETRY ( -- )
\ Restore context
	CF					\ get a copy of CF
	BF>CF					\ make BF the current
	Stack>BP DUP R> DROP CODE>PROC >R	\ get pointer to code record
	DUP CODE>NVARS IS NVARS	
	@ DUP BP>Stack 0=			\ get link to next code record
	IF Stack>BF THEN			\ reset BF if this not choice pt
	Stack>GS				\ restore SS pointer
	TS Stack>TS				\ restore TS
	TS RESET.VARS				\ reset vars on the trail
	INIT.VARS INIT.^ARG
	IS CF ;					\ restore CF

\ Binding Trail
\ keep track of variable bindings that may need
\ to be reset on backtracking

: >TRAIL ( ^var -- ^var )
\ put a variable cell address on the trail
	TS ! TS 1 cells+ IS TS ;
: >TRAIL? ( ^var -- ^var )
\ trail a variable if necessary
	DUP BF U< OVER SS U< OR
	IF DUP >TRAIL THEN ;

\ Creating and Fetching a Binding
: BIND ( ^term type ^var -- )
\ bind a variable
	>TRAIL? 2! ;	\ smash variable cell

: >ULT.BINDING ( ^term0 -- ^term1 )
\ completely dereference a variable bindings
	BEGIN
	DUP >TYPE VAR.TYPE =				\ check for variable
	IF DUP >POINT OVER =				\ check if unbound var
		IF TRUE ELSE >POINT FALSE THEN		\ chase pointer if bound
	ELSE TRUE THEN					\ not variable then done
	UNTIL ;

\ Save and Restore Arguments

: POP.ARG ( -- ^term )
\ pop an argument off control/structure stack
\ leave term pointer on data stack
	ARG DUP BYTES/CELL + IS ARG ;
: PUSH.ARG ( ^term type -- )
\ push an argument onto the control/structure stack
	ARG 2! ARG BYTES/CELL + IS ARG ;

\ Save and Restore Arg Pointers
: PUSH.^ARG ( addr -- )
\ save then reset argument pointer
	1 cells ^ARG.STACK ARG OVER @ ! +! IS ARG ;
: POP.^ARG ( -- )
	^ARG.STACK -1 cells OVER +! @ @ IS ARG ;

: ARG&TYPE ( -- ^term type )
\ pop an argument, dereference it if necessary, return with type
	POP.ARG >ULT.BINDING DUP >TYPE ;

\ Unify Variable (match mode)
\ see VAR
: UNIFY.VAR ( ^var -- flag )
\ unify the variable with an argument
ARG&TYPE VAR.TYPE =			\ get the argument
IF 2DUP U> IF SWAP THEN 1 cells+ !	\ bind variables
ELSE 2@ ROT BIND THEN TRUE ;		\ bind it to the variable

\ Unify Constant 
\ see VAR
: UNIFY.CONST ( ^const -- flag )
\ unify the constant with an argument
	ARG&TYPE CASE				\ get the argument
	VAR.TYPE
	OF >R 2@ R> BIND TRUE ENDOF
	CONST.TYPE
	OF >POINT SWAP >POINT =			\ compare pointers
		IF TRUE ELSE FALSE THEN		\ succeed if pointers match
	ENDOF
	SWAP FALSE ENDCASE ;			\ nothing else recognized

\ Unify STRUCTURE
\ see VAR
: UNIFY.FUNCT ( ^functor -- flag )
\ unify the functor with an argument
	ARG&TYPE CASE				\ get the argument
	VAR.TYPE OF >R 2@ R> BIND TRUE ENDOF
	FUNCT.TYPE OF ." Not Implemented " TRUE ENDOF
	SWAP FALSE ENDCASE ;
	
\ Build a Term Reference (arg mode)

: REF>ARG ( ^term -- )
\ builds an argument from a term reference
	DUP >TYPE VAR.TYPE = 	\ check for variable
	IF VAR.TYPE 		\ make a new variable
	ELSE 2@ THEN PUSH.ARG ;	\ otherwise copy
: VAR>ARG ( n -- )
\ builds an argument from a variable reference
COPY.FLG @
IF NF ELSE CF THEN + 		\ get address of variable
>ULT.BINDING REF>ARG ;		\ get binding for argument

\ Build a Structure Record (copy, arg modes)

: COPY.FUNCT ( arity ^atom -- )
\ build a functor record on the structure stack
	-1 ARG.FLG +!			\ increment the counter
	OVER BYTES/CELL * 2 cells +	\ compute # of bytes in record
	SS DUP ROT + IS SS		\ allocate space
	DUP 2 cells + PUSH.^ARG		\ reset arg pointer for restore
	2! ;				\ fill head of functor record

\ Match a Structure (match mode)
\ see FUNCTOR
: MATCH.FUNCT ( arity ^atom ^term -- flag )
\ match functor with an argument
\ ARG is reset if functor (name) and arity match
\ remainder of match is handled by code in clause head
	>POINT						\ get pointer to record
	DUP STRUC>FUNCTOR ROT =				\ check functor match
	IF DUP STRUC>ARITY ROT =			\ check arity match
		IF STRUC>ARGS PUSH.^ARG TRUE		\ reset arg pointer, return T
		ELSE DROP FALSE THEN
	ELSE 2DROP FALSE THEN ;				\ return false if no match

\ Copy a Structure (copy mode)
\ see FUNCTOR
: MATCH.VAR ( arity ^atom ^var -- flag )
\ Builds a structure record and binds it to the variable
\ The structure args are build by the remainder of the head code
	COPY.FLG ON					\ copy variable from ND not CF
	SS FUNCT.TYPE ROT BIND				\ bind the variable to funct rec
	COPY.FUNCT TRUE ;				\ set to copy functor, return T
	
\ Prolog Virtual Machine Instructions
\ Notes: VAR tales a byte offset from the start of a frame
\ (base address) to compute the address of the variable.
\ ARG.FLG = 0, COPY.FLG = 0 indicates match mode
\ ARG.FLG not 0, COPY.FLG = 0 indicates arg mode
\ ARG.FLG not 0, COPY.FLG not 0 indicates copy mode
\ in copy mode, nesting is handled by decrementing ARG.FLG
\ at the start of a structure, and incrementing on exit
\ (via POP).
\ COPY.FLG is used to indicate which frame pointer (CF or NF)
\ should be used for the base address of the variable.

\ Prolog Machine Instructions
: CALL ( n cfa -- )
\ Call a Prolog procedure
	\ dup wordbyaddr type cr			\ print
	ARG.FLG OFF					\ switch mode to match
	FIND.PROC					\ get pointer to procedure rec
	IF	DUP CODE>NVARS IS NVARS			\ cache NVARS
		DUP CODE>ARITY IS ARITY 		\ cache ARITY
		INIT.VARS R> NF !			\ init vars and set up stack
		SAVE.BACKTRACK
		INIT.^ARG				\ set argument pointer
		2 cells + >R EXIT			\ pass control to procedure
	ELSE ." backtrack call, " BACKTRACK THEN ;	\ backtrack if no procedure
	
\ Prolog Machine Instruction ENTER
: ENTER ( -- )
\ Enter a procedure and begin execution of the body
	ARG.FLG ON		\ switch mode to "arg"
	COPY.FLG OFF
	CF>Stack		\ adjust frame pointer
	NF>CF RESET.NF		\ adjust next frame pointer
	INIT.^ARG ;		\ set arg pointer for next call

\ Prolog Machine Instruction RETURN
: RETURN ( -- )
\ Return from a procedure
	ARG.FLG @				\ check mode
	IF R> DROP CF @ >R CF BF U>
		IF CF>NF THEN			\ reclaim if not backtrack pnt
		Stack>CF			\ adjust frame pointers
	ELSE R> DROP NF @ >R BF NF =	 	\ if ret from unit clause
		IF CF>Stack			\ save parent frame pointer
			RESET.NF		\ reset frame pointer
		THEN
	THEN ARG.FLG ON				\ turn off matcher
	INIT.^ARG ;				\ set arg pointer for next call
	
\ Prolog Machine Instruction CONST
: CONST ( ^atom -- )
\ match of copy a constant
	ARG.FLG @
	IF CONST.TYPE PUSH.ARG			\ push arg in arg mode
	ELSE ARG&TYPE VAR.TYPE =		\ get first argument
		IF CONST.TYPE SWAP BIND		\ if variable, bind it
		ELSE >POINT = NOT		\ otherwise must be Equates
			IF R> DROP NF BF =
				IF  RETRY	\ retry if new call
				ELSE ." backtrack const, " BACKTRACK THEN	\ backtrack if not
			THEN
		THEN								\ else continue
	THEN ;

\ Prolog Machine Instruction VAR
: VAR ( n -- )
	ARG.FLG @
	IF VAR>ARG			\ get binding for argument
	ELSE NF + >ULT.BINDING  	\ get the variable bindings
		DUP >TYPE CASE		\ case analysis on type
			VAR.TYPE 	OF UNIFY.VAR	ENDOF
			CONST.TYPE 	OF UNIFY.CONST  ENDOF
			FUNCT.TYPE 	OF UNIFY.FUNCT	ENDOF
		ENDCASE NOT
		IF R> DROP NF BF =				\ if match not successful
			IF RETRY				\ retry
			ELSE ." backtrack var, " BACKTRACK THEN \ or backtrack
		THEN
	THEN ; 							\ build an argument

\ Prolog Machine Instruction POP
: POP ( -- )
\ pop from a FUNCTOR
	POP.^ARG				\ restore argument pointer
	ARG.FLG @				\ look for "arg" mode
	IF 1 ARG.FLG +! THEN ; 	\ decrement counter

\ Prolog Machine Instruction FUNCTOR
: FUNCTOR ( arity ^atom -- )
\ Compiler object indicating a structure
	ARG.FLG @
	IF SS FUNCT.TYPE PUSH.ARG COPY.FUNCT
	ELSE ARG&TYPE CASE
		VAR.TYPE OF MATCH.VAR ENDOF
	FUNCT.TYPE OF 	MATCH.FUNCT ENDOF
	FALSE SWAP ENDCASE
	NOT IF R> DROP NF BF =
		IF RETRY ELSE ." backtrack functor, " BACKTRACK THEN
		THEN
	THEN ;

\ Support Routines
\
\ ASSERTZ is the PVM to Forth Compiler.
\ It requires as parameters the number of variables
\ in the clause, the arity of the clause, and the pfa
\ of the clause functor.
\ If the FVM word set were extend, with different words
\ for instructions in the head body, much of the compilation
\ to the extended word set could be handled by ASSERTZ, since
\ it can tell the differencew between the head and body of a
\ clause. Thus the Prolog-PVM compiler could stay simple.
			
\ Prolog Print Words
: PRINT.CONST ( ^const -- )
\ print a constant
	>POINT WordByAddr TYPE ;
	\ >POINT BODY> .ID ;
: PRINT.VAR ( ^var -- )
\ print a variable
	>POINT BASE @ R>
	[char] _ EMIT HEX U. R> BASE ! ;

: PRINT.FUNCT ( ^term -- )
\ print a structure
	\ >POINT DUP @ BODY> .ID 
	>POINT DUP @ WordByAddr TYPE 
	[char] ( EMIT
	0 swap cell+ DUP cell+ SWAP @ BYTES/CELL * OVER + SWAP
	DO if [char] , emit then -1 I PRINT.TERM BYTES/CELL +LOOP drop [char] ) EMIT ;
: <PRINT.TERM> ( ^term -- )
\ print a Prolog term
	>ULT.BINDING DUP >TYPE CASE
	CONST.TYPE OF PRINT.CONST ENDOF
		VAR.TYPE OF PRINT.VAR ENDOF
	FUNCT.TYPE OF PRINT.FUNCT ENDOF ENDCASE ;
' <PRINT.TERM> IS PRINT.TERM

\ Auxiliary Words
: !CODE.DATA ( nvars arity -- )
\ pack the number of variables (nvars) and arity
\ then enclose
	256 * + , ;		\ arity is in high order byte
: \LINK ( start.addr -- end.addr )
\ traverse links to end
	BEGIN DUP @ IF @ FALSE ELSE TRUE THEN UNTIL ;

\ PVM to Forth Compiler
: :ASSERTZ ( nvars arity pred -- )
\ add a clause to the Prolog database
	2DUP FIND.PROC			\ find prov record
	IF \LINK 			\ if found, get last clause rec
		HERE SWAP ! 0 ,		\ install links
		DROP !CODE.DATA		\ install nvars, arity
	ELSE \LINK			\ if not found get last proc
		HERE SWAP ! 0 ,		\ install links
		DUP , HERE 1 cells+ ,	\ install arity and link to clause
		0 , !CODE.DATA		\ set clause link
	THEN STATE ON ;			\ compile remainder of input
: ;ASSERT ( -- )
	STATE OFF ; IMMEDIATE 		\ turn off compilation

\ Initialization words for test routines
: INIT.^ARG.STACK
\ init argument pointer stack
	^ARG.STACK DUP 1 cells+ SWAP ! ;
: INIT.STACKS
\ initialize stacks prior to CALL
	STRUCTURE.STACK IS SS
	TRAIL IS TS
	CONTROL.STACK IS CF
	CF IS NF	0 IS BF
	ARG.FLG OFF COPY.FLG OFF
	CONTROL.STACK 3000 0 FILL	INIT.^ARG.STACK ;
: TEST INIT.STACKS CR ;

\ Test Procedures
\ Create Dictionary Entries for all Test Words
ATOM: REV	ATOM: APPEND
ATOM: NIL	ATOM: cons
ATOM: bob	ATOM: art 
ATOM: fred

\ APPEND and REV (Note arguments of VAR)
\ append([],X,X).
\ append([X|Y],Z,[X|L]) :- append(Y,Z,L).
1 3 APPEND :ASSERTZ NIL CONST 48 VAR 48 VAR RETURN ;ASSERT
4 3 APPEND :ASSERTZ 2 cons FUNCTOR 48 VAR 56 VAR POP
					64 VAR
					2 cons FUNCTOR 48 VAR 72 VAR POP
				ENTER 56 VAR 64 VAR 72 VAR 3 APPEND CALL
				RETURN ;ASSERT

\ rev([],[]).
\ rev([X|Y],L) :- rev(Y,Z), append(Z,[X],L).
0 2 REV		:ASSERTZ NIL CONST NIL CONST RETURN ;ASSERT
4 2 REV		:ASSERTZ 2 cons FUNCTOR 40 VAR 48 VAR POP 56 VAR
				ENTER 48 VAR 64 VAR 2 REV CALL
				64 VAR
				2 cons FUNCTOR 40 VAR NIL CONST POP 56 VAR
				3 APPEND CALL
			RETURN ;ASSERT

\ Test of Append
\ use: TEST 0 TEST1 CALL
\ check result with CONTROL.STACK 24 + PRINT.TERM
ATOM: TEST1
\ append([bob,fred],[art],L).
1 0 TEST1 :ASSERTZ ENTER
			2 cons FUNCTOR bob CONST
			2 cons FUNCTOR fred CONST NIL CONST POP POP
			2 cons FUNCTOR art CONST NIL CONST POP
			24 VAR 3 APPEND CALL RETURN ;ASSERT

\ Test of REV
\ use: TEST 0 TEST2 CALL
\ check result with CONTROL.STACK 24 + PRINT.TERM
ATOM: TEST2
\ rev([bob,art,fred,L).
1 0 TEST2 :ASSERTZ ENTER
	2 cons FUNCTOR bob CONST
	2 cons FUNCTOR art CONST
	2 cons FUNCTOR fred CONST NIL CONST
		POP POP POP
	24 VAR 2 REV CALL RETURN ;ASSERT
