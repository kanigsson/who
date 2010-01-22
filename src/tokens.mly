%token <Big_int.big_int Loc.t> INT
%token <Loc.loc> LPAREN RPAREN LCURL SECTION END
%token LBRACKET RBRACKET RCURL DLCURL DRCURL PREDEFINED DLBRACKET DRBRACKET
%token <string Loc.t> IDENT
%token <string> TYVAR STRING
%token IN SEMICOLON COQ ALLOCATES TAKEOVER PANGOLINE
%token <Loc.loc> PLUS MINUS EQUAL STAR NEQ BEQUAL BNEQ ARROW COMMA AND OR
%token <Loc.loc> ASSIGN GE GT LE LT REF LETREGION TILDE
%token <Loc.loc> BLE BLT BGT BGE
%token EOF
%token REC
%token <Loc.loc> EXCLAM DEXCLAM IF FUN PTRUE PFALSE VOID LET AXIOM
%token <Loc.loc> LOGIC TYPE FORALL EXISTS PARAMETER TO DOWNTO FOR DONE GOAL
%token COLON MID THEN ELSE TINT UNIT PROP DOT DO

%nonassoc forall
%nonassoc let_
%right ARROW
%nonassoc ifprec
%left AND OR
%nonassoc LE LT GE GT BLE BLT BGT BGE
%nonassoc ASSIGN
%right EQUAL NEQ BEQUAL BNEQ
%right COMMA
%left PLUS MINUS
%right STAR

%%

