#include <stdio.h>

#define NRW        19     // number of reserved words
#define TXMAX      500    // length of identifier table
#define MAXNUMLEN  14     // maximum number of digits in numbers
#define NSYM       17    // maximum number of symbols in array ssym and csym
#define MAXIDLEN   10     // length of identifiers
#define STEP	1
#define MAXADDRESS 32767  // maximum address
#define MAXLEVEL   32     // maximum depth of nesting block
#define CXMAX      500    // size of code array
#define MAXNUM     65535
#define MAXSYM     30     // maximum number of symbols  

#define STACKSIZE  1000   // maximum storage

#define DIM 10		//maximum dimension
#define RECUSION_DEPTH     10  // recusion depth

enum symtype
{
	SYM_NULL,
	SYM_IDENTIFIER,
	SYM_NUMBER,
	SYM_PLUS,
	SYM_NEG, 
	SYM_MINUS,
	SYM_TIMES,
	SYM_SLASH,
	SYM_ODD,
	SYM_EQU,//==
	SYM_NEQ,//!=
	SYM_LES,//<
	SYM_LEQ,//<=
	SYM_GTR,//>
	SYM_GEQ,//>=
	SYM_LPAREN,
	SYM_RPAREN,
	SYM_COMMA,
	SYM_SEMICOLON,
	SYM_PERIOD,
	SYM_BECOMES,//:= 
    SYM_BEGIN,
	SYM_END,
	SYM_IF,
	SYM_THEN,
	SYM_WHILE,
	SYM_DO,
	SYM_CONST,
	SYM_VAR,
	SYM_PROCEDURE,
	SYM_AND,
	SYM_OR,
	SYM_NOT,
	SYM_AND_B,
	SYM_OR_B,
	SYM_XOR_B,
	SYM_MOD,
	SYM_LBRT,//[
	SYM_RBRT,//]
	SYM_ELSE,
	SYM_EXIT,
	SYM_ELIF,
	SYM_ADDEQU,//+=
	SYM_SUBEQU,//-=
	SYM_MULEQU,//*=
	SYM_DIVEQU,///=
	SYM_ADDADD,//++
	SYM_SUBSUB,//--
	SYM_MODEQU,//%=
	SYM_SHL,//<<
	SYM_SHR,//>>
	SYM_SHLEQU,//<<=
	SYM_SHREQU,//>>=
	SYM_QUES,//?
        SYM_COLON,//:
	SYM_ADDR,//&
	SYM_RETURN,
        SYM_FOR,
        SYM_RAND,
        SYM_PRINT,
    SYM_LABEL,
    SYM_GOTO

};

enum idtype
{
	ID_CONSTANT, ID_VARIABLE, ID_PROCEDURE, ID_ARR
};

enum opcode
{
        LIT, OPR, LOD, STO, CAL, INT, JMP, JPC, EXT, STA, LTA, RET, JNZ, JZ,RAND,PRT
};

enum oprcode
{
	OPR_RET, OPR_NEG, OPR_ADD, OPR_MIN,
	OPR_MUL, OPR_DIV, OPR_ODD, OPR_EQU,
	OPR_NEQ, OPR_LES, OPR_LEQ, OPR_GTR,
	OPR_GEQ, OPR_AND, OPR_OR, OPR_NOT,
	OPR_AND_B, OPR_OR_B, OPR_XOR_B, OPR_MOD,
	OPR_SHL, OPR_SHR
};


typedef struct
{
	int f; // function code
	int l; // level
	int a; // displacement address
} instruction;

//////////////////////////////////////////////////////////////////////
char* err_msg[] =
{
/*  0 */    "can't find label",
/*  1 */    "Found ':=' when expecting '='.",
/*  2 */    "There must be a number to follow '='.",
/*  3 */    "There must be an '=' to follow the identifier.",
/*  4 */    "There must be an identifier to follow 'const', 'var', or 'procedure'.",
/*  5 */    "Missing ',' or ';'.",
/*  6 */    "Incorrect procedure name.",
/*  7 */    "Statement expected.",
/*  8 */    "Follow the statement is an incorrect symbol.",
/*  9 */    "'.' expected.",
/* 10 */    "';' expected.",
/* 11 */    "Undeclared identifier.",
/* 12 */    "Illegal assignment.",
/* 13 */    "':=' expected.",
/* 14 */    "There must be an identifier to follow the 'call'.",
/* 15 */    "A constant or variable can not be called.",
/* 16 */    "'then' expected.",
/* 17 */    "';' or 'end' expected.",
/* 18 */    "'do' expected.",
/* 19 */    "Incorrect symbol.",
/* 20 */    "Relative operators expected.",
/* 21 */    "Procedure identifier can not be in an expression.",
/* 22 */    "Missing ')'.",
/* 23 */    "The symbol can not be followed by a factor.",
/* 24 */    "The symbol can not be as the beginning of an expression.",
/* 25 */    "The number is too great.",
/* 26 */    "Array declaration constant expected.",
/* 27 */    "Array declaration missing ']'.",
/* 28 */    "Identifier or number expected in '[]'",
/* 29 */    "There must be an array type after '&'.",
/* 30 */    "Missing'('",
/* 31 */    "':'expected",
/* 32 */    "There are too many levels.",
/* 33 */      "No way back"
};

//////////////////////////////////////////////////////////////////////
char ch;         // last character read
int  sym;        // last symbol read
char id[MAXIDLEN + 1]; // last identifier read
int  num;        // last number read
int  cc;         // character count
int  ll;         // line length
int  kk;
int  err;
int  cx;         // index of current instruction to be generated.
int  level = 0;
int  tx = 0;
int dimension;		//to record the dimension
int dim[DIM];		//to record the dimension
int off;		//to record the offset of an array
int number;
int ProcedureDepth = 0;
int paracount[RECUSION_DEPTH];
char line[80];
//声明的 label的数目。
int labeltotal = 0;

//程序中调用 goto 的数目
int gotototal = 0;

//存放 label 的标识， 最多存放 10 个，每声明一个label 就顺序在
//labelnum[] 中存放相应的 label 值。
int labelnum[10]={0};

//存放 label 跳转地址，假设声明 label:a 那么程序中 goto a; 的跳
//转地址为 labelcx[a]。在程序中中每出现一个 label 标识就记录它
//的当前地址赋值给 labelcx[]。goto 语句跳转时会查询 labelcx[]
//数组确认它的跳转地址。
int labelcx[10000]={0};

// gotonum[i][0]存放 goto 语句对应的 label 值，gotonum[i][1]记
//录相应的需要跳转的地址，当然跳转地址不知道，必须要在所有代码
//扫描完毕后再回填跳转地址。
int gotonum[10][2]={0};

//某个 label 可能声明了，但是并没有出现。如果 goto 跳转到那个
//label 应当报错，建立 labelbool[] 判断 label 是否在程序中出现，
//出现为 1， 否为 0。
int labelbool[10000];
instruction code[CXMAX];

char* word[NRW + 1] =
{
	"", /* place holder */
	"begin", "const", "do", "end","if",
	"odd", "procedure", "then", "var", "while",
    "else", "exit", "elif", "return", "for","random","print","label","goto"
};

int wsym[NRW + 1] =
{
	SYM_NULL, SYM_BEGIN, SYM_CONST, SYM_DO, SYM_END,
	SYM_IF, SYM_ODD, SYM_PROCEDURE, SYM_THEN, SYM_VAR, SYM_WHILE,
        SYM_ELSE, SYM_EXIT, SYM_ELIF, SYM_RETURN, SYM_FOR,SYM_RAND,SYM_PRINT,SYM_LABEL,SYM_GOTO
};

int ssym[NSYM + 1] =
{
	SYM_NULL, SYM_PLUS, SYM_NEG, SYM_TIMES, SYM_SLASH,
	SYM_LPAREN, SYM_RPAREN, SYM_EQU, SYM_COMMA, SYM_PERIOD, SYM_SEMICOLON,
    SYM_LBRT, SYM_RBRT, SYM_QUES, SYM_COLON, SYM_ADDR
};

char csym[NSYM + 1] =
{
        ' ', '+', '-', '*', '/', '(', ')', '=', ',', '.', ';', '[', ']', '?', ':', '&'
};

#define MAXINS   15
char* mnemonic[MAXINS] =
{
        "LIT", "OPR", "LOD", "STO", "CAL", "INT", "JMP", "JPC", "EXT", "STA", "LTA", "RET", "JNZ", "JZ","PRT"
};

typedef struct
{
	char name[MAXIDLEN + 1];
	int  kind;
	int  value;
	int  dimension;
	int  dim[DIM];
	int  tag;
} comtab;

comtab table[TXMAX];

typedef struct
{
	char  name[MAXIDLEN + 1];
	int   kind;
	short level;
	short address;
	int  dimension;
	int  dim[DIM];
	int  tag;
} mask;

FILE* infile;

// EOF PL0.h
