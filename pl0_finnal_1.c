// pl0 compiler source code

#pragma warning(disable:4996)


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>
#include "pl0.h"
#include "set.c"

//////////////////////////////////////////////////////////////////////
// print error message.
void error(int n)
{
	int i;

	printf("      ");
	for (i = 1; i <= cc - 1; i++)
		printf(" ");
	printf("^\n");
	printf("Error %3d: %s\n", n, err_msg[n]);
	err++;
} // error

//////////////////////////////////////////////////////////////////////

void getch(void)
{
	if (cc == ll)
	{
		if (feof(infile))
		{
			printf("\nPROGRAM INCOMPLETE\n");
			exit(1);
		}
		ll = cc = 0;
		printf("%5d  ", cx);
		while ( (!feof(infile)) // added & modified by alex 01-02-09
			    && ((ch = getc(infile)) != '\n'))
		{
			printf("%c", ch);
			line[++ll] = ch;
		} // while
		printf("\n");
		line[++ll] = ' ';
	}
	ch = line[++cc];
} // getch

//////////////////////////////////////////////////////////////////////
// gets a symbol from input stream.
void getsym(void)
{
	int i, k;
	char a[MAXIDLEN + 1];
	
	while (ch == ' '||ch == '\t')
		getch();

	if (isalpha(ch))
	{ // symbol is a reserved word or an identifier.
		k = 0;
		do
		{
			if (k < MAXIDLEN)
				a[k++] = ch;
			getch();
		}
		while (isalpha(ch) || isdigit(ch));
		a[k] = 0;
		strcpy(id, a);
		word[0] = id;
		i = NRW;
		while (strcmp(id, word[i--]));
		if (++i)
			sym = wsym[i]; // symbol is a reserved word
		else
			sym = SYM_IDENTIFIER;   // symbol is an identifier

	}
	else if (isdigit(ch))
	{ // symbol is a number.
		k = num = 0;
		sym = SYM_NUMBER;
		do
		{
			num = num * 10 + ch - '0';
			k++;
			getch();
		}
		while (isdigit(ch));
		if (k > MAXNUMLEN)
			error(25);     // The number is too great.
	}
	else if (ch == ':')
	{
		getch();
		if (ch == '=')
		{
			sym = SYM_BECOMES; // :=
			getch();
		}
		else
		{
            sym = SYM_COLON;       // illegal?
		}
	}
	else if (ch == '>')
	{
		getch();
		if (ch == '=')
		{
			sym = SYM_GEQ;     // >=
			getch();
		}
		else if(ch == '>'){
			getch();
			if(ch == '='){
				sym = SYM_SHREQU;		//>>=
				getch();
			}
			else{
				sym = SYM_SHR;		//>>
			}
		}
		else
		{
			sym = SYM_GTR;     // >
		}
	}
	else if (ch == '<')
	{
		getch();
		if (ch == '=')
		{
			sym = SYM_LEQ;     // <=
			getch();
		}
		else if(ch == '<'){
			getch();
			if(ch == '='){
				sym = SYM_SHLEQU;		//<<=
				getch();
			}
			else{
				sym = SYM_SHL;		//<<
			}
		}
		else
		{
			sym = SYM_LES;     // <
		}
	}
	else if(ch == '='){
		getch();
		if(ch == '='){		//==
			sym = SYM_EQU;
			getch();
		}
		else{
			printf("Fatal Error: Unknown character.\n");
			exit(1);
		}
	}
	else if(ch == '!'){
		getch();
		if(ch == '='){		//!=
			sym = SYM_NEQ;
			getch();
		}
		else{		//!
			sym = SYM_NOT;
		}
	}
	else if(ch == '&'){		//& and &&
		getch();
		if(ch == '&'){
			sym = SYM_AND;
			getch();
		}
		else{
			sym = SYM_AND_B;
		}
	}
	else if(ch == '|'){		//| and ||
		getch();
		if(ch == '|'){
			sym = SYM_OR;
			getch();
		}
		else{
			sym = SYM_OR_B;
		}
	}
	else if(ch == '^'){		//^
		sym = SYM_XOR_B;
		getch();
	}
	else if(ch == '%'){		//%
		getch();
		if(ch == '='){		// %=
			sym = SYM_MODEQU;
			getch();
		}
		else{
			sym = SYM_MOD;
		}
	}
	else if(ch == '?'){		// ? :
		sym = SYM_QUES;
		getch();
	}
	else if(ch == '/'){		// annotation
		getch();
		if(ch == '/'){
			while(ll - cc){
				getch();
			}
			getsym();
		}
		else if(ch == '*'){
			int starflag = 1;
			getch();
			while(starflag){
				while(ch != '*'){
					getch();
				}
				getch();
				if(ch == '/'){
					starflag = 0;
				}
			}
			getch();
			getsym();
		}
		else if(ch == '='){		// /=
			sym = SYM_DIVEQU;
			getch();
		}
		else{		//SYM_SPLASH
			sym = ssym[4];
		}
	}
	else
	{ // other tokens
		i = NSYM;
		csym[0] = ch;
		while (csym[i--] != ch);
		if (++i)
		{
			if(ch == '+'){
				getch();
				if(ch == '='){
					sym = SYM_ADDEQU;		// +=
					getch();
				}
				else if(ch == '+'){
					sym = SYM_ADDADD;		// ++
					getch();
				}
				else{
					sym = SYM_PLUS;
				}
			}
			else if(ch == '-'){
				getch();
				if(ch == '='){
					sym = SYM_SUBEQU;		// -=
					getch();
				}
				else if(ch == '-'){
					sym = SYM_SUBSUB;		// --
					getch();
				}
				else{
					sym = SYM_MINUS;
				}
			}
			else if(ch == '*'){
				getch();
				if(ch == '='){
					sym = SYM_MULEQU;		// *=
					getch();
				}
				else{
					sym = SYM_TIMES;
				}
			}
			else{
				sym = ssym[i];
				getch();
			}			
		}
		else
		{
			printf("Fatal Error: Unknown character.\n");
			exit(1);
		}
	}
} // getsym

//////////////////////////////////////////////////////////////////////
// generates (assembles) an instruction.
void gen(int x, int y, int z)
{
	if (cx > CXMAX)
	{
		printf("Fatal Error: Program too long.\n");
		exit(1);
	}
	code[cx].f = x;
	code[cx].l = y;
	code[cx++].a = z;
} // gen

//////////////////////////////////////////////////////////////////////
// tests if error occurs and skips all symbols that do not belongs to s1 or s2.
void test(symset s1, symset s2, int n)
{
	symset s;

	if (! inset(sym, s1))
	{
		error(n);
		s = uniteset(s1, s2);
		while(! inset(sym, s))
			getsym();
		destroyset(s);
	}
} // test

//////////////////////////////////////////////////////////////////////
int dx;  // data allocation index

// enter object(constant, variable or procedre) into table.
void enter(int kind)
{
	mask* mk;
	mask* arr;
	int i = 0;

	tx++;
	strcpy(table[tx].name, id);
	table[tx].kind = kind;
	switch (kind)
	{
	case ID_CONSTANT:
		if (num > MAXADDRESS)
		{
			error(25); // The number is too great.
			num = 0;
		}
		table[tx].value = num;
		break;
	case ID_VARIABLE:
		mk = (mask*) &table[tx];
		mk->level = level;
		mk->address = dx++;
		mk->tag = 0;
		break;
	case ID_PROCEDURE:
		mk = (mask*) &table[tx];
		mk->level = level;
		break;
    case ID_ARR:
		arr = (mask *) &table[tx];
		arr->level = level;
		arr->address = dx;		// data allocation index
		dx = dx + off;
		for(i = 0;i < dimension;i++)
			arr->dim[i] = dim[i];
		arr->dimension = dimension;
		break;
	} // switch
} // enter

void ParaEnter(int kind){
	mask* mk;
	mask* ay;
	int j = 0;
	tx++;//
	strcpy(table[tx].name, id);
	table[tx].kind = kind;
	switch (kind)
	{
	case ID_VARIABLE:
		mk = (mask*) &table[tx];
		mk->level = level;
		break;
	case ID_ARR:
		ay = (mask *)&table[tx];
		ay->tag = 1;
		for (j = 0; j<dimension; j++)
			ay->dim[j] = dim[j];
		ay->dimension = dimension;
		break;
	}
}

//////////////////////////////////////////////////////////////////////
// locates identifier in symbol table.
int position(char* id)
{
	int i;
	strcpy(table[0].name, id);
	i = tx + 1;
	while (strcmp(table[--i].name, id) != 0);
	return i;
} // position

//////////////////////////////////////////////////////////////////////
void constdeclaration()
{
	if (sym == SYM_IDENTIFIER)
	{
		getsym();
		if (sym == SYM_EQU || sym == SYM_BECOMES)
		{
			if (sym == SYM_BECOMES)
				error(1); // Found ':=' when expecting '='.
			getsym();
			if (sym == SYM_NUMBER)
			{
				enter(ID_CONSTANT);
				getsym();
			}
			else
			{
				error(2); // There must be a number to follow '='.
			}
		}
		else
		{
			error(3); // There must be an '=' to follow the identifier.
		}
	} else	error(4);
	 // There must be an identifier to follow 'const', 'var', or 'procedure'.
} // constdeclaration

//////////////////////////////////////////////////////////////////////
void vardeclaration(void)
{
    dimension = 0;
            off = 1;
            if (sym == SYM_IDENTIFIER)
            {
                    getsym();
                    while (sym == SYM_LBRT)		//[
                    {
                            getsym();
                            if (sym == SYM_NUMBER)		//[a
                            {
                                    off = off * num;
                                    dim[dimension] = num;
                                    dimension++;
                                    getsym();
                            }
                            else	error(26);		//wrong declaration
                            if (sym == SYM_RBRT)		//[a]
                            {
                                    getsym();
                            }
                            else	error(27);		//missing ']'
                    }
                    if (!dimension)	enter(ID_VARIABLE);		//dimension == 0 means it's a varible
                    else	enter(ID_ARR);		//dimension != 0 means it's an array
            }
            else
            {
                    error(4); // There must be an identifier to follow 'const', 'var', or 'procedure'.
    }
} // vardeclaration

void ParaDecalration(void)
{
	off = 1;
	dimension = 0;
	if (sym == SYM_IDENTIFIER)
	{
		getsym();
		while (sym == SYM_LBRT)
		{
			getsym();
			if (sym == SYM_NUMBER)
			{
				off = off * num;
				dim[dimension] = num;
				dimension++;
				getsym();
			}
			else
			{
				error(28);
			}
			if (sym == SYM_RBRT)
			{
				getsym();
			}
			else
			{
				error(27);
			}
		}
		if (dimension == 0)
		{
			ParaEnter(ID_VARIABLE);
		}
		else
			ParaEnter(ID_ARR);
	}
	else
	{
		
		//error(4); // There must be an identifier to follow 'const', 'var', or 'procedure'.
	}
}

//////////////////////////////////////////////////////////////////////
void listcode(int from, int to)
{
	int i;
	
	printf("\n");
	for (i = from; i < to; i++)
	{
		printf("%5d %s\t%d\t%d\n", i, mnemonic[code[i].f], code[i].l, code[i].a);
	}
	printf("\n");
} // listcode

//////////////////////////////////////////////////////////////////////
void factor(symset fsys)
{
    void expression(symset fsys);
	int i;
    int n;
    int index;
	symset set;
	
	test(facbegsys, fsys, 24); // The symbol can not be as the beginning of an expression.

	while (inset(sym, facbegsys))
	{
		if(sym == SYM_RAND){
            if (num > MAXNUM){
                error(25); // The number is too great.
                num = 0;
            }
            else{
                getsym();

                if(sym != SYM_LPAREN)
                    error(30);
                getsym();
                if(sym == SYM_RPAREN)
                    number = MAXNUM;
                else
                {
                    number = num;
                    getsym();
                    if(sym != SYM_RPAREN)
                        error(22);
                }
                srand(time(NULL));
                num=rand()%number;
			}
			gen(LIT, 0, num);
            getsym();
        }
        else if (sym == SYM_IDENTIFIER)
		{
			if ((i = position(id)) == 0)
			{
				error(11); // Undeclared identifier.
			}
			else
			{
				switch (table[i].kind)
				{
					mask* mk;
					mask* mk2;
					mask* arr;
					mask* ay;
				case ID_CONSTANT:
					gen(LIT, 0, table[i].value);
					break;
                case ID_VARIABLE:
					mk = (mask*) &table[i];
					gen(LOD, level - mk->level, mk->address);
					break;
				case ID_PROCEDURE:
					mk = (mask*) &table[i];
					getsym();
					if (sym == SYM_LPAREN)		//(
					{
						getsym();
						if(sym == SYM_RPAREN){
							gen(CAL, level - mk->level, mk->address);
							break;
						}
						expression_select(uniteset(fsys, createset(SYM_SEMICOLON, SYM_NULL)));
						while (sym == SYM_COMMA)
						{
							getsym();
							expression_select(uniteset(fsys, createset(SYM_SEMICOLON, SYM_NULL)));
						}
						if (sym == SYM_RPAREN)
						{
							//getsym();
						}
						else
						{
							error(22);
						}
					}
					gen(CAL, level - mk->level, mk->address);
					//error(21); // Procedure identifier can not be in an expression.
					break;
				case  ID_ARR:
				{
					arr = (mask*) &table[i];
					getsym();
					int ArrayDim = 0;
					if (sym == SYM_LBRT)
					{
						if (arr->tag == 1)   //array item as parameter
						{
							gen(LOD, 0, arr->level);
							gen(LOD, 0, arr->address);
						}
						else
						{
							gen(LIT, 0, arr->level);
							gen(LIT, 0, arr->address);
						}
						while (sym == SYM_LBRT)
						{
							if (ArrayDim)
							{
								gen(LIT, 0, arr->dim[ArrayDim]);
								gen(OPR, 0, OPR_MUL);
							}
							getsym();
							expression_select(uniteset(fsys, createset(SYM_RBRT, SYM_NULL)));
							if (ArrayDim)
							{
								gen(OPR, 0, OPR_ADD);
							}
							ArrayDim++;
							if (sym == SYM_RBRT){
								//getsym();
							}
							else	error(27);		//missing ']'
						}//while
					}
					else
					{
						error(28);
					}
					gen(LTA, level, arr->address);
					break;
				}
				} // switch
			}
			getsym();
		}
		else if (sym == SYM_NUMBER)
		{
			if (num > MAXADDRESS)
			{
				error(25); // The number is too great.
				num = 0;
			}
			gen(LIT, 0, num);
			getsym();
		}
		else if (sym == SYM_LPAREN)
		{
			getsym();
			set = uniteset(createset(SYM_RPAREN, SYM_NULL), fsys);
			expression_select(set);
			destroyset(set);
			if (sym == SYM_RPAREN)
			{
				getsym();
			}
			else
			{
				error(22); // Missing ')'.
			}
		}
		else if(sym == SYM_NEG) // UMINUS,  Expr -> '-' Expr
		{  
			 getsym();
			 expression_select(fsys);
			 gen(OPR, 0, OPR_NEG);
		}
		else if(sym == SYM_MINUS)
		{  
			 getsym();
			 expression_select(fsys);
			 gen(OPR, 0, OPR_MIN);
		}
		else	test(fsys, createset(SYM_LPAREN, SYM_NULL), 23);
	} // while
} // factor

//////////////////////////////////////////////////////////////////////
void term(symset fsys)
{
	int mulop;
	symset set;
	
	set = uniteset(fsys, createset(SYM_TIMES, SYM_SLASH, SYM_MOD, SYM_NULL));
	factor(set);
	while (sym == SYM_TIMES || sym == SYM_SLASH || sym == SYM_MOD)
	{
		mulop = sym;
		getsym();
		factor(set);
		if (mulop == SYM_TIMES)
		{
			gen(OPR, 0, OPR_MUL);
		}
		else if(mulop == SYM_SLASH)
		{
			gen(OPR, 0, OPR_DIV);
		}
		else{
			gen(OPR, 0, OPR_MOD);
		}
	} // while
	destroyset(set);
} // term

//////////////////////////////////////////////////////////////////////
void expression(symset fsys)
{
    int addop;
            symset set;

            set = uniteset(fsys, createset(SYM_PLUS, SYM_MINUS, SYM_NULL));

            term(set);
            while (sym == SYM_PLUS || sym == SYM_MINUS)
            {
                    addop = sym;
                    getsym();
                    term(set);
                    if (addop == SYM_PLUS)
                    {
                            gen(OPR, 0, OPR_ADD);
                    }
                    else
                    {
                            gen(OPR, 0, OPR_MIN);
                    }
            } // while
    destroyset(set);
   \
} // expression

void expression_shift(symset fsys)
{
	int shop;
	symset set;

	set = uniteset(fsys, createset(SYM_SHL, SYM_SHR, SYM_NULL));
	
	expression(set);
	while (sym == SYM_SHL || sym == SYM_SHR)
	{
		shop = sym;
		getsym();
		expression(set);
		if (shop == SYM_SHL)
		{
			gen(OPR, 0, OPR_SHL);
		}
		else{
			gen(OPR, 0, OPR_SHR);
		}
	} // while

	destroyset(set);
} // expression_shift

void expression_rel(symset fsys)
{
	int relop;
	symset set;

	set = uniteset(fsys, createset(SYM_LES, SYM_LEQ, SYM_GTR, SYM_GEQ));
	
	expression_shift(set);
	while (sym == SYM_LES || sym == SYM_LEQ || sym == SYM_GTR || sym == SYM_GEQ)
	{
		relop = sym;
		getsym();
		expression_shift(set);
		if (relop == SYM_LES)
		{
			gen(OPR, 0, OPR_LES);
		}
		else if(relop == SYM_LEQ)
		{
			gen(OPR, 0, OPR_LEQ);
		}
		else if(relop == SYM_GTR){
			gen(OPR, 0, OPR_GTR);
		}
		else{
			gen(OPR, 0, OPR_GEQ);
		}
	} // while

	destroyset(set);
} // expression_rel

void expression_equ(symset fsys)
{
	int equop;
	symset set;

	set = uniteset(fsys, createset(SYM_EQU, SYM_NEQ));
	
	expression_rel(set);
	while (sym == SYM_EQU || sym == SYM_NEQ)
	{
		equop = sym;
		getsym();
		expression_rel(set);
		if (equop == SYM_EQU)
		{
			gen(OPR, 0, OPR_EQU);
		}
		else
		{
			gen(OPR, 0, OPR_NEQ);
		}
	} // while

	destroyset(set);
} // expression_equ

void expression_bit(symset fsys)
{
	int bitop;
	symset set;

	set = uniteset(fsys, createset(SYM_AND_B, SYM_XOR_B, SYM_OR_B));
	
	expression_equ(set);
	while (sym == SYM_AND_B || sym == SYM_XOR_B || sym == SYM_OR_B)
	{
		bitop = sym;
		getsym();
		expression_equ(set);
		if (bitop == SYM_AND_B)
		{
			gen(OPR, 0, OPR_AND_B);
		}
		else if (bitop == SYM_XOR_B)
		{
			gen(OPR, 0, OPR_XOR_B);
		}
		else{
			gen(OPR, 0, OPR_OR_B);
		}
	} // while

	destroyset(set);
} // expression_bit

void expression_logic(symset fsys)
{
	int logicop;
	int c1, c2, c3, c4;
	symset set;
	set = uniteset(fsys, createset(SYM_NOT, SYM_AND, SYM_OR));		//! has higher priority
	if(sym == SYM_NOT){
		getsym();
		expression_logic(set);
		gen(OPR, 0, OPR_NOT);
	}
	else{
		expression_bit(set);
	}

	while(sym == SYM_AND || sym == SYM_OR){
		if(sym == SYM_AND){
			c1 = cx;		//save next instruction number
			gen(JNZ, 0, 0);		//!=0
			c2 = cx;		//falselist
			gen(JMP, 0, 0);
			code[c1].a = cx;
			getsym();
			expression_bit(set);
			c3 = cx;		//falselist
			gen(JZ, 0, 0);		//==0
			gen(LIT, 0, 1);		//true answer
			c4 = cx;
			gen(JMP, 0, 0);
			code[c2].a = cx;
			code[c3].a = cx;
			gen(LIT, 0, 0);		//false answer
			code[c4].a = cx;		//truelist out
		}
		else{		//SYM_OR
			c1 = cx;		//truelist
			gen(JNZ, 0, 0);
			getsym();
			expression_bit(set);
			c2 = cx;		//falselist
			gen(JZ, 0, 0);
			code[c1].a = cx;
			gen(LIT, 0, 1);		//true answer
			c3 = cx;
			gen(JMP, 0, 0);		//truelist out
			code[c2].a = cx;
			gen(LIT, 0, 0);		//false answer
			code[c3].a = cx;
		}
	}
	destroyset(set);
}//expression_logic

void expression_select(symset fsys)
{
	int c1, c2;
	symset set;

	set = uniteset(fsys, createset(SYM_QUES, SYM_COLON));		//? :
	
	expression_logic(set);		//exp1
	while (sym == SYM_QUES)
	{
		c1 = cx;
		gen(JZ, 0, 0);		//if stack top is 0 then jump, else continue
		//in this condition, if exp1==1 then it won't jump, else if exp1==0 then it will jump
		getsym();
		expression_select(set);		//exp2
		c2 = cx;
		gen(JMP, 0, 0);
		code[c1].a = cx;
		getsym();
		expression_select(set);		//exp3
		code[c2].a = cx;
	} // while
	destroyset(set);
} // expression_select

void expression_assign(symset fsys)
{
	int c1, c2;
	int i=position(id);
	mask* mk;
	symset set;

	set = uniteset(fsys, createset(SYM_BECOMES));
	
	expression_select(set);
	while (sym == SYM_BECOMES)
	{		
		getsym();
		expression_assign(set);
		mk = (mask*) &table[i];
		gen(STO, level - mk->level, mk->address);
		mk = (mask*) &table[i];
		gen(LOD, level - mk->level, mk->address);
	} // while

	destroyset(set);
} // expression_assign

//////////////////////////////////////////////////////////////////////
void condition(symset fsys)
{
	int relop;
	symset set;

	int ci = 0, cj = 0;
	if (sym == SYM_ODD)
	{
		getsym();
		expression_select(fsys);
		gen(OPR, 0, 6);
	}
	else
	{
		set = uniteset(relset, fsys);
		expression_select(set);
		destroyset(set);
		if (! inset(sym, relset))
		{
			if(sym != SYM_THEN && sym != SYM_LB){
				error(20);
			}
		}
		else
		{
			relop = sym;
			getsym();
			expression_select(fsys);
			switch (relop)
			{
			case SYM_NOT:
				gen(OPR, 0, OPR_NOT);
				break;
			case SYM_EQU:
				gen(OPR, 0, OPR_EQU);
				break;
			case SYM_NEQ:
				gen(OPR, 0, OPR_NEQ);
				break;
			case SYM_LES:
				gen(OPR, 0, OPR_LES);
				break;
			case SYM_GEQ:
				gen(OPR, 0, OPR_GEQ);
				break;
			case SYM_GTR:
				gen(OPR, 0, OPR_GTR);
				break;
			case SYM_LEQ:
				gen(OPR, 0, OPR_LEQ);
				break;
			case SYM_AND:
				gen(OPR, 0, OPR_AND);
				code[ci].a = cx;
				break;
			case SYM_OR:
				gen(OPR, 0, OPR_OR);
				code[ci].a = cx;
				break;
			case SYM_AND_B:
				gen(OPR, 0, OPR_AND_B);
				code[ci].a = cx;
				break;
			case SYM_OR_B:
				gen(OPR, 0, OPR_OR_B);
				code[ci].a = cx;
				break;
			case SYM_XOR_B:
				gen(OPR, 0, OPR_XOR_B);
				code[ci].a = cx;
				break;
			} // switch
		} // else
	} // else
} // condition

//////////////////////////////////////////////////////////////////////
void statement(symset fsys)
{
	int i, cx1, cx2, cx3, cx4;
	int j3, c1=0, c2=0, c3[10]={0};
	int j;
	symset set1, set;
	int isarr = 0;
        mask *mk;

	if (sym == SYM_IDENTIFIER)
	{ // variable assignment
		mask* mk;
		mask* arr;    //get array table
		mask *mk2;   //get temporary table
	isid:
		if (! (i = position(id)))
		{
			getsym();
			if(sym == SYM_COLON){		//is a flag
				j = gotoi;
				while(j){
					if(!strcmp(id,flags[j])){
						code[gotocx[j]].a = cx;
						break;
					}
					j--;
				}
				if(!j){
					gotoi++;
					strcpy(flags[gotoi],id);
					gotocx[gotoi] = cx;
				}
				getsym();
				if(sym==SYM_IDENTIFIER)	goto isid;
				else if(sym==SYM_RETURN)	goto isret;
				else if(sym==SYM_WHILE)	goto iswhile;
				else if(sym==SYM_IF)	goto isif;
				else if(sym==SYM_EXIT)	goto isexit;
				else if(sym==SYM_FOR)	goto isfor;
				else	statement(fsys);
			}
			else error(11); // Undeclared identifier.
		}
		else if (table[i].kind != ID_VARIABLE && table[i].kind != ID_ARR && table[i].kind != ID_PROCEDURE)
		{
			error(12); // Illegal assignment.
			i = 0;
		}
		getsym();
		if (table[i].kind == ID_ARR)
		{
			isarr = 1;
			arr = (mask *) &table[i];
		}
		else	mk = (mask *) &table[i];
		if (table[i].kind == ID_ARR)
		{
			int ArrayDim = 0;
			if (sym == SYM_LBRT)		//[
			{
				if (arr->tag == 1)     //array item as parameter
				{
					gen(LOD, 0, arr->level);
					gen(LOD, 0, arr->address);
				}
				else
				{
					gen(LIT, 0, arr->level);
					gen(LIT, 0, arr->address);
				}
				while (sym == SYM_LBRT)
				{
					if (ArrayDim)
					{
						gen(LIT, 0, arr->dim[ArrayDim]);
						gen(OPR, 0, OPR_MUL);
					}
					getsym();
					expression(uniteset(fsys, createset(SYM_RBRT, SYM_NULL)));
					if (ArrayDim)
					{
						gen(OPR, 0, OPR_ADD);
					}
					ArrayDim++;
					if (sym == SYM_RBRT)		//]
					{
						getsym();
					}
					else	error(27);
				}//while
			}
			else	error(28);
		}
		/*if (sym == SYM_BECOMES)
		{
			getsym();
		}
		else
		{
			error(13); // ':=' expected.
		}
		expression_logic(uniteset(fsys, createset(SYM_SEMICOLON, SYM_NULL)));
		if (!isarr){
			if (i)	gen(STO, level - mk->level, mk->address);
		}
		else{
			if (i)	gen(STA, level, arr->address);
		}*/
		if (i){
            if ((table[i].kind == ID_VARIABLE)){
            	if (sym == SYM_BECOMES){
					getsym();
					//expression_select(uniteset(fsys, createset(SYM_SEMICOLON, SYM_NULL)));
					expression_assign(uniteset(fsys, createset(SYM_SEMICOLON, SYM_NULL)));
	            	mk = (mask*) &table[i];
	        		gen(STO, level - mk->level, mk->address);
				}
				else if(sym == SYM_ADDEQU){
		        	getsym();
                	mk = (mask*) &table[i];
			    	gen(LOD,level-mk->level,mk->address);		//get to stack top
					expression_select(uniteset(fsys, createset(SYM_SEMICOLON, SYM_NULL)));
			    	gen(OPR,0,OPR_ADD);		//=a+b
			    	gen(STO,level-mk->level,mk->address);
		        }
		        else if(sym==SYM_SUBEQU){
		        	getsym();
                	mk = (mask*) &table[i];
			    	gen(LOD,level-mk->level,mk->address);
					expression_select(uniteset(fsys, createset(SYM_SEMICOLON, SYM_NULL)));
			    	gen(OPR,0,OPR_MIN);		//=a-b
			    	gen(STO,level-mk->level,mk->address);
		        }
		    	else if(sym == SYM_MULEQU){
		        	getsym();
                	mk = (mask*) &table[i];
		   			gen(LOD,level-mk->level,mk->address);
					expression_select(uniteset(fsys, createset(SYM_SEMICOLON, SYM_NULL)));
			    	gen(OPR,0,OPR_MUL);		//=a*b
			    	gen(STO,level-mk->level,mk->address);
		        }
				else if(sym == SYM_DIVEQU){
		        	getsym();
		        	mk = (mask*) &table[i];
					gen(LOD,level-mk->level,mk->address);
					expression_select(uniteset(fsys,createset(SYM_SEMICOLON,SYM_NULL)));
			    	gen(OPR,0,OPR_DIV);		//=a/b
			    	gen(STO,level-mk->level,mk->address);
		        }
		        else if(sym == SYM_MODEQU){
					getsym();
					mk = (mask*) &table[i];
					gen(LOD,level-mk->level,mk->address);
					expression_select(uniteset(fsys,createset(SYM_SEMICOLON,SYM_NULL)));
			    	gen(OPR,0,OPR_MOD);		//=a%b
			    	gen(STO,level-mk->level,mk->address);
				}
				else if(sym == SYM_SHLEQU){
					getsym();
					mk = (mask*) &table[i];
					gen(LOD,level-mk->level,mk->address);
					expression_select(uniteset(fsys,createset(SYM_SEMICOLON,SYM_NULL)));
			    	gen(OPR,0,OPR_SHL);		//=a<<b
			    	gen(STO,level-mk->level,mk->address);
				}
				else if(sym == SYM_SHREQU){
					getsym();
					mk = (mask*) &table[i];
					gen(LOD,level-mk->level,mk->address);
					expression_select(uniteset(fsys,createset(SYM_SEMICOLON,SYM_NULL)));
			    	gen(OPR,0,OPR_SHR);		//=a>>b
			    	gen(STO,level-mk->level,mk->address);
				}
				else if(sym == SYM_ADDADD){
			    	mk = (mask*) &table[i];
			    	gen(LOD,level-mk->level,mk->address);
					add: 
			    	getsym();
			    	while(sym == SYM_ADDADD){
			    		getsym();
			    		gen(LIT,0,1);
			    		gen(OPR,0,OPR_ADD);		//=a+1
					}
			    	gen(LIT,0,1);
			    	gen(OPR,0,OPR_ADD);		//=a+1
					if(sym == SYM_SUBSUB)	goto sub;
					gen(STO,level-mk->level,mk->address);
				}
				else if(sym == SYM_SUBSUB){
			    	mk = (mask*) &table[i];
			    	gen(LOD,level-mk->level,mk->address);
					sub: 
			    	getsym();
			    	while(sym == SYM_SUBSUB){
			    		getsym();
			    		gen(LIT,0,1);
			    		gen(OPR,0,OPR_MIN);		//a-1
					}
			    	gen(LIT,0,1);
			    	gen(OPR,0,OPR_MIN);		//a-1
					if(sym == SYM_ADDADD)	goto add;
					gen(STO,level-mk->level,mk->address);
				}
				else error(13);   
            }
            else if(table[i].kind == ID_PROCEDURE){
				int index;
            	mask* mk;
				mask* ay;
            	mk = (mask*) &table[i];
            	//getsym();
				if (sym == SYM_LPAREN)		//( 
				{
					getsym();
					if(sym == SYM_RPAREN){		//), no parameters
						getsym();
					}
					else{
						expression_select(uniteset(fsys, createset(SYM_SEMICOLON, SYM_NULL)));
						while (sym == SYM_COMMA)		//,
						{
							getsym();
							expression_select(uniteset(fsys, createset(SYM_SEMICOLON, SYM_NULL)));
						}
						if (sym == SYM_RPAREN)		//)
						{
							getsym();
						}
						else
						{
							error(22);
						}
					}
				}
				gen(CAL, level - mk->level, mk->address);
			}
            else{
            	if(sym == SYM_BECOMES){
					getsym();
					expression_select(uniteset(fsys, createset(SYM_SEMICOLON, SYM_NULL)));
        			mk = (mask*) &table[i];
            		gen(STA, level - mk->level, mk->address);
				}
               else error(13); // ':=' expected.
            }
        }
	}
	/*else if (sym == SYM_CALL)
	{ // procedure call
		getsym();
		if (sym != SYM_IDENTIFIER)
		{
			error(14); // There must be an identifier to follow the 'call'.
		}
		else
		{
			if (! (i = position(id)))
			{
				error(11); // Undeclared identifier.
			}
			else if (table[i].kind == ID_PROCEDURE)
			{
				mask* mk;
				mk = (mask*) &table[i];
				gen(CAL, level - mk->level, mk->address);
			}
			else
			{
				error(15); // A constant or variable can not be called. 
			}
			getsym();
		}
	}*/ //12_13 delete "call"
	else if(sym == SYM_RETURN){		//return procedure
	isret:
		getsym();
		if(sym != SYM_SEMICOLON){
			expression_select(uniteset(fsys, createset(SYM_SEMICOLON, SYM_NULL)));
			gen(RET, 0, 0);
		}
		else{
			gen(OPR, 0, OPR_RET);
		}
	}
	else if (sym == SYM_IF)
	{ // if statement
	isif:
        getsym();
        set1 = createset(SYM_THEN, SYM_NULL);
        set = uniteset(set1, fsys);
        condition(set);
        destroyset(set1);
        destroyset(set);
        if (sym == SYM_THEN)
            getsym();
        else error(16);
        cx1 = cx;
        gen(JPC, 0, 0);		//to else or go out
        statement(uniteset(fsys, createset(SYM_ELSE, SYM_ELIF,SYM_NULL)));
        getsym();
        if(sym == SYM_ELSE){
            cx2 = cx; //??????????
            gen(JMP, 0, 0); //?????????????????????????0
            getsym();
            code[cx1].a = cx; //????????????????????????else?????????
            statement(fsys); //???else??????
            code[cx2].a = cx; //?????????????????????then??????????else????
        }
		else { //??????else
            code[cx1].a = cx; //???????????????????????????then????????
        }
        if(sym == SYM_ELIF){
            getsym();
            set1 = createset(SYM_THEN, SYM_NULL);
            set = uniteset(set1, fsys);
            condition(set);
            destroyset(set1);
            destroyset(set);
            if (sym == SYM_THEN)
                getsym();
            else error(16);
            cx1 = cx;
            gen(JPC, 0, 0);		//to else or go out
            statement(uniteset(fsys, createset(SYM_ELSE, SYM_NULL)));
        }
	}
	else if (sym == SYM_BEGIN)
	{ // block
		getsym();
		set1 = createset(SYM_SEMICOLON, SYM_END, SYM_NULL);
		set = uniteset(set1, fsys);
		statement(set);
		while (sym == SYM_SEMICOLON || inset(sym, statbegsys))
		{
			if (sym == SYM_SEMICOLON)
			{
				getsym();
			}
			else
			{
				error(10);
			}
			statement(set);
		} // while
		destroyset(set1);
		destroyset(set);
		if (sym == SYM_END)
		{
			getsym();
		}
		else
		{
			error(17); // ';' or 'end' expected.
		}
	}
	else if (sym == SYM_WHILE)
	{ // while statement
	iswhile:
		c1 = cx;
		getsym();
		set1 = createset(SYM_LB, SYM_NULL);
		set = uniteset(set1, fsys);
		condition(set);
		destroyset(set1);
		destroyset(set);
		c2 = cx;
		gen(JZ, 0, 0);
		if (sym == SYM_LB)
		{
			getsym();
		}
		else
		{
			error(33); // '{' expected.
		}
		j3 = 0;
		while(sym != SYM_RB){		//'}'
			//statement(fsys);
			if(sym == SYM_BREAK){		//break
				j3++;
				c3[j3] = cx;
				gen(JMP, 0, 0);
				getsym();
			}
			else if(sym == SYM_CONTINUE){		//continue
				gen(JMP, 0, c1);
				getsym();
			}
			else if (sym == SYM_IF)
			{
			    getsym();
		        set1 = createset(SYM_THEN, SYM_NULL);
		        set = uniteset(set1, fsys);
		        condition(set);
		        destroyset(set1);
		        destroyset(set);
		        if (sym == SYM_THEN)
		            getsym();
		        else error(16);
		        
		        cx1 = cx;
		        gen(JZ, 0, 0);		//to else or go out
				if(sym == SYM_BREAK){
		        	j3++;
		        	c3[j3] = cx;
					gen(JMP, 0, 0);
					getsym();
				}
				else if(sym == SYM_CONTINUE){
					gen(JMP, 0, c1);
					getsym();
				}
		        else{
		        	statement(uniteset(fsys, createset(SYM_ELSE, SYM_ELIF,SYM_NULL)));
				}
		        getsym();
		        if(sym == SYM_ELSE){
		            cx2 = cx; //??????????
		            gen(JMP, 0, 0); //?????????????????????????0
		            getsym();
		            code[cx1].a = cx; //????????????????????????else?????????
		            if(sym == SYM_BREAK){
			        	j3++;
			        	c3[j3] = cx;
						gen(JMP, 0, 0);
						getsym();
					}
					else if(sym == SYM_CONTINUE){
						gen(JMP, 0, c1);
						getsym();
					}
					else{
						statement(fsys); //???else??????
					}
		            code[cx2].a = cx; //?????????????????????then??????????else????
		        }
				else { //??????else
		            code[cx1].a = cx; //???????????????????????????then????????
		        }
		        if(sym == SYM_ELIF){
		            getsym();
		            set1 = createset(SYM_THEN, SYM_NULL);
		            set = uniteset(set1, fsys);
		            condition(set);
		            destroyset(set1);
		            destroyset(set);
		            if (sym == SYM_THEN)
		                getsym();
		            else error(16);
		            cx1 = cx;
		            gen(JZ, 0, 0);		//to else or go out
		            if(sym == SYM_BREAK){
		            	j3++;
		            	c3[j3] = cx;
						gen(JMP, 0, 0);
		            	getsym();
					}
					else if(sym == SYM_CONTINUE){
						gen(JMP, 0, c1);
						getsym();
					}
					else{
						statement(uniteset(fsys, createset(SYM_ELSE, SYM_NULL)));
					}
		        }
			}
			else{
				statement(fsys);
				getsym();
			}
		}
		gen(JMP, 0, c1);
		code[c2].a = cx;
		while(j3 > 0){
			code[c3[j3]].a = cx;
			j3--;
		}
		getsym();
		statement(fsys);
	}
	else if(sym == SYM_EXIT){
	isexit:
		gen(EXT, 0, 0);
		getsym();
	}
	else if(sym == SYM_GOTO){
		getsym();
		if(sym == SYM_IDENTIFIER){		//goto flags
			j = gotoi;
			while(j){
				if(!strcmp(id, flags[j])){
					gen(JMP, 0, gotocx[j]);
					break;
				}
				j--;
			}
			if(!j){
				gotoi++;
				strcpy(flags[gotoi],id);
				gotocx[gotoi] = cx;
				gen(JMP, 0, 0);
			}
		}
		getsym();
	}
    else if (sym == SYM_FOR){
    isfor:
        getsym();
        if(sym != SYM_LPAREN)
            error(30);
        getsym();

        if (sym != SYM_IDENTIFIER)
            error(4);
        statement(fsys);
        cx1=cx;

        if (sym != SYM_SEMICOLON) //;
            error(10);
        getsym();
        expression_logic(fsys);
        cx2=cx; gen(JPC, 0, 0);		//出循环 
        cx3=cx; gen(JMP, 0, 0);		//跳到执行代码 
        if (sym != SYM_SEMICOLON) //;
            error(10);
        getsym();
        cx4=cx;
        statement(fsys);
		gen(JMP, 0, cx1);		//返回循环 

        if(sym != SYM_RPAREN)
            error(22);

        getsym();
        code[cx3].a = cx;
        statement(fsys);

        /*	  处理循环变量
              将循环变量地址压到栈顶
              将循环变量压到栈顶
              将步长压到栈顶
              执行 add 命令， 弹出栈顶和次栈顶， 将 add 结果压到栈顶
              执行 sto 命令， 弹出栈顶和次栈顶， 将栈顶的值存入次栈顶对应的地址中去，不再压栈
        */

        gen(LIT, 0, STEP); //??????????
        gen(OPR, 0, OPR_MIN); //??????
        gen(JMP, 0, cx4);//执行自增等指令 
        code[cx2].a = cx;
    }
        //test(fsys, phi, 19);
} // statement
			
//////////////////////////////////////////////////////////////////////
void block(symset fsys)
{
	int cx0; // initial code index
	mask* mk;
	int block_dx;
	int savedTx;
	symset set1, set;

	dx = 3;
	block_dx = dx;
	if (ProcedureDepth)
	{
		mk = (mask*) &table[tx - paracount[ProcedureDepth - 1]];
	}
	else
	{
		mk = (mask*) &table[tx];
	}
	//mk = (mask*) &table[tx];
	mk->address = cx;
	gen(JMP, 0, 0);
	if (level > MAXLEVEL)
	{
		error(32); // There are too many levels.
	}
	do
	{
		if (sym == SYM_CONST)
		{ // constant declarations
			getsym();
			do
			{
				constdeclaration();
				while (sym == SYM_COMMA)
				{
					getsym();
					constdeclaration();
				}
				if (sym == SYM_SEMICOLON)
				{
					getsym();
				}
				else
				{
					error(5); // Missing ',' or ';'.
				}
			}
			while (sym == SYM_IDENTIFIER);
		} // if

		if (sym == SYM_VAR)
		{ // variable declarations
			getsym();
			do
			{
				vardeclaration();
				while (sym == SYM_COMMA)
				{
					getsym();
					vardeclaration();
				}
				if (sym == SYM_SEMICOLON)
				{
					getsym();
				}
				else
				{
					error(5); // Missing ',' or ';'.
				}
			}
			while (sym == SYM_IDENTIFIER);
		} // if
		block_dx = dx; //save dx before handling procedure call!
		while (sym == SYM_PROCEDURE)
		{ // procedure declarations
			int ParaNum = 0;
			getsym();
			if (sym == SYM_IDENTIFIER)
			{
				enter(ID_PROCEDURE);
				getsym();
			}
			else
			{
				error(4); // There must be an identifier to follow 'const', 'var', or 'procedure'.
			}
			savedTx = tx;
			level++;
			if (sym == SYM_LPAREN)
			{
				int t = 0;
				int savet1;
				int savet2;
				int space = 0;
				mask* pm;
				getsym();
				if(sym == SYM_RPAREN){		//), no parameter.
					ParaNum = 0;
					getsym();
				}
				else{
					space = (sym == ID_VARIABLE) ? space + 1 : space + 2;		//1 for var, 2 for arr
					ParaDecalration();
					savet1 = tx;		//first para
					ParaNum++;
					while (sym == SYM_COMMA)
					{
						getsym();
						space = (sym == ID_VARIABLE) ? space + 1 : space + 2;
						ParaDecalration();
						ParaNum++;
					}
					savet2 = tx;		//last para
					for (t = savet1; t <= savet2; t++)
					{
						pm = (mask *) &table[t];
						if (table[t].kind == ID_VARIABLE)
						{
							pm->address = 0 - space;		//addr is below 0
							space = space - 1;
						}
						else
						{
							pm->level = -space;
							space--;
							pm->address = -space;
							space--;
						}
					}
					if (sym == SYM_RPAREN)
					{
						getsym();
					}
					else
					{
						error(22);
					}
				}
			}
			/*if (sym == SYM_SEMICOLON)
			{
				getsym();
			}
			else
			{
				error(5); // Missing ',' or ';'.
			}*/
			paracount[ProcedureDepth] = ParaNum;
			ProcedureDepth++;
			set1 = createset(SYM_SEMICOLON, SYM_NULL);
			set = uniteset(set1, fsys);
			block(set);
			destroyset(set1);
			destroyset(set);
			tx = savedTx;
			level--;
			ProcedureDepth--;
			if (sym == SYM_SEMICOLON)
			{
				getsym();
				set1 = createset(SYM_IDENTIFIER, SYM_PROCEDURE, SYM_NULL);
				set = uniteset(statbegsys, set1);
				test(set, fsys, 6);
				destroyset(set1);
				destroyset(set);
			}
			else
			{
				error(5); // Missing ',' or ';'.
			}
		} // while
		dx = block_dx; //restore dx after handling procedure call!
		set1 = createset(SYM_IDENTIFIER, SYM_NULL);
		set = uniteset(statbegsys, set1);
		test(set, declbegsys, 7);
		destroyset(set1);
		destroyset(set);
	}
	while (inset(sym, declbegsys));

	code[mk->address].a = cx;
	mk->address = cx;
	cx0 = cx;
	gen(INT, 0, block_dx);
	set1 = createset(SYM_SEMICOLON, SYM_END, SYM_NULL);
	set = uniteset(set1, fsys);
	statement(set);
	destroyset(set1);
	destroyset(set);
	gen(OPR, 0, OPR_RET); // return
	test(fsys, phi, 8); // test for error: Follow the statement is an incorrect symbol.
	listcode(cx0, cx);
} // block

//////////////////////////////////////////////////////////////////////
int base(int stack[], int currentLevel, int levelDiff)
{
	int b = currentLevel;
	
	while (levelDiff--)
		b = stack[b];
	return b;
} // base

//////////////////////////////////////////////////////////////////////
// interprets and executes codes.
void interpret()
{
	int pc;        // program counter
	int stack[STACKSIZE];
	int top;       // top of stack
	int b;         // program base, and top-stack register
	instruction i; // instruction register
	int j = 0;		//to record dimension
	int ArrayOffset;
	printf("Begin executing PL/0 program.\n");
	
	
	int temp;
	int tempb;

	pc = 0;
	b = 1;
	top = 3;
	stack[1] = stack[2] = stack[3] = 0;
	do
	{
		i = code[pc++];
		switch (i.f)
		{
		case LIT:
			stack[++top] = i.a;
			break;
		case OPR:
			switch (i.a) // operator
			{
			case OPR_RET:
				top = b - 1;
				pc = stack[top + 3];
				b = stack[top + 2];
				break;
			case OPR_NEG:
				stack[top] = -stack[top];
				break;
			case OPR_ADD:
				top--;
				stack[top] += stack[top + 1];
				break;
			case OPR_MIN:
				top--;
				stack[top] -= stack[top + 1];
				break;
			case OPR_MUL:
				top--;
				stack[top] *= stack[top + 1];
				break;
			case OPR_DIV:
				top--;
				if (stack[top + 1] == 0)
				{
					fprintf(stderr, "Runtime Error: Divided by zero.\n");
					fprintf(stderr, "Program terminated.\n");
					continue;
				}
				stack[top] /= stack[top + 1];
				break;
			case OPR_ODD:
				stack[top] %= 2;
				break;
			case OPR_EQU:
				top--;
				stack[top] = stack[top] == stack[top + 1];
				break;
			case OPR_NEQ:
				top--;
				stack[top] = stack[top] != stack[top + 1];
				break;
			case OPR_LES:
				top--;
				stack[top] = stack[top] < stack[top + 1];
				break;
			case OPR_GEQ:
				top--;
				stack[top] = stack[top] >= stack[top + 1];
				break;
			case OPR_GTR:
				top--;
				stack[top] = stack[top] > stack[top + 1];
				break;
			case OPR_LEQ:
				top--;
				stack[top] = stack[top] <= stack[top + 1];
				break;
			case OPR_AND:
				top--;
				if ((stack[top] != 0) && (stack[top + 1] != 0))
				{
					stack[top] = 1;
				}
				else
					stack[top] = 0;
				break;
			case OPR_OR:
				top--;
				if ((stack[top] != 0) || (stack[top + 1] != 0))
				{
					stack[top] = 1;
				}
				else
					stack[top] = 0;
				break;
			case OPR_NOT:
				if (stack[top] == 0)
					stack[top] = 1;
				else
					stack[top] = 0;
				break;
			case OPR_AND_B:
				top--;
				stack[top] = stack[top] & stack[top + 1];
				break;
			case OPR_OR_B:
				top--;
				stack[top] = stack[top] | stack[top + 1];
				break;
			case OPR_XOR_B:
				top--;
				stack[top] = stack[top] ^ stack[top + 1];
				break;
			case OPR_MOD:
				top--;
				stack[top] = stack[top] % stack[top + 1];
				break;
			case OPR_SHL:
				top--;
				stack[top] = stack[top] << stack[top + 1];
				break;
			case OPR_SHR:
				top--;
				stack[top] = stack[top] >> stack[top + 1];
				break;
			} // switch
			break;
		case LOD:
			stack[++top] = stack[base(stack, b, i.l) + i.a];
			break;
		case STO:
			stack[base(stack, b, i.l) + i.a] = stack[top];
			printf("%d\n", stack[top]);
			top--;
			break;
		case CAL:
			stack[top + 1] = base(stack, b, i.l);
			// generate new block mark
			stack[top + 2] = b;
			stack[top + 3] = pc;
			b = top + 1;
			pc = i.a;
			top = top + 4;
			break;
		case RET:
			temp = top;
			top = b - 1;
			pc = stack[top + 3];
			b = stack[top + 2];
			stack[top] = stack[temp];
			break;
		case INT:
			top += i.a;
			break;
		case JMP:
			pc = i.a;
			break;
		case JPC:
			if (stack[top] == 0)
				pc = i.a;
			top--;
			break;
		case EXT:
			printf("PL/0 program exit.\n");
			goto ext;
		case STA:
			i.l = i.l - stack[top - 3];
			i.a = stack[top - 2];
			ArrayOffset = base(stack, b, i.l) + i.a + stack[top - 1];
			stack[ArrayOffset] = stack[top];
			printf("%d\n", stack[top]);
			top = top - 4;
			break;
		case LTA:
			i.l = i.l - stack[top - 2];
			i.a = stack[top - 1];
			ArrayOffset = base(stack, b, i.l) + i.a + stack[top];
			top = top - 2;
			stack[top] = stack[ArrayOffset];
			break;
		case JNZ:
			if(stack[top] != 0)	pc = i.a;
			top--;
			break;
		case JZ:
			if(stack[top] == 0)	pc = i.a;
			top--;
			break;
		} // switch
	}
	while (pc);
	ext: 
	printf("End executing PL/0 program.\n");
} // interpret

//////////////////////////////////////////////////////////////////////
void main ()
{
	FILE* hbin;
	char s[80];
	int i;
	symset set, set1, set2;

    /*    printf("Please input source file name: "); // get file name to be compiled
        scanf("%s", s);
	if ((infile = fopen(s, "r")) == NULL)
	{
		printf("File %s can't be opened.\n", s);
		exit(1);
        }*/
    infile=fopen("../../8.txt","r");

	phi = createset(SYM_NULL);
	relset = createset(SYM_EQU, SYM_NEQ, SYM_LES, SYM_LEQ, SYM_GTR, SYM_GEQ, SYM_NULL);
	
	// create begin symbol sets
	declbegsys = createset(SYM_CONST, SYM_VAR, SYM_PROCEDURE, SYM_NULL);
	statbegsys = createset(SYM_BEGIN, SYM_IF, SYM_WHILE, SYM_NULL);
	facbegsys = createset(SYM_IDENTIFIER, SYM_NUMBER, SYM_RAND, SYM_LPAREN, SYM_MINUS, SYM_NULL);

	err = cc = cx = ll = 0; // initialize global variables
	ch = ' ';
	kk = MAXIDLEN;

	getsym();

	set1 = createset(SYM_PERIOD, SYM_NULL);
	set2 = uniteset(declbegsys, statbegsys);
	set = uniteset(set1, set2);
	block(set);
	destroyset(set1);
	destroyset(set2);
	destroyset(set);
	destroyset(phi);
	destroyset(relset);
	destroyset(declbegsys);
	destroyset(statbegsys);
	destroyset(facbegsys);

	if (sym != SYM_PERIOD)
		error(9); // '.' expected.
	if (err == 0)
	{
		hbin = fopen("hbin.txt", "w");
		for (i = 0; i < cx; i++)
			fwrite(&code[i], sizeof(instruction), 1, hbin);
		fclose(hbin);
	}
	if (err == 0)
		interpret();
	else
		printf("There are %d error(s) in PL/0 program.\n", err);
	listcode(0, cx);
} // main

//////////////////////////////////////////////////////////////////////
// eof pl0.c
