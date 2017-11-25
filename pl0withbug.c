// pl0 compiler source code

#pragma warning(disable:4996)


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

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
			sym = SYM_NULL;       // illegal?
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
			getch();
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
			getch();
		}
	}
	else if(ch == '^'){		//^
		sym = SYM_XOR_B;
		getch();
	}
	else if(ch == '%'){		//%
		sym = SYM_MOD;
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
			sym = ssym[i];
			getch();
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
int position(char* id) {
        int i;
        strcpy(table[0].name, id);
        i = tx + 1;
        while (strcmp(table[--i].name, id) != 0)
                ;
        mask * mk = (mask*) &table[i];
        array * ar = (array*) &table[i];
        if (mk->level == level) { //cy_quote
                table[i].quote = 1;
        } else
                table[i].quote = 2;

        return i;
} // position

int constfactor(symset fsys) {
        int constexpre(symset fsys);
        int i;
        int n;
        symset set;

        test(facbegsys, fsys, 24); // The symbol can not be as the beginning of an expression.

        while (inset(sym, facbegsys)) {
                if (sym == SYM_IDENTIFIER) {
                        if ((i = position(id)) == 0) {
                                error(11); // Undeclared identifier.
                        } else {
                                array* ar = (array*) &table[i];

                                switch (table[i].kind) {
                                mask* mk;
                        case ID_CONSTANT:
                                n = table[i].value;
                                getsym();
                                break;
                        case ID_VARIABLE:
                                error(37);
                                getsym();
                                break;
                        case ID_PROCEDURE:
                                error(21); // Procedure identifier can not be in an expression.
                                getsym();
                                break;
                        default:
                                error(37);
                                break;
                                } // switch
                        }
                } else if (sym == SYM_NUMBER) {
                        if (num > MAXADDRESS) {
                                error(25); // The number is too great.
                                num = 0; //number???????????0
                        }
                        n = num;
                        getsym();
                } else if (sym == SYM_LPAREN) //(expression)
                                {
                        getsym();
                        set = uniteset(createset(SYM_RPAREN, SYM_NULL), fsys);
                        n = constexpre(set);
                        destroyset(set);
                        if (sym == SYM_RPAREN) {
                                getsym();
                        } else {
                                error(22); // Missing ')'.
                        }
                }
                //test(fsys, createset(SYM_LPAREN, SYM_NULL), 23);
        } // while
        return n;
} // factor

int constterm(symset fsys) {
        int mulop;
        symset set;

        set = uniteset(fsys, createset(SYM_TIMES, SYM_SLASH, SYM_NULL));
        int n1 = constfactor(set);
        int n = n1;
        while (sym == SYM_TIMES || sym == SYM_SLASH) {
                mulop = sym;
                getsym();
                int n2 = constfactor(set);
                if (mulop == SYM_TIMES) {
                        n1 = n1 * n2;
                } else {
                        n1 = n1 / n2;
                }
        } // while
        destroyset(set);
        return n1;
} // term

int constexpre(symset fsys) {
        int addop;
        symset set;
        int n = 0;
        set = uniteset(fsys, createset(SYM_PLUS, SYM_MINUS, SYM_NULL));
        if (sym == SYM_PLUS || sym == SYM_MINUS) {
                addop = sym;
                getsym();
                n = constterm(set);
                if (addop == SYM_MINUS) {
                        n = -n;
                }
        } else {
                n = constterm(set);
        }

        while (sym == SYM_PLUS || sym == SYM_MINUS) {
                addop = sym;
                getsym();
                int n1 = constterm(set);
                if (addop == SYM_PLUS) {
                        n = n + n1;
                } else {
                        n = n - n1;
                }
        } // while

        destroyset(set);
        return n;
} // expression

void dimdeclaration(void) {
        void enter(int kind);
        char idsaved[MAXIDLEN + 1] = { '\0' };
        int constexpre(symset fsys);
        strcpy(idsaved, id);
        dim = 0; //?????
        array_size = 1; //?????
        while (sym == SYM_LSQUARE) { //'['
                getsym();
                /*if (sym == SYM_NUMBER) {
                 latit[dim++] = num;
                 array_size *= num;
                 getsym();
                 } else {
                 error(26); //lack num
                 }*/
                symset set = createset(SYM_RSQUARE, SYM_NULL);
                int nn = constexpre(set);
                latit[dim++] = nn;
                destroyset(set);
                array_size *= nn;
                if (sym == SYM_RSQUARE) { //']'
                        getsym();
                } else {
                        error(27); //lack ']'
                }
        }
        strcpy(id, idsaved);
        enter(ID_ARRAY);

}
//////////////////////////////////////////////////////////////////////
// tests if error occurs and skips all symbols that do not belongs to s1 or s2.


//////////////////////////////////////////////////////////////////////
int dx[MAXLEVEL];  // data allocation index
int zx[MAXLEVEL];
// enter object(constant, variable or procedre) into table.
void enter(int kind)
{
	mask* mk;
        array* ar;
                tx++;
                //search the name before entering
                int i;
                for (i = tx_[level]; i < tx; i++) {
                        if (!strcmp(id, table[i].name)) {
                                error(36);
                                goto l1;
                        }
                }

                strcpy(table[tx].name, id);
                table[tx].kind = kind;
        table[tx].quote = 0; //cy_quote
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
                mk->address = dx[level]++;
		break;
	case ID_PROCEDURE:
		mk = (mask*) &table[tx];
		mk->level = level;
		break;
        case ID_ARRAY:
                        ar = (array*) &table[tx];
                        ar->dim_n = dim;
                        ar->level = level;
                        ar->address = dx[level];
                        ar->kind = (short) kind;
                        dx[level] += array_size;
                        p_dim* p = NULL;
                        int i;
                        for (i = dim - 1; i >= 0; i--) {
                                p_dim* q = (p_dim*) malloc(sizeof(p_dim));
                                q->dim_len = latit[i];
                                q->next = p;
                                p = q;
                        }
                        ar->next = p;
                        break;
	} // switch
        l1: ;
} // enter

//////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////
void constdeclaration(symset fsys)
{
    int constexpre(symset fsys);
            if (sym == SYM_IDENTIFIER) {
                    getsym();
                    if (sym == SYM_EQU || sym == SYM_BECOMES) {
                            if (sym == SYM_BECOMES)
                                    error(1); // Found ':=' when expecting '='.
                            getsym();
                            num = constexpre(
                                            uniteset(fsys, createset(SYM_SEMICOLON, SYM_NULL)));
                            enter(ID_CONSTANT);
                    } else {
                            error(3); // There must be an '=' to follow the identifier.
                    }
            } else
                    error(4);
            // There must be an identifier to follow 'const', 'var', or 'procedure'.
} // constdeclaration

//////////////////////////////////////////////////////////////////////
void vardeclaration(void)
{
    if (sym == SYM_IDENTIFIER) {
                    char idsaved[MAXIDLEN + 1] = { '\0' };
                    strcpy(idsaved, id);
                    getsym();
                    if (sym == SYM_LSQUARE) {
                            strcpy(id, idsaved);
                            dimdeclaration();
                    } else {
                            char idsaved2[MAXIDLEN + 1] = { '\0' };
                            strcpy(idsaved2, id);
                            strcpy(id, idsaved);
                            enter(ID_VARIABLE);
                            strcpy(id, idsaved2);
                    }
    }
	else
	{
		error(4); // There must be an identifier to follow 'const', 'var', or 'procedure'.
	}
} // vardeclaration

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
	symset set;
        array* ar;
	test(facbegsys, fsys, 24); // The symbol can not be as the beginning of an expression.

	while (inset(sym, facbegsys))
	{
		if (sym == SYM_IDENTIFIER)
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
				case ID_CONSTANT:
					gen(LIT, 0, table[i].value);
					break;
				case ID_VARIABLE:
					mk = (mask*) &table[i];
					gen(LOD, level - mk->level, mk->address);
					break;
				case ID_PROCEDURE:
					error(21); // Procedure identifier can not be in an expression.
					break;
                                default:
                                            if ((ar->kind == ID_ARRAY)) { //???????????????????
                                                                                    getsym();
                                                                                    int dl = 0;
                                                                                    p_dim* p = ar->next;
                                                                                    if (sym == SYM_LSQUARE) {
                                                                                            gen(LIT, 0, 0);
                                                                                            gen(LIT, 0, p->dim_len);
                                                                                            while (sym == SYM_LSQUARE) {
                                                                                                    if (p) {
                                                                                                            p = p->next;
                                                                                                    }
                                                                                                    gen(OPR, 0, OPR_MUL);
                                                                                                    getsym();
                                                                                                    expression(
                                                                                                                    uniteset(fsys,
                                                                                                                                    createset(SYM_COMMA, SYM_NULL)));
                                                                                                    dl++;
                                                                                                    if (sym == SYM_RSQUARE) {
                                                                                                            getsym();
                                                                                                    } else {
                                                                                                            error(27);
                                                                                                    }
                                                                                                    gen(OPR, 0, OPR_ADD);
                                                                                                    if (p) {
                                                                                                            gen(LIT, 0, p->dim_len);
                                                                                                    }
                                                                                            }
                                                                                            if (dl != ar->dim_n) {
                                                                                                    error(26);
                                                                                            }
                                                                                            gen(LAD, level - ar->level, ar->address);
                                                                                    } else {
                                                                                            error(28); //need'['
                                                                                    }
                                                                            }
                                            break;
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
			expression(set);
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
		else if(sym == SYM_MINUS) // UMINUS,  Expr -> '-' Expr
		{  
			 getsym();
			 expression(fsys);
			 gen(OPR, 0, OPR_NEG);
		}
		test(fsys, createset(SYM_LPAREN, SYM_NULL), 23);
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
} // expression

void expression_rel(symset fsys)
{
	int relop;
	symset set;

	set = uniteset(fsys, createset(SYM_LES, SYM_LEQ, SYM_GTR, SYM_GEQ));
	
	expression(set);
	while (sym == SYM_LES || sym == SYM_LEQ || sym == SYM_GTR || sym == SYM_GEQ)
	{
		relop = sym;
		getsym();
		expression(set);
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
		expression_equ(set);
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
		expression_bit(set);
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

void expression_bool(symset fsys)
{
	int boolop;
	int ci, cj;
	symset set;
	set = uniteset(fsys, createset(SYM_NOT, SYM_AND, SYM_OR));/*´´½¨Ò»¸ö!£¬&&£¬||µÄ·ûºÅ¼¯*/
	//»ùÓÚÓÅÏÈ¼¶µÄ¹ØÏµ£¬ÏÈÅÐ¶Ï !
	if (sym == SYM_NOT)
	{
		getsym();
		expression_bit(set);//µ÷ÓÃº¯Êý
		gen(OPR, 0, OPR_NOT);//²úÉúnotÖ¸Áî
	}
	else
	{
		expression_bit(set);//µ÷ÓÃexpression()º¯Êý
	}

	while (sym == SYM_AND || sym == SYM_OR)
	{

		gen(LIT, 0, 0);   //Õ»¶¥ÔªËØÔªËØ³õÊ¼»¯Îª0
						  ////////////////////////¶ÌÂ·Ìø×ª///////////////////////////////////
		if (sym == SYM_AND)
			gen(OPR, 0, OPR_EQU);//   =£¬Èç¹ûÊÇandÔËËã£¬²¢ÇÒÓë0ÏàµÈ£¬ÔòÉ¾³ýÕâÁ½¸ö0£¬²¢½«1Ñ¹½øÕ»
		else//sym=SYM_OR
			gen(OPR, 0, OPR_GTR);//  >£¬Èç¹ûÊÇorÔËËã£¬²¢ÇÒ1´óÓÚ0£¬ÔòÉ¾³ý0ºÍ1£¬²¢½«1Ñ¹½øÕ»
		cj = cx;//±£´æµ±Ç°ÎªµÚ¼¸ÌõÖ¸Áî
		gen(JPC, 0, 0);//Õ»¶¥ÔªËØÎª0£¬Ìø×ª£»1µÄ»°£¬²»Ìø×ª
					   /////////////////////»Ö¸´Õ»¶¥ÔªËØ//////////////////////////////
		if (sym == SYM_AND)
			gen(LIT, 0, 0);
		else
			gen(LIT, 0, 1);
		gen(LIT, 0, 0);
		ci = cx;//±£´æµ±Ç°ÎªµÚ¼¸ÌõÖ¸Áî
		gen(JPC, 0, 0);
		code[cj].a = cx;
		/**/
		if (sym == SYM_AND)
			gen(LIT, 0, 1);
		else
			gen(LIT, 0, 0);

		boolop = sym;
		getsym();//
		expression_bool(set);     //ÓÅÏÈ¼¶
		if (boolop == SYM_AND)
		{
			gen(OPR, 0, OPR_AND);
		}
		else
		{
			gen(OPR, 0, OPR_OR);
		}
		code[ci].a = cx;//È·¶¨Ìø×ªµÄÎ»ÖÃ
	} // while
	destroyset(set);
}

//////////////////////////////////////////////////////////////////////
void condition(symset fsys)
{
	int relop;
	symset set;

	int ci = 0, cj = 0;
	if (sym == SYM_ODD)
	{
		getsym();
		expression_bool(fsys);
		gen(OPR, 0, 6);
	}
	else
	{
		set = uniteset(relset, fsys);
		expression_bool(set);
		destroyset(set);
		if (! inset(sym, relset))
		{
                        if(sym != SYM_THEN)
                        error(20);
		}
		else
		{
			relop = sym;
			getsym();
			expression_bool(fsys);
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
int arsize(int i) {
        array *ar = (array*) &table[i];
        p_dim *p = ar->next;
        int c = 1;
        while (p) {
                c *= p->dim_len;
                p = p->next;
        }
        /*	for (int i = ar->dim_n; i; i--) {
         printf("i:%d",i);
         c *= p->dim_len;
         p=p->next;
         }*/
        return c;
}
void enterPar() {
        mask* mk;
        tx++;
        strcpy(table[tx].name, id);
        table[tx].kind = ID_VARIABLE;
        mk = (mask*) &table[tx];
        mk->level = level + 1; //differences
        mk->address = zx[level]++; //differences
}
void modifyTable(int numOfPar) {
        int i;
        mask* mk;
        for (i = 0; i < numOfPar; i++) {
                mk = (mask*) &table[tx - i];
                mk->address = mk->address - numOfPar;
        }
}
//////////////////////////////////////////////////////////////////////
void statement(symset fsys)
{
	int i, cx1, cx2;
	symset set1, set;

	if (sym == SYM_IDENTIFIER)
	{ // variable assignment
		mask* mk;
		if (! (i = position(id)))
		{
			error(11); // Undeclared identifier.
		}
		else if (table[i].kind != ID_VARIABLE)
		{
			error(12); // Illegal assignment.
			i = 0;
		}
		getsym();
                                array* ar = (array*) &table[i];
                                if (!i) {
                                        error(11); // Undeclared identifier.
                                } else if ((table[i].kind != ID_VARIABLE) && (ar->kind != ID_ARRAY)) {
                                        error(12); // Illegal assignment.
                                        i = 0;
                                }
                                getsym();
                                if ((ar->kind == ID_ARRAY)) { //???????????????????
                                        int dl = 0;
                                        p_dim* p = ar->next;
                                        if (sym == SYM_LSQUARE) {
                                                gen(LIT, 0, 0);
                                                gen(LIT, 0, p->dim_len);
                                                while (sym == SYM_LSQUARE) { //cy_array
                                                        if (p) { //cy_array
                                                                p = p->next;
                                                        }
                                                        gen(OPR, 0, OPR_MUL);
                                                        getsym();
                                                        expression(uniteset(fsys, createset(SYM_COMMA, SYM_NULL)));
                                                        dl++; //cy_array
                                                        if (sym == SYM_RSQUARE) {
                                                                getsym();
                                                        } else {
                                                                error(27);
                                                        }
                                                        gen(OPR, 0, OPR_ADD);
                                                        if (p) {
                                                                gen(LIT, 0, p->dim_len);
                                                        }
                                                }
                                                if (sym != SYM_BECOMES) { //cy_array
                                                        set1 = createset(SYM_BECOMES, SYM_NULL); //??????????????
                                                        test(set1, fsys, 0);
                                                        destroyset(set1);
                                                }
                                                if (dl != ar->dim_n) { //cy_array
                                                        error(26);
                                                }
                                        } else {
                                                error(28); //need'['
                                        }
                                } //???????????;
		if (sym == SYM_BECOMES)
		{
			getsym();
		}
		else
		{
			error(13); // ':=' expected.
		}
		expression_bool(fsys);
		mk = (mask*) &table[i];
		if (i)
		{
			gen(STO, level - mk->level, mk->address);
		}
	}
	else if (sym == SYM_CALL)
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
	} 
        else if (sym == SYM_IF)
	{ // if statement
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
                        if(sym == SYM_ELSE){
                            cx2 = cx; //??????????
                            gen(JMP, 0, 0); //?????????????????????????0
                            getsym();
                            code[cx1].a = cx; //????????????????????????else?????????
                            statement(fsys); //???else??????
                            code[cx2].a = cx; //?????????????????????then??????????else????
                            } else { //???û??else
                            code[cx1].a = cx; //???????????????????????????then????????
                            }
                        if(sym == SYM_ELIF)
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
		cx1 = cx;
		getsym();
		set1 = createset(SYM_DO, SYM_NULL);
		set = uniteset(set1, fsys);
		condition(set);
		destroyset(set1);
		destroyset(set);
		cx2 = cx;
		gen(JPC, 0, 0);
		if (sym == SYM_DO)
		{
			getsym();
		}
		else
		{
			error(18); // 'do' expected.
		}
		statement(fsys);
		gen(JMP, 0, cx1);
		code[cx2].a = cx;
	}
	else if(sym == SYM_EXIT){
		gen(EXT, 0, 0);
		getsym();
	}
        else if (sym == SYM_FOR) //?????for???
                        {
                getsym();
                mask* mk;
                if (sym != SYM_IDENTIFIER)
                        error(4); //for???????????
                i = position(id);
                mk = (mask*) &table[i];
                if (i == 0)
                        error(11);
                else if (table[i].kind != ID_VARIABLE) //ASSIGNMENT TO NON-VARIABLE
                        error(12); //????
                getsym();
                if (sym != SYM_BECOMES) //:=
                        error(13);
                getsym();
                set1 = createset(SYM_DOWNTO, SYM_DO, SYM_TO, SYM_NULL);
                set = uniteset(fsys, set1);
                expression(set); //????????????????E1
                destroyset(set1);
                destroyset(set);
                if (sym == SYM_DOWNTO) {
                        getsym();
                        cx1 = cx; //??????????,????????
                        gen(STO, level - mk->level, mk->address); //???????????????
                        gen(LOD, level - mk->level, mk->address); //????????????????
                        set1 = createset(SYM_DO, SYM_NULL);
                        set = uniteset(fsys, set1);
                        expression(set); //???????E2
                        destroyset(set1);
                        destroyset(set);
                        //????????????????????for i:=E1 to E2 do S??????i??????E2?????????????????????????????????
                        gen(OPR, 0, OPR_GEQ); //?????????????
                        cx2 = cx; //?????????????????????
                        gen(JPC, 0, 0); //???????????????????????????????
                        if (sym == SYM_DO) { //?????
                                getsym();
                                cxb cxbsaved = cxbreak; //cy
                                cxbreak.flag = 0; //cy
                                cxbreak.sign = 1; //cy
                                cxbreak.then = NULL;
                                ; //cy

                                set1 = createset(SYM_SEMICOLON, SYM_NULL);
                                set = uniteset(set1, fsys);
                                statement(set);
                                destroyset(set1);
                                destroyset(set);
                                gen(LOD, level - mk->level, mk->address); //????????????????
                                gen(LIT, 0, STEP); //??????????
                                gen(OPR, 0, OPR_MIN); //??????
                                gen(JMP, 0, cx1); //???????????????????
                                code[cx2].a = cx; //?????????????????????????????????????
                                if (cxbreak.flag) { //cy
                                        cxbrklink p = cxbreak.then;
                                        while (p) {
                                                code[p->cxbrk].a = cx;
                                                cxbrklink q = p;
                                                free(p);
                                                p = q->next;
                                        }

                                }
                                cxbreak.flag = cxbsaved.flag; //cy
                                cxbreak.then = cxbsaved.then; //cy
                                cxbreak.sign = cxbsaved.sign; //cy

                        } else
                                error(18); //do expected
                } else if (sym == SYM_TO) {
                        getsym();
                        cxb cxbsaved = cxbreak; //cy
                        cxbreak.flag = 0; //cy
                        cxbreak.sign = 1; //cy
                        cxbreak.then = NULL;
                        ; //cy
                        cx1 = cx; //????????
                        gen(STO, level - mk->level, mk->address); //???????????????
                        gen(LOD, level - mk->level, mk->address); //????????????????????????
                        set1 = createset(SYM_DO, SYM_NULL);
                        set = uniteset(fsys, set1);
                        expression(set); //????????E2,????????
                        destroyset(set1);
                        destroyset(set);
                        gen(OPR, 0, OPR_LEQ); //???????   <=  ???????????
                        cx2 = cx; //????????
                        gen(JPC, 0, 0); //??????????????????????????????????????????
                        if (sym == SYM_DO) {
                                getsym();
                                set1 = createset(SYM_SEMICOLON, SYM_NULL);
                                set = uniteset(set1, fsys);
                                statement(set); //?????????
                                destroyset(set1);
                                destroyset(set);
                                gen(LOD, level - mk->level, mk->address); //??????????????????
                                gen(LIT, 0, STEP);
                                gen(OPR, 0, OPR_ADD); //??????
                                gen(JMP, 0, cx1); //???????????????????
                                code[cx2].a = cx; //????????????????????????????????
                                if (cxbreak.flag) { //cy
                                        cxbrklink p = cxbreak.then;
                                        while (p) {
                                                code[p->cxbrk].a = cx;
                                                cxbrklink q = p;
                                                free(p);
                                                p = q->next;
                                        }

                                }
                                cxbreak.flag = cxbsaved.flag; //cy
                                cxbreak.then = cxbsaved.then; //cy
                                cxbreak.sign = cxbsaved.sign; //cy

                        } else
                                error(18); //do expected
                } else
                        error(30); //to or downto expected
}
	test(fsys, phi, 19);
} // statement
int search_var(int len, int from) { //cy_quote
        int count = 0;
        int arsize(int i);
        int i;
        for (i = tx - from; len > 0; i--, len--) {
                array* ar = (array*) &table[i];
                if (table[i].quote == 0) {
                        if (ar->kind == ID_ARRAY) {
                                mask *mk = (mask*) &table[i];
                                count += arsize(i);
                        } else if (ar->kind == ID_VARIABLE) {
                                count++;
                        }
                }
        }
        return count;
}

int search_pro(int n) { //cy_quote
        int count = 0;
        int con = (tx - n + 1);
        for (int i = tx - n + 1; n; i++, n--) {
                if (table[i].kind == ID_PROCEDURE) {
                        if (table[i].quote == 0) {
                                proth[count] = i - con;
                                count++;

                        }
                }
        }
        return count;
}
//////////////////////////////////////////////////////////////////////
void block(symset fsys)
{
    int cx0; // initial code index
            mask* mk;
            int savedTx;
            int var_n = 0; //cy_quote
            int pro_n = 0; //cy_quote
            symset set1, set;
            dx[level] = 3; //iiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiii
            if (level == 0)
                    mk = (mask*) &table[tx]; //mk -> procedure in the table
            else
                    mk = (mask*) &table[tx - zx[level - 1]];
            mk->address = cx;
            int jmpcx = cx; //cy_quote
            gen(JMP, 0, 0);
            int varnum = 0; //cy_quote
            int pronum = 0; //cy_quote
            prolink* pro = NULL; //cy_quote
            tx_[level] = tx + 1;
            if (level > MAXLEVEL) {
                    error(32); // There are too many levels.
            }
            do {
                    if (sym == SYM_CONST) { // constant declarations
                            getsym();
                            do {
                                    constdeclaration(fsys);
                                    while (sym == SYM_COMMA) {
                                            getsym();
                                            constdeclaration(fsys);
                                            printf("OK\n");
                                    }
                                    if (sym == SYM_SEMICOLON) {
                                            getsym();
                                    } else {
                                            error(5); // Missing ',' or ';'.
                                            //	printf("there\n");
                                    }
                            } while (sym == SYM_IDENTIFIER);
                    } // if
                    if (sym == SYM_VAR) { // variable declarations
                            getsym();
                            do {
                                    varnum++;
                                    vardeclaration();
                                    while (sym == SYM_COMMA) {
                                            getsym();
                                            varnum++;
                                            vardeclaration();
                                    }
                                    if (sym == SYM_SEMICOLON) {
                                            getsym();
                                    } else {
                                            error(5); // Missing ',' or ';'.
                                    }
                            } while (sym == SYM_IDENTIFIER);
    //			block = dx;
                    } // if
                    prolink* head = NULL;
                    while (sym == SYM_PROCEDURE) { // procedure declarations
                            pronum++; //cy_quote
                            prolink* p = (prolink*) malloc(sizeof(prolink)); //cy_quote
                            p->next = NULL;
                            if (pro == NULL) { //cy_quote
                                    pro = p;
                            } else {
                                    head->next = p;
                            }
                            head = p;
                            zx[level] = 0; //???????
                            getsym();
                            if (sym == SYM_IDENTIFIER) {
                                    enter(ID_PROCEDURE);
                                    head->table_adr = tx;
                                    getsym();
                            } else {
                                    error(4); // There must be an identifier to follow 'const', 'var', or 'procedure'.
                            }

                            if (sym == SYM_LPAREN) //added by zq
                                            {
                                    do {
                                            getsym();
                                            if (sym == SYM_IDENTIFIER) {
                                                    //declare
                                                    enterPar();
                                                    getsym();
                                            } else if (sym == SYM_RPAREN) {
                                                    /*break;*/
                                            } else {
                                                    error(19); //incorrect symbol
                                                    getsym();
                                            }
                                    } while (sym == SYM_COMMA);

                                    if (sym == SYM_RPAREN) {
                                            modifyTable(zx[level]);
                                    } else {
                                            error(22); //')' missing
                                    }
                                    getsym();
                            } else {
                            }

                            if (sym == SYM_SEMICOLON) {
                                    getsym();
                            } else {
                                    error(5); // Missing ',' or ';'.
                            }
                            level++;
                            savedTx = tx;
                            set1 = createset(SYM_SEMICOLON, SYM_NULL);
                            set = uniteset(set1, fsys);
                            head->start = cx; //cy_quote
                            block(set);
                            head->end = cx; //cy_quote
                            destroyset(set1);
                            destroyset(set);
                            level--;
                            tx = savedTx - zx[level]; //modified by zq.  need to substract the parameters.

                            if (sym == SYM_SEMICOLON) {
                                    getsym();
                                    set1 = createset(SYM_IDENTIFIER, SYM_PROCEDURE, SYM_NULL);
                                    set = uniteset(statbegsys, set1);
                                    test(set, fsys, 6);
                                    destroyset(set1);
                                    destroyset(set);
                            } else {
                                    error(5); // Missing ',' or ';'.
                            }
                    } // while
                    set1 = createset(SYM_IDENTIFIER, SYM_NULL);
                    set = uniteset(statbegsys, set1);
                    test(set, declbegsys, 7);
                    destroyset(set1);
                    destroyset(set);
            } while (inset(sym, declbegsys));

            code[mk->address].a = cx;
            mk->address = cx;
            if (level == 0)
                    mk->numOfPar = zx[level]; //added by zq
            else
                    mk->numOfPar = zx[level - 1];
            cx0 = cx; //procedure enter address
            gen(INT, 0, dx[level]);
            set1 = createset(SYM_SEMICOLON, SYM_END, SYM_NULL);
            set = uniteset(set1, fsys);
            statement(set);
            destroyset(set1);
            destroyset(set);

            var_n = search_var(varnum, pronum); //cy_quote
    //	int var_n2 = search_var(varnum, pronum, 2); //cy_quote
            pro_n = search_pro(pronum); //cy_quote
           /* if (var_n) {
                    cutprovarcode(cx0, cx, tx_[level], tx - pro_n); //cy_quote
                    cutprovarcode(jmpcx + 1, cx0, tx_[level], tx - pro_n); //cy_quote
            }*/
            code[cx0].a -= var_n; //cy_quote
            if (pro_n) { //????????
                    prolink* q = pro;
                    int proth_formor = -1;
                    for (int k = 0; k < pro_n; k++) {
                            for (int n = proth[k] - proth_formor; n != 1; n--) {
                                    q = q->next;
                            }
                    prolink* head = NULL;	proth_formor = proth[k];
                            int codelen = q->end - q->start; //???????;
                            for (prolink* qq = q->next; qq; qq = qq->next) {
                                    qq->start -= codelen;
                                    qq->end -= codelen;
                                    //			mask* mk = (mask*) &table[qq->table_adr]; //???????table
                                    //			mk->address -= codelen;
                            }
                           // cutcode(q->start, q->end); //????????jmp\jpc\call
                            code[jmpcx].a -= codelen;
                            cx0 -= codelen; //cx0????INT???????block?statement????
                    }
            }
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
	int b;         // program, base, and top-stack register
	instruction i; // instruction register

	printf("Begin executing PL/0 program.\n");

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
			exit(0);
                case STA: //??????????????
                        stack[base(stack, b, i.l) + stack[top - 1] + i.a] = stack[top];
                        top -= 2;
                        break;
                case LAD:
                        stack[top] = stack[base(stack, b, i.l) + stack[top] + i.a];
                        break;
		} // switch
	}
	while (pc);

	printf("End executing PL/0 program.\n");
} // interpret

//////////////////////////////////////////////////////////////////////
void main ()
{
	FILE* hbin;
	char s[80];
	int i;
	symset set, set1, set2;

	printf("Please input source file name: "); // get file name to be compiled
	scanf("%s", s);
	if ((infile = fopen(s, "r")) == NULL)
	{
		printf("File %s can't be opened.\n", s);
		exit(1);
	}

	phi = createset(SYM_NULL);
	relset = createset(SYM_EQU, SYM_NEQ, SYM_LES, SYM_LEQ, SYM_GTR, SYM_GEQ, SYM_NULL);
	
	// create begin symbol sets
	declbegsys = createset(SYM_CONST, SYM_VAR, SYM_PROCEDURE, SYM_NULL);
	statbegsys = createset(SYM_BEGIN, SYM_CALL, SYM_IF, SYM_WHILE, SYM_NULL);
	facbegsys = createset(SYM_IDENTIFIER, SYM_NUMBER, SYM_LPAREN, SYM_MINUS, SYM_NULL);

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
