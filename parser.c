#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "compiler.h"

#define MAX_CODE_LENGTH 200
#define MAX_SYMBOL_COUNT 50
#define MAX_REG_COUNT 10
#define MAX_SYMBOL_LENGTH 11

// generated code
instruction *code;
int cIndex;

// symbol table
symbol *table;
int tIndex;

// list of instructions
lexeme *list;
int listIndex = 0;

int level, registercounter;

void emit(int opname, int reg, int level, int mvalue);
void addToSymbolTable(int k, char n[], int s, int l, int a, int m);
void mark();
int multipledeclarationcheck(char name[]);
int findsymbol(char name[], int kind);
void printparseerror(int err_code);
void printsymboltable();
void printassemblycode();
void factor();
void term();
void expression();

void factor()
{
    char symbolName[MAX_SYMBOL_LENGTH];
    int symIndex, arrayIdxReg, varLocReg;

    if (list[listIndex].type == identsym)
    {
        // Get symbol name
        strcpy(list[listIndex].name, symbolName);
        listIndex++;

        // Check for presence of left bracket
        if (list[listIndex].type == lbracketsym)
        {
            listIndex++;

            // Try to find an array
            symIndex = findsymbol(symbolName, 2);
            if (symIndex == -1)
            {
                // Print error if var
                if (findsymbol(symbolName, 1) != -1)
                    printparseerror(11);
                // Print error if procedure
                else if (findsymbol(symbolName, 3) != 1)
                    printparseerror(9);
                else
                    printparseerror(10);
            }

            expression();
            arrayIdxReg = registercounter;

            if (list[listIndex].type != rbracketsym)
                printparseerror(5);

            listIndex++;
            registercounter++;

            if (registercounter >= 10)
                printparseerror(14);

            emit(1, registercounter, 0, table[symIndex].addr);
            emit(13, arrayIdxReg, arrayIdxReg, registercounter);
            emit(3, registercounter, level - table[symIndex].level, arrayIdxReg);
        }
        else
        {
            // Try to find a var
            symIndex = findsymbol(symbolName, 1);
            if (symIndex == -1)
            {
                // Print error if array
                if (findsymbol(symbolName, 2) != -1)
                    printparseerror(12);
                // Print error if procedure
                else if (findsymbol(symbolName, 3) != 1)
                    printparseerror(9);
                else
                    printparseerror(10);
            }

            registercounter++;

            if (registercounter >= 10)
                printparseerror(14);

            emit(1, registercounter, 0, table[symIndex].addr);

            varLocReg = registercounter;

            emit(3, registercounter, level - table[symIndex].level, varLocReg);
        }
    }
    else if (list[listIndex].type == numbersym)
    {
        registercounter++;

        if (registercounter >= 10)
            printparseerror(14);

        emit(1, registercounter, 0, list[listIndex].value);

        listIndex++;
    }
    else if (list[listIndex].type == lparenthesissym)
    {
        listIndex++;

        expression();

        if (list[listIndex].type != rparenthesissym)
            printparseerror(23);

        listIndex++;
    }
    else
    {
        printparseerror(24);
    }
}

void expression()
{
    if (list[listIndex].type == subsym)
    {
        listIndex++;
        term();
        emit(12, registercounter, 0, registercounter);

        while (list[listIndex].type == addsym || list[listIndex].type == subsym)
        {
            if (list[listIndex].type == addsym)
            {
                listIndex++;
                term();
                emit(13, registercounter - 1, registercounter - 1, registercounter);
                registercounter--;
            }
            else
            {
                listIndex++;
                term();
                emit(14, registercounter - 1, registercounter - 1, registercounter);
                registercounter--;
            }
        }
    }
    else
    {
        term();

        while (list[listIndex].type == addsym || list[listIndex].type == subsym)
        {
            if (list[listIndex].type == addsym)
            {
                listIndex++;
                term();
                emit(13, registercounter - 1, registercounter - 1, registercounter);
                registercounter--;
            }
            else
            {
                listIndex++;
                term();
                emit(14, registercounter - 1, registercounter - 1, registercounter);
                registercounter--;
            }
        }
    }

    if (list[listIndex].type == lparenthesissym || list[listIndex].type == identsym || list[listIndex].type == numbersym)
    {
        printparseerror(22);
    }
}

void term()
{
    factor();
    while (list[listIndex].type == multsym || list[listIndex].type == divsym || list[listIndex].type == modsym)
    {
        if (list[listIndex].type == multsym)
        {
            listIndex++;
            factor();
            emit(15, registercounter - 1, registercounter - 1, registercounter);
            registercounter--;
        }
        else if (list[listIndex].type == divsym)
        {
            listIndex++;
            factor();
            emit(16, registercounter - 1, registercounter - 1, registercounter);
            registercounter--;
        }
        else
        {
            listIndex++;
            factor();
            emit(17, registercounter - 1, registercounter - 1, registercounter);
            registercounter--;
        }
    }
}

instruction *parse(lexeme *list, int printTable, int printCode)
{
    // set up program variables
    code = malloc(sizeof(instruction) * MAX_CODE_LENGTH);
    cIndex = 0;
    table = malloc(sizeof(symbol) * MAX_SYMBOL_COUNT);
    tIndex = 0;

    // print off table and code
    if (printTable)
        printsymboltable();
    if (printCode)
        printassemblycode();

    // mark the end of the code
    code[cIndex].opcode = -1;
    return code;
}

void emit(int opname, int reg, int level, int mvalue)
{
    code[cIndex].opcode = opname;
    code[cIndex].r = reg;
    code[cIndex].l = level;
    code[cIndex].m = mvalue;
    cIndex++;
}

void addToSymbolTable(int k, char n[], int s, int l, int a, int m)
{
    table[tIndex].kind = k;
    strcpy(table[tIndex].name, n);
    table[tIndex].size = s;
    table[tIndex].level = l;
    table[tIndex].addr = a;
    table[tIndex].mark = m;
    tIndex++;
}

void mark()
{
    int i;
    for (i = tIndex - 1; i >= 0; i--)
    {
        if (table[i].mark == 1)
            continue;
        if (table[i].level < level)
            return;
        table[i].mark = 1;
    }
}

int multipledeclarationcheck(char name[])
{
    int i;
    for (i = 0; i < tIndex; i++)
        if (table[i].mark == 0 && table[i].level == level && strcmp(name, table[i].name) == 0)
            return i;
    return -1;
}

int findsymbol(char name[], int kind)
{
    int i;
    int max_idx = -1;
    int max_lvl = -1;
    for (i = 0; i < tIndex; i++)
    {
        if (table[i].mark == 0 && table[i].kind == kind && strcmp(name, table[i].name) == 0)
        {
            if (max_idx == -1 || table[i].level > max_lvl)
            {
                max_idx = i;
                max_lvl = table[i].level;
            }
        }
    }
    return max_idx;
}

void printparseerror(int err_code)
{
    switch (err_code)
    {
    case 1:
        printf("Parser Error: Program must be closed by a period\n");
        break;
    case 2:
        printf("Parser Error: Symbol names must be identifiers\n");
        break;
    case 3:
        printf("Parser Error: Confliciting symbol declarations\n");
        break;
    case 4:
        printf("Parser Error: Array sizes must be given as a single, nonzero number\n");
        break;
    case 5:
        printf("Parser Error: [ must be followed by ]\n");
        break;
    case 6:
        printf("Parser Error: Multiple symbols in var declaration must be separated by commas\n");
        break;
    case 7:
        printf("Parser Error: Symbol declarations should close with a semicolon\n");
        break;
    case 8:
        printf("Parser Error: Procedure declarations should contain a semicolon before the body of the procedure begins\n");
        break;
    case 9:
        printf("Parser Error: Procedures may not be assigned to, read, or used in arithmetic\n");
        break;
    case 10:
        printf("Parser Error: Undeclared identifier\n");
        break;
    case 11:
        printf("Parser Error: Variables cannot be indexed\n");
        break;
    case 12:
        printf("Parserr Error: Arrays must be indexed\n");
        break;
    case 13:
        printf("Parser Error: Assignment operator missing\n");
        break;
    case 14:
        printf("Parser Error: Register Overflow Error\n");
        break;
    case 15:
        printf("Parser Error: call must be followed by a procedure identifier\n");
        break;
    case 16:
        printf("Parser Error: Statements within begin-end must be separated by a semicolon\n");
        break;
    case 17:
        printf("Parser Error: begin must be followed by end\n");
        break;
    case 18:
        printf("Parser Error: if must be followed by ?\n");
        break;
    case 19:
        printf("Parser Error: do must be followed by while\n");
        break;
    case 20:
        printf("Parser Error: read must be followed by a var or array identifier\n");
        break;
    case 21:
        printf("Parser Error: Relational operator missing from condition\n");
        break;
    case 22:
        printf("Parser Error: Bad arithmetic\n");
        break;
    case 23:
        printf("Parser Error: ( must be followed by )\n");
        break;
    case 24:
        printf("Parser Error: Arithmetic expressions may only contain arithmetic operators, numbers, parentheses, and variables\n");
        break;
    default:
        printf("Implementation Error: unrecognized error code\n");
        break;
    }

    free(code);
    free(table);
}

void printsymboltable()
{
    int i;
    printf("Symbol Table:\n");
    printf("Kind | Name        | Size | Level | Address | Mark\n");
    printf("---------------------------------------------------\n");
    for (i = 0; i < tIndex; i++)
        printf("%4d | %11s | %5d | %4d | %5d | %5d\n", table[i].kind, table[i].name, table[i].size, table[i].level, table[i].addr, table[i].mark);

    free(table);
    table = NULL;
}

void printassemblycode()
{
    int i;
    printf("Line\tOP Code\tOP Name\tR\tL\tM\n");
    for (i = 0; i < cIndex; i++)
    {
        printf("%d\t", i);
        printf("%d\t", code[i].opcode);
        switch (code[i].opcode)
        {
        case 1:
            printf("LIT\t");
            break;
        case 2:
            printf("RET\t");
            break;
        case 3:
            printf("LOD\t");
            break;
        case 4:
            printf("STO\t");
            break;
        case 5:
            printf("CAL\t");
            break;
        case 6:
            printf("INC\t");
            break;
        case 7:
            printf("JMP\t");
            break;
        case 8:
            printf("JPC\t");
            break;
        case 9:
            printf("WRT\t");
            break;
        case 10:
            printf("RED\t");
            break;
        case 11:
            printf("HLT\t");
            break;
        case 12:
            printf("NEG\t");
            break;
        case 13:
            printf("ADD\t");
            break;
        case 14:
            printf("SUB\t");
            break;
        case 15:
            printf("MUL\t");
            break;
        case 16:
            printf("DIV\t");
            break;
        case 17:
            printf("MOD\t");
            break;
        case 18:
            printf("EQL\t");
            break;
        case 19:
            printf("NEQ\t");
            break;
        case 20:
            printf("LSS\t");
            break;
        case 21:
            printf("LEQ\t");
            break;
        case 22:
            printf("GTR\t");
            break;
        case 23:
            printf("GEQ\t");
            break;
        default:
            printf("err\t");
            break;
        }
        printf("%d\t%d\t%d\n", code[i].r, code[i].l, code[i].m);
    }

    if (table != NULL)
        free(table);
}
