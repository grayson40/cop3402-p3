#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include "compiler.h"

#define MAX_CODE_LENGTH 200
#define MAX_SYMBOL_COUNT 50
#define MAX_REG_COUNT 10
#define MAX_SYMBOL_LENGTH 12

// generated code
instruction *code;
int cIndex;

// symbol table
symbol *table;
int tIndex;

// list of instructions
//lexeme *list;
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
void factor(lexeme *list);
void term(lexeme *list);
void expression(lexeme *list);
void block(lexeme *list);
int var_decleration(lexeme *list);
void procedure_decleration(lexeme *list);
void statement(lexeme *list);
void condition(lexeme *list);

instruction *parse(lexeme *list, int printTable, int printCode)
{
    // set up program variables
    code = malloc(sizeof(instruction) * MAX_CODE_LENGTH);
    cIndex = 0;
    table = malloc(sizeof(symbol) * MAX_SYMBOL_COUNT);
    tIndex = 0;
    registercounter=-1;

    emit(7, 0, 0, 0);
    addToSymbolTable(3, "main", 0, 0, 0, 0);
    level = -1;
    block(list);

    if (list[listIndex].type != periodsym){
        printparseerror(1);
        return NULL;
    }
    
    emit(11, 0, 0, 0);
    code[0].m = table[0].addr;

    for (int i = 0; i < cIndex; i++)
    {
        if (code[i].opcode == 5)
           code[i].m = table[code[i].m].addr;
    }

    // print off table and code
    if (printTable)
        printsymboltable();
    if (printCode)
        printassemblycode();

    // mark the end of the code
    code[cIndex].opcode = -1;
    return code;
}

void statement(lexeme *list)
{
    char symbolName[MAX_SYMBOL_LENGTH]="";
    int arrayIdxReg, symIndex, varLocReg, jpcIndex, jmpIndex, loopIndex;

    // assignment
    if (list[listIndex].type == assignsym)
    {
        strcpy(symbolName, list[listIndex].name);
        listIndex++;
        if (list[listIndex].type == lbracketsym)
        {
            listIndex++;
            symIndex = findsymbol(symbolName, 2);
            if (symIndex == -1)
            {
                if (findsymbol(symbolName, 1) != -1)
                {
                    printparseerror(11);
                }
                else if (findsymbol(symbolName, 3) != -1)
                {
                    printparseerror(9);
                }
                else
                {
                    printparseerror(10);
                }
            }
            expression(list);
            arrayIdxReg = registercounter;
            if (list[listIndex].type != rbracketsym)
            {
                printparseerror(5);
            }
            listIndex++;
            if (list[listIndex].type != assignsym)
            {
                printparseerror(13);
            }
            listIndex++;
            expression(list);
            registercounter++;
            if (registercounter >= 10)
            {
                printparseerror(14);
            }
            emit(1, registercounter, 0, table[symIndex].addr);
            emit(13, arrayIdxReg, arrayIdxReg, registercounter);
            registercounter--;
            emit(4, registercounter, level - table[symIndex].level, arrayIdxReg);
            registercounter -= 2;
        }
        else
        {
            symIndex = findsymbol(symbolName, 1);
            if (symIndex == -1)
            {
                if (findsymbol(symbolName, 2) != -1)
                {
                    printparseerror(12);
                }
                else if (findsymbol(symbolName, 3) != -1)
                {
                    printparseerror(9);
                }
                else
                {
                    printparseerror(10);
                }
            }
            registercounter++;
            if (registercounter >= 10)
            {
                printparseerror(14);
            }
            emit(1, registercounter, 0, table[symIndex].addr);
            varLocReg = registercounter;
            if (list[listIndex].type != assignsym)
            {
                printparseerror(13);
            }
            listIndex++;
            expression(list);
            emit(4, registercounter, level - table[symIndex].level, varLocReg);
            registercounter -= 2;
        }
    }

    // call
    else if (list[listIndex].type == callsym)
    {
        listIndex++;
        if (list[listIndex].type != identsym)
        {
            printparseerror(15);
        }
        symIndex = findsymbol(list[listIndex].name, 3);
        if (symIndex == -1)
        {
            if (findsymbol(list[listIndex].name, 1) != -1 || findsymbol(list[listIndex].name, 2) != -1)
            {
                printparseerror(15);
            }
            else
            {
                printparseerror(10);
            }
        }
        emit(5, 0, level - table[symIndex].level, symIndex);
        listIndex++;
    }

    // begin-end
    else if (list[listIndex].type == beginsym)
    {
        do
        {
            listIndex++;
            statement(list);
        } while (list[listIndex].type == semicolonsym);
        if (list[listIndex].type != endsym)
        {
            if (list[listIndex].type == identsym || list[listIndex].type == callsym || list[listIndex].type == beginsym || list[listIndex].type == ifsym || list[listIndex].type == dosym || list[listIndex].type == readsym || list[listIndex].type == writesym)
            {
                printparseerror(16);
            }
            else
            {
                printparseerror(17);
            }
        }
        listIndex++;
    }

    // if
    else if (list[listIndex].type == ifsym)
    {
        listIndex++;
        condition(list);
        jpcIndex = cIndex;
        emit(8, registercounter, 0, 0);
        registercounter--;
        if (list[listIndex].type != questionsym)
        {
            printparseerror(18);
        }
        listIndex++;
        statement(list);
        if (list[listIndex].type == colonsym)
        {
            listIndex++;
            jmpIndex = cIndex;
            emit(7, 0, 0, 0);
            code[jpcIndex].m = cIndex;
            statement(list);
            code[jmpIndex].m = cIndex;
        }
        else
        {
            code[jpcIndex].m = cIndex;
        }
    }

    // do-while
    else if (list[listIndex].type == dosym)
    {
        listIndex++;
        loopIndex = cIndex;
        statement(list);
        if (list[listIndex].type != whilesym)
        {
            printparseerror(19);
        }
        listIndex++;
        condition(list);
        registercounter++;
        if (registercounter >= 10)
        {
            printparseerror(14);
        }
        emit(1, registercounter, 0, 0);
        emit(18, registercounter - 1, registercounter - 1, registercounter);
        registercounter--;
        emit(8, registercounter, 0, loopIndex);
        registercounter--;
    }

    // read
    else if (list[listIndex].type == readsym)
    {
        listIndex++;
        if (list[listIndex].type != identsym)
        {
            printparseerror(20);
        }
        strcpy(symbolName, list[listIndex].name);
        listIndex++;
        if (list[listIndex].type == lbracketsym)
        {
            listIndex++;
            symIndex = findsymbol(symbolName, 2);
            if (symIndex == -1)
            {
                if (findsymbol(symbolName, 1) != -1)
                {
                    printparseerror(11);
                }
                else if (findsymbol(symbolName, 3) != -1)
                {
                    printparseerror(9);
                }
                else
                {
                    printparseerror(10);
                }
            }
            expression(list);
            arrayIdxReg = registercounter;
            if (list[listIndex].type != rbracketsym)
            {
                printparseerror(5);
            }
            listIndex++;
            registercounter++;
            if (registercounter >= 10)
            {
                printparseerror(14);
            }
            emit(10, registercounter, 0, 0);
            registercounter++;
            if (registercounter >= 10)
            {
                printparseerror(14);
            }
            emit(1, registercounter, 0, table[symIndex].addr);
            emit(13, arrayIdxReg, arrayIdxReg, registercounter);
            registercounter--;
            emit(4, registercounter, level - table[symIndex].level, arrayIdxReg);
            registercounter -= 2;
        }
        else
        {
            symIndex = findsymbol(symbolName, 1);
            if (symIndex == -1)
            {
                if (findsymbol(symbolName, 2) != -1)
                {
                    printparseerror(12);
                }
                else if (findsymbol(symbolName, 3) != -1)
                {
                    printparseerror(9);
                }
                else
                {
                    printparseerror(10);
                }
            }
            registercounter++;
            if (registercounter >= 10)
            {
                printparseerror(14);
            }
            emit(1, registercounter, 0, table[symIndex].addr);
            varLocReg = registercounter;
            registercounter++;
            if (registercounter >= 10)
            {
                printparseerror(14);
            }
            emit(10, registercounter, 0, 0);
            emit(4, registercounter, level - table[symIndex].level, varLocReg);
            registercounter -= 2;
        }
    }

    // write
    else if (list[listIndex].type == writesym)
    {
        listIndex++;
        expression(list);
        emit(9, registercounter, 0, 0);
        registercounter--;
    }
    else
    {
        return;
    }
}

void factor(lexeme *list)
{
    char symbolName[MAX_SYMBOL_LENGTH]="";
    int symIndex, arrayIdxReg, varLocReg;

    if (list[listIndex].type == identsym)
    {
        // Get symbol name
        strcpy(symbolName, list[listIndex].name);
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

            expression(list);
            arrayIdxReg = registercounter;

            if (list[listIndex].type != rbracketsym){
                printparseerror(5);
            }

            listIndex++;
            registercounter++;

            if (registercounter >= 10){
                printparseerror(14);
            }

            emit(1, registercounter, 0, table[symIndex].addr);
            emit(13, arrayIdxReg, arrayIdxReg, registercounter);
            registercounter--;
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

            if (registercounter >= 10){
                printparseerror(14);
            }

            emit(1, registercounter, 0, table[symIndex].addr);

            varLocReg = registercounter;

            emit(3, registercounter, level - table[symIndex].level, varLocReg);
        }
    }
    else if (list[listIndex].type == numbersym)
    {
        registercounter++;

        if (registercounter >= 10){
            printparseerror(14);
        }

        emit(1, registercounter, 0, list[listIndex].value);

        listIndex++;
    }
    else if (list[listIndex].type == lparenthesissym)
    {
        listIndex++;

        expression(list);

        if (list[listIndex].type != rparenthesissym){
            printparseerror(23);
        }

        listIndex++;
    }
    else
    {
        printparseerror(24);
    }
    return;
}

void expression(lexeme *list)
{
    if (list[listIndex].type == subsym)
    {
        listIndex++;
        term(list);
        emit(12, registercounter, 0, registercounter);

        while (list[listIndex].type == addsym || list[listIndex].type == subsym)
        {
            if (list[listIndex].type == addsym)
            {
                listIndex++;
                term(list);
                emit(13, registercounter - 1, registercounter - 1, registercounter);
                registercounter--;
            }
            else
            {
                listIndex++;
                term(list);
                emit(14, registercounter - 1, registercounter - 1, registercounter);
                registercounter--;
            }
        }
    }
    else
    {
        term(list);

        while (list[listIndex].type == addsym || list[listIndex].type == subsym)
        {
            if (list[listIndex].type == addsym)
            {
                listIndex++;
                term(list);
                emit(13, registercounter - 1, registercounter - 1, registercounter);
                registercounter--;
            }
            else
            {
                listIndex++;
                term(list);
                emit(14, registercounter - 1, registercounter - 1, registercounter);
                registercounter--;
            }
        }
    }

    if (list[listIndex].type == lparenthesissym || list[listIndex].type == identsym || list[listIndex].type == numbersym)
    {
        printparseerror(22);
    }
    return;
}

void term(lexeme *list)
{
    factor(list);
    while (list[listIndex].type == multsym || list[listIndex].type == divsym || list[listIndex].type == modsym)
    {
        if (list[listIndex].type == multsym)
        {
            listIndex++;
            factor(list);
            emit(15, registercounter - 1, registercounter - 1, registercounter);
            registercounter--;
        }
        else if (list[listIndex].type == divsym)
        {
            listIndex++;
            factor(list);
            emit(16, registercounter - 1, registercounter - 1, registercounter);
            registercounter--;
        }
        else
        {
            listIndex++;
            factor(list);
            emit(17, registercounter - 1, registercounter - 1, registercounter);
            registercounter--;
        }
    }
    return;
}

void block(lexeme *list)
{
    level++;
    int procedureIndex = tIndex - 1;
    int x = var_decleration(list);
    procedure_decleration(list);
    table[procedureIndex].addr = cIndex;
    emit(6, 0, 0, x);
    statement(list);
    mark();
    level--;
}

int var_decleration(lexeme *list)
{
    int memory_size = 3;
    char symbole_name[MAX_SYMBOL_LENGTH]="";
    int array_size;
    if (list[listIndex].type == varsym)
    {
        do
        {
            listIndex++;
            if (list[listIndex].type != identsym){
                printparseerror(2);
            }
            if (multipledeclarationcheck(list[listIndex].name) != -1){
                printparseerror(3);
            }
            strcpy(symbole_name, list[listIndex].name);
            listIndex++;
            if (list[listIndex].type == lbracketsym)
            {
                listIndex++;
                if (list[listIndex].type != numbersym || list[listIndex].value == 0){
                    printparseerror(4);
                }
                array_size = list[listIndex].value;
                listIndex++;
                if (list[listIndex].type == multsym || list[listIndex].type == divsym || list[listIndex].type == modsym || list[listIndex].type == addsym || list[listIndex].type == subsym){
                    printparseerror(4);
                }
                else if (list[listIndex].type != rbracketsym){
                    printparseerror(5);
                }
                listIndex++;
                addToSymbolTable(2, symbole_name, array_size, level, memory_size, 0);
                memory_size += array_size;
            }
            else
            {
                addToSymbolTable(1, symbole_name, 0, level, memory_size, 0);
                memory_size++;
            }
        } while (list[listIndex].type == commasym);

        if (list[listIndex].type == identsym){
            printparseerror(6);
        }
        else if (list[listIndex].type != semicolonsym){
            printparseerror(7);
        }
        listIndex++;
        return memory_size;
    }
    else
        return memory_size;
}

void procedure_decleration(lexeme *list)
{
    char symbol_name[MAX_SYMBOL_LENGTH]="";
    while (list[listIndex].type == procsym)
    {
        listIndex++;
        if (list[listIndex].type != identsym){
            printparseerror(2);
        }
        else if (multipledeclarationcheck(list[listIndex].name) != -1){
            printparseerror(3);
        }
        strcpy(symbol_name, list[listIndex].name);
        listIndex++;
        if (list[listIndex].type != semicolonsym){
            printparseerror(8);
        }
        listIndex++;
        addToSymbolTable(3, symbol_name, 0, level, 0, 0);
        block(list);
        if (list[listIndex].type != semicolonsym){
            printparseerror(7);
        }
        listIndex++;
        emit(2, 0, 0, 0);
    }
}

void condition(lexeme *list)
{
    expression(list);
    if (list[listIndex].type == eqlsym)
    {
        listIndex++;
        expression(list);
        emit(18, registercounter - 1, registercounter - 1, registercounter);
        registercounter--;
    }
    else if (list[listIndex].type == neqsym)
    {
        listIndex++;
        expression(list);
        emit(19, registercounter - 1, registercounter - 1, registercounter);
        registercounter--;
    }
    else if (list[listIndex].type == lsssym)
    {
        listIndex++;
        expression(list);
        emit(20, registercounter - 1, registercounter - 1, registercounter);
        registercounter--;
    }
    else if (list[listIndex].type == leqsym)
    {
        listIndex++;
        expression(list);
        emit(21, registercounter - 1, registercounter - 1, registercounter);
        registercounter--;
    }
    else if (list[listIndex].type == gtrsym)
    {
        listIndex++;
        expression(list);
        emit(22, registercounter - 1, registercounter - 1, registercounter);
        registercounter--;
    }
    else if (list[listIndex].type == geqsym)
    {
        listIndex++;
        expression(list);
        emit(23, registercounter - 1, registercounter - 1, registercounter);
        registercounter--;
    }
    else{
        printparseerror(21);
    }
    return;
}

void emit(int opname, int reg, int level, int mvalue)
{
    code[cIndex].opcode = opname;
    code[cIndex].r = reg;
    code[cIndex].l = level;
    code[cIndex].m = mvalue;
    cIndex++;
    return;
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
    return;
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
    exit(0);
    return;
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
    return;
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

    return;
}
