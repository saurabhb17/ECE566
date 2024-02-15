%{
#include <cstdio>
#include <list>
#include <vector>
#include <map>
#include <iostream>
#include <string>
#include <memory>
#include <stdexcept>
#include <unordered_map>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"

#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/FileSystem.h"

using namespace llvm;
using namespace std;

// Need for parser and scanner
extern FILE *yyin;
int yylex();
void yyerror(const char*);
int yyparse();
 
// Needed for LLVM
string funName;
Module *M;
LLVMContext TheContext;
IRBuilder<> Builder(TheContext);

unordered_map<string, Value*> Map;
Value *regs[8] = {nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr};

%}


%union {
  vector<string> *params_list;
  Value *val;
  int reg;
  int num;
  char *ch;
}

/*%define parse.trace*/

%type <params_list> params_list
%type <val> expr
%type <val> ensemble
%type <val> final
%type <val> statement
%type <val> statements
%type <val> statements_opt

%token IN FINAL
%token ERROR
%token <num> NUMBER
%token <ch> ID 
%token BINV INV PLUS MINUS XOR AND OR MUL DIV MOD
%token COMMA ENDLINE ASSIGN LBRACKET RBRACKET LPAREN RPAREN NONE COLON
%token REDUCE EXPAND

%precedence BINV
%precedence INV
%left PLUS MINUS OR
%left MUL DIV AND XOR MOD

%start program

%%

program: inputs statements_opt final
{
  YYACCEPT;
}
;

inputs: IN params_list ENDLINE
{  
  std::vector<Type*> param_types;
  for(auto s: *$2)
    {
      param_types.push_back(Builder.getInt32Ty());
    }
  ArrayRef<Type*> Params (param_types);
  
  // Create int function type with no arguments
  FunctionType *FunType = 
    FunctionType::get(Builder.getInt32Ty(),Params,false);

  // Create a main function
  Function *Function = Function::Create(FunType,GlobalValue::ExternalLinkage,funName,M);

  int arg_no=0;
  for(auto &a: Function->args()) {
    // iterate over arguments of function
    // match name to position
  }
  
  //Add a basic block to main to hold instructions, and set Builder
  //to insert there
  Builder.SetInsertPoint(BasicBlock::Create(TheContext, "entry", Function));

}
| IN NONE ENDLINE
{ 
  // Create int function type with no arguments
  FunctionType *FunType = 
    FunctionType::get(Builder.getInt32Ty(),false);

  // Create a main function
  Function *Function = Function::Create(FunType,  
         GlobalValue::ExternalLinkage,funName,M);

  //Add a basic block to main to hold instructions, and set Builder
  //to insert there
  Builder.SetInsertPoint(BasicBlock::Create(TheContext, "entry", Function));
}
;

params_list: ID
{
  $$ = new vector<string>;
  // add ID to vector
}
| params_list COMMA ID
{
  // add ID to $1
}
;

final: FINAL ensemble endline_opt
{
  $$ = Builder.CreateRet($2);
}
;

endline_opt: %empty | ENDLINE;
            

statements_opt: %empty
            | statements{
              $$ = $1;
            };

statements:   statement{
  $$ = $1;
}
 | statements statement {
  $$ = $1;
 } 
;

statement: ID ASSIGN ensemble ENDLINE
{
  if(Map.find(($1)) == Map.end()) { //does not find the value in the map
    Map[$1] = $3;
    llvm::Value* strConstant = Builder.CreateGlobalStringPtr($1, "  ");
    $$ = strConstant;
  }
}
| ID NUMBER ASSIGN ensemble ENDLINE
| ID LBRACKET ensemble RBRACKET ASSIGN ensemble ENDLINE
;

ensemble:  expr {
  $$ = $1;
}
| expr COLON NUMBER // 566 only
| ensemble COMMA expr //double check
{
  //cout << "In ensemble, $1 and $3 are  " << $1 << "and " << $3 << "  \n";
  Value *one_shl = Builder.CreateShl($1, Builder.getInt32(1));
  Value *two_shl = Builder.CreateShl($3, Builder.getInt32(0));
  $$ = Builder.CreateOr(one_shl, two_shl);
  //cout << "In ensemble, $$ is " << $$ << "  \n"; 
}
| ensemble COMMA expr COLON NUMBER   // 566 only;

expr: ID{

    $$ = Map[$1];

}
| ID NUMBER{
    Value* charPtr_arg1 = Map[$1];
    Value* intPtr_arg2  = ConstantInt::get(Builder.getInt32Ty(), $2);
    regs[1] = charPtr_arg1;
    regs[2] = intPtr_arg2;
    regs[3] = Builder.CreateLShr(regs[1], regs[2]);
    $$ = charPtr_arg1;
    Value* intPtr_arg3  = ConstantInt::get(Builder.getInt32Ty(), 1);
    $$ = Builder.CreateAnd( regs[3], intPtr_arg3);
}
| NUMBER
{
  //  cout << "\t\t\tIn expr Number is  " << $1 << "   \n";
  $$ = Builder.getInt32($1);
}
| expr PLUS expr
| expr MINUS expr
| expr XOR expr{
    //Value* exprPtr_arg1 = Builder.CreateGlobalStringPtr($1, "1deadbee");
    //Value* exprPtr_arg3 = Builder.CreateGlobalStringPtr($3, "2badcafe");
    $$ = Builder.CreateXor($1, $3);
}
| expr AND expr
| expr OR expr
| INV expr
| BINV expr
| expr MUL expr
| expr DIV expr
| expr MOD expr
| ID LBRACKET ensemble RBRACKET
| LPAREN ensemble RPAREN
/* 566 only */
| LPAREN ensemble RPAREN LBRACKET ensemble RBRACKET
| REDUCE AND LPAREN ensemble RPAREN
| REDUCE OR LPAREN ensemble RPAREN
| REDUCE XOR LPAREN ensemble RPAREN
| REDUCE PLUS LPAREN ensemble RPAREN
| EXPAND  LPAREN ensemble RPAREN
;

%%

unique_ptr<Module> parseP1File(const string &InputFilename)
{
  funName = InputFilename;
  if (funName.find_last_of('/') != string::npos)
    funName = funName.substr(funName.find_last_of('/')+1);
  if (funName.find_last_of('.') != string::npos)
    funName.resize(funName.find_last_of('.'));
    
  //errs() << "Function will be called " << funName << ".\n";
  
  // unique_ptr will clean up after us, call destructor, etc.
  unique_ptr<Module> Mptr(new Module(funName.c_str(), TheContext));

  // set global module
  M = Mptr.get();
  
  /* this is the name of the file to generate, you can also use
     this string to figure out the name of the generated function */
  yyin = fopen(InputFilename.c_str(),"r");

  for(int i=0; i<8; i++)
    regs[i] = Builder.getInt32(0);
  
  //yydebug = 1; 
  if (yyparse() != 0)
    // errors, so discard module
    Mptr.reset();
  else
    // Dump LLVM IR to the screen for debugging
    M->print(errs(),nullptr,false,true);
  
  return Mptr;
}

void yyerror(const char* msg)
{
  printf("%s\n",msg);
}
