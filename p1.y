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
  string func_name_str;
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

  vector<string> args;
  for(auto s: *$2)
  {
    args.push_back(s);
  }

  int arg_no=0;
  for(auto &a: Function->args()) {
    // iterate over arguments of function
    // match name to position
    Value *arg_ptr = &a;// as it loops, refers first to a, then b, then c
    Map.insert({args[arg_no],arg_ptr});

    arg_no++;
  }
     for (const auto& pair : Map) {
        std::cout << "Key: " << pair.first << ", Value: \n" << pair.second << std::endl;
        // If you want to access the actual object pointed by the Value*
        // Uncomment the line below and replace 'YourValueType' with the actual type
        // std::cout << "Key: " << pair.first << ", Value: " << pair.second->YourValueTypeMember << std::endl;
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
  $$->push_back($1);
}
| params_list COMMA ID
{
  $1->push_back($3);
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
  if(Map.find(($1)) == Map.end()) { //doesn't find value in map
    Map[$1] = $3;
    llvm::Value* strConstant = Builder.CreateGlobalStringPtr($1, "  ");
    $$ = strConstant;
  }
  else{
    Map[$1] = $3;
    $$ = Map[$1];
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
  Value *one_shl = Builder.CreateShl($1, Builder.getInt32(1));
  $$ = Builder.CreateOr(one_shl, $3);
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
  $$ = Builder.getInt32($1);
}
| expr PLUS expr
{
  $$ = Builder.CreateAdd($1, $3);
}
| expr MINUS expr
{
  $$ = Builder.CreateSub($1, $3);
}
| expr XOR expr
{
  $$ = Builder.CreateXor($1, $3);
}
| expr AND expr
{
  $$ = Builder.CreateAnd($1, $3);
}
| expr OR expr
{
  $$ = Builder.CreateOr($1, $3);
}
| INV expr
{
  $$ = Builder.CreateNot($2);
}
| BINV expr
{
  //Value* temp = ConstantInt::get(Builder.getInt32Ty(), 1);
  $2->dump();
  Value* temp2 = Builder.CreateXor($2, Builder.getInt32(1));
  temp2->dump();
  $$ = Builder.CreateNot(temp2);
  $$->dump();
}
| expr MUL expr
{
  $$ = Builder.CreateMul($1, $3);
  cout << "MUL result is " << $$ << " \n";
}
| expr DIV expr
{
  $$ = Builder.CreateSDiv($1, $3);
}
| expr MOD expr
{
  $$ = Builder.CreateSRem($1, $3);
}
| ID LBRACKET ensemble RBRACKET
{
  $$ = $3;
}
| LPAREN ensemble RPAREN
{
  $$ = $2;
}
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
