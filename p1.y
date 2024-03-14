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

  //create a vector of strings and push all the args from params_list
  vector<string> args;
  for(auto s: *$2)
  {
    args.push_back(s);
  }

  int arg_no=0;
  for(auto &a: Function->args()) {
    // iterate over arguments of function
    // match name to position
    Value *arg_ptr = &a;
    //insert the argument against its argument number such that it forms a key-value pair
    Map.insert({args[arg_no],arg_ptr});
    //increment the argument count for each iteration
    arg_no++;
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
  //if single argument is there, push it to the vector
  $$->push_back($1);
}
| params_list COMMA ID
{
  //if multiple arguments are seperated by COMMA, add ID to the vector.
  $1->push_back($3);
}
;

final: FINAL ensemble endline_opt
{
  //return the ensemble
  $$ = Builder.CreateRet($2);
}
;

endline_opt: %empty | ENDLINE;
            

statements_opt: %empty{
  
}
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
  if(Map.find(($1)) == Map.end()) { 
    // Case: doesn't find value in map.
    // Insert the ensemble in the Map such that it is linked against ID, 
    // such that ID and ensemble form a pair in the hashmap
    Map[$1] = $3;
    llvm::Value* strConstant = Builder.CreateGlobalStringPtr($1, "  ");
    $$ = strConstant;
  }
  else{
    // Case: Value exists in the hashmap. That means the Value against the key "ID" 
    // is to be updated. So store the ensemble in ID's index in hashmap
    Map[$1] = $3;
    $$ = Map[$1];
  }
}
| ID NUMBER ASSIGN ensemble ENDLINE //TODO, making fail_4 fail
{
  //get the Value assigned to key ID
  Value* val_from_map = Map[$1];
  //Create mask by Left shift the ensemble by NUMBER bits
  Value* temp_1 = Builder.CreateShl($4, $2);
  //AND the Extracted bit with 1
  Value* temp_2 = Builder.CreateAnd(temp_1, Builder.getInt32(1));
  // OR the Anded Value in val_from_map
  Value* result = Builder.CreateOr(temp_2, val_from_map);
  //store the result back in the hashmap for the same ID
  Map[$1] = result;
  $$ = result;
}
| ID LBRACKET ensemble RBRACKET ASSIGN ensemble ENDLINE
{
  //original existing value
  Value* map_value = Map[$1];
  //bit position of ensemble $3 which will be updated with ensemble $6 
  Value* bitposition = $3;
  Value* bit_to_be_pushed = $6;
  // Equivalent C code for inserting the 'bit' at i'th position -> result = result | (bit << i);
  Value* leftShiftedBit = Builder.CreateShl(bit_to_be_pushed, bitposition);
  Value* result = Builder.CreateOr(map_value, leftShiftedBit);
  Map[$1] = result;
  $$ = Map[$1];
}
;

ensemble:  expr {
  //return expr as is
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
    // look up Value for ID in the map
    Value* charPtr_arg1 = Map[$1];
    //create a temp variable to store value of NUMBER
    Value* intPtr_arg2  = ConstantInt::get(Builder.getInt32Ty(), $2);
    regs[1] = charPtr_arg1;
    regs[2] = intPtr_arg2;
    //Right shift Value from Map by NUMBER bits
    regs[3] = Builder.CreateLShr(regs[1], regs[2]);
    $$ = charPtr_arg1;
    //Once value is right shifted, AND it with 1 and return it using $$
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
  $$ = Builder.CreateXor($2, Builder.getInt32(1));
}
| expr MUL expr
{
  $$ = Builder.CreateMul($1, $3);
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
  //value of the key 'ID'
  Value* val_from_map = Map[$1];
  // shift the $3 position bit of key ID's value to the LSB
  Value* temp_1 = Builder.CreateLShr(val_from_map, $3);
  //AND that value with 1 and return it
  Value* temp_2 = Builder.CreateAnd(temp_1, Builder.getInt32(1)); 
  $$ = temp_2;
}
| LPAREN ensemble RPAREN
{
  $$ = $2;
}
/* 566 only */
/* Test 13 */
| LPAREN ensemble RPAREN LBRACKET ensemble RBRACKET
{
  // value of the ensemble at $2
  Value* val_of_arg1 = $2;
  // Right shift the value of ensemble by $5 bits
  Value* temp_1 = Builder.CreateLShr(val_of_arg1, $5);
  //AND that value with 1 and return it
  Value* temp_2 = Builder.CreateAnd(temp_1, Builder.getInt32(1)); 
  $$ = temp_2;
}
| REDUCE AND LPAREN ensemble RPAREN
{
  Value* result = Builder.getInt32(0);
  Value* number_to_be_modified = $4;
  Value* temp1 = Builder.getInt32(0);
  Value* temp2 = Builder.getInt32(0);
  for(int i = 0; i < 32; i++){
    //right shift the ith bit of the number to be modified to the LSB
    temp1 = Builder.CreateLShr(number_to_be_modified, Builder.getInt32(i));
    // AND it with 1 to extract it, and the store it
    temp2 = Builder.CreateAnd(temp1, Builder.getInt32(1));
    // AND the mask obtained from above code with the original value
    result = Builder.CreateAnd(temp2, result);
  }
  $$ = result;
}
| REDUCE OR LPAREN ensemble RPAREN
{
  Value* result = Builder.getInt32(0);
  Value* number_to_be_modified = $4;
  Value* temp1 = Builder.getInt32(0);
  Value* temp2 = Builder.getInt32(0);
  for(int i = 0; i < 32; i++){
    //right shift the ith bit of the number to be modified to the LSB
    temp1 = Builder.CreateLShr(number_to_be_modified, Builder.getInt32(i));//(bit >> i)
    // AND it with 1 to extract it, and the store it
    temp2 = Builder.CreateAnd(temp1, Builder.getInt32(1));//~(1 << pos)
    // OR the mask obtained from above code with the original value
    result = Builder.CreateOr(temp2, result);
  }
  $$ = result;
}
| REDUCE XOR LPAREN ensemble RPAREN
{
  Value* result = Builder.getInt32(0);
  Value* temp = $4;
  Value* temp1 = Builder.getInt32(0);
  Value* temp2 = Builder.getInt32(0);
  for(int i = 0; i < 32; i++){
    //right shift the ith bit of the number to be modified to the LSB
    temp1 = Builder.CreateLShr(temp, Builder.getInt32(i));//(bit >> i)
    // AND it with 1 to extract it, and the store it
    temp2 = Builder.CreateAnd(temp1, Builder.getInt32(1));//~(1 << pos)
    // XOR the mask obtained from above code with the original value
    result = Builder.CreateXor(temp2, result);
  }
  $$ = result;
}
| REDUCE PLUS LPAREN ensemble RPAREN
{
  Value* result = Builder.getInt32(0);
  Value* temp = $4;
  Value* temp1 = Builder.getInt32(0);
  Value* temp2 = Builder.getInt32(0);
  for(int i = 0; i < 32; i++){
    //right shift the ith bit of the number to be modified to the LSB
    temp1 = Builder.CreateLShr(temp, Builder.getInt32(i));//(bit >> i)
    // AND it with 1 to extract it, and the store it
    temp2 = Builder.CreateAnd(temp1, Builder.getInt32(1));//~(1 << pos)
    // ADD the mask obtained from above code with the original value
    result = Builder.CreateAdd(temp2, result);
  }
  $$ = result;
}
| EXPAND LPAREN ensemble RPAREN
{
  Value* bit_to_be_pushed = $3;
  Value* result = Builder.getInt32(0);
  Value* temp;
  int i;
  for(i = 0; i < 32; i++){
    //Insert the bit obtained from ensemble at all 32 bits of the return integer
    //by left shifting the bit, one position at a time and then ORing it with
    //original number
    temp = Builder.CreateShl(bit_to_be_pushed, Builder.getInt32(i));//(bit << i)
    result = Builder.CreateOr(result, temp);//~(1 << pos)
  }
  $$ = result;
}
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
