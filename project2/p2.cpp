#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <vector>

#include "llvm-c/Core.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Analysis/InstructionSimplify.h"

using namespace llvm;
using namespace std;

static void CommonSubexpressionElimination(Module *);

static void summarize(Module *M);
static void print_csv_file(std::string outputfile);

static cl::opt<std::string>
        InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::Required, cl::init("-"));

static cl::opt<std::string>
        OutputFilename(cl::Positional, cl::desc("<output bitcode>"), cl::Required, cl::init("out.bc"));

static cl::opt<bool>
        Mem2Reg("mem2reg",
                cl::desc("Perform memory to register promotion before CSE."),
                cl::init(false));

static cl::opt<bool>
        NoCSE("no-cse",
              cl::desc("Do not perform CSE Optimization."),
              cl::init(false));

static cl::opt<bool>
        Verbose("verbose",
                    cl::desc("Verbose stats."),
                    cl::init(false));

static cl::opt<bool>
        NoCheck("no",
                cl::desc("Do not check for valid IR."),
                cl::init(false));

int main(int argc, char **argv) {
    // Parse command line arguments
    cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

    // Handle creating output files and shutting down properly
    llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.
    LLVMContext Context;

    // LLVM idiom for constructing output file.
    std::unique_ptr<ToolOutputFile> Out;
    std::string ErrorInfo;
    std::error_code EC;
    Out.reset(new ToolOutputFile(OutputFilename.c_str(), EC,
                                 sys::fs::OF_None));

    EnableStatistics();

    // Read in module
    SMDiagnostic Err;
    std::unique_ptr<Module> M;
    M = parseIRFile(InputFilename, Err, Context);

    // If errors, fail
    if (M.get() == 0)
    {
        Err.print(argv[0], errs());
        return 1;
    }

    // If requested, do some early optimizations
    if (Mem2Reg)
    {
        legacy::PassManager Passes;
        Passes.add(createPromoteMemoryToRegisterPass());
        Passes.run(*M.get());
    }

    if (1) {
        CommonSubexpressionElimination(M.get());
    }

    // Collect statistics on Module
    summarize(M.get());
    print_csv_file(OutputFilename);

    if (Verbose)
        PrintStatistics(errs());

    // Verify integrity of Module, do this by default
    if (!NoCheck)
    {
        legacy::PassManager Passes;
        Passes.add(createVerifierPass());
        Passes.run(*M.get());
    }

    // Write final bitcode
    WriteBitcodeToFile(*M.get(), Out->os());
    Out->keep();

    return 0;
}

static llvm::Statistic nFunctions = {"", "Functions", "number of functions"};
static llvm::Statistic nInstructions = {"", "Instructions", "number of instructions"};
static llvm::Statistic nLoads = {"", "Loads", "number of loads"};
static llvm::Statistic nStores = {"", "Stores", "number of stores"};

static void summarize(Module *M) {
    for (auto i = M->begin(); i != M->end(); i++) {
        if (i->begin() != i->end()) {
            nFunctions++;
        }

        for (auto j = i->begin(); j != i->end(); j++) {
            for (auto k = j->begin(); k != j->end(); k++) {
                Instruction &I = *k;
                nInstructions++;
                if (isa<LoadInst>(&I)) {
                    nLoads++;
                } else if (isa<StoreInst>(&I)) {
                    nStores++;
                }
            }
        }
    }
}

static void print_csv_file(std::string outputfile)
{
    std::ofstream stats(outputfile + ".stats");
    auto a = GetStatistics();
    for (auto p : a) {
        stats << p.first.str() << "," << p.second << std::endl;
    }
    stats.close();
}

static llvm::Statistic CSEDead = {"", "CSEDead", "CSE found dead instructions"};
static llvm::Statistic CSEElim = {"", "CSEElim", "CSE redundant instructions"};
static llvm::Statistic CSESimplify = {"", "CSESimplify", "CSE simplified instructions"};
static llvm::Statistic CSELdElim = {"", "CSELdElim", "CSE redundant loads"};
static llvm::Statistic CSEStore2Load = {"", "CSEStore2Load", "CSE forwarded store to load"};
static llvm::Statistic CSEStElim = {"", "CSEStElim", "CSE redundant stores"};

bool isDead(Instruction &I) {
 
  int opcode = I.getOpcode();
  switch(opcode){
  case Instruction::Add:
    case Instruction::FNeg:
    case Instruction::FAdd: 	
    case Instruction::Sub:
    case Instruction::FSub: 	
    case Instruction::Mul:
    case Instruction::FMul: 	
    case Instruction::UDiv:	
    case Instruction::SDiv:	
    case Instruction::FDiv:	
    case Instruction::URem: 	
    case Instruction::SRem: 	
    case Instruction::FRem:
    case Instruction::Shl: 	
    case Instruction::LShr: 	
    case Instruction::AShr: 	
    case Instruction::And: 	
    case Instruction::Or: 	
    case Instruction::Xor:
    case Instruction::GetElementPtr: 	
    case Instruction::Trunc: 	
    case Instruction::ZExt: 	
    case Instruction::SExt: 	
    case Instruction::FPToUI: 	
    case Instruction::FPToSI: 	
    case Instruction::UIToFP: 	
    case Instruction::SIToFP: 	
    case Instruction::FPTrunc: 	
    case Instruction::FPExt: 	
    case Instruction::PtrToInt: 	
    case Instruction::IntToPtr: 	
    case Instruction::BitCast: 	
    case Instruction::AddrSpaceCast: 	
    case Instruction::ICmp: 	
    case Instruction::FCmp: 	
    case Instruction::ExtractElement: 	
    case Instruction::InsertElement: 	
    case Instruction::ShuffleVector: 	
    case Instruction::ExtractValue: 	
    case Instruction::InsertValue:
    case Instruction::Alloca:
    case Instruction::PHI: 
    case Instruction::Select: 

      if ( I.use_begin() == I.use_end() )
	{
	  return true;
	}
      break;

    case Instruction::Load:
      {
	LoadInst *li = dyn_cast<LoadInst>(&I);
	if (li && li->isVolatile())
	  return false;
	if (I.use_begin() == I.use_end())
	  return true;
	break;
	
      }
      
    default: 
      // any other opcode fails 
	return false;
    }
     
 
  return false;
}

static void DeadInstRemoval(Module *M){
    // uint32_t dead_inst_count = 0;
  // looping over the functions inside a module
  for(Module::iterator i = M->begin(); i!=M->end(); i++){
    Function &Func = *i;
    // looping over all the basic blocks in the function, F
    for(Function::iterator j = Func.begin(); j != Func.end(); j++){
      BasicBlock *bscblk = &*j;
      for(BasicBlock::iterator k = bscblk->begin(); k != bscblk->end();){
        Instruction &inst = *k;
        if (isDead(inst)) {
            k = inst.eraseFromParent();
            CSEDead++;
        } else {
            Value *val = simplifyInstruction(&inst, M->getDataLayout());
            if(val != NULL){
              inst.replaceAllUsesWith(val);
              CSESimplify++;
              //remove later
              CSELdElim++;
              CSEStore2Load++;
              CSEStElim++;
            }
            k++;
        }
      }
    }
  }
    // dead_inst_count = CSEDead;
    //errs() << "Found a dead instruction "; errs() << CSEDead ; errs()  << "\n";

}
/*
Module
Func
BB
Inst
 r1 = add 2,3   
 branch z
 r1 = add 2,3
 call label 1
 r1 = add 2,3
 mul r2, r1
*/

static void CSEElim_for_CSE(Module *M) {
    unsigned int i_num_of_Operands;
    unsigned int j_num_of_Operands;
    unsigned int j_opcode;
    unsigned int i_opcode;
    vector<Value*> i_operands;
    unsigned int matchFoundCntr = 0;
    bool instructionCopyFound = true;

    for (Module::iterator iter = M->begin(); iter != M->end(); ++iter) {
        Function &Func = *iter;

        for (inst_iterator i = inst_begin(Func), e = inst_end(Func); i != e; ++i) {
            i_operands.clear();
            matchFoundCntr = 0;
            instructionCopyFound = true;
            Instruction *i_inst = &*i;
            i_opcode = i_inst->getOpcode();
            Type *i_inst_type = i_inst->getType();
            i_num_of_Operands = i_inst->getNumOperands();

            for (unsigned int i_oprnd = 0; i_oprnd < i_num_of_Operands; ++i_oprnd) {
                Value *operand = i_inst->getOperand(i_oprnd);
                i_operands.push_back(operand);
            }

            for (inst_iterator j = std::next(i); j != e; ++j) {
                Instruction *j_inst = &*j;
                j_opcode = j_inst->getOpcode();
                Type *j_inst_type = j_inst->getType();
                j_num_of_Operands = j_inst->getNumOperands();

                // Compare and perform your CSE logic here
                if((i_inst_type == j_inst_type) && (i_opcode == j_opcode) && (i_num_of_Operands == j_num_of_Operands)){
                    for (unsigned int j_oprnd = 0; j_oprnd < j_num_of_Operands; ++j_oprnd) {
                        Value *operand = j_inst->getOperand(j_oprnd);
                        if(i_operands[j_oprnd] == operand){
                            matchFoundCntr++;
                        }
                        else
                            instructionCopyFound = false;
                    }
                    if( (matchFoundCntr == i_num_of_Operands) && (instructionCopyFound == true) ){
                        /*replace all uses of j with i
                        erase j
                        CSE_Basic++
                        */
                       j_inst->replaceAllUsesWith(i_inst);
                    //    LLVMValueRef rm = j_inst;
                       //j_inst->eraseFromParent();
                       CSEElim++;
                    }
                }
            }
        }
    }
}
// static void CSEElim_for_CSE(Module *M){
//     inst_iterator i;//i will traverse all instructions in the module, one instruction at a time
//     inst_iterator j;//j will traverse such that j = i+1
//                     // if j matches i, delete j and replace all uses of j with i
//     uint32_t i_opcode;
//     uint32_t j_opcode;
//     Value* i_inst_type;
//     Value* j_inst_type;

//     for(Module::iterator iter = M->begin(); iter!=M->end(); iter++){
//         Function &Func = *iter;
//         i = inst_begin(Func);

//         while(i != inst_end(Func)){
//             i_inst_type = LLVMTypeOf(*i);
//             i_opcode = i->getOpcode();
//             *j = LLVMGetNextInstruction(*i);
//             while(j != inst_end(Func)){
//                 j_inst_type = LLVMTypeOf(*j);
//                 j_opcode = *j->getOpcode();
//                 j = LLVMGetNextInstruction(*j);
//             } 
//         i = LLVMGetNextInstruction(*i);
//         }         
//     }
// }

//static void CSEElim_for_CSE(Module *M){
//     std::set<Instruction*> new_worklist;
//     bool duplicate_inst_found = false;
//     bool first_opcode_match_found = false;
//     unsigned int worklist_inst_opcode;
//     unsigned int inst_iterator_opcode;


//     for(Module::iterator i = M->begin(); i!=M->end(); i++){
//         Function &Func = *i;
//         for (inst_iterator I = inst_begin(Func), E = inst_end(Func); I != E; ++I){
//             if (new_worklist.find(&*I) != new_worklist.end()) {
//             // Instruction already exists in the worklist, ignore
//                 continue;
//             } else {
//                 new_worklist.insert(&*I);
//             }
//         }
//     }
//     //All unique instructions are now in new_worklist

//     for (auto it = new_worklist.begin(); it != new_worklist.end(); ++it) {
//         // 'it' is an iterator pointing to the current instruction
//         Instruction* currentInstruction = *it;
//         worklist_inst_opcode = currentInstruction->getOpcode();

//         for(Module::iterator i = M->begin(); i!=M->end(); i++){
//             Function &Func = *i;
//             for (inst_iterator I = inst_begin(Func), E = inst_end(Func); I != E; ++I){
//                 inst_iterator_opcode = I->getOpcode();
//                 if(inst_iterator_opcode == worklist_inst_opcode){
//                     first_opcode_match_found = true;
//                 }

//                 if(first_opcode_match_found){

//                 }
//             }
//         }
// }


//     // //Iterate through all instructions again, if there is a hit in the new_worklist, delete it from parent
//     // for(Module::iterator i = M->begin(); i!=M->end(); i++){
//     //     Function &Func = *i;
//     //     for (inst_iterator I = inst_begin(Func), E = inst_end(Func); I != E; ++I){
//     //         if (new_worklist.find(&*I) != new_worklist.end()) {
//     //         // Atleast 1 match for the Instruction found in the worklist
//     //             for(inst_iterator Inst = I, E = inst_end(Func); Inst != E; ++Inst){
//     //                 if(Inst == )
//     //                 Inst->eraseFromParent();
//     //                 CSEElim++;
//     //             }
//     //         }
//     //     }
//     // }    
        
//     // LLVMValueRef i = LLVMGetNextInstruction(wrap(&(*I)));
//     // I is iterator for insturctions in basicblcok    
//}

static void CommonSubexpressionElimination(Module *M) {
    DeadInstRemoval(M);
    CSEElim_for_CSE(M);
}
