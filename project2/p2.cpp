#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <vector>

#include "llvm-c/Core.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Casting.h"
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

    if (!NoCSE) {
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
    //process the received instruction to extract the opcode and compare it using switch statement
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
  // looping over the functions inside a module
  for(Module::iterator i = M->begin(); i!=M->end(); i++){
    Function &Func = *i;
    // looping over all the basic blocks in the function, F
    for(Function::iterator j = Func.begin(); j != Func.end(); j++){
      BasicBlock *bscblk = &*j;
      for(BasicBlock::iterator k = bscblk->begin(); k != bscblk->end();){
        Instruction &inst = *k;
        //if instruction is dead, remove it from parent
        //and increment CSEDead counter
        if (isDead(inst)) {
            k = inst.eraseFromParent();
            CSEDead++;
        } else {
            //if instruction is not dead, simplify it, replace the uses
            // and increment CSESimplify counter
            Value *val = simplifyInstruction(&inst, M->getDataLayout());
            if(val != NULL){
              inst.replaceAllUsesWith(val);
              CSESimplify++;
              //remove later
              
            }
            k++;
        }
      }
    }
  }
}


// bool isFunctionEmpty(const Function *func) {
//     const BasicBlock &entryBlock = func->getEntryBlock();
//     return entryBlock.empty();
// }

static void global_CSE(BasicBlock *bb, Instruction *Inst_in){
    //get the function of which the received basic block is part of
    Function *function = bb->getParent();
    //create the dominator tree for the function extracted 
    DominatorTree DT_gcse(*function);

    //create a vector that will store the descendants
    //of the basic block
    SmallVector<BasicBlock*, 8> BB_descendants;
    DT_gcse.getDescendants(bb, BB_descendants);//Piazza 324
    
    for(auto &iterating_bb : BB_descendants){
        //if the basic block is same as one received, ignore it
        //duplicate instructions in that block was removed during local CSE
        if(iterating_bb == bb){
            continue;
        }
        else {
            std::vector<Instruction*> inst_tobe_deleted;
            for(auto I = iterating_bb->begin(); I != iterating_bb->end(); I++){
                auto next_inst = I;
                //if there is an instruction that is identical to the one
                //received by this function, then replace the uses of the 
                //instruction in 'this' basic block and increment the CSEElim counter
                if(next_inst->isIdenticalTo(Inst_in) == true){
                    next_inst->replaceAllUsesWith(Inst_in);
                    CSEElim++;
                    //inst has been replaced, can be removed from parent
                    //on the safe side, added it to a vector to be deleted later
                    inst_tobe_deleted.push_back(&(*next_inst));
                }
            }
            //delete the instructions 
            for (auto* instruction : inst_tobe_deleted) {
                instruction->eraseFromParent();
            }
        }
    }
}

// int glob_counter = 0;
static void local_CSE(Module *M){
    bool isRestrictedInst; //dont perform CSE on these instructions

    for(auto &func : *M){
        for(auto &basicblock : func){
            
            for(auto inst = basicblock.begin(); inst != basicblock.end(); inst++){
                isRestrictedInst = false;
                //check if the inst is load, store, branch, phi, return, call. 
                //If yes, we need to ignore them for CSE
                if( (isa<LoadInst>(*inst)) || (isa<AllocaInst>(*inst))  || (isa<StoreInst>(*inst)) || (isa<ReturnInst>(*inst)) ||
                    (isa<CallInst>(*inst)) || (isa<PHINode>(*inst))     || (isa<BranchInst>(*inst)) ) {
                        isRestrictedInst = true;
                }

                if(isRestrictedInst){
                    // glob_counter++;
                    // errs() << ("glob counter = ") << glob_counter << " \n";
                    continue;
                }
                else{
                    auto next_inst = inst;
                    next_inst++;
                    //if there is an instruction that is identical to the one
                    //received by this function, then replace the uses of the 
                    //instruction in 'this' basic block and increment the CSEElim counter 
                    std::vector<Instruction*> tobe_deleted;
                    for(; next_inst != basicblock.end(); next_inst++){
                        if((*next_inst).isIdenticalTo(&*inst)){
                            (*next_inst).replaceAllUsesWith(&(*inst));
                            //inst has been replaced, can be removed from parent
                            //on the safe side, added it to a vector to be deleted later
                            tobe_deleted.push_back(&(*next_inst));
                        }
                    }

                    for(auto inst_iter: tobe_deleted){
                        //erase from parent and increment CSEElim
                        inst_iter->eraseFromParent();
                        CSEElim++;
                    }
                    //pass this instruction and basicblock to global_CSE
                    //in order to recursively remove any occurences of inst
                    //throughout the module
                    global_CSE(&basicblock, &(*inst));
                }
            }
        }
    }
}

/*
While traversing the instructions in a single basic block, if you come across a load we will look to see if there are redundant loads within the same basic block only.
You may only eliminate a later load as redundant if the later load is not volatile, it loads the same address, it loads the same type of operand, and there are no 
intervening stores or calls to any address.

Here is the pseudocode you should follow:
for each load, L:
    for each instruction, R, that follows L in its basic block:
        if R is load && R is not volatile and R’s load address is the same as L && TypeOf(R)==TypeOf(L):
            Replace all uses of R with L
            Erase R
            CSERLoad++
        if R is a store:
            break (stop considering load L, move on)
*/

static void elim_red_loads(Module* M){
    for(auto &func : *M){
        for(auto &basicblock : func){     
                   
            for(auto inst = basicblock.begin(); inst != basicblock.end(); inst++){
                //(*inst).print(errs() << "\n");

                //check if load
                if((isa<LoadInst>(*inst))){
                    bool LoadMatchDetected = false;
                    // errs() << "\nIs a load instruction\n";
                    //find address of load inst
                    Value* val1 = inst->getOperand(0);
                    auto next_inst = inst;
                    next_inst++;
                    std::vector<Instruction*> inst_tobe_deleted;
                    for(; next_inst != basicblock.end(); next_inst++){
                        //if inst is store or call, can it and move on
                        if( (isa<StoreInst>(*next_inst)) || (isa<CallInst>(*next_inst)) ){
                            //stop considering inst altogether
                            //errs() << "\t\tstop considering inst altogether\n" ;
                            //(*next_inst).print(errs() << "\n");
                            break;
                        }
                        
                        //later inst is load, NOT volatile, has same address and has same type (phew!! what a relief!)
                        if( ( isa<LoadInst>(*next_inst) ) && ( (*next_inst).isVolatile() == false ) && 
                            ( (*inst).getType() == (*next_inst).getType() ) ) {
                            //Replace all uses of next_inst with inst
                            Value* val2 = next_inst->getOperand(0);
                            if(val1 == val2){
                                (*next_inst).replaceAllUsesWith(&(*inst));
                                //Erase next_inst
                                inst_tobe_deleted.push_back((&*next_inst));
                                //increment countter CSELdElim
                                CSELdElim++;
                                //set this flag to remove instructions from vector later on
                                LoadMatchDetected = true;
                            }
                        }
                        else
                            continue;
                    }//end of checking if the instructions after the detected load 'could be' a match for elimination 
                        //delete all redundantinstructions
                    if(LoadMatchDetected == true){
                        for(auto inst_iter: inst_tobe_deleted){
                            inst_iter->eraseFromParent();
                        }
                    }
                }
            }//end of instruction iteration in the basic block
        }//end of block iteration within a function
    }//end of function iteration within a module
}

static void elim_red_store(Module* M){
    for(auto &func : *M){
        for(auto &basicblock : func){
            for(auto inst = basicblock.begin(); inst != basicblock.end(); inst++){
                
                bool StoreMatchDetected = false;
                if((isa<StoreInst>(*inst))){// S , earlier store instn in program order
                    StoreMatchDetected = false;
                    //typecast inst as StoreInst
                    StoreInst *s_inst = dyn_cast<StoreInst>(inst);
                    auto next_inst = inst;
                    next_inst++;//R
                    std::vector<Instruction*> inst_tobe_deleted;
                    for(; next_inst != basicblock.end(); next_inst++){
                        
                        //if  R is a load   &&  R is not volatile
                        if( ( isa<LoadInst>(*next_inst) ) && ( (*next_inst).isVolatile() == false ) ) {
                            //get the address of instructions and their types, their operand's type
                            LoadInst *r_inst            = dyn_cast<LoadInst>(next_inst);
                            Value* s_addr               = s_inst->getOperand(0);
                            llvm::Type* s_val_op_type   = s_inst->getOperand(0)->getType();
                            Value* r_addr               = r_inst->getOperand(0);
                            llvm::Type* r_type          = r_inst->getType();
                            //(R’s load address is the same as S) && (type of r == type of s_inst's operand)
                            if( (s_addr == r_addr) && (s_val_op_type == r_type) ){
                                //replace r_inst's use with s_inst's operand
                                (*r_inst).replaceAllUsesWith(s_inst->getOperand(1));
                                //Erase next_inst
                                inst_tobe_deleted.push_back((&*r_inst));
                                //increment the counter for CSEStore2Load
                                CSEStore2Load++;
                                StoreMatchDetected = true;
                                continue;//seems irrelevant
                            }
                        }
                        //Could not do this properly so commented it out
                            // else if(( isa<StoreInst>(*next_inst) ) && ( (*inst).isVolatile() == false )){
                            //     StoreInst *r_inst   = dyn_cast<StoreInst>(next_inst);
                            //     Value* r_addr       = r_inst->getOperand(0);
                            //     Value* s_addr       = s_inst->getOperand(0);
                            //     llvm::Type* r_val_op_type   = r_inst->getOperand(0)->getType();
                            //     llvm::Type* s_val_op_type   = s_inst->getOperand(0)->getType();
                            //     if( (r_addr == s_addr) && (r_val_op_type == s_val_op_type)){
                            //         inst_tobe_deleted.push_back((&*s_inst));
                            //         CSEStElim++;
                            //         StoreMatchDetected = true;
                            //         break;
                            //     }
                            // }
                            // Does not work properly so commented it out
                        else {//if(( isa<LoadInst>(*next_inst) ) || ( isa<StoreInst>(*next_inst) ) || ( isa<CallInst>(*next_inst) )){
                            // CSEStElim++;
                            break;
                        }
                    }//1 store found, checking other inst
                    //delete the instruction
                    if(StoreMatchDetected == true){
                        for(auto inst_iter: inst_tobe_deleted){
                            CSEStElim++;
                            inst_iter->eraseFromParent();
                        }
                    }

            }//end of inst traversing withing the block

            }//end of block traversing
        }//end of function traversing withing module
    }
}

static void CommonSubexpressionElimination(Module *M) {
    DeadInstRemoval(M);
    local_CSE(M);
    elim_red_loads(M);
    elim_red_store(M);
    // errs() << "CSEElim = " << CSEElim << " \n";
    // errs() << "CSEDead = " << CSEDead << " \n";
    // errs() << "CSELdElim = " << CSELdElim << " \n";
}
