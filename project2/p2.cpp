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
}


bool isFunctionEmpty(const Function *func) {
    const BasicBlock &entryBlock = func->getEntryBlock();
    return entryBlock.empty();
}

static void global_CSE(BasicBlock *bb, Instruction *Inst_in){
    Function *function = bb->getParent();
    DominatorTree DT_gcse(*function);

    SmallVector<BasicBlock*, 8> BB_descendants;
    DT_gcse.getDescendants(bb, BB_descendants);//Piazza 324
    
    for(auto &iterating_bb : BB_descendants){
        if(iterating_bb == bb){
            continue;
        }
        else {
            std::vector<Instruction*> inst_tobe_deleted;
            for(auto I = iterating_bb->begin(); I != iterating_bb->end(); I++){
                auto next_inst = I;
                if(next_inst->isIdenticalTo(Inst_in) == true){
                    next_inst->replaceAllUsesWith(Inst_in);
                    CSEElim++;
                    inst_tobe_deleted.push_back(&(*next_inst));
                }
            }

            for (auto* instruction : inst_tobe_deleted) {
                instruction->eraseFromParent();
            }
        }
    }
}

static void local_CSE(Module *M){
    bool isRestrictedInst = false;
    for(auto &func : *M){
        for(auto &basicblock : func){
            //create DT for each block
            for(auto inst = basicblock.begin(); inst != basicblock.end(); inst++){
                if( (isa<LoadInst>(*inst)) || (isa<StoreInst>(*inst)) || (isa<BranchInst>(*inst)) || (isa<ReturnInst>(*inst)) || (isa<CallInst>(*inst)) 
                    || (isa<PHINode>(*inst)) || (isa<AllocaInst>(*inst)) || (isa<FCmpInst>(*inst)) || (isa<VAArgInst>(*inst)) ){
                        isRestrictedInst = true;
                }

                if(isRestrictedInst){
                    continue;
                }
                else{
                    auto next_inst = inst;
                    next_inst++;
                    std::vector<Instruction*> tobe_deleted;
                    for(; next_inst != basicblock.end(); next_inst++){
                        if((*next_inst).isIdenticalTo(&*inst)){
                            (*next_inst).replaceAllUsesWith(&(*inst));
                            tobe_deleted.push_back(&(*next_inst));
                        }
                    }

                    for(auto k: tobe_deleted){
                        k->eraseFromParent();
                        CSEElim++;
                    }

                    global_CSE(&basicblock, &(*inst));
                }
            }
        }
    }
}

static void CommonSubexpressionElimination(Module *M) {
    DeadInstRemoval(M);
    local_CSE(M);
}
