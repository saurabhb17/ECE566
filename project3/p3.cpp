#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <set>
#include <vector>
#include <utility>
#include <map>
#include <unordered_map>
#include <iostream>
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
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Instruction.h"
//#include "llvm/Analysis/CGSCCAnalysisManager.h"
//#include "llvm/Analysis/ModuleAnalysisManager.h"


using namespace llvm;
using namespace std;

static LLVMContext Context;

LLVMContext& getGlobalContext() {
  return Context;
}


static void SoftwareFaultTolerance(Module *);

static void print_csv_file(std::string outputfile);

static cl::opt<std::string>
        InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::Required, cl::init("-"));

static cl::opt<std::string>
        OutputFilename(cl::Positional, cl::desc("<output bitcode>"), cl::Required, cl::init("out.bc"));

static cl::opt<bool>
        NoSWFT("no-swft",
              cl::desc("Do not perform SWFT."),
              cl::init(false));


static cl::opt<bool>
        Verbose("verbose",
                    cl::desc("Verbose stats."),
                    cl::init(false));

static cl::opt<bool>
        NoCheck("no",
                cl::desc("Do not check for valid IR."),
                cl::init(false));

// Use this to enable your bonus code
static cl::opt<bool>
        Bonus("bonus",
                cl::desc("Run the bonus code."),
                cl::init(false));

// Use these to control whether or not parts of your pass run
static cl::opt<bool>
        NoReplicate("no-replicate",
              cl::desc("Do not perform code replication."),
              cl::init(false));

static cl::opt<bool>
        NoControlProtection("no-control-protection",
              cl::desc("Do not perform control flow protection."),
              cl::init(false));



void RunO2(Module *M);
void BuildHelperFunctions(Module *);
void summarize(Module *M);
FunctionCallee AssertFT;
FunctionCallee AssertCFG;
static void CloneInstAndSetOperands(Function *passed_func);
static void VerifyCfg(Function *passed_func);

int main(int argc, char **argv) {
    // Parse command line arguments
    cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

    // Handle creating output files and shutting down properly
    llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.

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

    // Run O2 optimizations
    RunO2(M.get());

    BuildHelperFunctions(M.get());      
    
    if (!NoSWFT) {
      SoftwareFaultTolerance(M.get());
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

static void print_csv_file(std::string outputfile)
{
    std::ofstream stats(outputfile + ".stats");
    auto a = GetStatistics();
    for (auto p : a) {
        stats << p.first.str() << "," << p.second << std::endl;
    }
    stats.close();
}

static llvm::Statistic SWFTAdded = {"", "SWFTadd", "SWFT added instructions"};
/*  cloneMap = {} // empty map, use O(1) lookup
    for all instructions, i:
      if okay to clone i:
          c = clone(i)
          insert c in to basic block beside i
          cloneMap[i] = c // map each original to each clone
*/

/*  for all cloned instructions, c:
    for i in operands range:
      // change each operand to match the cloned version
      if getOperand(c,i) is an instruction with a clone:
        setOperand(c, i, cloneMap[getOperand(c,i)]
*/

//Global Variables and structres
map<Instruction*, Instruction*> cloneMap;
uint32_t my_UID = 1760;
std::vector<llvm::Type*> arg_for_assert;

static void CloneInstAndSetOperands(Function *passed_func){
  bool doNotReplicateInst;
  //Insert instructions in cloneMap
  for (BasicBlock &bscblk : *passed_func) {

    for (auto inst = bscblk.begin(); inst != bscblk.end(); inst++) {
      doNotReplicateInst = false;

      //These instructions should not be repliacted
      if( (isa<AllocaInst>(*inst)) || (isa<StoreInst>(*inst)) || (isa<CallInst>(*inst)) || inst->isTerminator() || (isa<ReturnInst>(*inst)) ||
          (isa<CallInst>(*inst)) || (isa<BranchInst>(*inst)))
      {
        doNotReplicateInst = true;
      }

      if(doNotReplicateInst)
        continue;
      else if(dyn_cast<Instruction>(inst) != nullptr){

        auto clone = inst->clone();
        clone->insertBefore(&*inst);
        cloneMap.insert( {dyn_cast<Instruction>(inst), clone} );
      }
    }
  }//Instructions added in cloneMap

  // set operands of the cloned instruction if that operand is an instruction itself
  if(!cloneMap.empty()){
    for (const auto& c : cloneMap) {
      //iterate through the map, for every cloned instruction's operands
      Instruction* clonedInst = c.second;
      for(unsigned op=0; op < clonedInst->getNumOperands(); op++){
          Value* cloneI_operand = clonedInst->getOperand(op); // --> getOperand(c,i)
          Instruction *inst_op = dyn_cast<Instruction>(cloneI_operand);

          if(inst_op != NULL){
            if(cloneMap.count(inst_op) > 0)
              clonedInst->setOperand(op, cloneMap[inst_op]);  // --> clone->setOperand(0, newOperand);
          }

        }
    }
  }
}


static void SoftwareFaultTolerance(Module *M) {
  Module::FunctionListType &list = M->getFunctionList();

  std::vector<Function*> flist;
  // FIND THE ASSERT FUNCTIONS AND DO NOT INSTRUMENT THEM
  for(Module::FunctionListType::iterator it = list.begin(); it!=list.end(); it++) {
    Function *fptr = &*it;
    if (fptr->size() > 0 && fptr != AssertFT.getCallee() && fptr != AssertCFG.getCallee())
      flist.push_back(fptr);
  }

  // PROTECT CODE IN EACH FUNCTION
  for(std::vector<Function*>::iterator it=flist.begin(); it!=flist.end(); it++)
    {
      // CALL A FUNCTION TO REPLICATE CODE in *it
      //Here I am only cloning instructions and setting the operands
      CloneInstAndSetOperands(*it);
      // VerifyCfg(*it);
    }

    
    if(!cloneMap.empty()){
      for (const auto& c : cloneMap) {
        //fprintf(stderr, "\t%s %d\n",__FILE__, __LINE__);
        Instruction* orign_inst = c.first;
        Instruction* clone_inst = c.second;

        Value* orig_val     = orign_inst;
        Value* clone_value  = clone_inst;

        BasicBlock *bscblk = orign_inst->getParent();
        IRBuilder<> Builder(bscblk);
        //if it is a PHI instruction, set insertPoint at the first non-phi instruction
        (orign_inst->getOpcode() == Instruction::PHI) ? Builder.SetInsertPoint(orign_inst->getParent()->getFirstNonPHI()) : Builder.SetInsertPoint(orign_inst->getNextNode());

        //check the cloned or original instruction is of integer or pointer type, and based
        //on that; insert ICMPEQ, ZEXT and ASSERT instruction for it.
        if(orig_val->getType()->isIntegerTy() || clone_value->getType()->isIntegerTy() || 
            orig_val->getType()->isPointerTy() || clone_value->getType()->isPointerTy())
        {
          Value* ret = Builder.CreateICmpEQ(orign_inst, clone_inst);
          SWFTAdded++;
          Value* zextRetVal = Builder.CreateZExt(ret, IntegerType::getInt32Ty(getGlobalContext()));
          SWFTAdded++;
          std::vector<Value*> args_for_assert;
          args_for_assert.push_back(zextRetVal);
          args_for_assert.push_back(Builder.getInt32(my_UID));
          Function *F = M->getFunction("assert_ft");
          Builder.CreateCall(F->getFunctionType(), F, args_for_assert);
          SWFTAdded++;
          //Global Variable UID is used to assihn it for ZEXT
          my_UID++;
        }
      }
    }
}
