#include <iostream>
#include <vector>
#include <cstring>
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

namespace
{

    class AugmentedBasicBlock{
    private:
        std::string blockId;
        bool isConditionalBlock;
        bool hasInlineAssembly;
        AugmentedBasicBlock *trueBlock;
        AugmentedBasicBlock *falseBlock;
        AugmentedBasicBlock *nextBlock;
        std::vector<StringRef> instructions;
        std::vector<StringRef> functions;
        std::vector<std::string> parents;        
    public:

        AugmentedBasicBlock(){
            isConditionalBlock = false;
            trueBlock = NULL;
            falseBlock = NULL;
            nextBlock = NULL;
            hasInlineAssembly = false;
        }
        
        std::string getBlockId(){
            return blockId;
        }
        void setBlockId(std::string blockID){
            blockId = blockID;
        }
        void setInlineAssembly(){
            hasInlineAssembly = true;
        }
        bool getInlineAssemblyStatus(){
            return hasInlineAssembly;
        }

        AugmentedBasicBlock *getNextBlock(){
            return nextBlock;
        }
        void setNextBlock(AugmentedBasicBlock *nextB){
            nextBlock = nextB;
        }

        std::vector<StringRef> getInstructions(){
            return instructions;
        }
        void addInstruction(StringRef instruction){
            instructions.push_back(instruction);
        }
        std::vector<StringRef> getFunctions(){
            return functions;
        }
        void addFunction(StringRef functionName){
            functions.push_back(functionName);
        }
        std::vector<std::string> getParents(){
            return parents;
        }
        void addParent(std::string parent){
            parents.push_back(parent);
        }
    };

    static std::string getSimpleNodeLabel(const BasicBlock &Node)
    { // Copied from Github
        if (!Node.getName().empty())
            return Node.getName().str();

        std::string Str;
        raw_string_ostream OS(Str);

        Node.printAsOperand(OS, false);
        return OS.str();
    }

    static std::string getSimpleNodeLabel(const BasicBlock *Node)
    { // Pointer Version
        if (!Node->getName().empty())
            return Node->getName().str();

        std::string Str;
        raw_string_ostream OS(Str);

        Node->printAsOperand(OS, false);
        return OS.str();
    }

    static void parseCallInstruction(CallInst *call){
        assert(call != NULL);
        int numOperands = call->getNumOperands();
        for(int i=0;i<numOperands-1;i++){
            Value *operand = call->getArgOperand(i);
            operand->print(errs(), false);
            errs()<<"\n";
        }
    }

    static void parseBinaryBranchInstruction(BranchInst *branch){

    }

    struct BasicBlockExtractionPass : public ModulePass
    {
        static char ID;
        BasicBlockExtractionPass() : ModulePass(ID){};

        virtual bool runOnModule(Module &M)
        {
            errs() << "In a Module called " << M.getName() << "\n";
            for (Module::iterator functionIt = M.begin(), endFunctionIt = M.end(); functionIt != endFunctionIt; ++functionIt)
            {
                const Function &currentFunction = *functionIt;
                // currentFunction.viewCFG();
                errs() << "Got Function: " << currentFunction.getName() << "\n";
                if(currentFunction.getBasicBlockList().size() == 0){
                    errs()<< "INFO: "<< currentFunction.getName() <<" has no element in its basic block list. May be a libc function.\n";
                    continue;
                }
                for (auto &basicBlock : currentFunction)
                {
                    const BasicBlock *rootBlock = NULL;  
                    const BasicBlock *predecessor = NULL;
                    std::vector<BasicBlock *> predecessorNodes; // Vector copies object. So pointers are the way to go.

                    bool isRootBlock = false; // Boolean variables to track parent child relationships
                    bool hasUniquePredecessor = false;
                    bool hasMultiplePredecessors = false;

                    if (basicBlock.hasNPredecessors(1))
                    {
                        // errs() << "Found a block with a unique predecessor block.\n";
                        predecessor = basicBlock.getUniquePredecessor();
                        hasUniquePredecessor = true;
                    }
                    else if (basicBlock.hasNPredecessorsOrMore(2)){
                        // errs() << "Found a block with multiple predecessor blocks.\n";
                        BasicBlock *pointerToCurrentBlock = const_cast<BasicBlock *>(&basicBlock); //This is BAD. Do not try this in production code 
                        if(pointerToCurrentBlock != NULL){
                            for( BasicBlock *predecessor: predecessors(pointerToCurrentBlock) ){
                                predecessorNodes.push_back(predecessor);    
                            }
                            hasMultiplePredecessors = true;
                        }
                        else{
                            errs()<<"ERROR: The const to non-const conversion may have gone wrong.\n";
                            continue;
                        }
                    }
                    else{
                        // errs()<< "Found the starting block of the function.\n";
                        rootBlock = const_cast<BasicBlock *>(&basicBlock); // BAD CODE, do not try this in production
                        isRootBlock = true;
                    }
        
                    if (hasUniquePredecessor)
                    {
                        if(predecessor != NULL){
                            errs() << "Found Basic Block With Single Predecessor: " << getSimpleNodeLabel(basicBlock) << "<--" << getSimpleNodeLabel(predecessor) << "\n";
                        }
                        else{
                            errs()<<"ERROR: Unique Predecessor is NULL while hasUniquePredecessor is set to true.\n";
                        }
                    }
                    else if(hasMultiplePredecessors)
                    {
                        errs() << "Found Basic Block with Multiple Predecessors: " << getSimpleNodeLabel(basicBlock) << "<-";
                        for(BasicBlock *bb: predecessorNodes){
                            errs()<< getSimpleNodeLabel(bb)<<" ";
                        }
                        errs()<<"\n";
                    }
                    else if(isRootBlock){
                        // errs()<< "Found the root Block: "<<getSimpleNodeLabel(rootBlock)<<"\n";
                    }
                    else{
                        errs()<<"ERROR: Not a root block, unique predecessor or multi predecessor block.\n";
                    }

                    for (auto &instruction : basicBlock)
                    {
                        if(isa<CallInst>(instruction)){
                            Instruction *inst = const_cast<Instruction *>(&instruction);
                            CallInst *call = dyn_cast<CallInst>(inst);
                            errs()<<"*************** Call Instruction found **************\n";
                            instruction.print(errs(), false);
                            errs()<<"\n";
                            if(call->isInlineAsm()){
                                errs()<<"Its an inline assembly instruction"<<"\n";
                                parseCallInstruction(call);                               
                            }




                            errs()<<"*************** Call Instruction Ends **************\n";


                        }
                        else if(isa<BranchInst>(instruction)){
                            // errs()<<"Found a branch instruction: ";
                            // Instruction *inst =  const_cast<Instruction *>(&instruction); // casting shenanigans 
                            // BranchInst *brInst = dyn_cast<BranchInst>(inst); // Oh God, why ?????
                            // if(brInst->isConditional()){
                            //     errs()<<"Conditional :";
                            //     instruction.print(errs(), false);
                            //     errs()<<"\n\n";
                            //     errs()<<"operand 0: ";    
                            //     Value *op0 = brInst->getOperand(0);
                            //     op0->print(errs(), false);
                            //     errs()<<"\n";
                            //     errs()<<"operand 1: ";
                            //     Value *op1 = brInst->getSuccessor(0);                                
                            //     op1->print(errs(), false);
                            //     errs()<<"\n";
                            //     errs()<<"operand 2: ";
                            //     Value *op2 = brInst->getSuccessor(1);                                
                            //     op2->print(errs(), false);
                            //     errs()<<"\nConditional Block ends.\n";
                            // }
                            // else if(brInst->isUnconditional()){
                            //     errs()<<"Unconditional :";
                            //     instruction.print(errs(), false);
                            //     errs()<<"\n\n";
                            // }
                        }
                        else if(isa<SwitchInst>(instruction)){
                            // errs()<<"Found a switch instruction: ";
                            // instruction.print(errs(), false);
                            // errs()<<"\n\n";
                        }
                    }
                }
            }
            return false;
        }        
    };
}


char BasicBlockExtractionPass::ID = 0;

static RegisterPass<BasicBlockExtractionPass> X("basic-block-extract", "Pass to extract basic blocks from function definitons");

static void registerBasicBlockExtractionPass(const PassManagerBuilder &, legacy::PassManagerBase &PM)
{
    PM.add(new BasicBlockExtractionPass());
}

static RegisterStandardPasses RegisterCustomBasicBlockPass(PassManagerBuilder::EP_EarlyAsPossible, registerBasicBlockExtractionPass);