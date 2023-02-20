#include <iostream>
#include <vector>
#include <map>
#include <utility>
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
#include <jsoncpp/json/json.h>

using namespace llvm;

namespace
{

    class AugmentedBasicBlock{
    private:
        std::string blockId; // Unique Block Id
        bool isRootBlock; // Defines if this is the starting block of the function. 
        bool isConditionalBlock; // Does it have branching at the end or just a straight jump to next block
        bool hasInlineAssembly; // Is there any inline assembly instruction? Then parse separately
        std::string trueBlock;  // If branched, then next true block
        std::string falseBlock; // If branched, then next false block
        std::string nextBlock; // If not branched, then next block
        std::vector<std::string> instructions; // All the call instructions are stored here (operation and arguments)
        std::vector<StringRef> functions; // All the functions are stored here (Name only)
        std::vector<std::string> parents; // Can keep track of the parent blocks if implementation wants        
    public:

        AugmentedBasicBlock(){
            isConditionalBlock = false;
            hasInlineAssembly = false;
            isRootBlock = false;
        }
        
        std::string getBlockId(){
            return blockId;
        }
        void setBlockId(std::string blockID){
            blockId = blockID;
        }

        void setRootBlock(){
            isRootBlock = true;
        }
        bool isARootBlock(){
            return isRootBlock;
        }
        void setInlineAssembly(){
            hasInlineAssembly = true;
        }
        bool getInlineAssemblyStatus(){
            return hasInlineAssembly;
        }
        void setConditionalBlock(){
            isConditionalBlock = true;
        }
        bool getConditionalBlock(){
            return isConditionalBlock;
        }
        std::string getNextBlock(){
            return nextBlock;
        }
        void setNextBlock(std::string nextB){
            nextBlock = nextB;
        }
        std::string getTrueBlock(){
            return trueBlock;
        }
        void setTrueBlock(std::string trueB){
            trueBlock = trueB;
        }
        std::string getFalseBlock(){
            return falseBlock;
        }
        void setFalseBlock(std::string falseB){
            falseBlock = falseB;
        }

        std::vector<std::string> getInstructions(){
            return instructions;
        }
        void addInstruction(std::string instruction){
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


    static std::string getInstructionString(Instruction *inst){
        std::string s;
        raw_string_ostream ss(s);
        ss<<*inst;
        return ss.str();
    }

    static void parseCallInstruction(CallInst *call, Instruction *inst, AugmentedBasicBlock *currBlock){
        // assert(call != NULL);
        // int numOperands = call->getNumOperands();
        // for(int i=0;i<numOperands-1;i++){
        //     Value *operand = call->getArgOperand(i);
        //     operand->print(errs(), false);
        //     errs()<<"\n";
        // }
        if(call->isInlineAsm()){
            currBlock->setInlineAssembly();
            currBlock->addInstruction(getInstructionString(inst));           
        }
        else{
            currBlock->addInstruction(getInstructionString(inst));
            Function *function = call->getCalledFunction();
            if(function != NULL){
                currBlock->addFunction(function->getName());
            }
            else{
                errs()<<"ERROR: function from call instruction is null. Can be a function pointer.\n";
            }
        }
    }

    static void parseBinaryBranchInstruction(BranchInst *brInst, AugmentedBasicBlock *acfgNode){
        if(brInst->isConditional()){
            acfgNode->setConditionalBlock();
            Value *op1 = brInst->getSuccessor(0);                                
            acfgNode->setTrueBlock(getSimpleNodeLabel(dyn_cast<BasicBlock>(op1)));
            Value *op2 = brInst->getSuccessor(1);                                
            acfgNode->setFalseBlock(getSimpleNodeLabel(dyn_cast<BasicBlock>(op2)));
        }
        else if(brInst->isUnconditional()){
            Value *op = brInst->getSuccessor(0);
            acfgNode->setNextBlock(getSimpleNodeLabel(dyn_cast<BasicBlock>(op)));
        }
    }

    static void parseSwitchInstruction(SwitchInst *switch_inst){
        // [TODO]
    }

    
    
    struct BasicBlockExtractionPass : public ModulePass
    {
        static char ID;
        BasicBlockExtractionPass() : ModulePass(ID){};
        

        virtual bool runOnModule(Module &M)
        {
            for (Module::iterator functionIt = M.begin(), endFunctionIt = M.end(); functionIt != endFunctionIt; ++functionIt)
            {
                const Function &currentFunction = *functionIt;
                errs() << "Current Function: " << currentFunction.getName() << "\n";
                std::map<std::string, AugmentedBasicBlock> idAcfgNode;
                std::map<std::string, std::string> edgeList;
                
                if(currentFunction.getBasicBlockList().size() == 0){
                    continue;
                }
                // currentFunction.viewCFG();
                for (auto &basicBlock : currentFunction)
                {
                    AugmentedBasicBlock acfgNode; 

                    const BasicBlock *rootBlock = NULL;  
                    const BasicBlock *predecessor = NULL;
                    std::vector<BasicBlock *> predecessorNodes;

                    bool isRootBlock = false;
                    bool hasUniquePredecessor = false;
                    bool hasMultiplePredecessors = false;

                    
                    acfgNode.setBlockId(getSimpleNodeLabel(basicBlock)); 
                    
                    if (basicBlock.hasNPredecessors(1))
                    {
                        predecessor = basicBlock.getUniquePredecessor();
                        hasUniquePredecessor = true;
                        acfgNode.addParent(getSimpleNodeLabel(predecessor));
                    }
                    else if (basicBlock.hasNPredecessorsOrMore(2)){
                        BasicBlock *pointerToCurrentBlock = const_cast<BasicBlock *>(&basicBlock);
                        if(pointerToCurrentBlock != NULL){
                            for( BasicBlock *predecessor: predecessors(pointerToCurrentBlock) ){
                                acfgNode.addParent(getSimpleNodeLabel(predecessor));
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
                        rootBlock = const_cast<BasicBlock *>(&basicBlock);
                        isRootBlock = true;
                        acfgNode.setRootBlock();
                    }
        
                    if(isRootBlock){
                        acfgNode.setRootBlock();
                    }

                    for (auto &instruction : basicBlock)
                    {
                        if(isa<CallInst>(instruction)){
                            Instruction *inst = const_cast<Instruction *>(&instruction);
                            CallInst *call = dyn_cast<CallInst>(inst);
                            parseCallInstruction(call, inst, &acfgNode);                        
                        }
                        else if(isa<BranchInst>(instruction)){
                            Instruction *inst =  const_cast<Instruction *>(&instruction); // casting shenanigans
                            BranchInst *brInst = dyn_cast<BranchInst>(inst); // Oh God, why ?????
                            parseBinaryBranchInstruction(brInst, &acfgNode);
                        }
                        else if(isa<SwitchInst>(instruction)){
                            //TODO
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