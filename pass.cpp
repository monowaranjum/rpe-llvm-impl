#include <iostream>
#include <vector>
#include <map>
#include <stack>
#include <list>
#include <utility>
#include <string>
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
using namespace std;

namespace
{
    vector< string > loopingBlocks;    
    map< string,int > visited;
    enum State {WHITE, GRAY, BLACK};

    class AugmentedBasicBlock
    {
    private:
        string blockId;                   // Unique Block Id
        bool isRootBlock;                      // Defines if this is the starting block of the function.
        bool isConditionalBlock;               // Does it have branching at the end or just a straight jump to next block
        bool hasInlineAssembly;                // Is there any inline assembly instruction? Then parse separately
        string trueBlock;                 // If branched, then next true block
        string falseBlock;                // If branched, then next false block
        string nextBlock;                 // If not branched, then next block
        vector<string> instructions; // All the call instructions are stored here (operation and arguments)
        vector<StringRef> functions;      // All the functions are stored here (Name only)
        vector<string> parents;      // Can keep track of the parent blocks if implementation wants
    public:
        AugmentedBasicBlock()
        {
            isConditionalBlock = false;
            hasInlineAssembly = false;
            isRootBlock = false;
        }

        string getBlockId()
        {
            return blockId;
        }
        void setBlockId(string blockID)
        {
            blockId = blockID;
        }

        void setRootBlock()
        {
            isRootBlock = true;
        }
        bool isARootBlock()
        {
            return isRootBlock;
        }
        void setInlineAssembly()
        {
            hasInlineAssembly = true;
        }
        bool getInlineAssemblyStatus()
        {
            return hasInlineAssembly;
        }
        void setConditionalBlock()
        {
            isConditionalBlock = true;
        }
        bool getConditionalBlock()
        {
            return isConditionalBlock;
        }
        string getNextBlock()
        {
            return nextBlock;
        }
        void setNextBlock(string nextB)
        {
            nextBlock = nextB;
        }
        string getTrueBlock()
        {
            return trueBlock;
        }
        void setTrueBlock(string trueB)
        {
            trueBlock = trueB;
        }
        string getFalseBlock()
        {
            return falseBlock;
        }
        void setFalseBlock(string falseB)
        {
            falseBlock = falseB;
        }

        vector<string> getInstructions()
        {
            return instructions;
        }
        void addInstruction(string instruction)
        {
            instructions.push_back(instruction);
        }
        vector<StringRef> getFunctions()
        {
            return functions;
        }
        void addFunction(StringRef functionName)
        {
            functions.push_back(functionName);
        }
        vector<string> getParents()
        {
            return parents;
        }
        void addParent(string parent)
        {
            parents.push_back(parent);
        }
    };

    static string getSimpleNodeLabel(const BasicBlock &Node)
    { // Copied from Github
        if (!Node.getName().empty())
            return Node.getName().str();

        string Str;
        raw_string_ostream OS(Str);

        Node.printAsOperand(OS, false);
        return OS.str();
    }

    static string getSimpleNodeLabel(const BasicBlock *Node)
    { // Pointer Version
        if (!Node->getName().empty())
            return Node->getName().str();

        string Str;
        raw_string_ostream OS(Str);

        Node->printAsOperand(OS, false);
        return OS.str();
    }

    static string getInstructionString(Instruction *inst)
    {
        string s;
        raw_string_ostream ss(s);
        ss << *inst;
        return ss.str();
    }

    static void parseCallInstruction(CallInst *call, Instruction *inst, AugmentedBasicBlock *currBlock)
    {
        // assert(call != NULL);
        // int numOperands = call->getNumOperands();
        // for(int i=0;i<numOperands-1;i++){
        //     Value *operand = call->getArgOperand(i);
        //     operand->print(errs(), false);
        //     errs()<<"\n";
        // }
        if (call->isInlineAsm())
        {
            currBlock->setInlineAssembly();
            currBlock->addInstruction(getInstructionString(inst));
        }
        else
        {
            currBlock->addInstruction(getInstructionString(inst));
            Function *function = call->getCalledFunction();
            if (function != NULL)
            {
                currBlock->addFunction(function->getName());
            }
            else
            {
                errs() << "ERROR: function from call instruction is null. Might be a function pointer.\n";
            }
        }
    }

    static void parseBinaryBranchInstruction(BranchInst *brInst, AugmentedBasicBlock *acfgNode)
    {
        if (brInst->isConditional())
        {
            acfgNode->setConditionalBlock();
            Value *op1 = brInst->getSuccessor(0);
            acfgNode->setTrueBlock(getSimpleNodeLabel(dyn_cast<BasicBlock>(op1)));
            Value *op2 = brInst->getSuccessor(1);
            acfgNode->setFalseBlock(getSimpleNodeLabel(dyn_cast<BasicBlock>(op2)));
        }
        else if (brInst->isUnconditional())
        {
            Value *op = brInst->getSuccessor(0);
            acfgNode->setNextBlock(getSimpleNodeLabel(dyn_cast<BasicBlock>(op)));
        }
    }

    static void parseSwitchInstruction(SwitchInst *switch_inst)
    {
        // [TODO]
    }

    static void printEdgeList(vector<pair<string, string>> eList)
    {
        for (pair<string, string> edge : eList)
        {
            errs() << edge.first << " -> " << edge.second << "\n";
        }
    }

    static bool dfsUtil(map<string, vector<string>> adjList, string node){
        // errs()<<"Called with node: "<<node<<"\n";
        visited[node] = GRAY;
        vector<string> children = adjList[node];
        bool res = false;
        for(string child: children){
            if(visited[child] == GRAY){
                // errs()<<"Loop detected\n";
                loopingBlocks.push_back(child);
                res = true;
            }
            if(visited[child] == WHITE && dfsUtil(adjList, child)){
                res = true;
            }
        }
        visited[node] = BLACK;
        return res;
    }

    static pair<bool,vector<string>> containsLoop(map<string, vector<string>> adjList, string root){

        loopingBlocks.clear();
        visited.clear();

        bool hasLoop = false;
        for(auto key:adjList){
            visited[key.first] = WHITE;
        }

        hasLoop = dfsUtil(adjList, root);        

        return make_pair(hasLoop, loopingBlocks);
    }

    static void traverse(map<string, vector<string>> adjList, string root){

    }

    static void printAdjacencyList(map<string, vector<string>> adjacencyList){
        errs()<<"Adjacency List Is:\n";
        for(auto key: adjacencyList){
            errs() << key.first <<" -> ";
            for(auto elem: key.second){
                errs()<<elem<<", ";
            }
            errs()<<"\n";
        }
    }

    static vector<list<string>> extractPaths(vector<pair<string, string>> eList, string rootId)
    {
        vector<list<string>> paths;
        map<string, vector<string>> adjacencyList; 
        for( auto it = begin(eList); it != end(eList); ++it ){
            pair<string, string> temp = *it;
            if(adjacencyList.find(temp.first) == adjacencyList.end() ){
                vector<string> children;
                children.push_back(temp.second);
                adjacencyList[temp.first] = children;
                if(adjacencyList.find(temp.second) == adjacencyList.end()){
                    vector<string> emptyVector;
                    adjacencyList[temp.second] = emptyVector;
                }
            }
            else{
                vector<string> currChildren = adjacencyList[temp.first];
                currChildren.push_back(temp.second);
                adjacencyList[temp.first] = currChildren;
                if(adjacencyList.find(temp.second) == adjacencyList.end()){
                    vector<string> emptyVector;
                    adjacencyList[temp.second] = emptyVector;
                }
            }
        }
        // Traverse the graph by DFS

        printAdjacencyList(adjacencyList);
        
        pair<bool, vector<string> > loopAnalysis = containsLoop(adjacencyList, rootId);
        errs()<<loopAnalysis.first<<"\n";
        for(auto elem: loopAnalysis.second){
            errs()<< elem << "\n";
        }
        // Traversal ends
        return paths;
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
                map<string, AugmentedBasicBlock> idAcfgNode;
                vector< pair<string, string> > edgeList;
                string rootBlockId;
                if (currentFunction.getBasicBlockList().size() == 0)
                {
                    continue;
                }
                currentFunction.viewCFG();
                for (auto &basicBlock : currentFunction)
                {
                    AugmentedBasicBlock acfgNode;

                    const BasicBlock *rootBlock = NULL;
                    const BasicBlock *predecessor = NULL;
                    vector<BasicBlock *> predecessorNodes;

                    bool isRootBlock = false;
                    bool hasUniquePredecessor = false;
                    bool hasMultiplePredecessors = false;

                    acfgNode.setBlockId(getSimpleNodeLabel(basicBlock));

                    if (basicBlock.hasNPredecessors(1))
                    {
                        predecessor = basicBlock.getUniquePredecessor();
                        hasUniquePredecessor = true;
                        string parentName = getSimpleNodeLabel(predecessor);
                        acfgNode.addParent(parentName);
                        edgeList.push_back(make_pair(parentName, acfgNode.getBlockId()));
                    }
                    else if (basicBlock.hasNPredecessorsOrMore(2))
                    {
                        BasicBlock *pointerToCurrentBlock = const_cast<BasicBlock *>(&basicBlock);
                        if (pointerToCurrentBlock != NULL)
                        {
                            for (BasicBlock *predecessor : predecessors(pointerToCurrentBlock))
                            {
                                string tempParent = getSimpleNodeLabel(predecessor);
                                acfgNode.addParent(tempParent);
                                predecessorNodes.push_back(predecessor);
                                edgeList.push_back(make_pair(tempParent, acfgNode.getBlockId()));
                            }
                            hasMultiplePredecessors = true;
                        }
                        else
                        {
                            errs() << "ERROR: The const to non-const conversion may have gone wrong.\n";
                            continue;
                        }
                    }
                    else
                    {
                        rootBlock = const_cast<BasicBlock *>(&basicBlock);
                        rootBlockId = getSimpleNodeLabel(rootBlock);
                        isRootBlock = true;
                        acfgNode.setRootBlock();
                    }

                    if (isRootBlock)
                    {
                        acfgNode.setRootBlock();
                    }

                    for (auto &instruction : basicBlock)
                    {
                        if (isa<CallInst>(instruction))
                        {
                            Instruction *inst = const_cast<Instruction *>(&instruction);
                            CallInst *call = dyn_cast<CallInst>(inst);
                            parseCallInstruction(call, inst, &acfgNode);
                        }
                        else if (isa<BranchInst>(instruction))
                        {
                            Instruction *inst = const_cast<Instruction *>(&instruction); // casting shenanigans
                            BranchInst *brInst = dyn_cast<BranchInst>(inst);             // Oh God, why ?????
                            parseBinaryBranchInstruction(brInst, &acfgNode);
                        }
                        else if (isa<SwitchInst>(instruction))
                        {
                            // [TODO]
                        }
                    }

                    idAcfgNode[acfgNode.getBlockId()] = acfgNode;
                }
                // printEdgeList(edgeList);
                extractPaths(edgeList, rootBlockId);
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