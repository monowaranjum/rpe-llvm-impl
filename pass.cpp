// STL dependencies
#include <algorithm>
#include <vector>
#include <map>
#include <stack>
#include <list>
#include <utility>
#include <string>
#include <regex>
#include <iterator>
// LLVM dependencies
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
#include "llvm/Analysis/DDG.h"
#include "llvm/Analysis/DDGPrinter.h"
#include "llvm/IR/Constants.h"

// JSON dependencies
#include <jsoncpp/json/json.h>

// GraphViz dependencies
#include <graphviz/gvc.h>
// This dependency is not working at the moment. Lib file not found.
// [TODO: Fix GraphViz dependency issue. ]

// Boost dependencies
#include <boost/algorithm/string.hpp>

using namespace llvm;
using namespace std;

namespace
{
    vector<string> loopingBlocks;
    map<string, int> visited;
    vector<list<string>> paths;

    map<string, string> typeMap;
    map<string, vector< pair<string, string> >> adjListForDDG;

    map<string, pair<string, int> > relevantFunctions;

    map<string, vector<ProvenanceNode *>> provenanceAdjList;

    enum State
    {
        WHITE,
        GRAY,
        BLACK
    };

    class ProvenanceNode{
        public:
            string action;
            string artifact;
            string id;
            ProvenanceNode(){}
            ProvenanceNode(string act, string art, string i){
                action = act;
                artifact = art;
                id = i;
            }            
    };

    class AugmentedBasicBlock
    {
    private:
        string blockId;              // Unique Block Id
        bool isRootBlock;            // Defines if this is the starting block of the function.
        bool isConditionalBlock;     // Does it have branching at the end or just a straight jump to next block
        bool hasInlineAssembly;      // Is there any inline assembly instruction? Then parse separately
        string trueBlock;            // If branched, then next true block
        string falseBlock;           // If branched, then next false block
        string nextBlock;            // If not branched, then next block
        vector<Instruction *> instructions; // All the call instructions are stored here (operation and arguments)
        vector<StringRef> functions; // All the functions are stored here (Name only)
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

        vector<Instruction *> getInstructions()
        {
            return instructions;
        }
        void addInstruction(Instruction *instruction)
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
    { // Copied from Stack Overflow
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
        {
            return Node->getName().str();
        }
        string Str;
        raw_string_ostream OS(Str);

        Node->printAsOperand(OS, false);
        return OS.str();
    }

    static string getStringRepresentationOfValue(Value *value)
    {
        string s;
        raw_string_ostream OS(s);
        value->printAsOperand(OS, false);
        return OS.str();
    }

    static string getTypeFromAddress(Type *type)
    {
        string s;
        raw_string_ostream OS(s);
        type->print(OS, false);
        return OS.str();
    }

    static string getInstructionString(Instruction *inst)
    {
        string s;
        raw_string_ostream ss(s);
        ss << *inst;
        return ss.str();
    }

    static void parseInlineAssemblyString(string instructionString, CallInst *call)
    {

        // errs() << "\n\n";
        regex pattern("\"([^\"]*)\"");
        sregex_iterator start(instructionString.begin(), instructionString.end(), pattern);
        sregex_iterator end;
        for (sregex_iterator current = start; current != end; ++current)
        {
            smatch match = *current;
            // errs() << match.str() << "\n";
        }
        // errs() << "Parsing complete.\n";

        assert(call != NULL);
        int numOperands = call->getNumOperands();
        for (int i = 0; i < numOperands - 1; i++)
        {
            Value *operand = call->getArgOperand(i);
            // operand->print(errs(), false);
            // errs() << "\n";
        }
    }

    static string getLeftHandSide(Instruction *inst)
    {
        // Untested Functionality
        string Str;
        raw_string_ostream OS(Str);

        inst->print(OS, false);
        string instString = OS.str();
        size_t foundAt = instString.find('=');
        string returnValue;
        if (foundAt != string::npos)
        {
            returnValue = instString.substr(0, foundAt);
            boost::trim(returnValue);
        }
        return returnValue;
    }

    static string getRightHandSide(Instruction *inst)
    {
        string Str;
        raw_string_ostream OS(Str);

        inst->print(OS, false);
        string instString = OS.str();
        size_t foundAt = instString.find('=');
        string returnValue;
        int len = instString.length();
        if (foundAt != string::npos)
        {
            returnValue = instString.substr(foundAt + 1);
            boost::trim(returnValue);
        }
        return returnValue;
    }

    static void writeDDGToFile(string fileName){
        error_code ec;
        raw_fd_ostream output(fileName, ec);

        for(auto it = adjListForDDG.begin() ; it != adjListForDDG.end(); it++ ){
            string source = it->first;
            vector<pair<string, string>> adjList = it->second;

            for(pair<string, string> elem: adjList){
                output<<source<<","<<typeMap[source]<<","<<elem.first<<","<<typeMap[elem.first]<<","<<elem.second<<"\n";
            }
        }       
        output.close();
    }

    static int drawDDG(string graphName)
    {
        // This function needs libgraphviz but unformtunately I can not link it at the moment. The headers are there. But the lib files are not. I am not even sure what is the issue here. Will come back to the problem later.

        Agraph_t *ddg;
        ddg = agopen(const_cast<char *>(graphName.c_str()), Agdirected, NULL);

        Agnode_t *source, *dest;
        Agedge_t *link;
        Agsym_t *a;
        GVC_t *gvc;

        gvc = gvContext();
        char *layoutArgs[1];
        layoutArgs[0] = (char *)malloc(20 * sizeof(char));
        strcpy(layoutArgs[0], "dot");
        gvParseArgs(gvc, 1, layoutArgs);

        source = agnode(ddg, "source", 1);
        dest = agnode(ddg, "dest", 1);
        link = agedge(ddg, source, dest, "trunc", 1);

        agsafeset(source, "color", "red", "");

        gvLayoutJobs(gvc, ddg);
        gvRenderJobs(gvc, ddg);

        gvFreeLayout(gvc, ddg);
        agclose(ddg);

        return gvFreeContext(gvc);
    }

    static void addEdgeDDG(string source, string dest, string label )
    {
        if(source == "<badref>" || dest =="<badref>"){
            errs()<<"Badref found. Exiting without adding the edges.\n";
            return;
        }
        if (adjListForDDG.find(source) != adjListForDDG.end())
        {
            adjListForDDG[source].push_back(make_pair(dest, label));
        }
        else
        {
            vector< pair<string, string> > children;
            children.push_back(make_pair(dest, label));
            adjListForDDG[source] = children;
        }
    }

    static void parseInstructionForDDG(Instruction &inst)
    {
        if (isa<AllocaInst>(inst))
        {
            string allocationLocation = getLeftHandSide(&inst);
            AllocaInst *allocInst = dyn_cast<AllocaInst>(&inst);
            string typeInfo = getTypeFromAddress(allocInst->getAllocatedType());
            typeMap[allocationLocation] = typeInfo;
        }
        else if (isa<StoreInst>(inst))
        {
            StoreInst *storeInst = dyn_cast<StoreInst>(&inst);

            Value *storingElement = storeInst->getOperand(0);
            string storingElementName = getStringRepresentationOfValue(storingElement);
            string storingElementType = getTypeFromAddress(storingElement->getType());
            typeMap[storingElementName] = storingElementType;

            Value *storeLocation = storeInst->getPointerOperand();
            string storeLocationName = getStringRepresentationOfValue(storeLocation);
            string storeLocationType = getTypeFromAddress(storeLocation->getType());
            typeMap[storeLocationName] = storeLocationType;

            addEdgeDDG(storingElementName, storeLocationName, "store");

            // errs()<<"Found Store Instruction.\n";
            // errs()<<"Is return is :"<<storeInst->willReturn()<<"\n";
            // errs()<<"Operand 0: "<<getStringRepresentationOfValue(storingElement)<<" Type: "<<storingElementType<<"\n";
            // errs()<<"Operand 1: "<<getStringRepresentationOfValue(storeLocation)<<" Type: "<<storeLocationType<<"\n";
        }
        else if (isa<LoadInst>(inst))
        {
            LoadInst *loadInst = dyn_cast<LoadInst>(&inst);

            Value *loadingTo = dyn_cast<Value>(&inst);
            string loadingToName = getStringRepresentationOfValue(loadingTo);
            string loadingToType = getTypeFromAddress(loadingTo->getType());
            typeMap[loadingToName] = loadingToType;

            Value *loadingFrom = loadInst->getPointerOperand();
            string loadingFromName = getStringRepresentationOfValue(loadingFrom);
            string loadingFromType = getTypeFromAddress(loadingFrom->getType());
            typeMap[loadingFromName] = loadingFromType;

            addEdgeDDG(loadingFromName, loadingToName, "load");

            // errs()<<"Found load instruction\n";
            // errs()<<"Will return is: "<<loadInst->willReturn()<<"\n";
            // errs()<<"Loading to: "<<loadingToName<<" of Type: "<<loadingToType<<" ";
            // errs()<<"From "<<loadingFromName<<" of Type: "<<loadingFromType<<"\n";
        }
        else if (isa<CallInst>(inst))
        {
            CallInst *callInst = dyn_cast<CallInst>(&inst);
            if (callInst->isInlineAsm())
            {
                // We still need the return address and the operand List
                // This is actually a very rare case in user-space program
            }
            else
            {
                // This is the usual case
                // We need the function name, function's return value
                // And operand list
                string functionName = callInst->getCalledFunction()->getName().str();

                Value *returnPoint = dyn_cast<Value>(&inst);
                string returnPointName = getStringRepresentationOfValue(returnPoint);
                string returnPointType = getTypeFromAddress(returnPoint->getType());
                typeMap[returnPointName] = returnPointType;

                // errs() << "Function " << functionName << " will return to " << returnPointName << " with type " << returnPointType << "\n";

                int numOperands = callInst->getNumOperands();
                for (int i = 0; i < numOperands - 1; i++)
                {
                    Value *argument = callInst->getArgOperand(i);
                    string argumentName = getStringRepresentationOfValue(argument);
                    string argumentType = getTypeFromAddress(argument->getType());
                    typeMap[argumentName] = argumentType;
                    string label = "call:";
                    label = label.append(functionName);
                    addEdgeDDG(argumentName, returnPointName, label);
                    // errs() << "Argument Number: " << i << " Value: " << argumentName << " Type: " << argumentType << "\n";
                }
                // errs() << "\n";
            }
        }
        else if (isa<GetElementPtrInst>(inst))
        {
            Value *argument = dyn_cast<Value>(&inst);
            string returnPointName = getStringRepresentationOfValue(argument);
            string returnPointType = getTypeFromAddress(argument->getType());
            typeMap[returnPointName] = returnPointType;

            // errs() << "GetelementPointer will return to " << returnPointName << " with type " << returnPointType << "\n";

            GetElementPtrInst *gepInst = dyn_cast<GetElementPtrInst>(&inst);
            int numOperands = gepInst->getNumOperands();
            for (int i = 0; i < numOperands; i++)
            {
                Value *operand = gepInst->getOperand(i);
                string operandName = getStringRepresentationOfValue(operand);
                string operandType = getTypeFromAddress(operand->getType());
                typeMap[operandName] = operandType;
                addEdgeDDG(operandName, returnPointName, "getelementptr");
                // errs() << "Operand " << i << " Operand Name: " << operandName << " Operand Type: " << operandType << "\n";
            }
            // errs() << "\n";
        }
        else if (isa<ReturnInst>(inst))
        {
            // [TODO: Figure out what to do with return type ]
        }
        else if (isa<TruncInst>(&inst))
        {
            Value *val = dyn_cast<Value>(&inst);
            string returnPointName = getStringRepresentationOfValue(val);
            string returnPointType = getTypeFromAddress(val->getType());
            typeMap[returnPointName] = returnPointType;
            // errs() << "Truncation will return to " << returnPointName << " with type " << returnPointType << "\n";

            Value *argument = inst.getOperand(0);
            string truncationArgument = getStringRepresentationOfValue(argument);
            string truncationArgumentType = getTypeFromAddress(argument->getType());
            typeMap[truncationArgument] = truncationArgumentType;

            addEdgeDDG(truncationArgument, returnPointName, "truncate");

            // errs() << "Operand Name: " << truncationArgument << " Operand Type: " << truncationArgumentType << "\n\n";
        }
        else if (isa<BranchInst>(&inst))
        {
            // [TODO: BranchInstuction is about control flow transfer. We do not need that for DDG.]
        }
        else
        {
            // [TODO: Add more instruction type + Analyze which ones are needed for our use case.]
            Value *val = dyn_cast<Value>(&inst);
            string returnPointName = getStringRepresentationOfValue(val);
            string returnPointType = getTypeFromAddress(val->getType());
            typeMap[returnPointName] = returnPointType;

            // errs()<<"Instruction Name: "<<getTypeFromAddress(inst.getType()) <<" Return Point :"<<returnPointName<<" Return Type: "<<returnPointType<<"\n";

            int numOperands = inst.getNumOperands();
            for (int i = 0; i < numOperands; i++)
            {
                Value *operand = inst.getOperand(i);
                string operandName = getStringRepresentationOfValue(operand);
                string operandType = getTypeFromAddress(operand->getType());
                typeMap[operandName] = operandType;
                
                addEdgeDDG(operandName, returnPointName, "NYI"); 
                // errs()<<"Operand "<<i<<": Name: "<<operandName<<" Type: "<<operandType<<"\n";
            }
            // errs()<<"\n";
        }
    }

    static void loadRelevantFunction(){
        relevantFunctions["open"] = make_pair("FILE",-1);
        relevantFunctions["read"] = make_pair("FILE",0);
        relevantFunctions["write"] = make_pair("FILE",0);
        relevantFunctions["close"] = make_pair("FILE",0);
        relevantFunctions["fopen"] = make_pair("FILE",-1);
        relevantFunctions["fread"] = make_pair("FILE",0);
        relevantFunctions["fwrite"] = make_pair("FILE",0);
        relevantFunctions["fclose"] = make_pair("FILE",0);
    }

    static void parseCallInstruction(CallInst *call, Instruction *inst, AugmentedBasicBlock *currBlock)
    {
        if (call->isInlineAsm())
        {
            parseInlineAssemblyString(getInstructionString(inst), call);
            currBlock->setInlineAssembly();
            currBlock->addInstruction(inst);
        }
        else
        {

            currBlock->addInstruction(inst);
            Function *function = call->getCalledFunction();
            if (function != NULL)
            {
                currBlock->addFunction(function->getName());
                errs() << "Current Function: " << function->getName() << "\n";

                int numOperands = call->getNumOperands();
                // errs() << "Number of operands: " << numOperands << "\n";
                for (int i = 0; i < numOperands - 1; i++)
                {
                    Value *operand = call->getArgOperand(i);
                    operand->print(errs(), false);
                    // errs() << "\nOperand Type is: " << getTypeFromAddress(operand->getType()) << "\n";
                }
                // errs() << "Returns to: " << getLeftHandSide(inst) << "\n";
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

    static bool loopDfsUtil(map<string, vector<string>> adjList, string node)
    {
        // errs()<<"Called with node: "<<node<<"\n";
        visited[node] = GRAY;
        vector<string> children = adjList[node];
        bool res = false;
        for (string child : children)
        {
            if (visited[child] == GRAY)
            {
                // errs()<<"Loop detected\n";
                loopingBlocks.push_back(child);
                res = true;
            }
            if (visited[child] == WHITE && loopDfsUtil(adjList, child))
            {
                res = true;
            }
        }
        visited[node] = BLACK;
        return res;
    }

    static pair<bool, vector<string>> containsLoop(map<string, vector<string>> adjList, string root)
    {

        loopingBlocks.clear();
        visited.clear();

        bool hasLoop = false;
        for (auto key : adjList)
        {
            visited[key.first] = WHITE;
        }

        hasLoop = loopDfsUtil(adjList, root);

        return make_pair(hasLoop, loopingBlocks);
    }

    static void monolithicTraverse(map<string, vector<string>> adjList, string node, list<string> currentPath)
    {
        currentPath.push_back(node);
        vector<string> children = adjList[node];
        if (children.empty())
        {
            // This is a leaf node.
            paths.push_back(currentPath);
        }
        else
        {
            for (string child : children)
            {
                list<string> currPathClone(currentPath);
                monolithicTraverse(adjList, child, currPathClone);
            }
        }
    }

    static void loopAwareTraverse(map<string, vector<string>> adjList, map<string, AugmentedBasicBlock> acfgNodes, string node, list<string> currentPath)
    {
        // If loop exists we have to handle it differently
        errs() << "Loop aware traversal called for node: " << node << "\n";
        currentPath.push_back(node);
        AugmentedBasicBlock acfgNode = acfgNodes[node];
        if (acfgNode.getConditionalBlock())
        { // Find if this is a conditional block.
            if (!loopingBlocks.empty() && find(loopingBlocks.begin(), loopingBlocks.end(), node) != loopingBlocks.end())
            {
                // We are at a node that contains a looping block.
                // Isolating the true block and going to the false block only.
                errs() << "Found a looping block: " << node << "\n";
                string trueNode = acfgNode.getTrueBlock();
                string falseNode = acfgNode.getFalseBlock();
                // Clone the current path and call on the false node only.
                list<string> currentPathClone(currentPath);
                loopAwareTraverse(adjList, acfgNodes, falseNode, currentPathClone);
            }
            else
            {
                // We are at a node thats a branched node, but no loops
                vector<string> children = adjList[node];
                if (children.empty())
                {
                    paths.push_back(currentPath);
                }
                else
                {
                    for (string child : children)
                    {
                        list<string> currentPathClone(currentPath);
                        loopAwareTraverse(adjList, acfgNodes, child, currentPathClone);
                    }
                }
            }
        }
        else
        {
            // Not a conditional block. Straight to next children block
            vector<string> children = adjList[node];
            if (children.empty())
            {
                paths.push_back(currentPath);
            }
            else
            {
                for (string child : children)
                {
                    list<string> currentPathClone(currentPath);
                    loopAwareTraverse(adjList, acfgNodes, child, currentPathClone);
                }
            }
        }
    }

    static void printAdjacencyList(map<string, vector<string>> adjacencyList)
    {
        errs() << "Adjacency List Is:\n";
        for (auto key : adjacencyList)
        {
            errs() << key.first << " -> ";
            for (auto elem : key.second)
            {
                errs() << elem << ", ";
            }
            errs() << "\n";
        }
    }

    static void printPaths()
    {
        int pathNum = 0;
        for (list<string> path : paths)
        {
            errs() << "Path Number: " << ++pathNum << "\nSTART -> ";
            for (string node : path)
            {
                errs() << node << " -> ";
            }
            errs() << "END\n";
        }
    }

    static bool checkLoadStoreSequenceBetweenNodesinDDG(string source, string dest){
        if(source == dest){
            return true;
        }
        if(adjListForDDG.find(source) == adjListForDDG.end()){
            return false;
        }

        vector<pair<string, string> > adjList = adjListForDDG[source];
        bool ret = false;
        for(pair<string, string> element : adjList){
            if(element.second == "store" || element.second == "load" || element.second == "truncate"){
                ret |= checkLoadStoreSequenceBetweenNodesinDDG(element.first, dest);
            }
        }
        return ret;        
    }

    static void printFunctionalPaths(map<string, AugmentedBasicBlock> acfgNodes)
    {
        loadRelevantFunction();
        int count = 0;
        for (list<string> path : paths)
        {
            errs() << "Path Number : " << ++count << "\n\n";
            // Get each block id and access the function vector from the acfgNodesMap
            for (string node : path)
            {
                if (node != "START" && node != "END")
                {
                    //errs() << "Functions in Block : " << node << "\n";
                    AugmentedBasicBlock abb = acfgNodes[node];
                    vector<Instruction *> instructionsInBlock = abb.getInstructions();
                    for (Instruction *inst : instructionsInBlock)
                    {
                        CallInst *call = dyn_cast<CallInst>(inst);
                        string funcName = call->getCalledFunction()->getName().str();
                        if(relevantFunctions.find(funcName) != relevantFunctions.end()){
                            Value *val = dyn_cast<Value>(inst);

                        }
                        else{
                            errs()<<"Function "<<funcName<<" Is not relevant.\n";
                        }
                    }
                    errs() << "\n";
                }
            }
            break;
        }
    }

    static map<string, vector<string>> buildAdjacencyList(vector<pair<string, string>> eList, map<string, AugmentedBasicBlock> acfgNodes, bool debug = false)
    {
        map<string, vector<string>> adjacencyList;

        for (auto it = begin(eList); it != end(eList); ++it)
        {
            pair<string, string> temp = *it;
            if (adjacencyList.find(temp.first) == adjacencyList.end())
            {
                vector<string> children;
                children.push_back(temp.second);
                adjacencyList[temp.first] = children;
                if (adjacencyList.find(temp.second) == adjacencyList.end())
                {
                    vector<string> emptyVector;
                    adjacencyList[temp.second] = emptyVector;
                }
            }
            else
            {
                vector<string> currChildren = adjacencyList[temp.first];
                currChildren.push_back(temp.second);
                adjacencyList[temp.first] = currChildren;
                if (adjacencyList.find(temp.second) == adjacencyList.end())
                {
                    vector<string> emptyVector;
                    adjacencyList[temp.second] = emptyVector;
                }
            }
        }

        if (debug)
        {
            printAdjacencyList(adjacencyList);
        }
        return adjacencyList;
    }

    static void extractPaths(vector<pair<string, string>> eList, map<string, AugmentedBasicBlock> acfgNodes, string rootId)
    {
        map<string, vector<string>> adjList = buildAdjacencyList(eList, acfgNodes, true);
        pair<bool, vector<string>> loopAnalysis = containsLoop(adjList, rootId);
        if (!loopAnalysis.first)
        {
            errs() << "No Loop Found. Initiating monolithic traversal.\n";
            paths.clear();
            list<string> initialEmptyPath;
            monolithicTraverse(adjList, rootId, initialEmptyPath);
        }
        else
        {
            errs() << "Loop found. Initiating loop aware traversal.\n";
            errs() << "Looping blocks are: ";
            for (auto elem : loopingBlocks)
            {
                errs() << elem << " ";
            }
            errs() << "\n";
            paths.clear();
            list<string> initialEmptyPath;
            loopAwareTraverse(adjList, acfgNodes, rootId, initialEmptyPath);
        }
        printPaths();
        errs() << "\n";
        printFunctionalPaths(acfgNodes);
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
                vector<pair<string, string>> edgeList;
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
                        parseInstructionForDDG(const_cast<Instruction &>(instruction));

                        if (isa<CallInst>(instruction))
                        {
                            Instruction *inst = const_cast<Instruction *>(&instruction);
                            CallInst *call = dyn_cast<CallInst>(inst);
                            parseCallInstruction(call, inst, &acfgNode);
                        }
                        else if (isa<BranchInst>(instruction))
                        {
                            Instruction *inst = const_cast<Instruction *>(&instruction);
                            BranchInst *brInst = dyn_cast<BranchInst>(inst);
                            parseBinaryBranchInstruction(brInst, &acfgNode);
                        }
                        else if (isa<SwitchInst>(instruction))
                        {
                            // [TODO]
                        }
                    }

                    idAcfgNode[acfgNode.getBlockId()] = acfgNode;
                }
                // drawDDG("Demo");
                // printEdgeList(edgeList);
                extractPaths(edgeList, idAcfgNode, rootBlockId);

                // bool test1 = checkLoadStoreSequenceBetweenNodesinDDG("%17","%20");
                // bool test2 = checkLoadStoreSequenceBetweenNodesinDDG("%17","%24");
                // bool test3 = checkLoadStoreSequenceBetweenNodesinDDG("%24", "%28");

                // errs()<<test1<<" "<<test2<<" "<<test3<<"\n";
                // writeDDGToFile("ddgedges.txt");
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