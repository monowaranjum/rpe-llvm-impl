#include "utility.cpp"
#include "abb.cpp"

using namespace llvm;
using namespace std;

namespace
{
    vector<string> loopingBlocks;
    map<string, int> visited;
    vector<PATH> canonicalPaths;
    map<string, vector<PATH>> loopingPaths;
    vector<PATH> instantiatedPaths;

    map<string, string> typeMap;
    map<string, vector<EDGE>> adjListForDDG;
    map<string, pair<string, int>> relevantFunctions;
    
    set<string> loopAwareVisited;
    
    map<string, vector<ProvenanceNode *>> provenanceAdjList;
    map<string, EDGE> backEdges;
    
    GRAPH canonicalAdjList;
    GRAPH dagAdjList;
    
    map<string, string> constantValueFlowMap; // This is the key to static loop analysis

    static void writeDDGToFile(string fileName)
    {
        error_code ec;
        raw_fd_ostream output(fileName, ec);

        for (auto it = adjListForDDG.begin(); it != adjListForDDG.end(); it++)
        {
            string source = it->first;
            vector<pair<string, string>> adjList = it->second;

            for (pair<string, string> elem : adjList)
            {
                output << source << "," << typeMap[source] << "," << elem.first << "," << typeMap[elem.first] << "," << elem.second << "\n";
            }
        }
        output.close();
    }

    static void addEdgeDDG(string source, string dest, string label)
    {
        if (source == "<badref>" || dest == "<badref>")
        {
            errs() << "Badref found. Exiting without adding the edges.\n";
            return;
        }
        if (adjListForDDG.find(source) != adjListForDDG.end())
        {
            adjListForDDG[source].push_back(make_pair(dest, label));
        }
        else
        {
            vector<pair<string, string>> children;
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
        else if(isa<ICmpInst>(&inst)){
            Value *val = dyn_cast<Value>(&inst);
            string comparisonResult = getStringRepresentationOfValue(val);
            string comparisonResultType = getTypeFromAddress(val->getType());
            typeMap[comparisonResult] = comparisonResultType;

            Value *operand0 = inst.getOperand(0);
            Value *operand1 = inst.getOperand(1);

            string firstOperandName = getStringRepresentationOfValue(operand0);
            string firstOperandType = getTypeFromAddress(operand0->getType());
            typeMap[firstOperandName] = firstOperandType;

            string secondOperandName = getStringRepresentationOfValue(operand1);
            string seconndOperandType = getTypeFromAddress(operand1->getType());
            typeMap[secondOperandName] = seconndOperandType;

            ICmpInst *icmpInst = dyn_cast<ICmpInst>(&inst);
            string predicateName = icmpInst->getPredicateName(icmpInst->getPredicate()).str();

            addEdgeDDG(firstOperandName, comparisonResult, "icmp:0 "+predicateName);
            addEdgeDDG(secondOperandName, comparisonResult, "icmp:1 "+predicateName);
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

                addEdgeDDG(operandName, returnPointName, inst.getOpcodeName() );
            }
            // errs()<<"\n";
        }
    }

    static void loadRelevantFunction()
    {
        relevantFunctions["open"] = make_pair("FILE", -1);
        relevantFunctions["read"] = make_pair("FILE", 0);
        relevantFunctions["write"] = make_pair("FILE", 0);
        relevantFunctions["close"] = make_pair("FILE", 0);
        relevantFunctions["fopen"] = make_pair("FILE", -1);
        relevantFunctions["fread"] = make_pair("FILE", 0);
        relevantFunctions["fwrite"] = make_pair("FILE", 0);
        relevantFunctions["fclose"] = make_pair("FILE", 0);
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
                int numOperands = call->getNumOperands();
                for (int i = 0; i < numOperands - 1; i++)
                {
                    Value *operand = call->getArgOperand(i);
                }
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

    static bool loopDfsUtil(GRAPH adjList, string node)
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
                backEdges[node] = make_pair(node, child); // The looping block is the key. The backedge is the value.
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

    static pair<bool, vector<string>> containsLoop(GRAPH adjList, string root)
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

    static void monolithicTraverse(GRAPH adjList, string node, list<string> currentPath)
    {
        currentPath.push_back(node);
        vector<string> children = adjList[node];
        if (children.empty())
        {
            // This is a leaf node.
            canonicalPaths.push_back(currentPath);
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

    static void loopAwareTraverse(GRAPH adjList, map<string, AugmentedBasicBlock> acfgNodes, string node, list<string> currentPath)
    {
        // Check if it is a looping node and have been called already
        if (find(loopingBlocks.begin(), loopingBlocks.end(), node) != loopingBlocks.end())
        {
            if (find(loopAwareVisited.begin(), loopAwareVisited.end(), node) != loopAwareVisited.end())
            {
                return;
            }
        }

        currentPath.push_back(node);
        AugmentedBasicBlock acfgNode = acfgNodes[node];
        if (!loopingBlocks.empty() && find(loopingBlocks.begin(), loopingBlocks.end(), node) != loopingBlocks.end())
        {
            if (acfgNode.getConditionalBlock())
            {
                // Loop and Conditional. So either For loop or While Loop.
                string falseNode = acfgNode.getFalseBlock();
                list<string> clonedCurrentPath(currentPath);
                loopAwareVisited.insert(node);
                loopAwareTraverse(adjList, acfgNodes, falseNode, clonedCurrentPath);
            }
            else
            {
                // Loop and Unconditional. So do-while loop.
                string nextNode = acfgNode.getNextBlock();
                loopAwareVisited.insert(node);
                list<string> clonedCurrentPath(currentPath);
                loopAwareTraverse(adjList, acfgNodes, nextNode, clonedCurrentPath);
            }
        }
        else
        {
            // Not a conditional block. Straight to next children block
            vector<string> children = adjList[node];
            loopAwareVisited.insert(node);
            if (children.empty())
            {
                // Reached a leaf node. This is a complete path.
                canonicalPaths.push_back(currentPath);
            }
            else
            {
                for (string child : children)
                {
                    // Clone the existing path and pass it along for the next layer.
                    list<string> currentPathClone(currentPath);
                    loopAwareTraverse(adjList, acfgNodes, child, currentPathClone);
                }
            }
        }
    }

    static bool checkLoadStoreSequenceBetweenNodesinDDG(string source, string dest)
    {
        if (source == dest)
        {
            return true;
        }
        if (adjListForDDG.find(source) == adjListForDDG.end())
        {
            return false;
        }

        vector<pair<string, string>> adjList = adjListForDDG[source];
        bool ret = false;
        for (pair<string, string> element : adjList)
        {
            if (element.second == "store" || element.second == "load" || element.second == "truncate")
            {
                ret |= checkLoadStoreSequenceBetweenNodesinDDG(element.first, dest);
            }
        }
        return ret;
    }

    static void printProvenanceEdges()
    {
        vector<ProvenanceNode *> adjList = provenanceAdjList["process_name"];
        for (ProvenanceNode *node : adjList)
        {
            errs() << node->action << " " << node->artifact << " " << node->id << "\n";
        }
    }

    static void dumpProvenanceEdges(string fileName)
    {
        error_code ec;
        raw_fd_ostream output(fileName, ec);

        vector<ProvenanceNode *> adjList = provenanceAdjList["process_name"];
        for (ProvenanceNode *elem : adjList)
        {
            output << elem->action << "," << elem->artifact << "," << elem->id << "\n";
        }
        output.close();
    }

    static void generateProvenanceEdges(map<string, AugmentedBasicBlock> acfgNodes)
    {
        loadRelevantFunction();
        vector<ProvenanceNode *> edges;
        ProvenanceNode start("load", "FILE", "process_name_start");
        edges.push_back(&start);
        provenanceAdjList["process_name"] = edges;
        int count = 0;
        for (PATH path : canonicalPaths)
        {
            errs() << "Path Number : " << ++count << "\n\n";
            // Get each block id and access the function vector from the acfgNodesMap
            for (string node : path)
            {
                if (node != "START" && node != "END")
                {
                    // errs() << "Functions in Block : " << node << "\n";
                    AugmentedBasicBlock abb = acfgNodes[node];
                    vector<Instruction *> instructionsInBlock = abb.getInstructions();
                    for (Instruction *inst : instructionsInBlock)
                    {
                        CallInst *call = dyn_cast<CallInst>(inst);
                        string funcName = call->getCalledFunction()->getName().str();
                        if (relevantFunctions.find(funcName) != relevantFunctions.end())
                        {

                            pair<string, int> relevantInfo = relevantFunctions[funcName];
                            if (relevantInfo.second == -1)
                            {
                                Value *val = dyn_cast<Value>(inst);
                                string id = getStringRepresentationOfValue(val);
                                ProvenanceNode *node1 = new ProvenanceNode(funcName, relevantInfo.first, id);
                                provenanceAdjList["process_name"].push_back(node1);
                            }
                            else
                            {
                                Value *val = call->getArgOperand(relevantInfo.second);
                                string id = getStringRepresentationOfValue(val);
                                ProvenanceNode *node1 = new ProvenanceNode(funcName, relevantInfo.first, id);
                                provenanceAdjList["process_name"].push_back(node1);
                            }
                        }
                        else
                        {
                            errs() << "Function " << funcName << " Is not relevant.\n";
                        }
                    }
                }
            }
            ProvenanceNode *exitNode = new ProvenanceNode("exit", "PROCESS", "process_name_exit");
            provenanceAdjList["process_name"].push_back(exitNode);
            printProvenanceEdges();
            set<string> uniqueObjects;
            uniqueObjects.insert("process_name");
            vector<ProvenanceNode *> adjList = provenanceAdjList["process_name"];
            for (ProvenanceNode *elem : adjList)
            {
                string currId = elem->id;
                bool result = false;
                for (string uObj : uniqueObjects)
                {
                    result |= checkLoadStoreSequenceBetweenNodesinDDG(uObj, currId);
                    if (result)
                    {
                        elem->id = uObj;
                        break;
                    }
                }
                if (!result)
                {
                    uniqueObjects.insert(currId);
                }
            }

            printProvenanceEdges();
            dumpProvenanceEdges("prov_edges.txt");
            break; // This is temporary.
        }
    }

    static GRAPH buildAdjacencyList(vector<EDGE> eList, map<string, AugmentedBasicBlock> acfgNodes, bool debug = false)
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

    static GRAPH extractDirectedAdjList(GRAPH adjList, map<string, EDGE> bEdges)
    {
        map<string, vector<string>> directedAcgf;

        for (auto &elem : adjList)
        {
            if (bEdges.find(elem.first) != bEdges.end())
            {
                vector<string> clonedAdjList(elem.second);
                pair<string, string> edge = bEdges[elem.first];
                for (vector<string>::iterator it = clonedAdjList.begin(); it != clonedAdjList.end(); ++it)
                {
                    if (*it == edge.second)
                    {
                        clonedAdjList.erase(it);
                        break;
                    }
                }
                directedAcgf[elem.first] = clonedAdjList;
            }
            else
            {
                vector<string> clonedAdjList(elem.second);
                directedAcgf[elem.first] = clonedAdjList;
            }
        }
        return directedAcgf;
    }

    static void extractCanonicalPaths(vector<EDGE> eList, map<string, AugmentedBasicBlock> acfgNodes, string rootId)
    {
        GRAPH adjList = buildAdjacencyList(eList, acfgNodes, true);
        pair<bool, vector<string>> loopAnalysis = containsLoop(adjList, rootId);
        canonicalPaths.clear();
        list<string> initialEmptyPath;
        if (!loopAnalysis.first)
        {
            errs() << "No Loop Found. Initiating monolithic traversal.\n";
            monolithicTraverse(adjList, rootId, initialEmptyPath);
        }
        else
        {
            errs() << "Loop found. Initiating loop aware traversal.\n";
            printLoopingBlocks(loopingBlocks);
            printBackEdges(backEdges);
            loopAwareTraverse(adjList, acfgNodes, rootId, initialEmptyPath);
        }
        printPaths(canonicalPaths);
        canonicalAdjList = adjList;
        dagAdjList = extractDirectedAdjList(canonicalAdjList, backEdges);
        errs() << "******************** directed adjlist ****************\n";
        printAdjacencyList(dagAdjList);
        errs() << "\n\n";
        // generateProvenanceEdges(acfgNodes);
    }

    static void dagDfsUtil(GRAPH dagGraph, string anchor ,string src, string dst, PATH currentPath){
        currentPath.push_back(src);
        if(src == dst){
            // Enter this in the loops possible execution path. 
            if(loopingPaths.find(anchor) == loopingPaths.end()){
                vector<PATH> tempPaths;
                tempPaths.push_back(currentPath);
                loopingPaths[anchor] = tempPaths;
            }
            else{
                loopingPaths[anchor].push_back(currentPath);
            }
            return;
        }

        EDGE_LIST edge_list = dagGraph[src];
        for(string child: edge_list){
            PATH clonedCurrentPath(currentPath);
            dagDfsUtil(dagGraph, anchor, child, dst, clonedCurrentPath);
        }
    }

    static void extractLoopingPaths(GRAPH dagGraph){
        for(auto &elem: backEdges){
            EDGE edge = elem.second;
            PATH curr;
            dagDfsUtil(dagGraph, edge.second ,edge.second, edge.first, curr);
        }
        printLoopExecutionPaths(loopingPaths);
    }

    static vector<PATH> expandPath(PATH p){
        
        vector<PATH> expandedPaths;
        PATH initializer;
        expandedPaths.push_back(initializer);
        // errs()<<"Called ExpandPath for: ";
        // printPath(p);
        // errs()<<"\n";
        for(string n:p){
            if(find(loopingBlocks.begin(), loopingBlocks.end(), n) == loopingBlocks.end()){
                // Not a looping block.
                // errs()<<"Not a looping block: "<<n<<"\n";
                for(PATH &tempPath: expandedPaths){
                    // errs()<<"Pushing back "<<n<<"\n";
                    tempPath.push_back(n);
                    // printPath(tempPath);
                }
                // printPaths(expandedPaths);
            }
            else if(n!= "LOOP_START" && n!= "LOOP_END"){
                // errs()<<"Looping Block."<<n<<"\n";
                for(PATH &tempPath: expandedPaths){
                    tempPath.push_back("LOOP_START");
                    tempPath.push_back(n);
                    // printPath(tempPath);
                }
                
                vector<PATH> candidatePaths = loopingPaths[n];
                vector<PATH> innerExpandedPaths;
                for(PATH &cPath: candidatePaths){
                    PATH temp(cPath);
                    temp.erase(temp.begin());
                    if(temp.empty()){
                        continue;
                    }
                    vector<PATH> tempInnerPaths = expandPath(temp);
                    innerExpandedPaths.insert(innerExpandedPaths.end(), tempInnerPaths.begin(), tempInnerPaths.end()) ;
                    // append every path in innerexapndedpaths (n) to every path in the current expanded paths (m). 
                    // So the new expanded paths will have m*n paths
                }
                vector<PATH> tempHolder;
                for(PATH &tempPath: expandedPaths){
                    for(PATH &x: innerExpandedPaths){
                        PATH clonedTempPath(tempPath);
                        clonedTempPath.insert(clonedTempPath.end(), x.begin(), x.end());
                        tempHolder.push_back(clonedTempPath);
                    }
                }

                expandedPaths.clear();
                for(PATH &x:tempHolder){
                    expandedPaths.push_back(x);
                }

                for(PATH &tempPath: expandedPaths){
                    tempPath.push_back("LOOP_END");
                }
            }
        }
        return expandedPaths;
    }

    /**
     * We take the Canonical Paths here and Expand It Using the looping block paths. 
     * Then We push the extended path in a stack.
     * And then Instantiate it by naively executing the loops by sampling them.
    */
    static void generatePathsFromCanonicalPaths(){
        for(PATH p:canonicalPaths){
            vector<PATH> extractedPaths = expandPath(p);
            errs()<<"\n\n";
            printPaths(extractedPaths);
        }    
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
                printEdgeList(edgeList);
                extractCanonicalPaths(edgeList, idAcfgNode, rootBlockId);
                extractLoopingPaths(dagAdjList);
                generatePathsFromCanonicalPaths();        
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
// char LoopInformationExtractionPass::ID = 1;

static RegisterPass<BasicBlockExtractionPass> X("basic-block-extract", "Pass to extract basic blocks from function definitons");
// static RegisterPass<LoopInformationExtractionPass> Y("loop-info-extract", "Pass to extract to loop information");

static void registerBasicBlockAndLoopPass(const PassManagerBuilder &, legacy::PassManagerBase &PM)
{
    // PM.add(new LoopInformationExtractionPass());
    PM.add(new BasicBlockExtractionPass());
}

static RegisterStandardPasses RegisterCustomBasicBlockPass(PassManagerBuilder::EP_EarlyAsPossible, registerBasicBlockAndLoopPass);