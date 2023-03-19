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
#include <set>

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

// Boost dependencies
#include <boost/algorithm/string.hpp>

using namespace llvm;
using namespace std;

namespace{
    enum State
    {
        WHITE,
        GRAY,
        BLACK
    };

    class ProvenanceNode
    {
    public:
        string action;
        string artifact;
        string id;
        ProvenanceNode() {}
        ProvenanceNode(string act, string art, string i)
        {
            action = act;
            artifact = art;
            id = i;
        }
    };

    class AugmentedBasicBlock
    {
    private:
        string blockId;                     // Unique Block Id
        bool isRootBlock;                   // Defines if this is the starting block of the function.
        bool isConditionalBlock;            // Does it have branching at the end or just a straight jump to next block
        bool hasInlineAssembly;             // Is there any inline assembly instruction? Then parse separately
        string trueBlock;                   // If branched, then next true block
        string falseBlock;                  // If branched, then next false block
        string nextBlock;                   // If not branched, then next block
        vector<Instruction *> instructions; // All the call instructions are stored here (operation and arguments)
        vector<StringRef> functions;        // All the functions are stored here (Name only)
        vector<string> parents;             // Can keep track of the parent blocks if implementation wants
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

}