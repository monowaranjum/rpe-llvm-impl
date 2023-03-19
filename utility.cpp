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
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/DDG.h"
#include "llvm/Analysis/DDGPrinter.h"
#include "llvm/IR/Constants.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/Statistic.h"
// JSON dependencies
#include <jsoncpp/json/json.h>

// GraphViz dependencies
// #include <graphviz/gvc.h>
// This dependency is not working at the moment. Lib file not found.
// [TODO: Fix GraphViz dependency issue. ]

// Boost dependencies
#include <boost/algorithm/string.hpp>

using namespace llvm;
using namespace std;

typedef list<string> PATH;
typedef pair<string, string> EDGE;
typedef vector<string> EDGE_LIST;
typedef map<string, EDGE_LIST> GRAPH;

namespace
{
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

    static void printEdgeList(vector<pair<string, string>> eList)
    {
        for (pair<string, string> edge : eList)
        {
            errs() << edge.first << " -> " << edge.second << "\n";
        }
    }

    static void printLoopingBlocks(vector<string> loopingBlocks)
    {
        errs() << "Looping blocks are: ";
        for (auto elem : loopingBlocks)
        {
            errs() << elem << " ";
        }
        errs() << "\n";
    }

    static void printAdjacencyList(map<string, vector<string>> _adjacencyList)
    {
        errs() << "Adjacency List Is:\n";
        for (auto key : _adjacencyList)
        {
            errs() << key.first << " -> ";
            for (auto elem : key.second)
            {
                errs() << elem << ", ";
            }
            errs() << "\n";
        }
    }

    static void printPath(PATH p)
    {
        errs() << "START -> ";
        for (string s : p)
        {
            errs() << s << " ->";
        }
        errs() << " END\n";
    }

    static void printPaths(vector<PATH> _paths)
    {
        int pathNum = 0;
        for (PATH path : _paths)
        {
            errs() << "Path Number: " << ++pathNum << "\n";
            printPath(path);
        }
    }

    static void printBackEdges(map<string, EDGE> backEdges)
    {
        for (auto &elem : backEdges)
        {

            errs() << elem.first << " : " << elem.second.first << " -> " << elem.second.second << "\n";
        }
    }

    static void printLoopExecutionPaths(map<string, vector<PATH>> pathsInLoops)
    {
        for (auto &elem : pathsInLoops)
        {
            int numberOfPaths = elem.second.size();
            errs() << "There are " << numberOfPaths << " in the loop anchored at: " << elem.first << "\n";
            printPaths(elem.second);
        }
    }
}