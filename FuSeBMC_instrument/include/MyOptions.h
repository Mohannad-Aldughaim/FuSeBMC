#ifndef MYOPTIONS_H
#define MYOPTIONS_H

#include <string>
#include <map>
#include <vector>

using namespace std; 
class MyOptions
{
public:
	std::string inputFile;
	std::string outputFile;
	std::string goalOutputFile;
	std::string infoFile;
	std::string goalProFuncOutputDir;
	bool addElse             = false;
	bool addGoalAtEndOfFunc  = false;
	bool showParseTree       = false;
	bool addLabelInFunc      = false;
	bool addFuncCallInFunc   = false;
	bool addLabels           = false;
	bool addLabelAfterLoop   = false;
	bool addFuSeBMCFunc      = false;
	bool handleReturnInMain  = false;
	bool exportLineNumberForNonDetCalls = false;
	bool exportGoalInfo      = false;
	bool exportCallGraph     = false;
	
	bool handleInfiniteWhileLoop = false;
	//std::string infiniteWhileLoopLimit = "-1";
	//bool replace_reach_error = false;
	bool addCommentInFunc     = false;
	bool exportSelectiveInputs= false;
	bool exportStdCFunc= false;
	

	// func1 , lbl1
	// func 2, lbl2
	map<string,string> funcLabelMap;
	
	//main, call1 , 
	// func1 , newCall
	map<string,string> funcCallMap;
	
	map<string,string> funcCommentMap;
	MyOptions();
	string GetLabelForFunc(string func);
	string GetCallForFunc(string func);
	string GetCommentForFunc(string func);
	vector<string> * GetUniqueCalls();
	
};

#endif /* MYOPTIONS_H */