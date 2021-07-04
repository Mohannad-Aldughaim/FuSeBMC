#include <GoalCounter.h>
#include <string>

GoalCounter GoalCounter::instance {};

GoalCounter& GoalCounter::getInstance()
{
   return instance;
}

GoalCounter::GoalCounter()
{
    this->funcLabelMap = new map<string,vector<string>>();
}

std::string GoalCounter::GetNewGoalForFunc(std::string func)
{
    counter++;
    std::string someGoal = std::string("\nGOAL_") + std::to_string(counter) + std::string(":;\n");
    if(mustGenerateFuncLabelMap)
        (*funcLabelMap)[func].push_back(std::string("GOAL_") + std::to_string(counter));
    return someGoal;
}
