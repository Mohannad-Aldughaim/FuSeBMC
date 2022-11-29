SET(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
add_executable(FuSeBMC_instrument FuSeBMC_instrument.cpp FuncCallInfo.cpp FuncDeclInfo.cpp GoalCounter.cpp GoalCounter.cpp GoalInfo.cpp MyASTConsumer.cpp MyHolder.cpp MyOptions.cpp MyVisitor.cpp NonDetCallInfo.cpp NonDetConsumer.cpp NonDetVisitor.cpp SelectiveInputsHandler.cpp StdCFuncHandler.cpp)

target_include_directories(FuSeBMC_instrument
        PRIVATE ${CLANG_INCLUDE_DIRS}
        )
set_target_properties(FuSeBMC_instrument PROPERTIES COMPILE_FLAGS "-fno-rtti")
target_link_libraries(FuSeBMC_instrument clangTooling clangAST clangIndex Interval_approach )