add_library(Interval_approach Interval_approach.cpp)
target_include_directories(Interval_approach
        PRIVATE ${CLANG_INCLUDE_DIRS}
        )
target_link_libraries(Interval_approach clangTooling clangAST clangIndex)


find_package(PkgConfig REQUIRED)
pkg_search_module(IBEX REQUIRED IMPORTED_TARGET ibex)
target_link_libraries(Interval_approach PkgConfig::IBEX)