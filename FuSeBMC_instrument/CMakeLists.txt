#################################
# Project Information           #
#################################
cmake_minimum_required(VERSION 3.7)
project(FuSeBMC_instrument)

#################################
# Configuration                 #
#################################

# Adds custom modules from ESBMC and default Options
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/scripts/cmake/")


include(ExternalDependencies)

# Source Code

include_directories(include)
add_subdirectory(Interval_approach)
add_subdirectory(src)

