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
#set (DEFAULT_BUILD_TYPE "Release")

#option(BUILD_SHARED_LIBS "Build using shared libraries" OFF)
#option(BUILD_STATIC_LIBS "Build using shared libraries" ON)
#message(${BUILD_STATIC_LIBS})
#set (CMAKE_POSITION_INDEPENDENT_CODE ON)
#set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
#find_package(ZLIB REQUIRED)
#find_package(ZLIB REQUIRED)
#set (CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static -static-libstdc++ -static-libgcc -lm -l:libm.a")
set(ZLIB_USE_STATIC_LIBS "ON")
SET(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
find_package(ZLIB REQUIRED)

set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -static -static-libstdc++ -static-libgcc ")

include(ExternalDependencies)

# Source Code
include_directories(include)
add_subdirectory(Interval_approach)
add_subdirectory(src)
#include_directories(Frama-c)
#file(COPY Frama-c DESTINATION ${CMAKE_SOURCE_DIR}/)
install(TARGETS ${PROJECT_NAME} RUNTIME DESTINATION ${CMAKE_INSTALL_PREFIX}/${PROJECT_NAME})
install(FILES ${CMAKE_SOURCE_DIR}/myincludes.txt DESTINATION ${CMAKE_INSTALL_PREFIX}/${PROJECT_NAME})
install(DIRECTORY ${CMAKE_SOURCE_DIR}/external_include DESTINATION ${CMAKE_INSTALL_PREFIX}/${PROJECT_NAME})
install(DIRECTORY ${CMAKE_SOURCE_DIR}/Frama-c DESTINATION ${CMAKE_INSTALL_PREFIX}/${PROJECT_NAME})
install(DIRECTORY ${CMAKE_SOURCE_DIR}/examples DESTINATION ${CMAKE_INSTALL_PREFIX}/${PROJECT_NAME})
