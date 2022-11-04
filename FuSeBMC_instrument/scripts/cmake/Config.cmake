# Set a default build type if none was specified
set(default_build_type "RelWithDebInfo")
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
  message(STATUS "Setting build type to '${default_build_type}' as none was specified.")
  set(CMAKE_BUILD_TYPE "${default_build_type}" CACHE
      STRING "Choose the type of build." FORCE)
  # Set the possible values of build type for cmake-gui
  set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS
    "Debug" "Release" "MinSizeRel" "RelWithDebInfo" "Sanitizer")
endif()


#############################
# GENERAL
#############################
option(ENABLE_WERROR "All warnings are treated as errors during compilation (default: OFF)" OFF)

#############################
# OTHERS
#############################
if(WIN32)
    option(DOWNLOAD_WINDOWS_DEPENDENCIES "Download Windows LLVM and Z3 through CMake (default: OFF)" OFF)
endif()

#############################
# CMake extra Vars
#############################
# ESBMC_CLANG_HEADERS_BUNDLED: 'detect', On, Off
set(ESBMC_CLANG_HEADERS_BUNDLED "detect" CACHE STRING "Bundle the Clang resource-dir headers (default: detect)")
set(OVERRIDE_CLANG_HEADER_DIR "")
set(Clang_DIR "${LLVM_DIR}" CACHE STRING "Clang Directory (if not set, this will be set to the LLVM_DIR")

# Demand C++17
set (CMAKE_CXX_STANDARD 17)

# Used by try_compile
set(CMAKE_POSITION_INDEPENDENT_CODE ON)