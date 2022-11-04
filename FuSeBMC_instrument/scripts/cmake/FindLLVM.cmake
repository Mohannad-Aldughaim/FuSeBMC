# Module to find LLVM and checks it's version

if(NOT (("${LLVM_DIR}" STREQUAL "LLVM_DIR-NOTFOUND") OR ("${LLVM_DIR}" STREQUAL "")))

  find_package(LLVM REQUIRED CONFIG
    PATHS ${LLVM_DIR}
    NO_DEFAULT_PATH
  )

  find_package(Clang REQUIRED CONFIG
    PATHS ${Clang_DIR}
    NO_DEFAULT_PATH
  )
else()
  find_package(LLVM REQUIRED CONFIG)
  find_package(Clang REQUIRED CONFIG)
endif()

if (${LLVM_VERSION_MAJOR} LESS 11)
  message(FATAL_ERROR "Could not find LLVM/Clang >= 11.0 at all: please specify with -DLLVM_DIR/-DClang_DIR")
else()
  message(STATUS "LLVM version: ${LLVM_VERSION}")
endif()

message(STATUS "Clang found in: ${CLANG_INSTALL_PREFIX}")