cmake_minimum_required(VERSION 3.4.3)

if(NOT COMMAND add_llvm_loadable_module)
  if (DEFINED ENV{LLVM_DIR})
    set(CMAKE_CXX_STANDARD 11)
    find_package(LLVM REQUIRED CONFIG)

    list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
    include(AddLLVM)

    add_definitions(${LLVM_DEFINITIONS})
    include_directories(${LLVM_INCLUDE_DIRS})

    # map lib names
    llvm_map_components_to_libnames(llvm_libs core support bitreader irreader)
    # build target
    add_executable(llvm-cxxapi CxxApiWriterPass.cpp llvm-cxxapi.cpp)
    target_link_libraries(llvm-cxxapi ${llvm_libs})

  else()

    message(FATAL_ERROR "\
WARNING: The LLVM_DIR var was not set (required for an out-of-source build)!\n\
Please set this to environment variable to point to the LLVM build directory\
(e.g. on linux: export LLVM_DIR=/path/to/llvm/build/dir)")

  endif()
else()

  set(LLVM_CXXAPI_IN_SOURCE_BUILD 1)

  set(LLVM_LINK_COMPONENTS
    Core
    Support
    BitReader
    IRReader
    )

  add_llvm_tool(llvm-cxxapi
    CxxApiWriterPass.cpp
    llvm-cxxapi.cpp
    )
endif()

install(TARGETS llvm-cxxapi
  DESTINATION bin)
