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
