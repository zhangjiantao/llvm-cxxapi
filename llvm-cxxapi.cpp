//===-- llvm-cxxapi.cpp - Tool for converting LLVM IR to C++ ----*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the driver of llvm-cxxapi tool.
//
//===----------------------------------------------------------------------===//

#include "CxxApiWriterPass.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include <llvm/Support/SourceMgr.h>

#include <fstream>
#include <iostream>
#include <string>
#include <system_error>

using namespace llvm;

static cl::opt<std::string>
    InputFilename(cl::Positional, cl::desc("<input file>"), cl::init("-"));

static cl::opt<std::string> OutputFilename("o", cl::desc("Output filename"),
                                           cl::init("-"));

static cl::opt<bool> IR("ir", cl::Optional,
                        cl::desc("Print IR contents as comments."),
                        cl::init(false));


int main(int argc, char **argv) {
  cl::ParseCommandLineOptions(argc, argv, " llvm-cpp converter\n");

  LLVMContext Context;

  // Get the output stream
  std::error_code EC;
  raw_fd_ostream Out(OutputFilename, EC, sys::fs::F_None);
  if (EC) {
    errs() << "Error: Unable to open output file: " << EC.message() << "\n";
    return 1;
  }

  // Compile input file
  SMDiagnostic Err;
  auto M = parseIRFile(InputFilename, Err, Context);
  if (!M) {
    Err.print(argv[0], errs());
    return 1;
  }

  // Run cpp writer pass
  legacy::PassManager PM;
  PM.add(createCxxApiWriterPass(Out, IR));
  PM.run(*M);

  llvm_shutdown();
  return 0;
}
