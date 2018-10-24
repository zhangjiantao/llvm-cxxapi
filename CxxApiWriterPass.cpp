//===--- CxxApiWriterPass.cpp - Converting LLVM IR to C++ API ----*- C++-*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the writing of the LLVM IR as a set of C++ calls to the
// LLVM IR interface. The input module is assumed to be verified.
//
//===----------------------------------------------------------------------===//

#include "CxxApiWriterPass.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringExtras.h"
#if defined(LLVM_CXXAPI_IN_SOURCE_BUILD)
#include "llvm/Config/config.h"
#else
#include "llvm/Config/llvm-config.h"
#endif
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCInstrInfo.h"
#include "llvm/MC/MCSubtargetInfo.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <system_error>
#include <vector>

#define LLVM_VERSION_BEFORE(_MAJOR, _MINOR, _PATCH)                            \
  (LLVM_VERSION_MAJOR < _MAJOR ||                                              \
   (LLVM_VERSION_MAJOR == _MAJOR &&                                            \
    (LLVM_VERSION_MINOR < _MINOR ||                                            \
     (LLVM_VERSION_MINOR == _MINOR && LLVM_VERSION_PATCH < _PATCH))))

#if !LLVM_VERSION_BEFORE(3, 9, 1)
#include "llvm/Support/AtomicOrdering.h"
#endif

#if LLVM_VERSION_BEFORE(3, 8, 1)
#error LLVM version earlier than 3.8.1 is no longer supported.
#endif

using namespace llvm;

// Normalize a llvm value name to cxx variable name
static std::string Normalize(const std::string &);
// Normalize a llvm literal string to cxx literal string
static std::string Literally(const std::string &);

namespace {
using ValueMap = std::map<const Value *, std::string>;
using TypeMap = std::map<Type *, std::string>;
using TypeSet = std::set<Type *>;
using ConstSet = std::set<const Constant *>;

/// NameBuilder - Unique name builder for Type* or Value*
class NameBuilder {
  TypeMap Types;
  ValueMap Values;
  std::set<std::string> UsedNames;
  bool ShortName;

  std::string getPrefix(Type *Ty) {
    if (ShortName)
      return "";
    switch (Ty->getTypeID()) {
    case Type::VoidTyID:
      return "Void";
    case Type::FloatTyID:
      return "Float";
    case Type::DoubleTyID:
      return "Double";
    case Type::LabelTyID:
      return "Block";
    case Type::FunctionTyID:
      return "Func";
    case Type::StructTyID:
      return "Struct";
    case Type::TokenTyID:
      return "Tok";
    case Type::PointerTyID:
      return "Ptr" + getPrefix(Ty->getPointerElementType());
    case Type::IntegerTyID: {
      auto IntTy = cast<IntegerType>(Ty);
      if (IntTy->getBitWidth() == 1)
        return "Bool";
      if (IntTy->getBitWidth() == 8)
        return "Char";
      return "Int" + utostr(IntTy->getBitWidth()) + "t";
    }
    case Type::ArrayTyID: {
      auto ArrTy = cast<ArrayType>(Ty);
      auto EleTy = ArrTy->getElementType();
      if (auto IntEleTy = dyn_cast<IntegerType>(EleTy))
        if (IntEleTy->getBitWidth() == 8)
          return "String";
      return "Arr" + getPrefix(EleTy);
    }
    case Type::VectorTyID: {
      auto EleTy = cast<ArrayType>(Ty)->getElementType();
      return "Vec" + getPrefix(EleTy);
    }
    default:
      return "Unk";
    }
  }

  std::string getPrefix(const Value *Val) {
    if (ShortName)
      return "Var";
    if (auto G = dyn_cast<GlobalVariable>(Val)) {
      auto ET = G->getType()->getElementType();
      return "Global" + getPrefix(ET);
    } else if (isa<Function>(Val)) {
      return "Func" + Normalize(Val->getName().str());
    } else if (auto C = dyn_cast<Constant>(Val)) {
      return "Const" + getPrefix(C->getType());
    } else {
      return getPrefix(Val->getType());
    }
  }

  template <typename T> std::string getUnique(T *Obj, const char *Suffix = "") {
    unsigned i = 0;
    auto Prefix = getPrefix(Obj) + Suffix;
    auto Name = Prefix;
    while (UsedNames.find(Name) != UsedNames.end()) {
      Name = Prefix + utohexstr(++i, true);
    }
    UsedNames.insert(Name);
    return Name;
  }

public:
  explicit NameBuilder(bool Short) : ShortName(Short) {}

  bool has(Type *Ty) { return Types.find(Ty) != Types.end(); }
  bool has(const Value *Val) { return Values.find(Val) != Values.end(); }
  // Insert a defined name
  void set(Type *Ty, const std::string &Name) { Types[Ty] = Name; }
  void set(const Value *Val, const std::string &Name) { Values[Val] = Name; }

  // Get or create a unique name
  std::string get(Type *Ty) {
    if (has(Ty))
      return Types[Ty];
    return Types[Ty] = getUnique(Ty, "Ty");
  }
  std::string get(const Value *Val) {
    if (has(Val))
      return Values[Val];
    return Values[Val] = getUnique(Val);
  }
};

/// CxxApiWriterPass - This class is the main chunk of code that converts an
/// LLVM module to a C++ translation unit.
struct CxxApiWriterPass : public ModulePass {
  static char ID;
  explicit CxxApiWriterPass(raw_ostream &OS, bool IR, bool Short)
      : ModulePass(ID), Out(OS), isPrintIR(IR), TheModule(nullptr),
        DefNames(Short), IndentLevel(0) {}

  bool runOnModule(Module &M) override;

#if LLVM_VERSION_BEFORE(4, 0, 0)
  const char *getPassName() const override { return "llvm-cxxapi writer"; }
#else
  StringRef getPassName() const override { return "llvm-cxxapi writer"; }
#endif

private:
  raw_ostream &Out;
  bool isPrintIR;
  const Module *TheModule;
  NameBuilder DefNames;
  unsigned IndentLevel;

private:
  inline void indent() { ++IndentLevel; }
  inline void outdent() { --IndentLevel; }
  inline raw_ostream &nl() {
    Out << '\n';
    Out.indent(IndentLevel * 2);
    Out.flush();
    return Out;
  }
  inline raw_ostream &cl() { return Out; }

  inline StringRef btostr(bool B) { return B ? "true" : "false"; }
  inline std::string lastNameArg(const Instruction *I) {
    return I->hasName()
               ? std::string(", ") + Literally(I->getName().str()) + ");"
               : ");";
  }
  inline StringRef lastBoolArg(bool B) { return B ? ", true);" : ");"; }

private:
  bool hasAnyArgAttribute(const Function *);
  void printAttributes(const Function *, const std::string &);
  void printAttributes(const CallInst *, const std::string &);
  void printAttributes(const InvokeInst *, const std::string &);
  void printAttributes(const Argument *, const std::string &);
  void printConstantFP(const ConstantFP *);

  std::string getGEPInstOperands(const GetElementPtrInst *);
  std::string getGEPExprOperands(const GEPOperator *);
  std::string getCDSElements(const ConstantDataSequential *);
  std::string getCDSElementsAsInt(const ConstantDataSequential *);
  std::string getArgOperands(const iterator_range<User::const_op_iterator> &,
                             bool = false);
  std::string getTypeList(const std::vector<Type *> &, bool = false);
  template <typename T> std::string getAggregateElements(const T *);

  std::string getOperandName(const Value *, ValueMap &);

  void initCommonPtrType(PointerType *, TypeSet &);
  void initCommonType(Type *, TypeSet &);
  void initCommonConst(const Constant *, ConstSet &);

  void printArrayType(ArrayType *);
  void printFunctionType(FunctionType *);
  void printStructTypeHead(StructType *);
  void printStructTypeBody(StructType *);
  void printType(Type *);
  void printTypes(const Module *);

  void printConstant(const Constant *);
  void printConstants(const Module *);

  void printVariableHead(const GlobalVariable *);
  void printVariableBody(const GlobalVariable *);

  void printFunctionHead(const Function *);
  void printFunctionAttr(const Function *);
  void printFunctionBody(const Function *);

  bool isCommonIntrinsic(const Function *);
  bool isCommonIntrinsic(const CallInst *);
  void printIntrinsic(const CallInst *, ValueMap &);
  void printInstruction(const Instruction *, ValueMap &);

  void printModuleBody();
};
} // namespace

#define assert_cnt(Names, Begin, End)                                          \
  static_assert(End - Begin == sizeof(Names) / sizeof(*Names),                 \
                "not completely implemented")

static StringRef getBinOp(unsigned Opcode) {
  const char *BinOps[] = {
      "Add",  "FAdd", "Sub",  "FSub", "Mul",  "FMul", "UDiv", "SDiv", "FDiv",
      "URem", "SRem", "FRem", "Shl",  "LShr", "AShr", "And",  "Or",   "Xor",
  };
  assert_cnt(BinOps, Instruction::BinaryOpsBegin, Instruction::BinaryOpsEnd);
  return BinOps[Opcode - Instruction::BinaryOpsBegin];
}

static StringRef getCastOp(unsigned Opcode) {
  const char *CastOps[] = {
      "Trunc",    "ZExt",    "SExt",          "FPToUI", "FPToSI",
      "UIToFP",   "SIToFP",  "FPTrunc",       "FPExt",  "PtrToInt",
      "IntToPtr", "BitCast", "AddrSpaceCast",
  };
  assert_cnt(CastOps, Instruction::CastOpsBegin, Instruction::CastOpsEnd);
  return CastOps[Opcode - Instruction::CastOpsBegin];
}

static StringRef getFCmpPred(CmpInst::Predicate P) {
  const char *Cmps[] = {
      "FALSE", "OEQ", "OGT", "OGE", "OLT", "OLE", "ONE", "ORD",
      "UNO",   "UEQ", "UGT", "UGE", "ULT", "ULE", "UNE", "TRUE",
  };
  assert_cnt(Cmps, CmpInst::FIRST_FCMP_PREDICATE, CmpInst::BAD_FCMP_PREDICATE);
  return Cmps[P - CmpInst::FIRST_FCMP_PREDICATE];
}

static StringRef getICmpPred(CmpInst::Predicate P) {
  const char *Cmps[] = {
      "EQ", "NE", "UGT", "UGE", "ULT", "ULE", "SGT", "SGE", "SLT", "SLE",
  };
  assert_cnt(Cmps, CmpInst::FIRST_ICMP_PREDICATE, CmpInst::BAD_ICMP_PREDICATE);
  return Cmps[P - CmpInst::FIRST_ICMP_PREDICATE];
}

static StringRef getRMWBinOp(AtomicRMWInst::BinOp Opcode) {
  const char *RmwOps[] = {
      "Xchg", "Add", "Sub", "And",  "Nand", "Or",
      "Xor",  "Max", "Min", "UMax", "UMin",
  };
  assert_cnt(RmwOps, AtomicRMWInst::FIRST_BINOP, AtomicRMWInst::BAD_BINOP);
  return RmwOps[Opcode - AtomicRMWInst::FIRST_BINOP];
}
#undef assert_cnt

static StringRef getAtomicOrdering(AtomicOrdering Ordering) {
  switch (Ordering) {
  case AtomicOrdering::NotAtomic:
    return "AtomicOrdering::NotAtomic";
  case AtomicOrdering::Unordered:
    return "AtomicOrdering::Unordered";
  case AtomicOrdering::Monotonic:
    return "AtomicOrdering::Monotonic";
  case AtomicOrdering::Acquire:
    return "AtomicOrdering::Acquire";
  case AtomicOrdering::Release:
    return "AtomicOrdering::Release";
  case AtomicOrdering::AcquireRelease:
    return "AtomicOrdering::AcquireRelease";
  case AtomicOrdering::SequentiallyConsistent:
    return "AtomicOrdering::SequentiallyConsistent";
  }
  report_fatal_error("unknow AtomicOrdering");
}

template <typename T>
#if LLVM_VERSION_BEFORE(5, 0, 0)
static StringRef getAtomicSynchScope(const T *Obj) {
  switch (Obj->getSynchScope()) {
  case SingleThread:
    return "SingleThread";
  case CrossThread:
    return "CrossThread";
  }
  report_fatal_error("unknow AtomicSynchScope");
}
#else
static StringRef getAtomicSynchScope(const T *Obj) {
  switch (Obj->getSyncScopeID()) {
  case SyncScope::SingleThread:
    return "SyncScope::SingleThread";
  case SyncScope::System:
    return "SyncScope::System";
  }
  report_fatal_error("unknow AtomicSynchScope");
}
#endif

static StringRef getCallingConvImpl(CallingConv::ID ID) {
  // Get the calling convention.
  switch (ID) {
  case CallingConv::C:
    return "CallingConv::C";
  case CallingConv::Fast:
    return "CallingConv::Fast";
  case CallingConv::Cold:
    return "CallingConv::Cold";
  case CallingConv::FirstTargetCC:
    return "CallingConv::FirstTargetCC";
  default:
    return utostr(ID);
  }
}

template <typename T> static StringRef getCallingConv(const T *Obj) {
  return getCallingConvImpl(Obj->getCallingConv());
}

static StringRef getLinkageType(const GlobalValue *G) {
  switch (G->getLinkage()) {
  case GlobalValue::InternalLinkage:
    return "GlobalValue::InternalLinkage";
  case GlobalValue::PrivateLinkage:
    return "GlobalValue::PrivateLinkage";
  case GlobalValue::AvailableExternallyLinkage:
    return "GlobalValue::AvailableExternallyLinkage";
  case GlobalValue::LinkOnceAnyLinkage:
    return "GlobalValue::LinkOnceAnyLinkage";
  case GlobalValue::LinkOnceODRLinkage:
    return "GlobalValue::LinkOnceODRLinkage";
  case GlobalValue::WeakAnyLinkage:
    return "GlobalValue::WeakAnyLinkage";
  case GlobalValue::WeakODRLinkage:
    return "GlobalValue::WeakODRLinkage";
  case GlobalValue::AppendingLinkage:
    return "GlobalValue::AppendingLinkage";
  case GlobalValue::ExternalLinkage:
    return "GlobalValue::ExternalLinkage";
  case GlobalValue::ExternalWeakLinkage:
    return "GlobalValue::ExternalWeakLinkage";
  case GlobalValue::CommonLinkage:
    return "GlobalValue::CommonLinkage";
  }
  report_fatal_error("unknow LinageType");
}

static StringRef getVisibilityType(const GlobalValue *G) {
  switch (G->getVisibility()) {
  case GlobalValue::DefaultVisibility:
    return "GlobalValue::DefaultVisibility";
  case GlobalValue::HiddenVisibility:
    return "GlobalValue::HiddenVisibility";
  case GlobalValue::ProtectedVisibility:
    return "GlobalValue::ProtectedVisibility";
  }
  report_fatal_error("unknow Visibility");
}

static StringRef getDLLStorageClassType(const GlobalValue *G) {
  switch (G->getDLLStorageClass()) {
  case GlobalValue::DefaultStorageClass:
    return "GlobalValue::DefaultStorageClass";
  case GlobalValue::DLLImportStorageClass:
    return "GlobalValue::DLLImportStorageClass";
  case GlobalValue::DLLExportStorageClass:
    return "GlobalValue::DLLExportStorageClass";
  }
  report_fatal_error("unknow DLLStorageClass");
}

static StringRef getThreadLocalMode(const GlobalValue *G) {
  switch (G->getThreadLocalMode()) {
  case GlobalVariable::NotThreadLocal:
    return "GlobalVariable::NotThreadLocal";
  case GlobalVariable::GeneralDynamicTLSModel:
    return "GlobalVariable::GeneralDynamicTLSModel";
  case GlobalVariable::LocalDynamicTLSModel:
    return "GlobalVariable::LocalDynamicTLSModel";
  case GlobalVariable::InitialExecTLSModel:
    return "GlobalVariable::InitialExecTLSModel";
  case GlobalVariable::LocalExecTLSModel:
    return "GlobalVariable::LocalExecTLSModel";
  }
  report_fatal_error("unknow ThreadLocalMode");
}

static std::string Normalize(const std::string &Str) {
  auto Str1 = Str;
  for (size_t i = 0, e = Str.size(); i != e; ++i) {
    auto C = (unsigned char)Str[i];
    if (!((C >= '0' && C <= '9') || (C >= 'a' && C <= 'z') ||
          (C >= 'A' && C <= 'Z')))
      Str1[i] = '.';
  }

  StringRef StrRef(Str1);
  SmallVector<StringRef, 5> Vec;
  StrRef.split(Vec, ".", -1, false);

  if (Vec[0] == "llvm")
    Vec[0] = "LLVM";

  std::string Result;
  for (auto &Ref : Vec) {
    Result +=
        StringRef(Ref.data(), 1).upper() + StringRef(Ref).drop_front().str();
  }
  return Result;
}

static std::string Literally(const std::string &Str) {
  std::string Result;
  raw_string_ostream OS(Result);
  const std::map<unsigned char, std::string> Escapes = {
      {'\t', "\\t"}, {'\n', "\\n"},  {'\v', "\\v"}, {'\f', "\\f"},
      {'\r', "\\r"}, {'\\', "\\\\"}, {'\"', "\\"}};
  bool isValidLiteral = true;
  for (size_t i = 0, e = Str.size(); i != e; ++i) {
    auto C = (unsigned char)Str[i];
    // Unprintable and cannot be escaped
    if (!isprint(C) && Escapes.find(C) == Escapes.end()) {
      isValidLiteral = false;
      break;
    }
  }
  if (!isValidLiteral) {
    for (size_t i = 0, e = Str.size(); i != e; ++i) {
      auto C = (unsigned char)Str[i];
      OS << "\\x" << hexdigit(C >> 4)
         << hexdigit(static_cast<unsigned int>(C & 0x0F));
    }
    OS.flush();
    return "\"" + Result + "\"";
  } else {
    for (size_t i = 0, e = Str.size(); i != e; ++i) {
      auto C = (unsigned char)Str[i];
      if (Escapes.find(C) != Escapes.end()) {
        OS << Escapes.at(C);
      } else {
        OS << C;
      }
    }
    OS.flush();
    return "\"" + Result + "\"";
  }
}

// printConstantFP - Print a floating point constant .. very carefully :)
// This makes sure that conversion to/from floating yields the same binary
// result so that we don't lose precision.
void CxxApiWriterPass::printConstantFP(const ConstantFP *CFP) {
  auto APF = APFloat(CFP->getValueAPF());
  if (CFP->getType()->isFloatTy()) {
    bool ignored;
#if LLVM_VERSION_BEFORE(4, 0, 0)
    APF.convert(APFloat::IEEEdouble, APFloat::rmNearestTiesToEven, &ignored);
#else
    APF.convert(APFloat::IEEEdouble(), APFloat::rmNearestTiesToEven, &ignored);
#endif
  }
  cl() << "ConstantFP::get(Ctx, APFloat(";

  std::string StrVal;
  raw_string_ostream OS(StrVal);
/// FIXME: TEST
#if LLVM_VERSION_BEFORE(4, 0, 0)
  if (&CFP->getValueAPF().getSemantics() == &APFloat::IEEEdouble) {
#else
  if (&CFP->getValueAPF().getSemantics() == &APFloat::IEEEdouble()) {
#endif
    OS << CFP->getValueAPF().convertToDouble();
#if LLVM_VERSION_BEFORE(4, 0, 0)
  } else if (&CFP->getValueAPF().getSemantics() == &APFloat::IEEEsingle) {
#else
  } else if (&CFP->getValueAPF().getSemantics() == &APFloat::IEEEsingle()) {
#endif
    OS << (double)CFP->getValueAPF().convertToFloat();
  } else {
    report_fatal_error("unknown APFloat format!");
  }
  OS.flush();

  StrVal = StringRef(StrVal).trim().str();

  // Check to make sure that the stringized number is not some string like
  // "Inf" or NaN.  Check that the string matches the "[-+]?[0-9]" regex.
  auto BitCast64 = CFP->getValueAPF().bitcastToAPInt().getZExtValue();
  if (((StrVal[0] >= '0' && StrVal[0] <= '9') ||
       ((StrVal[0] == '-' || StrVal[0] == '+') &&
        (StrVal[1] >= '0' && StrVal[1] <= '9'))) &&
      (CFP->isExactlyValue(atof(StrVal.c_str())))) {
    if (CFP->getType()->isDoubleTy()) {
      cl() << StrVal;
    } else {
      cl() << StrVal << "f";
    }
  } else if (CFP->getType()->isDoubleTy()) {
    cl() << "BitsToDouble(0x" << utohexstr(BitCast64) << "ULL) /* " << StrVal
         << " */";
  } else {
    cl() << "BitsToFloat(0x" << utohexstr((uint32_t)BitCast64) << "U) /* "
         << StrVal << " */";
  }
  cl() << "))";
}

void CxxApiWriterPass::initCommonPtrType(PointerType *PT, TypeSet &Ts) {
  if (DefNames.has(PT))
    return;

  auto ET = PT->getPointerElementType();
  switch (ET->getTypeID()) {
  case Type::IntegerTyID: {
    unsigned BitWidth = cast<IntegerType>(ET)->getBitWidth();
    switch (BitWidth) {
    case 8:
    case 16:
    case 32:
    case 64:
      DefNames.set(PT, "Type::getInt" + utostr(BitWidth) + "PtrTy(Ctx)");
      return;
    default:
      DefNames.set(PT, "Type::getIntNPtrTy(Ctx, " + utostr(BitWidth) + ")");
      return;
    }
  }
  case Type::FloatTyID:
    DefNames.set(PT, "Type::getFloatPtrTy(Ctx)");
    return;
  case Type::DoubleTyID:
    DefNames.set(PT, "Type::getDoublePtrTy(Ctx)");
    return;
  case Type::X86_MMXTyID:
    DefNames.set(PT, "Type::getX86_MMXPtrTy(Ctx)");
    return;
  case Type::X86_FP80TyID:
    DefNames.set(PT, "Type::getX86_FP80PtrTy(Ctx)");
    return;
  default:
    initCommonType(ET, Ts);
    if (DefNames.has(ET)) {
      auto EN = DefNames.get(ET);
      auto AS = PT->getAddressSpace();
      if (AS) {
        DefNames.set(PT, "PointerType::get(" + EN + ", " + utostr(AS) + ")");
      } else {
        DefNames.set(PT, "PointerType::getUnqual(" + EN + ")");
      }
    }
    return;
  }
}

void CxxApiWriterPass::initCommonType(Type *Ty, TypeSet &Ts) {
  if (Ts.find(Ty) != Ts.end())
    return;
  Ts.insert(Ty);

  switch (Ty->getTypeID()) {
  default:
    break;
  case Type::IntegerTyID: {
    auto BitWidth = cast<IntegerType>(Ty)->getBitWidth();
    switch (BitWidth) {
    case 1:
    case 8:
    case 16:
    case 32:
    case 64:
      DefNames.set(Ty, "IRB.getInt" + utostr(BitWidth) + "Ty()");
      return;
    default:
      DefNames.set(Ty, "IRB.getIntNTy(" + utostr(BitWidth) + ")");
      return;
    }
  }
  case Type::PointerTyID:
    initCommonPtrType(cast<PointerType>(Ty), Ts);
    return;
  case Type::VoidTyID:
    DefNames.set(Ty, "IRB.getVoidTy()");
    return;
  case Type::HalfTyID:
    DefNames.set(Ty, "IRB.getHalfTy()");
    return;
  case Type::FloatTyID:
    DefNames.set(Ty, "IRB.getFloatTy()");
    return;
  case Type::DoubleTyID:
    DefNames.set(Ty, "IRB.getDoubleTy()");
    return;
  case Type::TokenTyID:
    DefNames.set(Ty, "Type::getTokenTy(Ctx)");
    return;
  case Type::LabelTyID:
    DefNames.set(Ty, "Type::getLabelTy(Ctx)");
    return;
  case Type::X86_MMXTyID:
    DefNames.set(Ty, "Type::getX86_MMXTy(Ctx)");
    return;
  case Type::X86_FP80TyID:
    DefNames.set(Ty, "Type::getX86_FP80Ty(Ctx)");
    return;
  }

  // recurse init all types
  for (unsigned N = 0; N < Ty->getNumContainedTypes(); N++) {
    initCommonType(Ty->getContainedType(N), Ts);
  }
}

std::string CxxApiWriterPass::getGEPInstOperands(const GetElementPtrInst *GEP) {
  std::string Names;
  for (unsigned N = 1; N < GEP->getNumOperands(); N++) {
    Names += DefNames.get(GEP->getOperand(N)) + ", ";
  }
  if (StringRef(Names).endswith(", "))
    Names = StringRef(Names).drop_back(2).str();
  return "{" + Names + "}";
}

std::string CxxApiWriterPass::getGEPExprOperands(const GEPOperator *GEP) {
  std::string Names;
  for (auto Idx = GEP->idx_begin(); Idx != GEP->idx_end(); Idx++) {
    auto C = cast<Constant>(Idx);
    printConstant(C);
    Names += DefNames.get(C) + ", ";
  }
  if (StringRef(Names).endswith(", "))
    Names = StringRef(Names).drop_back(2).str();
  return "ArrayRef<Constant *>({" + Names + "})";
}

std::string CxxApiWriterPass::getArgOperands(
    const iterator_range<User::const_op_iterator> &Operands, bool NeedCast) {
  std::string Names;
  for (auto &Arg : Operands) {
    Names += DefNames.get(Arg) + ", ";
  }
  std::string Prefix = NeedCast ? "ArrayRef<Value *>({" : "{";
  std::string Suffix = NeedCast ? "})" : "}";
  if (StringRef(Names).endswith(", "))
    Names = StringRef(Names).drop_back(2).str();
  return Prefix + Names + Suffix;
}

template <typename T>
std::string CxxApiWriterPass::getAggregateElements(const T *CA) {
  std::string Names;
  for (unsigned i = 0; i < CA->getNumOperands(); i++) {
    auto C = CA->getOperand(i);
    printConstant(C);
    Names += DefNames.get(C) + ", ";
  }
  if (StringRef(Names).endswith(", "))
    Names = StringRef(Names).drop_back(2).str();
  return "{" + Names + "}";
}

std::string
CxxApiWriterPass::getCDSElements(const ConstantDataSequential *CDS) {
  std::string Names;
  for (unsigned i = 0; i < CDS->getNumElements(); i++) {
    auto C = CDS->getElementAsConstant(i);
    printConstant(C);
    Names += DefNames.get(C) + ", ";
  }
  if (StringRef(Names).endswith(", "))
    Names = StringRef(Names).drop_back(2).str();
  return "{" + Names + "}";
}

std::string
CxxApiWriterPass::getCDSElementsAsInt(const ConstantDataSequential *CDS) {
  std::string Names;
  for (unsigned i = 0; i < CDS->getNumElements(); i++) {
    printConstant(CDS->getElementAsConstant(i));
    Names += utostr(CDS->getElementAsInteger(i)) + ", ";
  }
  if (StringRef(Names).endswith(", "))
    Names = StringRef(Names).drop_back(2).str();
  auto BWS = utostr(CDS->getElementType()->getIntegerBitWidth());
  return "ArrayRef<uint" + BWS + "_t>({" + Names + "})";
}

std::string CxxApiWriterPass::getTypeList(const std::vector<Type *> &TyList,
                                          bool NeedCast) {
  std::string Names;
  for (auto Ty : TyList) {
    printType(Ty);
    Names += DefNames.get(Ty) + ", ";
  }
  std::string Prefix = NeedCast ? "ArrayRef<Type *>({" : "{";
  std::string Suffix = NeedCast ? "})" : "}";
  if (StringRef(Names).endswith(", "))
    Names = StringRef(Names).drop_back(2).str();
  return Prefix + Names + Suffix;
}

static const std::map<Attribute::AttrKind, std::string> Attrs = {
  /// FIXME: not completely implemented
  //{Attribute::Alignment, "Alignment"},
  //{Attribute::AllocSize, "AllocSize"},
  {Attribute::AlwaysInline, "AlwaysInline"},
  {Attribute::ArgMemOnly, "ArgMemOnly"},
  {Attribute::Builtin, "Builtin"},
  {Attribute::ByVal, "ByVal"},
  {Attribute::Cold, "Cold"},
  {Attribute::Convergent, "Convergent"},
  //{Attribute::Dereferenceable, "Dereferenceable"},
  //{Attribute::DereferenceableOrNull, "DereferenceableOrNull"},
  {Attribute::InAlloca, "InAlloca"},
  {Attribute::InReg, "InReg"},
  {Attribute::InaccessibleMemOnly, "InaccessibleMemOnly"},
  {Attribute::InaccessibleMemOrArgMemOnly, "InaccessibleMemOrArgMemOnly"},
  {Attribute::InlineHint, "InlineHint"},
  {Attribute::JumpTable, "JumpTable"},
  {Attribute::MinSize, "MinSize"},
  {Attribute::Naked, "Naked"},
  {Attribute::Nest, "Nest"},
  {Attribute::NoAlias, "NoAlias"},
  {Attribute::NoBuiltin, "NoBuiltin"},
  {Attribute::NoCapture, "NoCapture"},
  {Attribute::NoDuplicate, "NoDuplicate"},
  {Attribute::NoImplicitFloat, "NoImplicitFloat"},
  {Attribute::NoInline, "NoInline"},
  {Attribute::NoRecurse, "NoRecurse"},
  {Attribute::NoRedZone, "NoRedZone"},
  {Attribute::NoReturn, "NoReturn"},
  {Attribute::NoUnwind, "NoUnwind"},
  {Attribute::NonLazyBind, "NonLazyBind"},
  {Attribute::NonNull, "NonNull"},
  {Attribute::OptimizeForSize, "OptimizeForSize"},
  {Attribute::OptimizeNone, "OptimizeNone"},
  {Attribute::ReadNone, "ReadNone"},
  {Attribute::ReadOnly, "ReadOnly"},
  {Attribute::Returned, "Returned"},
  {Attribute::ReturnsTwice, "ReturnsTwice"},
  {Attribute::SExt, "SExt"},
  {Attribute::SafeStack, "SafeStack"},
  {Attribute::SanitizeAddress, "SanitizeAddress"},
  {Attribute::SanitizeMemory, "SanitizeMemory"},
  {Attribute::SanitizeThread, "SanitizeThread"},
  {Attribute::StackAlignment, "StackAlignment"},
  {Attribute::StackProtect, "StackProtect"},
  {Attribute::StackProtectReq, "StackProtectReq"},
  {Attribute::StackProtectStrong, "StackProtectStrong"},
  {Attribute::StructRet, "StructRet"},
#if !LLVM_VERSION_BEFORE(3, 9, 0)
  {Attribute::SwiftError, "SwiftError"},
  {Attribute::SwiftSelf, "SwiftSelf"},
#endif
  {Attribute::UWTable, "UWTable"},
  {Attribute::ZExt, "ZExt"},
#if !LLVM_VERSION_BEFORE(3, 9, 1)
  {Attribute::WriteOnly, "WriteOnly"},
#endif
};

bool CxxApiWriterPass::hasAnyArgAttribute(const Function *F) {
  using Pair = std::pair<Attribute::AttrKind, std::string>;
  return std::any_of(F->arg_begin(), F->arg_end(), [&](const Argument &Arg) {
    return std::any_of(Attrs.begin(), Attrs.end(), [&](const Pair &Att) {
#if LLVM_VERSION_BEFORE(3, 9, 1)
      return Arg.getParent()->getAttributes().hasAttribute(Arg.getArgNo() + 1,
                                                           Att.first);
#else
      return Arg.hasAttribute(Att.first);
#endif
    });
  });
}

void CxxApiWriterPass::printAttributes(const Function *F,
                                       const std::string &Name) {
  using Pair = std::pair<Attribute::AttrKind, std::string>;
  std::for_each(Attrs.begin(), Attrs.end(), [&](const Pair &Att) {
    if (F->hasFnAttribute(Att.first)) {
      nl() << Name << "->addFnAttr(Attribute::" << Att.second << ");";
    }
  });
}

void CxxApiWriterPass::printAttributes(const CallInst *CI,
                                       const std::string &Name) {
  using Pair = std::pair<Attribute::AttrKind, std::string>;
#if LLVM_VERSION_BEFORE(5, 0, 0)
  std::for_each(Attrs.begin(), Attrs.end(), [&](const Pair &Att) {
    if (CI->getAttributes().hasAttribute(AttributeSet::ReturnIndex,
                                         Att.first)) {
      nl() << Name << "->addAttribute(AttributeSet::ReturnIndex, Attribute::"
           << Att.second << ");";
    }
  });
#else
  std::for_each(Attrs.begin(), Attrs.end(), [&](const Pair &Att) {
    if (CI->getAttributes().hasAttribute(AttributeList::ReturnIndex,
                                         Att.first)) {
      nl() << Name << "->addAttribute(AttributeList::ReturnIndex, Attribute::"
           << Att.second << ");";
    }
  });
#endif
}

void CxxApiWriterPass::printAttributes(const InvokeInst *Inv,
                                       const std::string &Name) {
  using Pair = std::pair<Attribute::AttrKind, std::string>;
#if LLVM_VERSION_BEFORE(5, 0, 0)
  std::for_each(Attrs.begin(), Attrs.end(), [&](const Pair &Att) {
    if (Inv->getAttributes().hasAttribute(AttributeSet::ReturnIndex,
                                          Att.first)) {
      nl() << Name << "->addAttribute(AttributeSet::ReturnIndex, Attribute::"
           << Att.second << ");";
    }
  });
#else
  std::for_each(Attrs.begin(), Attrs.end(), [&](const Pair &Att) {
    if (Inv->getAttributes().hasAttribute(AttributeList::ReturnIndex,
                                          Att.first)) {
      nl() << Name << "->addAttribute(AttributeList::ReturnIndex, Attribute::"
           << Att.second << ");";
    }
  });
#endif
}

void CxxApiWriterPass::printAttributes(const Argument *Arg,
                                       const std::string &Name) {
  using Pair = std::pair<Attribute::AttrKind, std::string>;
  std::for_each(Attrs.begin(), Attrs.end(), [&](const Pair &Att) {
#if LLVM_VERSION_BEFORE(3, 9, 1)
    auto AttrIdx = Arg->getArgNo() + 1;
    auto Attrs = Arg->getParent()->getAttributes();
    if (Attrs.hasAttribute(AttrIdx, Att.first)) {
      /// FIXME: not completely implemented
      nl() << "// " << Name << "->addAttr(Attribute::" << Att.second << ");";
    }
#else
    if (Arg->hasAttribute(Att.first)) {
      nl() << Name << "->addAttr(Attribute::" << Att.second << ");";
    }
#endif
  });
}

static bool getIfBuiltinIntType(Type *Ty, std::string &R) {
  if (auto PtrTy = dyn_cast<PointerType>(Ty)) {
    R += "*";
    return getIfBuiltinIntType(PtrTy->getPointerElementType(), R);
  }
  if (auto IntTy = dyn_cast<IntegerType>(Ty)) {
    auto BitWidth = IntTy->getBitWidth();
    switch (BitWidth) {
    case 8:
    case 16:
    case 32:
    case 64:
      R = "int" + utostr(BitWidth) + "_t" + R;
      return true;
    default:
      R = "types::i<" + utostr(BitWidth) + ">";
      return true;
    }
  }
  if (Ty->isVoidTy()) {
    R = "void" + R;
    return true;
  }
  return false;
}

void CxxApiWriterPass::printFunctionType(FunctionType *FT) {
  auto TypeName = DefNames.get(FT);

  for (unsigned i = 0; i < FT->getNumContainedTypes(); i++)
    printType(FT->getContainedType(i));

  if (isPrintIR) {
    nl();
    nl() << "/* " << *FT << " */";
  }

  auto isBuiltinInt = false;
  std::string Ty, TyStr;
  if (FT->getNumParams() < 6) {
    isBuiltinInt = getIfBuiltinIntType(FT->getReturnType(), Ty);
    if (isBuiltinInt) {
      TyStr += Ty + "(";
      for (unsigned i = 0; i < FT->getNumParams(); i++) {
        Ty.clear();
        isBuiltinInt = getIfBuiltinIntType(FT->getParamType(i), Ty);
        if (!isBuiltinInt)
          break;
        TyStr += Ty + ", ";
      }
      if (isBuiltinInt) {
        if (FT->isVarArg()) {
          TyStr += "...)";
        } else {
          if (FT->getNumParams())
            TyStr = StringRef(TyStr).drop_back(2).str();
          TyStr += ")";
        }
        nl() << "auto " << TypeName << " = TypeBuilder<" << TyStr
             << ", false>::get(Ctx);";
      }
    }
  }

  if (!isBuiltinInt) {
    auto Pars = getTypeList(FT->params().vec());
    nl() << "auto " << TypeName << " = FunctionType::get("
         << DefNames.get(FT->getReturnType()) << ", " << Pars << ", "
         << btostr(FT->isVarArg()) << ");";
  }
}

void CxxApiWriterPass::printArrayType(ArrayType *AT) {
  auto TypeName = DefNames.get(AT);
  auto ET = AT->getElementType();
  printType(ET);

  if (isPrintIR) {
    nl();
    nl() << "/* " << *AT << " */";
  }

  std::string Ty;
  if (getIfBuiltinIntType(ET, Ty)) {
    nl() << "auto " << TypeName << " = TypeBuilder<" << Ty << "["
         << AT->getNumElements() << "], false>::get(Ctx);";
  } else {
    nl() << "auto " << TypeName << " = ArrayType::get(" << DefNames.get(ET)
         << ", " << AT->getNumElements() << ");";
  }
}

void CxxApiWriterPass::printStructTypeHead(StructType *ST) {
  if (isPrintIR) {
    nl();
    nl() << "/* " << *ST << " */";
  }

  auto TypeName = DefNames.get(ST);
  if (ST->isLiteral()) {
    auto Pars = getTypeList(ST->elements().vec());
    nl() << "auto " << TypeName << " = StructType::get(Ctx, " << Pars << ", "
         << btostr(ST->isPacked()) << "); // isLiteral";
  } else {
    nl() << "auto " << TypeName << " = StructType::create(Ctx, "
         << Literally(ST->getName()) << ");";
    if (ST->isOpaque()) {
      cl() << "  // opaque";
    }
  }
}

void CxxApiWriterPass::printStructTypeBody(StructType *ST) {
  if (ST->isOpaque() || ST->isLiteral())
    return;

  auto TypeName = DefNames.get(ST);
  auto Pars = getTypeList(ST->elements().vec(), true);
  nl() << TypeName << "->setBody(" << Pars << ", " << btostr(ST->isPacked())
       << ");";
}

void CxxApiWriterPass::printType(Type *Ty) {
  // If we already defined this type, we don't need to define it again.
  if (DefNames.has(Ty))
    return;

  // Everything below needs the name for the type so get it now.
  auto TypeName = DefNames.get(Ty);

  // Print the type definition
  switch (Ty->getTypeID()) {
  case Type::StructTyID:
    printStructTypeHead(cast<StructType>(Ty));
    return;
  case Type::FunctionTyID:
    printFunctionType(cast<FunctionType>(Ty));
    return;
  case Type::ArrayTyID:
    printArrayType(cast<ArrayType>(Ty));
    return;
  case Type::PointerTyID: {
    auto PT = cast<PointerType>(Ty);
    auto ET = PT->getElementType();
    printType(ET);
    if (PT->getAddressSpace()) {
      nl() << "auto " << TypeName << " = PointerType::get(" << DefNames.get(ET)
           << ", " << PT->getAddressSpace() << ");";
    } else {
      nl() << "auto " << TypeName << " = PointerType::getUnqual("
           << DefNames.get(ET) << ");";
    }
    return;
  }
  case Type::VectorTyID: {
    auto VT = cast<VectorType>(Ty);
    auto ET = VT->getElementType();
    printType(ET);
    nl() << "auto " << TypeName << " = VectorType::get(" << DefNames.get(ET)
         << ", " << VT->getNumElements() << ");";
    return;
  }
  default:
    report_fatal_error("invalid TypeID!");
  }
}

void CxxApiWriterPass::printTypes(const Module *M) {
  TypeSet Ts;
  for (auto &G : M->globals()) {
    initCommonType(G.getType(), Ts);
    if (G.hasInitializer())
      initCommonType(G.getInitializer()->getType(), Ts);
  }

  for (auto &FI : M->functions()) {
    initCommonType(FI.getReturnType(), Ts);
    initCommonType(FI.getFunctionType(), Ts);
    for (auto &AI : FI.args())
      initCommonType(AI.getType(), Ts);

    for (auto &BB : FI.getBasicBlockList()) {
      initCommonType(BB.getType(), Ts);
      for (auto &I : BB.getInstList()) {
        initCommonType(I.getType(), Ts);
        for (unsigned i = 0; i < I.getNumOperands(); ++i)
          initCommonType(I.getOperand(i)->getType(), Ts);
      }
    }
  }

  if (!Ts.empty()) {
    nl() << "//";
    nl() << "// Type Definitions";
    nl() << "//";
  } else {
    return;
  }

  for (auto T : Ts)
    if (T->isStructTy())
      printStructTypeHead(cast<StructType>(T));
  for (auto T : Ts)
    if (T->isStructTy())
      printStructTypeBody(cast<StructType>(T));
  nl();

  for (auto T : Ts)
    if (T->isArrayTy())
      printType(T);
  nl();
  for (auto T : Ts)
    if (T->isVectorTy())
      printType(T);
  nl();
  for (auto T : Ts)
    if (T->isFunctionTy())
      printType(T);
  nl();

  // Init common PointerType again, for better readability
  TypeSet PtrTs;
  for (auto T : Ts)
    if (T->isPointerTy())
      initCommonPtrType(cast<PointerType>(T), PtrTs);

  for (auto T : Ts)
    printType(T);
}

// printConstant - Print out a constant pool entry...
void CxxApiWriterPass::printConstant(const Constant *C) {
  if (isa<ConstantInt>(C) || isa<BlockAddress>(C) ||
      isa<ConstantPointerNull>(C) || isa<UndefValue>(C) ||
      isa<ConstantTokenNone>(C) || isa<ConstantAggregateZero>(C)) {
    ConstSet Cs;
    initCommonConst(C, Cs);
  }

  // First, if the constant is actually a GlobalValue (variable or
  // function) or its already in the constant list then we've printed it
  // already and we can just return.
  if (DefNames.has(C) || isa<GlobalValue>(C))
    return;

  // Create val name
  auto ValName = DefNames.get(C);
  auto TypeName = DefNames.get(C->getType());

  // Define all operands
  std::vector<std::string> OpNames;
  for (unsigned i = 0; i < C->getNumOperands(); i++) {
    auto OpN = C->getOperand(i);
    if (auto COP = dyn_cast<Constant>(OpN)) {
      printConstant(COP);
    }
    OpNames.push_back(DefNames.get(OpN));
  }

  if (isPrintIR) {
    nl();
    nl() << "/*  " << *C << "  */";
  }

  //
  // ConstantInt (BitWidth > 64)
  if (auto CI = dyn_cast<ConstantInt>(C)) {
    auto BwStr = utostr(CI->getBitWidth());
    std::string ValStr;
    raw_string_ostream OS(ValStr);
    OS << CI->getValue();
    OS.flush();
    nl() << "auto " << ValName << " = ConstantInt::get(IRB.getIntNTy(" << BwStr
         << "), APInt(" << BwStr << ", \"" << ValStr << "\", 10));";
  }
  //
  // ConstantFP
  else if (auto CFP = dyn_cast<ConstantFP>(C)) {
    nl() << "auto " << ValName << " = ";
    printConstantFP(CFP);
    cl() << ";";
  }
  //
  // ConstantDataSequential
  else if (auto CDS = dyn_cast<ConstantDataSequential>(C)) {
    auto EleTy = CDS->getElementType();
    auto EleBitWidth = EleTy->getIntegerBitWidth();
    auto isArrayTy = isa<ArrayType>(CDS->getType());
    //
    // literal string
    if (CDS->isString() && !CDS->getAsString().drop_back().count('\0')) {
      nl() << "auto " << ValName << " = ConstantDataArray::getString(Ctx, ";
      auto Str = CDS->getAsString();
      auto NulTerm = (Str.back() == 0);
      if (NulTerm)
        Str = Str.drop_back();
      cl() << Literally(Str) << ", " << btostr(NulTerm) << ");";
    }
    //
    // integer array
    else if (EleTy->isIntegerTy() && EleBitWidth <= 64) {
      auto Elts = getCDSElementsAsInt(CDS);
      auto Method = isArrayTy ? " = ConstantDataArray::get(Ctx, "
                              : " = ConstantDataVector::get(Ctx, ";
      nl() << "auto " << ValName << Method << Elts << ");";
    }
    //
    // etc...
    else {
      auto Elts = getCDSElements(CDS);
      auto Method =
          isArrayTy ? " = ConstantArray::get(" : " = ConstantVector::get(";
      nl() << "auto " << ValName << Method << TypeName << ", " << Elts << ");";
    }
  }
#if LLVM_VERSION_BEFORE(3, 9, 1)
  else if (auto CA = dyn_cast<ConstantArray>(C)) {
    auto Elts = getAggregateElements(CA);
    nl() << "auto " << ValName << " = ConstantArray::get(" << TypeName << ", "
         << Elts << ");";
  } else if (auto CS = dyn_cast<ConstantStruct>(C)) {
    auto Elts = getAggregateElements(CS);
    nl() << "auto " << ValName << " = ConstantStruct::get(" << TypeName << ", "
         << Elts << ");";
  } else if (auto CV = dyn_cast<ConstantVector>(C)) {
    auto Elts = getAggregateElements(CV);
    nl() << "auto " << ValName << " = ConstantVector::get(" << TypeName << ", "
         << Elts << ");";
  }
#else
  //
  // ConstantAggregate
  else if (auto CA = dyn_cast<ConstantAggregate>(C)) {
    auto Elts = getAggregateElements(CA);
    nl() << "auto " << ValName << " = ";
    if (isa<ConstantArray>(C)) {
      cl() << "ConstantArray::get(";
    } else if (isa<ConstantStruct>(C)) {
      cl() << "ConstantStruct::get(";
    } else if (isa<ConstantVector>(C)) {
      cl() << "ConstantVector::get(";
    } else {
      report_fatal_error("unknow ConstantAggregate");
    }
    cl() << TypeName << ", " << Elts << ");";
  }
#endif
  //
  // ConstantExpr
  else if (auto CE = dyn_cast<ConstantExpr>(C)) {
    // GetElementPtrExpr
    if (CE->getOpcode() == Instruction::GetElementPtr) {
      auto GEP = cast<GEPOperator>(CE);
      auto Indices = getGEPExprOperands(GEP);
      auto Method =
          GEP->isInBounds() ? "getInBoundsGetElementPtr" : "getGetElementPtr";
      nl() << "auto " << ValName << " = ConstantExpr::" << Method
           << "(nullptr, " << OpNames[0] << ", " << Indices << ");";
    }
    // ConstantExpr Cast
    else if (CE->isCast()) {
      nl() << "auto " << ValName << " = ConstantExpr::get"
           << getCastOp(CE->getOpcode()) << "(" << OpNames[0] << ", "
           << TypeName << ");";
    }
    // ConstantExpr BinOp
    else if (Instruction::isBinaryOp(CE->getOpcode())) {
      nl() << "auto " << ValName << " = ConstantExpr::get"
           << getBinOp(CE->getOpcode()) << "(" << OpNames[0];
      for (unsigned i = 1; i < CE->getNumOperands(); ++i) {
        cl() << ", " << OpNames[i];
      }
      cl() << ");";
    }
    // ConstantExpr cmp, etc
    else {
      nl() << "auto " << ValName << " = ConstantExpr::get";
      switch (CE->getOpcode()) {
      case Instruction::ICmp:
        cl() << "ICmp(ICmpInst::ICMP_"
             << getICmpPred((ICmpInst::Predicate)CE->getPredicate());
        break;
      case Instruction::FCmp:
        cl() << "FCmp(FCmpInst::FCMP_"
             << getFCmpPred((FCmpInst::Predicate)CE->getPredicate());
        break;
      case Instruction::Select:
        cl() << "Select(";
        break;
      case Instruction::ExtractElement:
        cl() << "ExtractElement(";
        break;
      case Instruction::InsertElement:
        cl() << "InsertElement(";
        break;
      case Instruction::ShuffleVector:
        cl() << "ShuffleVector(";
        break;
      default:
        report_fatal_error("invalid constant bin expression");
      }
      cl() << OpNames[0];
      for (unsigned i = 1; i < CE->getNumOperands(); ++i)
        cl() << ", " << OpNames[i];
      cl() << ");";
    }
  } else {
    report_fatal_error("unknow constant!");
  }
}

void CxxApiWriterPass::initCommonConst(const Constant *C, ConstSet &Cs) {
  if (Cs.find(C) != Cs.end())
    return;
  Cs.insert(C);

  if (auto BA = dyn_cast<BlockAddress>(C)) {
    DefNames.set(C, "BlockAddress::get(" + DefNames.get(BA->getBasicBlock()) +
                        ")");
    return;
  }

  auto TyName = DefNames.get(C->getType());
  if (isa<UndefValue>(C)) {
    DefNames.set(C, "UndefValue::get(" + TyName + ")");
    return;
  }
  if (isa<ConstantPointerNull>(C)) {
    DefNames.set(C, "ConstantPointerNull::get(" + TyName + ")");
    return;
  }
  if (isa<ConstantTokenNone>(C)) {
    DefNames.set(C, "ConstantTokenNone::get(Ctx)");
    return;
  }
  if (isa<ConstantAggregateZero>(C)) {
    DefNames.set(C, "ConstantAggregateZero::get(" + TyName + ")");
    return;
  }

  if (auto CI = dyn_cast<ConstantInt>(C)) {
    auto Val = CI->getValue().toString(10, true);
    auto BitWidth = CI->getBitWidth();
    auto BWS = utostr(BitWidth);
    switch (BitWidth) {
    default: {
      if (BitWidth > 64)
        return;
      DefNames.set(C, "IRB.getIntN(" + BWS + ", " + Val + ")");
      return;
    }
    case 1: {
      DefNames.set(C, CI->isNullValue() ? "IRB.getFalse()" : "IRB.getTrue()");
      return;
    }
    case 8:
    case 16:
    case 32:
    case 64:
      DefNames.set(C, "IRB.getInt" + BWS + "(" + Val + ")");
      return;
    }
  }

  if (auto CDS = dyn_cast<ConstantDataSequential>(C)) {
    if (!CDS->isString()) {
      for (unsigned i = 0; i < CDS->getNumElements(); i++) {
        auto Elt = CDS->getElementAsConstant(i);
        initCommonConst(Elt, Cs);
      }
    }
    return;
  }

  for (unsigned i = 0; i < C->getNumOperands(); i++) {
    if (auto OP = dyn_cast<Constant>(C->getOperand(i))) {
      initCommonConst(OP, Cs);
    }
  }
}

void CxxApiWriterPass::printConstants(const Module *M) {
  ConstSet Cs;
  for (auto &G : M->globals())
    if (G.hasInitializer())
      initCommonConst(G.getInitializer(), Cs);

  for (auto &F : M->functions()) {
    if (F.hasPersonalityFn())
      initCommonConst(F.getPersonalityFn(), Cs);
    for (auto I = inst_begin(F), E = inst_end(F); I != E; ++I)
      for (auto &Op : I->operands())
        if (auto C = dyn_cast<Constant>(&Op))
          initCommonConst(C, Cs);
  }

  if (!Cs.empty()) {
    nl() << "//";
    nl() << "// Constant Definitions";
    nl() << "//";
  }

  for (auto C : Cs)
    if (!isa<ConstantExpr>(C))
      printConstant(C);
  for (auto C : Cs)
    printConstant(C);
}

void CxxApiWriterPass::printVariableHead(const GlobalVariable *GV) {
  if (isPrintIR) {
    nl();
    nl() << "/*  " << *GV << "  */";
  }
  auto Name = DefNames.get(GV);
  auto EleTyName = DefNames.get(GV->getType()->getElementType());
  if (!isPrintIR && GV->hasInitializer()) {
    nl() << "// has initializer, specified below";
  }
  nl() << "auto " << Name << " = new GlobalVariable(*M, " << EleTyName << ", "
       << btostr(GV->isConstant()) << ", " << getLinkageType(GV)
       << ", nullptr);";
  if (GV->hasName()) {
    nl() << Name << "->setName(" << Literally(GV->getName()) << ");";
  }
  if (GV->hasSection()) {
    nl() << Name << "->setSection(" << Literally(GV->getSection()) << ");";
  }
  if (GV->getAlignment()) {
    nl() << Name << "->setAlignment(" << GV->getAlignment() << ");";
  }
  if (GV->getVisibility() != GlobalValue::DefaultVisibility) {
    nl() << Name << "->setVisibility(" << getVisibilityType(GV) << ");";
  }
  if (GV->getDLLStorageClass() != GlobalValue::DefaultStorageClass) {
    nl() << Name << "->setDLLStorageClass(" << getDLLStorageClassType(GV)
         << ");";
  }
  if (GV->isThreadLocal()) {
    nl() << Name << "->setThreadLocalMode(" << getThreadLocalMode(GV) << ");";
  }
  if (GV->hasComdat()) {
    nl() << Name << "->setComdat(M->getOrInsertComdat(";
    if (GV->getName() == GV->getComdat()->getName()) {
      cl() << Name << "->getName()));";
    } else {
      cl() << Literally(GV->getComdat()->getName()) << ")));";
    }
  }
#if !LLVM_VERSION_BEFORE(6, 0, 1)
  if (GV->isDSOLocal()) {
    nl() << Name << "->setDSOLocal(true);";
  }
#endif
#if !LLVM_VERSION_BEFORE(3, 9, 1)
  if (GV->hasAtLeastLocalUnnamedAddr()) {
    auto UA = GV->hasGlobalUnnamedAddr() ? "Global);" : "Local);";
    nl() << Name << "->setUnnamedAddr(GlobalValue::UnnamedAddr::" << UA;
  }
#endif
  nl();
}

void CxxApiWriterPass::printVariableBody(const GlobalVariable *GV) {
  if (GV->hasInitializer()) {
    nl() << DefNames.get(GV) << "->setInitializer("
         << DefNames.get(GV->getInitializer()) << ");";
  }
}

// getOperandName - Get oprand def name, if undef, make a placeholder
std::string CxxApiWriterPass::getOperandName(const Value *V, ValueMap &Refs) {
  // See if its alread in the map of forward references, if so just return
  // the name we already set up for it
  if (Refs.find(V) != Refs.end())
    return Refs[V];

  if (!isa<Instruction>(V) || DefNames.has(V))
    return DefNames.get(V);

  // This is a new forward reference. Generate a unique name for it
  auto Name = "Ref" + DefNames.get(V);
  auto Owner = "Own" + DefNames.get(V);

  // Yes, this is a hack. An Argument is the smallest instantiable value
  // that we can make as a placeholder for the real value. We'll replace
  // these Argument instances later.
  nl() << "// Reference to undef value " << DefNames.get(V)
       << ", make a placeholder";
  nl() << "auto " << Owner << " = llvm::make_unique<Argument>("
       << DefNames.get(V->getType()) << ");";
  nl() << "auto " << Name << " = " << Owner << ".get();";
  return Refs[V] = Name;
}

bool CxxApiWriterPass::isCommonIntrinsic(const Function *F) {
  if (F->isIntrinsic()) {
    switch (F->getIntrinsicID()) {
    case Intrinsic::lifetime_start:
    case Intrinsic::lifetime_end:
    case Intrinsic::memcpy:
    case Intrinsic::memmove:
    case Intrinsic::memset:
    case Intrinsic::assume:
      return true;
    default:
      return false;
    }
  }
  return false;
}

bool CxxApiWriterPass::isCommonIntrinsic(const CallInst *CI) {
  if (auto F = CI->getCalledFunction())
    return isCommonIntrinsic(F);
  return false;
}

// printIntrinsic - Print llvm intrinsic, this assume CI is a intrinsic call
void CxxApiWriterPass::printIntrinsic(const CallInst *CI, ValueMap &Refs) {
  assert(isCommonIntrinsic(CI) && "not a common intrisic!");

  std::vector<std::string> ArgNames;
  for (unsigned i = 0; i < CI->getNumArgOperands(); i++) {
    ArgNames.push_back(getOperandName(CI->getArgOperand(i), Refs));
  }

  auto F = CI->getCalledFunction();
  switch (F->getIntrinsicID()) {
  case Intrinsic::lifetime_start: {
    nl() << "IRB.CreateLifetimeStart(" << ArgNames[1] << ", " << ArgNames[0]
         << ");";
    return;
  }
  case Intrinsic::lifetime_end: {
    nl() << "IRB.CreateLifetimeEnd(" << ArgNames[1] << ", " << ArgNames[0]
         << ");";
    return;
  }
  case Intrinsic::memcpy: {
    auto Align = cast<ConstantInt>(CI->getArgOperand(3))->getZExtValue();
    auto Volatile =
        btostr(cast<ConstantInt>(CI->getArgOperand(4))->getZExtValue() != 0);
    nl() << "IRB.CreateMemCpy(" << ArgNames[0] << ", " << ArgNames[1] << ", "
         << ArgNames[2] << ", " << Align << ", " << Volatile << ");";
    return;
  }
  case Intrinsic::memmove: {
    auto Align = cast<ConstantInt>(CI->getArgOperand(3))->getZExtValue();
    auto isVolatile =
        btostr(cast<ConstantInt>(CI->getArgOperand(4))->getZExtValue() != 0);
    nl() << "IRB.CreateMemMove(" << ArgNames[0] << ", " << ArgNames[1] << ", "
         << ArgNames[2] << ", " << Align << ", " << isVolatile << ");";
    return;
  }
  case Intrinsic::memset: {
    auto Align = cast<ConstantInt>(CI->getArgOperand(3))->getZExtValue();
    auto isVolatile =
        btostr(cast<ConstantInt>(CI->getArgOperand(4))->getZExtValue() != 0);
    nl() << "IRB.CreateMemSet(" << ArgNames[0] << ", " << ArgNames[1] << ", "
         << ArgNames[2] << ", " << Align << ", " << isVolatile << ");";
    return;
  }
  case Intrinsic::assume: {
    nl() << "IRB.CreateAssumption(" << ArgNames[0] << ");";
    return;
  }
  default:
    report_fatal_error("not a common intrisic!");
  }
}

// printInstruction - This member is called for each Instruction in a
// function.
void CxxApiWriterPass::printInstruction(const Instruction *I, ValueMap &Refs) {
  if (isPrintIR) {
    nl();
    nl() << "/*" << *I << "  */";
  }

  auto ValName = DefNames.get(I);
  auto ValTyName = DefNames.get(I->getType());

  // If defined instruction has forward reference, update Refs map
  if (Refs.find(I) != Refs.end()) {
    assert((Refs[I] == "Ref" + ValName) && "bad forward reference!");
    Refs[I] = ValName;
  }

  // Before we emit this instruction, we need to take care of generating
  // any forward references. So, we get the names of all the operands in
  // advance
  std::vector<std::string> OpNames;
  for (unsigned i = 0; i < I->getNumOperands(); i++) {
    OpNames.push_back(getOperandName(I->getOperand(i), Refs));
  }

  if (Instruction::isBinaryOp(I->getOpcode())) {
    auto BinOpName = getBinOp(I->getOpcode());
    nl() << "auto " << ValName << " = IRB.Create" << BinOpName << "("
         << OpNames[0] << ", " << OpNames[1];
    if (auto BO = dyn_cast<OverflowingBinaryOperator>(I)) {
      auto Nuw = BO->hasNoUnsignedWrap();
      auto Nsw = BO->hasNoSignedWrap();
      if (Nuw || Nsw) {
        cl() << ", " << Literally(I->getName()) << ", " << btostr(Nuw) << ", "
             << btostr(Nsw) << ");";
        return;
      }
    }
    cl() << lastNameArg(I);
    return;
  }

  if (Instruction::isCast(I->getOpcode())) {
    auto CastOpName = getCastOp(I->getOpcode());
    nl() << "auto " << ValName << " = IRB.Create" << CastOpName << "("
         << OpNames[0] << ", " << ValTyName << lastNameArg(I);
    return;
  }

  switch (I->getOpcode()) {
  case Instruction::Ret: {
    auto Ret = cast<ReturnInst>(I);
    if (Ret->getReturnValue()) {
      nl() << "IRB.CreateRet(" << OpNames[0] << ");";
    } else {
      nl() << "IRB.CreateRetVoid();";
    }
    return;
  }
  case Instruction::Br: {
    auto BR = cast<BranchInst>(I);
    if (BR->isConditional()) {
      nl() << "IRB.CreateCondBr(" << OpNames[0] << ", " << OpNames[2] << ", "
           << OpNames[1] << ");";
    } else if (BR->isUnconditional()) {
      nl() << "IRB.CreateBr(" << OpNames[0] << ");";
    } else {
      report_fatal_error("Branch with 2 operands?");
    }
    return;
  }
  case Instruction::Switch: {
    auto SI = cast<SwitchInst>(I);
    nl() << "auto " << ValName << " = IRB.CreateSwitch(" << OpNames[0] << ", "
         << OpNames[1] << ", " << SI->getNumCases() << ");";
    for (auto It = SI->case_begin(); It != SI->case_end(); ++It) {
#if LLVM_VERSION_BEFORE(5, 0, 0)
      auto Case = &It;
#else
      auto Case = It;
#endif
      auto CaseVal = DefNames.get(Case->getCaseValue());
      auto BBName = DefNames.get(Case->getCaseSuccessor());
      nl() << ValName << "->addCase(" << CaseVal << ", " << BBName << ");";
    }
    nl();
    return;
  }
  case Instruction::IndirectBr: {
    auto IBI = cast<IndirectBrInst>(I);
    auto NumDest = IBI->getNumDestinations();
    nl() << "auto " << ValName << " = IRB.CreateIndirectBr(" << OpNames[0]
         << ", " << NumDest << ");";
    for (unsigned i = 0; i != NumDest; ++i)
      nl() << ValName << "->addDestination("
           << DefNames.get(IBI->getDestination(i)) << ");";
    nl();
    return;
  }
  case Instruction::Resume: {
    nl() << "IRB.CreateResume(" << OpNames[0] << ");";
    return;
  }
  case Instruction::Invoke: {
    auto Inv = cast<InvokeInst>(I);
#if LLVM_VERSION_BEFORE(3, 9, 1)
    auto Args = getArgOperands(Inv->arg_operands(), true);
#else
    auto Args = getArgOperands(Inv->arg_operands());
#endif
    nl() << "auto " << ValName << " = IRB.CreateInvoke("
         << getOperandName(Inv->getCalledValue(), Refs) << ", "
         << DefNames.get(Inv->getNormalDest()) << ", "
         << DefNames.get(Inv->getUnwindDest()) << ", " << Args
         << lastNameArg(I);
    nl() << ValName << "->setCallingConv(" << getCallingConv(Inv) << ");";
    printAttributes(Inv, ValName);
    nl();
    return;
  }
  case Instruction::Unreachable: {
    nl() << "IRB.CreateUnreachable();";
    return;
  }
  case Instruction::Alloca: {
    auto AI = cast<AllocaInst>(I);
    auto AllocTy = DefNames.get(AI->getAllocatedType());
    nl() << "auto " << ValName << " = IRB.CreateAlloca(" << AllocTy;
    if (AI->isArrayAllocation()) {
      cl() << ", " << OpNames[0] << lastNameArg(I);
    } else if (I->hasName()) {
      cl() << ", nullptr" << lastNameArg(I);
    } else {
      cl() << ");";
    }
    if (AI->getAlignment()) {
      nl() << ValName << "->setAlignment(" << AI->getAlignment() << ");";
      nl();
    }
    return;
  }
  case Instruction::Load: {
    auto LD = cast<LoadInst>(I);
    if (LD->isAtomic() || LD->hasNUsesOrMore(1))
      nl() << "auto " << ValName << " = ";
    else
      nl();

    if (LD->getAlignment()) {
      cl() << "IRB.CreateAlignedLoad(" << OpNames[0] << ", "
           << LD->getAlignment() << lastBoolArg(LD->isVolatile());
    } else {
      auto Vol = LD->isVolatile() ? ", true" : "";
      cl() << "IRB.CreateLoad(" << OpNames[0] << Vol << lastNameArg(I);
    }
    if (LD->isAtomic()) {
      auto Ordering = getAtomicOrdering(LD->getOrdering());
      auto Scope = getAtomicSynchScope(LD);
      nl() << ValName << "->setAtomic(" << Ordering << ", " << Scope << ");";
      nl();
    }
    return;
  }
  case Instruction::Store: {
    auto ST = cast<StoreInst>(I);
    if (ST->isAtomic())
      nl() << "auto " << ValName << " = ";
    else
      nl();

    if (ST->getAlignment()) {
      cl() << "IRB.CreateAlignedStore(" << OpNames[0] << ", " << OpNames[1]
           << ", " << ST->getAlignment() << lastBoolArg(ST->isVolatile());
    } else {
      cl() << "IRB.CreateStore(" << OpNames[0] << ", " << OpNames[1]
           << lastBoolArg(ST->isVolatile());
    }
    if (ST->isAtomic()) {
      auto Ordering = getAtomicOrdering(ST->getOrdering());
      auto Scope = getAtomicSynchScope(ST);
      nl() << ValName << "->setAtomic(" << Ordering << ", " << Scope << ");";
    }
    return;
  }
  case Instruction::GetElementPtr: {
    auto GEP = cast<GetElementPtrInst>(I);
    auto Method = GEP->isInBounds() ? "CreateInBoundsGEP(" : "CreateGEP(";
    nl() << "auto " << ValName << " = IRB." << Method << OpNames[0];
    if (GEP->getNumIndices() == 1)
      cl() << ", " << OpNames[1];
    else if (GEP->getNumIndices() > 1)
      cl() << ", " << getGEPInstOperands(GEP);

    cl() << lastNameArg(I);
    return;
  }
  case Instruction::ICmp: {
    auto Pred = getICmpPred(cast<ICmpInst>(I)->getPredicate());
    nl() << "auto " << ValName << " = IRB.CreateICmp" << Pred << "("
         << OpNames[0] << ", " << OpNames[1] << lastNameArg(I);
    return;
  }
  case Instruction::FCmp: {
    auto Pred = getFCmpPred(cast<FCmpInst>(I)->getPredicate());
    nl() << "auto " << ValName << " = IRB.CreateFCmp" << Pred << "("
         << OpNames[0] << ", " << OpNames[1] << lastNameArg(I);
    return;
  }
  case Instruction::PHI: {
    auto Phi = cast<PHINode>(I);
    auto NumIncom = Phi->getNumIncomingValues();
    nl() << "auto " << ValName << " = IRB.CreatePHI(" << ValTyName << ", "
         << NumIncom << lastNameArg(I);
    for (unsigned i = 0; i < NumIncom; ++i) {
      nl() << ValName << "->addIncoming("
           << getOperandName(Phi->getIncomingValue(i), Refs) << ", "
           << DefNames.get(Phi->getIncomingBlock(i)) << ");";
    }
    nl();
    return;
  }
  case Instruction::Call: {
    auto Call = cast<CallInst>(I);
    if (isCommonIntrinsic(Call)) {
      printIntrinsic(Call, Refs);
      return;
    }

    auto FunName = getOperandName(Call->getCalledValue(), Refs);
    if (auto ILA = dyn_cast<InlineAsm>(Call->getCalledValue())) {
      FunName = "ILA" + ValName;
      nl() << "auto " << FunName << " = InlineAsm::get(";
      cl() << DefNames.get(ILA->getFunctionType()) << ", ";
      cl() << Literally(ILA->getAsmString()) << ", ";
      cl() << Literally(ILA->getConstraintString()) << ", ";
      cl() << btostr(ILA->hasSideEffects()) << ");";
    }
    if (Call->getCallingConv() || Call->isTailCall() ||
        Call->hasNUsesOrMore(1) /*|| !Call->getType()->isVoidTy()*/) {
      nl() << "auto " << ValName << " = ";
    } else {
      nl();
    }
    cl() << "IRB.CreateCall(" << FunName << ", "
         << getArgOperands(Call->arg_operands()) << lastNameArg(I);
    if (Call->getCallingConv()) {
      nl() << ValName << "->setCallingConv(" << getCallingConv(Call) << ");";
    }
    if (Call->isTailCall()) {
      nl() << ValName << "->setTailCall();";
    }
    printAttributes(Call, ValName);
    nl();
    return;
  }
  case Instruction::Select: {
    nl() << "auto " << ValName << " = IRB.CreateSelect(" << OpNames[0] << ", "
         << OpNames[1] << ", " << OpNames[2] << lastNameArg(I);
    return;
  }
  case Instruction::UserOp1:
  case Instruction::UserOp2: {
    /// FIXME: What should be done here?
    break;
  }
  case Instruction::VAArg: {
    nl() << "auto " << ValName << " = IRB.CreateVAArg(" << OpNames[0] << ", "
         << ValTyName << lastNameArg(I);
    return;
  }
  case Instruction::ExtractElement: {
    nl() << "auto " << ValName << " = IRB.CreateExtractElement(" << OpNames[0]
         << ", " << OpNames[1] << lastNameArg(I);
    return;
  }
  case Instruction::InsertElement: {
    nl() << "auto " << ValName << " = IRB.CreateInsertElement(" << OpNames[0]
         << ", " << OpNames[1] << ", " << OpNames[2] << lastNameArg(I);
    return;
  }
  case Instruction::ShuffleVector: {
    nl() << "auto " << ValName << " = IRB.CreateShuffleVector(" << OpNames[0]
         << ", " << OpNames[1] << ", " << OpNames[2] << lastNameArg(I);
    return;
  }
  case Instruction::ExtractValue: {
    auto EVI = cast<ExtractValueInst>(I);
    auto Idxs = std::string("{");
    for (auto i : EVI->indices())
      Idxs += utostr(i) + ", ";
    Idxs = StringRef(Idxs).drop_back(2).str() + "}";
    cl() << "auto " << ValName << " = IRB.CreateExtractValue(" << OpNames[0]
         << ", " << Idxs << lastNameArg(I);
    return;
  }
  case Instruction::InsertValue: {
    auto IVI = cast<InsertValueInst>(I);
    auto Idxs = std::string("{");
    for (auto i : IVI->indices())
      Idxs += utostr(i) + ", ";
    Idxs = StringRef(Idxs).drop_back(2).str() + "}";
    cl() << "auto " << ValName << " = IRB.CreateInsertValue(" << OpNames[0]
         << ", " << OpNames[1] << ", " << Idxs << lastNameArg(I);
    return;
  }
  case Instruction::Fence: {
    auto FI = cast<FenceInst>(I);
    auto Ordering = getAtomicOrdering(FI->getOrdering());
    auto Scope = getAtomicSynchScope(FI);
    nl() << "auto " << ValName << " = IRB.CreateFence(" << Ordering << ", "
         << Scope << lastNameArg(I);
    return;
  }
  case Instruction::LandingPad: {
    auto LPI = cast<LandingPadInst>(I);
    nl() << "auto " << ValName << " = IRB.CreateLandingPad(" << ValTyName
         << ", " << LPI->getNumClauses() << lastNameArg(I);
    if (LPI->isCleanup())
      nl() << ValName << "->setCleanup(true);";
    for (unsigned i = 0, e = LPI->getNumClauses(); i != e; ++i)
      nl() << ValName << "->addClause("
           << getOperandName(LPI->getClause(i), Refs) << ");";
    nl();
    return;
  }
  case Instruction::AtomicCmpXchg: {
    auto CXI = cast<AtomicCmpXchgInst>(I);
    auto SuccOrd = getAtomicOrdering(CXI->getSuccessOrdering());
    auto FailOrd = getAtomicOrdering(CXI->getFailureOrdering());
    auto SyncScope = getAtomicSynchScope(CXI);
    nl() << "auto " << ValName << " = IRB.CreateAtomicCmpXchg(" << OpNames[0]
         << ", " << OpNames[1] << ", " << OpNames[2] << ", " << SuccOrd << ", "
         << FailOrd << ", " << SyncScope << ");";
    if (I->hasName())
      nl() << ValName << "->setName(" << Literally(I->getName()) << ");";
    if (CXI->isVolatile())
      nl() << ValName << "->setVolatile(true);";
    if (CXI->isWeak())
      nl() << ValName << "->setWeak(true);";
    nl();
    return;
  }
  case Instruction::AtomicRMW: {
    auto RMWI = cast<AtomicRMWInst>(I);
    auto Ordering = getAtomicOrdering(RMWI->getOrdering());
    auto SyncScope = getAtomicSynchScope(RMWI);
    auto Operation = getRMWBinOp(RMWI->getOperation());
    nl() << "auto " << ValName
         << " = IRB.CreateAtomicRMW(AtomicRMWInst::" << Operation << OpNames[0]
         << ", " << OpNames[1] << ", " << Ordering << ", " << SyncScope << ");";
    if (I->hasName())
      nl() << ValName << "->setName(" << Literally(I->getName()) << ");";
    if (RMWI->isVolatile())
      nl() << ValName << "->setVolatile(true);";
    nl();
    return;
  }
  case Instruction::AddrSpaceCast: {
    nl() << "auto " << ValName << "IRB.CreateAddrSpaceCast(" << OpNames[0]
         << ", " << ValTyName << lastNameArg(I);
    return;
  }
  case Instruction::CleanupRet: {
    nl() << "IRB.CreateCleanupRet(" << OpNames[0] << ", " << OpNames[1] << ");";
    nl();
    return;
  }
  case Instruction::CatchRet: {
    nl() << "IRB.CreateCatchRet(" << OpNames[0] << ", " << OpNames[1] << ");";
    nl();
    return;
  }
  case Instruction::CatchPad: {
    auto CPI = cast<CatchPadInst>(I);
    nl() << "auto " << ValName << " = IRB.CreateCatchPad("
         << getOperandName(CPI->getParentPad(), Refs) << ", "
         << getArgOperands(CPI->arg_operands()) << lastNameArg(I);
    return;
  }
  case Instruction::CleanupPad: {
    auto CPI = cast<CleanupPadInst>(I);
    nl() << "auto " << ValName << " = IRB.CreateCleanupPad("
         << getOperandName(CPI->getParentPad(), Refs) << ", "
         << getArgOperands(CPI->arg_operands()) << lastNameArg(I);
    return;
  }
  case Instruction::CatchSwitch: {
    auto CSI = cast<CatchSwitchInst>(I);
    nl() << "auto " << ValName << " = IRB.CreateCatchSwitch("
         << getOperandName(CSI->getParentPad(), Refs) << ", ";
    if (CSI->hasUnwindDest())
      cl() << DefNames.get(CSI->getUnwindDest());
    else
      cl() << "nullptr";
    cl() << ", " << CSI->getNumHandlers() << lastNameArg(I);
    for (auto BB : CSI->handlers())
      nl() << ValName << "->addHandler(" << DefNames.get(BB) << ");";
    nl();
    return;
  }
  default:
    report_fatal_error("unknow instruction!");
  }
}

void CxxApiWriterPass::printFunctionHead(const Function *F) {
  nl();
  auto Name = DefNames.get(F);
  if (F->isDeclaration()) {
    if (F->isIntrinsic()) {
      nl() << "// llvm intrinsic";
    } else {
      nl() << "// external";
    }
    if (hasAnyArgAttribute(F))
      cl() << ", has arg attrs";
    if (F->hasPersonalityFn())
      cl() << ", has personalityfn";
  }
  nl() << "auto " << Name << " = Function::Create("
       << DefNames.get(F->getFunctionType()) << ", " << getLinkageType(F)
       << ", " << Literally(F->getName()) << ", M.get());";
}

void CxxApiWriterPass::printFunctionAttr(const Function *F) {
  auto Name = DefNames.get(F);
  if (F->getCallingConv()) {
    nl() << Name << "->setCallingConv(" << getCallingConv(F) << ");";
  }
  if (F->hasSection()) {
    nl() << Name << "->setSection(" << Literally(F->getSection()) << ");";
  }
  if (F->getAlignment()) {
    nl() << Name << "->setAlignment(" << F->getAlignment() << ");";
  }
  if (F->getVisibility() != GlobalValue::DefaultVisibility) {
    nl() << Name << "->setVisibility(" << getVisibilityType(F) << ");";
  }
  if (F->getDLLStorageClass() != GlobalValue::DefaultStorageClass) {
    nl() << Name << "->setDLLStorageClass(" << getDLLStorageClassType(F)
         << ");";
  }
  if (F->hasGC()) {
    nl() << Name << "->setGC(" << Literally(F->getGC()) << ");";
  }
  if (F->hasComdat()) {
    nl() << Name << "->setComdat(M->getOrInsertComdat(";
    if (F->getName() == F->getComdat()->getName()) {
      cl() << Name << "->getName()));";
    } else {
      cl() << "" << Literally(F->getComdat()->getName()) << ")));";
    }
  }
#if !LLVM_VERSION_BEFORE(6, 0, 1)
  if (F->isDSOLocal()) {
    nl() << Name << "->setDSOLocal(true);";
  }
#endif
#if !LLVM_VERSION_BEFORE(3, 9, 1)
  if (F->hasAtLeastLocalUnnamedAddr()) {
    auto UA = F->hasGlobalUnnamedAddr() ? "Global);" : "Local);";
    nl() << Name << "->setUnnamedAddr(GlobalValue::UnnamedAddr::" << UA;
  }
#endif
  if (F->hasPersonalityFn()) {
    nl() << Name << "->setPersonalityFn(" << DefNames.get(F->getPersonalityFn())
         << ");";
  }
  printAttributes(F, Name);
  nl();

  // Create all the argument values
  if (!F->arg_empty()) {
    nl() << "SmallVector<Argument *, " << F->getFunctionType()->getNumParams()
         << "> Args;";
    nl() << "for (auto &Arg : " << Name << "->args())";
    indent();
    nl() << "Args.push_back(&Arg);";
    outdent();
    nl();

    unsigned ArgNr = 0;
    for (auto &AI : F->args()) {
      auto AiName = "Args[" + utostr(ArgNr) + "]";
      DefNames.set(&AI, AiName);
      if (AI.hasName())
        nl() << AiName << "->setName(" << Literally(AI.getName()) << ");";
      printAttributes(&AI, AiName);
      ArgNr++;
    }
  }
}

void CxxApiWriterPass::printFunctionBody(const Function *F) {
  printFunctionAttr(F);

  if (F->isDeclaration())
    return;

  // Create all the basic blocks
  nl() << "// BasicBlocks";
  for (auto &BI : F->getBasicBlockList()) {
    auto BBName = DefNames.get(&BI);
    nl() << "auto " << BBName << " = BasicBlock::Create(Ctx, "
         << Literally(BI.getName()) << ", " << DefNames.get(F) << ");";
  }

  // Record undef refrences
  ValueMap ForwardRefs;

  // Output all of its basic blocks... for the function
  for (auto &BI : F->getBasicBlockList()) {
    auto BBName = DefNames.get(&BI);
    nl();
    nl() << "//";
    nl() << "// BasicBlock " << BI.getName() << " (" << BBName << ")";
    nl() << "IRB.SetInsertPoint(" << BBName << ");";
    for (auto &I : BI.getInstList())
      printInstruction(&I, ForwardRefs);
  }

  // Loop over the ForwardRefs and resolve them now that all instructions
  // are generated.
  if (!ForwardRefs.empty()) {
    nl();
    nl() << "// Resolve Forward References";
    for (auto &Ref : ForwardRefs) {
      auto Name = DefNames.get(Ref.first);
      nl() << "Ref" << Name << "->replaceAllUsesWith(" << Name << ");";
    }
  }
}

void CxxApiWriterPass::printModuleBody() {
  // Print moudle inline asm if has
  if (!TheModule->getModuleInlineAsm().empty()) {
    nl() << "//";
    nl() << "// Module InlineAsm";
    nl() << "//";
    nl() << "M->setModuleInlineAsm("
         << Literally(TheModule->getModuleInlineAsm()) << ");";
  }

  // Print out all the type definitions
  printTypes(TheModule);

  // Functions can call each other and global variables can reference them
  // so define all the functions first before emitting their function
  // bodies.
  if (!TheModule->empty()) {
    nl();
    nl() << "//";
    nl() << "// Function Declarations";
    nl() << "//";
    for (auto &F : TheModule->functions())
      if (!isCommonIntrinsic(&F))
        printFunctionHead(&F);
  }

  // Process the global variables declarations. We can't initialze them
  // until after the constants are printed so just print a header for each
  // global
  if (!TheModule->getGlobalList().empty()) {
    nl() << "//";
    nl() << "// Global Variable Declarations";
    nl() << "//";
    for (auto &G : TheModule->globals())
      printVariableHead(&G);
  }

  // Print out all the constants definitions. Constants don't recurse
  // except through GlobalValues. All GlobalValues have been declared at
  // this point so we can proceed to generate the constants.
  printConstants(TheModule);

  // Process the global variables definitions now that all the constants
  // have been emitted. These definitions just couple the gvars with their
  // constant initializers.
  if (!TheModule->getGlobalList().empty()) {
    nl();
    nl() << "//";
    nl() << "// Global Variable Definitions";
    nl() << "//";
    for (auto &G : TheModule->globals())
      printVariableBody(&G);
  }

  // Finally, we can safely put out all of the function bodies.
  if (!TheModule->empty()) {
    nl();
    nl() << "//";
    nl() << "// Function Definitions";
    nl() << "//";
    for (auto &F : TheModule->functions()) {
      if (!F.isDeclaration() ||
          (hasAnyArgAttribute(&F) && !isCommonIntrinsic(&F))) {
        nl() << "// Function: " << F.getName();
        nl() << "if (" << DefNames.get(&F) << ") {";
        indent();
        printFunctionBody(&F);
        outdent();
        nl() << "}";
        nl();
      }
    }
  }
}

bool CxxApiWriterPass::runOnModule(Module &M) {
  TheModule = &M;

  nl();
  nl() << "#include <llvm/ADT/STLExtras.h>";
  nl() << "#include <llvm/IR/IRBuilder.h>";
  nl() << "#include <llvm/IR/InlineAsm.h>";
  nl() << "#include <llvm/IR/Module.h>";
  nl() << "#include <llvm/IR/TypeBuilder.h>";
  nl() << "#include <llvm/IR/Verifier.h>";
  nl() << "#include <llvm/Support/raw_ostream.h>";
  nl();
  nl() << "#if (LLVM_VERSION_MAJOR != " << LLVM_VERSION_MAJOR
       << " || (LLVM_VERSION_MINOR != " << LLVM_VERSION_MINOR << "))";
  nl() << "#pragma message(\"\\nwarning : may not be compatible with this LLVM "
          "version.\\n\")";
  nl() << "#endif";
  nl();
  nl() << "using namespace llvm;";
  nl();
  nl() << "std::unique_ptr<Module> makeLLVMModule(LLVMContext &);";
  nl();
  nl() << "int main(int argc, char **argv) {";
  nl() << "  LLVMContext Ctx;";
  nl();
  nl() << "  auto M = makeLLVMModule(Ctx);";
  nl() << "  if (verifyModule(*M)) {";
  nl() << "    errs() << \"Error: module failed verification.\";";
  nl() << "    return 1;";
  nl() << "  }";
  nl();
  nl() << "  outs() << *M;";
  nl() << "  return 0;";
  nl() << "}";
  nl();
  nl() << "std::unique_ptr<Module> makeLLVMModule(LLVMContext &Ctx) {";
  indent();
  nl() << "auto M = llvm::make_unique<Module>("
       << Literally(M.getModuleIdentifier()) << ", Ctx);";
  nl() << "M->setDataLayout(" << Literally(M.getDataLayoutStr()) << ");";
  nl() << "M->setTargetTriple(" << Literally(M.getTargetTriple()) << ");";
  nl();
  nl() << "IRBuilder<> IRB(Ctx);";
  nl();

  printModuleBody();

  nl() << "return M;";
  outdent();
  nl() << "}";
  nl();

  return false;
}

char CxxApiWriterPass::ID = 0;

namespace llvm {
ModulePass *createCxxApiWriterPass(raw_ostream &OS, bool PrintIR, bool Short) {
  return new CxxApiWriterPass(OS, PrintIR, Short);
}
} // namespace llvm
