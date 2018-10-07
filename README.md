llvm-cxxapi
========

Resurrected LLVM "Cpp Backend", rebuild as a LLVM tool, with better compatibility and readability.


INSTALLATION INSTRUCTIONS
=========================

The `llvm-cxxapi` tool works with LLVM 3.7 ~ 6.0. You will have to compile these version of LLVM before you try to use `llvm-cxxapi`. This guide will walk you through the compilation and installation of both tools and show usage statements to verify that the `llvm-cxxapi` tool is compiled correctly.

The library is known to compile on various Linux versions (Redhat, Ubuntu), Mac OS X, and Windows (MSVC、Mingw-w64).

Step 1: Clone LLVM and llvm-cxxapi
=======================

The `llvm-cxxapi` relies on specific LLVM librarys, and so it is best to use it with a specific revision of the LLVM development tree. Currently, `llvm-cxxapi` works with the LLVM 3.7 ~ 6.0 release versions.

If you have never work with LLVM, the first step is to download LLVM on your machine.

    cd $HOME
    git clone https://github.com/llvm-mirror/llvm
    cd llvm
    git checkout release_50

Download `llvm-cxxapi`

    cd $HOME/llvm/projects
    git clone git@github.com:zhangjiantao/llvm-cxxapi.git

Step 2: Building
==========================

Now you can build the LLVM project, and the build target already contains `llvm-cxxapi`

    cd $HOME/llvm/
    mkdir build && cd build
    cmake -G Ninja ..
    ninja all

Step 3: Usage Examples
======================

If `llvm-cxxapi` compiles, you should be able to run it with the following commands.

```
$ cd $ANYWHERE

$ echo "int test(int a) { return (((a ^ 4) * 3) ^ 2) + 1;}" > test.c

$ $HOME/llvm/bin/clang -emit-llvm -S -O3 test.c

$ $HOME/llvm/bin/llvm-cxxapi test.ll -o test.ll.cpp
```

Or use pipe

```
$ alias clang=$HOME/llvm/bin/clang

$ alias cxxapi=$HOME/llvm/bin/llvm-cxxapi

$ echo "int test(int a) { return (((a ^ 4) * 3) ^ 2) + 1;}" | clang -x c - -emit-llvm -S -O3 -o - | cxxapi -o test.ll.cpp
```

Now you get C++ program to generate the IR of function f, such as

```c++
IRBuilder<> IRB(Ctx);

auto FuncTy = TypeBuilder<int32_t(int32_t), false>::get(Ctx);
auto FuncTest = Function::Create(FuncTy, GlobalValue::ExternalLinkage, "test", M);

// Function: test
if (1) {
  FuncTest->setCallingConv(CallingConv::C);
  FuncTest->setUnnamedAddr(GlobalValue::UnnamedAddr::Local);
  FuncTest->addFnAttr(Attribute::NoRecurse);
  FuncTest->addFnAttr(Attribute::NoUnwind);
  FuncTest->addFnAttr(Attribute::ReadNone);
    
  SmallVector<Argument *, 1> Args;
  for (auto &Arg : FuncTest->args())
    Args.push_back(&Arg);
    
  // BasicBlocks
  auto Block = BasicBlock::Create(Ctx, "", FuncTest);
  
  // BasicBlock  (Block)
  IRB.SetInsertPoint(Block);
  auto XorInt32t = IRB.CreateXor(Args[0], IRB.getInt32(4));
  auto MulInt32t = IRB.CreateMul(XorInt32t, IRB.getInt32(3), "", false, true);
  auto XorInt32t1 = IRB.CreateXor(MulInt32t, IRB.getInt32(2));
  auto AddInt32t = IRB.CreateAdd(XorInt32t1, IRB.getInt32(1), "", false, true);
  IRB.CreateRet(AddInt32t);
}
```

Compile Generated C++ Code and Run
================================
```

$ clang++ `llvm-config --cxxflags` -o test.ll.o -c test.ll.cpp

$ clang++ `llvm-config --ldflags` -o testcxx test.ll.o `llvm-config --libs core support`

$ ./testcxx
```
