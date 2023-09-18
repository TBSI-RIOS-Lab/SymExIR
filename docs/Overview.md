# LLVMSymEx

## Introduction

本文档主要是为了开发者简介LLVMSymEx项目的设计思路与细节。本文将从三个方面介绍LLVMSymEx的整体结构与细节：（1）设计目的与功能实现；（2）设计模块概述；（3）LLVMSymEx实现方法。

## 设计目的与功能实现

LLVMSymEx的产生目的是为了在静态环境下，验证BB块维度下的指令实际执行结果是否与LLVM中的指令预期执行结果相同。在LLVM IR向最终指令集相关的汇编代码生成过程中，编译器将针对特定平台对LLVM IR进行各类优化与实现，这会导致生成的汇编指令不是IR指令的一一对应，LLVMSymEx能够帮助编译器开发者验证指令转译等过程是否出现错误，辅助开发者快速验证编译器生成结果的正确性。

而由于实现的难度与验证范围当前的需求，LLVMSymEx的验证目标集中在BB块内部，即仅对同时存在一个相同的BB块内部的指令执行结果进行验证，同时由于验证信息条件的限制，所有被验证的LLVM指令都是以load指令作为开始。并且，LLVMSymEx的输入对象需要通过dependence graph验证保证内部指令的完整性，即参与分析的LLVM IR是具备内部逻辑完整性的，也就是除需要通过load加载的IR指令value对象外，所有参与验证的IR指令涉及到的对象都应由BB块内部指令通过运算产生。

综上，如果需要通过LLVMSymEx对指令执行结果进行验证，参与验证的IR指令与指令执行结果是必不可少的。

### 验证IR指令要求

所有参与验证的IR指令需要满足两个条件：(1) 能够通过符号执行进行模拟验证；(2) 指令中含有的变量都能被追溯。但需要明确的是，并非所有的IR指令都能够被验证，这主要是因为验证计算所使用的符号执行引擎的限制。尽管当前的符号执行引擎能够完成运算，但其能力是有限的。以目前最为流行的Z3符号执行工具为例，它提供的运算方法也是有限的，无法覆盖LLVM所有的计算对象。例如Function Call，执行引擎无法对其进行实现。这不仅是因为Function Call自身已超过了BB块范围，还因为通过符号执行对Function Call结果进行模拟的成本是巨大的。

在LLVMSymEx能够进行验证的范围内，所有参与运算的变量都需要有一个确定的数据来源。也就是说，每一个变量的具体数值只有两种来源：一是来自load类指令通过配置文件加载，二是通过符号执行对LLVM IR进行模拟运算获取计算结果。这就要求在将模拟对象传入LLVMSymEx之前，需要对其进行完备性检查。而LLVMSymEx自身也会在运行期间对其进行动态的检查，以确保所有变量都能被追溯。

### 指令执行结果

执行指令的结果需要与LLVMSymEx模拟生成的结果进行验证，以确保两者的一致性。LLVMSymEx的模拟是基于静态实现的，因此无法完全模拟LLVM IR，特别是与内存读写相关的部分，以及LLVM内置的特殊类型（如posion type，aggregate type）和普通函数返回值等等。
为此，在验证结果时，部分指令执行结果并不是简单地作为验证结果传入，而是作为相应的加载信息传入，并不进行相应的结果对比。同时，这部分LLVM IR指令也不会参与模拟计算过程，而是直接参照LLVM IR中的类型固定为一个确定的符号执行变量。
需要注意的是，这种验证方法仅是针对LLVMSymEx的静态实现模拟，其与实际执行结果可能仍然存在一定差异。因此，在执行指令时，需要对验证结果进行适当的分析和评估。

## 设计模块

从实现的角度来看，LLVMSymEx被划分为三个不同的模块，这些模块分别是验证数据读取模块、指令模拟转换模块和结果验证模块。这个分解是为了使得整个系统更具可读性和可维护性。下面对这三个模块进行详细说明：

1. 验证数据读取模块：该模块的主要任务是读取预设数据，这些预设数据包括验证LLVM IR指令和验证数据。预设数据需要按照格式进行读取，以确保数据的正确性和完整性。
2. 指令模拟转换模块：该模块的主要任务是将LLVM IR指令转换为符号执行引擎的相应指令。这些转换后的指令将成为后续结果验证模块的输入。该模块的设计是为了确保符号执行引擎语句的正确性和完整性。
3. 结果验证模块：该模块的主要任务是获取符号执行引擎计算结果，并将结果与验证值进行比较，以检验结果是否一致。该模块的设计是为了保证结果的正确性和完整性，同时也需要考虑结果的可读性和可维护性。

通过以上的模块分解，整个系统的实现变得更加清晰和可靠。同时也为未来的系统扩展和维护提供了更好的支持。

## LLVMSymEx实现方法

由于需要在不真实运行程序的情况下获取指令运行的结果，LLVMSymEx选取符号执行作为最重要的实现方法。通过将LLVM IR转换成相应的符号执行引擎语句。所谓的符号执行引擎在LLVMSymEx中特指约束求解器（Constraint solver），solver能够通过添加约束对数学多个维度（实数，向量，浮点数）的问题进行运算求解，能够承担LLVMSymEx的大部分运算任务。

LLVMSymEx采取的约束求解器为[Z3](https://github.com/Z3Prover/z3)，Z3在被Microsoft提出后，获得广泛应用，其具备几个方面的优点：运算领域广，语言api种类多与运算类型实现广泛。

通过手工对LLVM IR与SMT Solver语句进行匹配，例如IR中常见的`add` operation与Z3求解器中的<code>ADD</code>或`FADD`存在对应关系，可以在合适的条件下进行transfer或者lowering。还有许多其他的例子，如LLVM IR中的`urem`也与`z3.UREM`能起到相似的作用。

在对LLVM IR指令进行转换并存储后，就能对其计算结果进行验证。而在结果验证阶段，LLVMSymEx并不不会保留长线条的计算过程，而是会在对计算结果进行验证后，将LLVM IR计算结果直接替换成应当验证的数值。这样的做法能够充分地利用验证的数据，不只能避免因为过长的计算路径带来的时间负担，同时也可以避免由于长链条的浮点计算引入越来愈大的误差。

### 目前支持的数据类型与指令范围

由于实现的复杂性与可行性，目前的LLVMSymEx能够支持的数据类型与指令（及LLVM内置函数）是有限的，并未做到完全支持。下面对其进行简介：

首先需要明确的是，目前的LLVMSymEx支持进行计算的主要为LLVM Single Value Types，其中包括各类基础类型（i1..., f32...,ptr and etc.）及vector type与小部分Aggregate Types。
以下的指令为全部按照LLVM instruction设计要求实现，通过测试验证了执行结果的一致性。

```llvm
    "fneg",
    "add",
    "fadd",
    "sub",
    "fsub",
    "mul",
    "fmul",
    "udiv",
    "sdiv",
    "fdiv",
    "urem",
    "srem",
    "frem",
    "shl",
    "lshr",
    "ashr",
    "and",
    "or",
    "xor",
    "extractelement",
    "insertelement",
    "shufflevector",
    "cmpxchg",
    "atomicrmw",
    "trunc",
    "zext",
    "sext",
    "fptrunc",
    "fpext",
    "fptoui",
    "fptosi",
    "uitofp",
    "sitofp",
    "ptrtoint",
    "inttoptr",
    "bitcast",
    "icmp",
    "fcmp",
    "select",
```

`load`指令的实现则有些特殊，这是因为在实现上我们需要通过`load`指令加载预设置的数据，推动验证过程，所以`load`虽然提供了支持，但更加侧重于实现预设值到程序验证值的转换过程。

以下的执行指令并没纳入实现过程，也无法进行数值的验证，这是因为这些指令都归属于Terminator Instructions。这些指令超出了BB块的验证范围，也没有计算的功能实现。

```llvm
    "ret",
    "br",
    "switch",
    "indirectbr",
    "invoke",
    "callbr",
    "resume",
    "catchswitch",
    "catchret",
    "cleanupret",
    "unreachable",
```

针对以下的指令LLVMSymEx虽然并不提供验证能力，但仍然提供输入数据转换的能力，以保证整体的验证过程执行完整。原因是这些指令都与struct Type有关，超出了目前的实现范围。

```llvm
    "insertvalue",
    "extractvalue",
```

以下的执行指令并没纳入实现过程，也无法进行数值的验证，这是因为这些指令都归属于Memory Types。由于LLVMSymEx归属于静态验证工具，无法实际与内存进行交互，所有这些指令都完全无法实现。

```llvm
    "alloca",
    "store",
    "fence",
    "getelementptr",
```

以下的执行指令并没纳入实现过程，也无法进行数值的验证，这是因为这些指令与多线程实现或高级语言的异常实现有关，与计算过程无关，也不存在需要验证的数据。

```llvm
    "freeze",
    "va_arg",
    "landingpad",
    "catchpad",
    "cleanuppad",
```

`call`指令的实现也是非常具有特点的，当前LLVMSymEx中的`call`指令仅能实现部分LLVM Intrinsic Functions的返回值处理，也就是下面展示的这些。而与LLVM Intrinsic Functions无关的`call`指令则是完全无法实现，当然也不能提供数值的验证，但针对部分返回值为LLVM内置类型的指令而言，LLVMSymEx也提供了外部数据的转换能力，加强数值验证的完整性。需要强调的是，LLVM存在大量的内置函数与内存，指令集与复杂数据类型有关，超出了目前的支持范围，但在未来会尽可能地提供更加丰富的支持。

```llvm
    "llvm.abs",
    "llvm.smax",
    "llvm.umax",
    "llvm.smin",
    "llvm.umin",
    "llvm.sqrt",
    "llvm.fma",
    "llvm.fabs",
    "llvm.minnum",
    "llvm.maxnum",
    "llvm.minimum",
    "llvm.maximum",
    "llvm.llrint",
    "llvm.sin",
    "llvm.cos",
    "llvm.exp",
    "llvm.exp2",
    "llvm.log",
    "llvm.log10",
    "llvm.log2",
    "llvm.ldexp",
    "llvm.floor",
    "llvm.ceil",
    "llvm.trunc",
    "llvm.nearbyint",
    "llvm.round",
```

### Float Value Tolerance

由于浮点数计算的精确结果会因为浮点数的精度，执行程序的编写与执行计算单元的架构设计而发生变化。LLVMSymEx的计算依赖SMT Solver同样会因为以上的原因而产生波动，这些波动是需要在验证浮点数过程中纳入考虑的。LLVMSymEx为其做出了两点努力，一是，在验证时将允许一定的浮点数误差；二是，在单个value在验证结束后，将其替换成一个固定的数字，阻断过长的计算链条而带来不断越来越大的计算误差。

### 当前程序的不足与约束

虽然LLVMSymEx提供了高精度的指令符号执行和获取结果的功能，但仍存在以下几个明显的使用限制。首先，它仍然只能处理BB块内部的指令模拟，由于未能针对整体变量进行实现，所有的模拟维度都需要在一个BB块内完成；其次，目前尚未支持过于复杂的数据结构，在LLVM内部，Aggarate Data与Pioson Data的使用占据了一定数量，但由于其复杂性，LLVMSymEx目前尚未支持。第三，无法显示与内存交互的相关指令或操作，这是受制于LLVMSymEx是一个静态工具，无法真实运行程序，更无法真正实现与内存的交互。

## 执行过程详解

在这一章节，我们通过例子对LLVMSymEx的具体实现与执行过程进行一下更加详细的解释，LLVMSymEx会维护一个smt_block用来存储进行验证与计算的数据列表。

### 无法进行计算的指令

LLVM中存在许多与真实内存相关联的指令，超出了LLVMSymEx当前的验证范围。但LLVMSymEx仍需要提供对这些指令结果的传入操作，以满足正常数据运算流的完整性。这里以`load`为例。

当LLVMSymEx对指令`%1 = load i32, i32* %5, align 8, !tbaa !4`与数据`1`进行数据读取与验证时，因为`load`指令不在验证的范围内，LLVMSymEx将直接按照指令中指定的数据类型`i32`将指令对应的value`%1`在smt_block中存储成为`z3.BitVecVal(1, 32)`, 其中的1指示了数据具体值，32指示了数据对应的位长。

### 计算验证的指令

LLVMSymEx能够在静态的环境下，对LLVM内部的许多指令进行模拟计算，并与传入的真实验证数据进行对比，验证LLVM指令运行的正确性。这里以`add`指令为例。

假设LLVMSymEx将继续读取下一条指令`%2 = add i32 2, %1`与验证值`3`， LLVMSymEx将根据`add`的指令类型与操作数种类进行不同的处理。在示例`add`中，分别存在operand1`2`与`%1`，LLVMSymEx会将具体数字`2`同样转换为z3求解器的内置类型`z3.BitVecVal(2, 32)`，而根据`%1`所代表的操作数名称在smt_block中搜索并获取对应的z3数据变量。而后LLVMSymEx将会把利用求解器的计算指令将两个操作数进行计算，在`add`指令与`i32`的背景下，对应的计算操作也就是`z3.BitVec.add()`。随后，LLVMSymEx将验证值`3`也转换成为`i32`对应的z3变量`z3.BitVecVal(2, 32)`，并与计算操作的返回值进行比对，验证结果正确性，如果结果正确就会进行下一个指令的操作，如果结果不正确，则将立即退出验证过程，并返回错误相关信息。

而考虑到求解器内部实现与真实架构存在差异且float等高精度数据类型的计算存在不同的近似方法，为了避免会因误差传递导致最终计算结果失效，LLVMSymEx将会在每次指令验证结果正确时，利用验证数据替换掉对应指令的计算结果。例如在上面的`add`验证结束后，LLVMSymEx会在存在smt_block中的`z3.BitVec.add()`计算结果替换成验证值`3`转换来的z3变量`z3.BitVecVal(3, 32)`。

## 暂定文件读取形式

LLVMSymEx暂时提供了一个固定的文件读取形式，由于验证功能的执行需要两部分的信息，一部分来来自需要验证的LLVM代码，另外一部分，来自于需要参与验证的数据。在加载的数据中，除了load等无法参与验证的指令外对应的数据都不是必须的，如果验证指令对应的数据缺省，验证过程就不会执行，但同时也不会对应数值的替换。
综上，LLVMSymEx的输入文件包括为两个部分，一个包含LLVM指令，另外一个包含验证数据。
其中，包含LLVM指令的文件需要包括一个完整的运算逻辑链，也就是说通常情况下，指令输入文件需要以`load`指令作为开始，并且在计算过程中不存在所需数值的缺失。LLVMSymEx在运算及验证过程中也会不断地进行相应的检查，如果出现缺失，则整个验证过程将完全无法继续进行。下面给出了一个简单的LLVM指令输入文件，值得注意的是这个输入是完备的，计算逻辑链也是完整的。

```llvm
    %1 = load i32, i32* %5, align 8, !tbaa !4
    %6 = load i32, i32* %5, align 8, !tbaa !4
    %7 = add i32 %6, %1
    %9 = load i32, i32* %8, align 8, !tbaa !4
    %10 = add i32 %9, %1
    %11 = mul i32 %10, %1
    %12 = udiv i32 %10, %1
    %13 = sub i32 %10, %1
    %14 = add i32 %10, %1
    %15 = urem i32 %10, %1
    %16 = icmp ne i32 %14, %15
    %17 = and i32 %12, %14
    %18 = or i32 %12, %14
    %19 = xor i32 4, %14
    %20 = xor i64 4, 1
    %21 = xor i32 4, 1
    %22 = xor i1 0, 1
```

下面的则是验证数据，左侧一列的标志着对应value在LLVM验证文件的对应位置，右侧则是对应的验证数据，目前能够进行验证的数据形式包括integer, float, vector of integer and float.

```txt
    0, "1"
    1, "1"
    2, "2"
    3, "300"
    4, "301"
    5, "301"
    6, "301"
    7, "300"
    8, "302"
    9, "0"
    10, "0"
    11, "300"
    12, "303"
    13, "298"
    14, "5"
    15, "5"
    16, "1"
```

## LLVMSymEx的使用

当前LLVMSymEx的使用方法非常简单，假设已经安装好了运行所需的python环境（requirements.txt），使用者仅需通过`--instrfile`指定验证的LLVM instruction文件，通过`--assertfile`指定验证所需的文件。

```shell
python main.py --instrfile ../test/llvm_instr_1.txt --assertfile ../test/assert_info_1.txt
```

同时也可以通过`--dump`命令打印出验证执行的结果，如下所示：

```shell
%1 1
%6 1
%7 2
%9 300
%10 301
%11 301
%12 301
%13 300
%14 302
%15 0
%16 0
%17 300
%18 303
%19 298
%20 5
%21 5
%22 1
Verify success!
```

当然也可以通过`--help`或者`-h`获取命令帮助：
```shell
$ python main.py -h

usage: main.py [-h] [--instrfile INSTRFILE] [--assertfile ASSERTFILE] [--dumpinfo]

options:
  -h, --help            show this help message and exit
  --instrfile INSTRFILE
                        To specify llvm instrs file path
  --assertfile ASSERTFILE
                        To specify assert info file path
  --dumpinfo            To dump the info from verify proccess
```

## TODO

目前的LLVMSymEx已经能够初步使用，但仍然存在以下几个能够改进的方向：

1. 丰富LLVMSymEx的使用手册。
2. 添加更多的测试用例。
3. 实现对数组的完整支持。
4. 在保证精度的背景下，实现更多对LLVM Intrinsic Functions的支持。

## Reference

1. https://qemu.readthedocs.io/en/latest/devel/tracing.html
