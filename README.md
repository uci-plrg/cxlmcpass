# CXLMC LLVM Pass
This is an instrumentation pass for the CXLMC model checker built on LLVM 20.

# Build Instructions
Assuming CXLMCHOME is set to your working directory
```
export CXLMCHOME=/path/to/your/directory
```
First download the llvm source code and compile our llvm pass with:
```
	$ cd $CXLMCHOME
	# Download LLVM Source Code
	$ git clone https://github.com/llvm/llvm-project.git
	$ cd llvm-project
	$ git checkout e14827f0828d14ef17ab76316e8449d1b76e2617 
	$ cd ..
	# Download CXLMC LLVM Pass Source Code
	$ git clone https://github.com/uci-plrg/cxlmcpass.git
	# Compile CXLMC Pass
	$ mv CXLMCPass llvm-project/llvm/lib/Transforms/
    $ echo "add_subdirectory(CXLMCPass)" >> llvm-project/llvm/lib/Transforms/CMakeLists.txt
    $ cd llvm-project
    $ mkdir build
    $ cd build
    $ cmake -DLLVM_ENABLE_PROJECTS=clang -DCMAKE_BUILD_TYPE=Release -G "Unix Makefiles" ../llvm
    $ make -j 4
```
The pass will be built as a dynamic library. To run it in clang's compilation pipeline, 
load the library as a plugin. For example, to compile a program `test.c`, do 
```
	BUILD=${CXLMCHOME}/llvm-project/build
	${BUILD}/bin/clang++ -fpass-plugin=${BUILD}/lib/CXLMCPass.so test.c
``` 
For the compilation to succeed, the program needs to include the CXLMC API header files. 

To examine the intrumented LLVM IR, run the following:
```
	${BUILD}/bin/clang++ -fpass-plugin=${BUILD}/lib/CXLMCPass.so -emit-llvm -S test.c
```
This does not require the API header files. 
