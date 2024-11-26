#ifndef LLVM_TRANSFORMS_CXLMCPASS_H
#define LLVM_TRANSFORMS_CXLMCPASS_H

#include "llvm/IR/PassManager.h"

namespace llvm {

class CXLMCWrapperPass : public PassInfoMixin<CXLMCWrapperPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);

  static bool isRequired() { return true; }
};

}

#endif //LLVM_TRANSFORMS_CXLMCPASS_H
