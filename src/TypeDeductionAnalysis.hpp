#pragma once

#include "Containers/InsertionOrderedMap.hpp"
#include "TransparentType.hpp"

#include <llvm/IR/Instructions.h>
#include <llvm/IR/PassManager.h>

#include <unordered_set>

namespace tda {

using TypeAliasSet = std::unordered_set<std::unique_ptr<TransparentType>>;

class TypeDeductionAnalysis : public llvm::AnalysisInfoMixin<TypeDeductionAnalysis> {
  friend AnalysisInfoMixin;
  static llvm::AnalysisKey Key;

public:
  struct Result {
    llvm::DenseMap<llvm::Value*, TypeAliasSet> transparentTypes;
  };

  Result run(llvm::Module& m, llvm::ModuleAnalysisManager&);

private:
  std::list<llvm::Value*> deductionQueue;
  std::unordered_map<llvm::Value*, TypeAliasSet> deducedTypes;
  llvm::SmallPtrSet<llvm::Instruction*, 32> tbaaUsedForInstruction;
  llvm::Value* currDeductionValue = nullptr;
  bool changed = true;
  std::unordered_set<llvm::Value*> saturatedValues;
  unsigned statWidenedValues = 0;

  const TypeAliasSet& updateDeducedTypes(llvm::Value* value, std::unique_ptr<TransparentType> deducedType);
  TypeAliasSet getOrCreateDeducedTypes(llvm::Value* value);

  void deduceFromValue(llvm::Value* value);

  void deduceFromGlobalVariable(llvm::GlobalVariable* globalVar);
  void deduceFromAlloca(llvm::AllocaInst* alloca);
  void deduceFromLoadStore(llvm::Instruction* inst);
  void deduceFromGep(llvm::GetElementPtrInst* gep);

  void deduceFromCall(llvm::CallBase* call);
  void deduceFromFunction(llvm::Function* function);
  void deduceFromSupportedIntrinsicCall(llvm::CallBase* call);

  void mergeTypeAliasSets(llvm::Value* value1, llvm::Value* value2);

  void logDeducedTypes();
};

} // namespace tda
