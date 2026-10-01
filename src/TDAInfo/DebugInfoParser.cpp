#include "DebugInfoParser.hpp"

#include <llvm/BinaryFormat/Dwarf.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Module.h>

using namespace llvm;
using namespace tda;

void DebugInfoParser::insertPaddingInfo(DICompositeType* diCompositeType,
                                        std::unordered_map<StructType*, StructPaddingInfo>& paddingInfoMap,
                                        SmallDenseSet<DICompositeType*>& visited,
                                        LLVMContext& ctx,
                                        const DataLayout& dataLayout,
                                        StructType* structType) {
  if (!visited.insert(diCompositeType).second)
    return;
  // If we already know the IR struct that represents this DI type,
  // or we can discover it because the diNode has a name, register it
  if (!structType) {
    StringRef name = diCompositeType->getName();
    if (!name.empty()) {
      std::string prefix;
      switch (diCompositeType->getTag()) {
      case dwarf::DW_TAG_class_type:       prefix = "class."; break;
      case dwarf::DW_TAG_structure_type:   prefix = "struct."; break;
      case dwarf::DW_TAG_union_type:       prefix = "union."; break;
      case dwarf::DW_TAG_enumeration_type: return;
      default:                             llvm_unreachable("Unexpected DWARF tag for composite type");
      }
      structType = StructType::getTypeByName(ctx, prefix + name.str());
    }
  }
  if (!structType)
    return;
  StructPaddingInfo structPaddingInfo(diCompositeType);
  paddingInfoMap.insert({structType, structPaddingInfo});
  // Visit children in both IR structType and DI compositeType so that we can insert also unnamed composites
  auto paddingRanges = structPaddingInfo.getPaddingRanges();
  const StructLayout* structLayout = dataLayout.getStructLayout(structType);
  unsigned fieldIdx = 0;
  auto isPadding = [&paddingRanges, &structLayout, structType](unsigned& fieldIdx) -> bool {
    if (fieldIdx >= structType->getNumElements()) return false;
    return std::ranges::any_of(paddingRanges, [&structLayout, fieldIdx](const StructPaddingInfo::ByteRange& range) {
      return structLayout->getElementOffset(fieldIdx) == range.first;
    });
  };
  for (DINode* diNode : diCompositeType->getElements()) {
    if (!isa<DICompositeType>(diNode) && !isa<DIDerivedType>(diNode))
      continue;
    StructType* childStructType = nullptr;
    while (fieldIdx < structType->getNumElements() && isPadding(fieldIdx))
      fieldIdx++;
    if (fieldIdx < structType->getNumElements())
      childStructType = dyn_cast<StructType>(structType->getElementType(fieldIdx));
    // Direct nested composites
    if (auto* nestedDiCompositeType = dyn_cast<DICompositeType>(diNode))
      insertPaddingInfo(nestedDiCompositeType, paddingInfoMap, visited, ctx, dataLayout, childStructType);
    // Fields whose base type is itself a composites
    if (auto* derivedDiType = dyn_cast<DIDerivedType>(diNode))
      if (auto* compositeDiType = dyn_cast<DICompositeType>(derivedDiType->getBaseType()))
        insertPaddingInfo(compositeDiType, paddingInfoMap, visited, ctx, dataLayout, childStructType);
    fieldIdx++;
  }
}

std::unordered_map<StructType*, StructPaddingInfo> DebugInfoParser::getStructPaddingInfo(const Module& module) {
  SmallVector<DICompositeType*, 32> diCompositeTypes;
  DebugInfoFinder finder;
  finder.processModule(module);
  for (DIScope* diScope : finder.types())
    if (auto* diCompositeType = dyn_cast<DICompositeType>(diScope))
      diCompositeTypes.push_back(diCompositeType);
  // Recursively insert padding info of composite types
  std::unordered_map<StructType*, StructPaddingInfo> structPaddingInfo;
  SmallDenseSet<DICompositeType*> visited;
  LLVMContext& ctx = module.getContext();
  const DataLayout& dataLayout = module.getDataLayout();
  for (DICompositeType* diCompositeType : diCompositeTypes)
    insertPaddingInfo(diCompositeType, structPaddingInfo, visited, ctx, dataLayout);
  return structPaddingInfo;
}
