#include "Debug/Logger.hpp"
#include "TBAAParser.hpp"

#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include <algorithm>

using namespace llvm;
using namespace tda;

std::pair<std::unique_ptr<TransparentType>, std::unique_ptr<TransparentType>>
TBAAParser::getLoadStoreTypesFromTbaa(const Instruction* inst) {
  assert(isa<LoadInst>(inst) || isa<StoreInst>(inst));
  const MDNode* mdNode = inst->getMetadata(LLVMContext::MD_tbaa);
  if (!mdNode || mdNode->getNumOperands() < 3)
    return {nullptr, nullptr};

  auto* baseTypeMd = dyn_cast<MDNode>(mdNode->getOperand(0));
  auto* accessTypeMd = dyn_cast<MDNode>(mdNode->getOperand(1));
  auto* offsetConst = mdconst::dyn_extract_or_null<ConstantInt>(mdNode->getOperand(2));

  if (!baseTypeMd || !accessTypeMd || !offsetConst)
    return {nullptr, nullptr};

  unsigned accessOffset = offsetConst->getZExtValue();
  if (!isStructTypeDescriptor(baseTypeMd))
    return {nullptr, nullptr};

  return getPlaceholderStructTypes(baseTypeMd, accessTypeMd, accessOffset);
}

std::pair<std::unique_ptr<TransparentType>, std::unique_ptr<TransparentType>>
TBAAParser::getPlaceholderStructTypes(const MDNode* structTypeMd, const MDNode* accessTypeMd, unsigned accessOffset) {
  if (structTypeMd->getNumOperands() < 6)
    return {nullptr, nullptr};

  unsigned numFields = structTypeMd->getNumOperands() / 3 - 1;
  std::unique_ptr<TransparentType> accessedType = nullptr;
  SmallVector<std::unique_ptr<TransparentType>> fieldTypes;
  SmallVector<unsigned> fieldOffsets;
  SmallVector<unsigned> fieldSizes;
  fieldTypes.reserve(numFields);
  bool foundAccess = false;

  for (unsigned i = 0; i < numFields; i++) {
    unsigned baseIdx = 3 + i * 3;
    if (baseIdx + 2 >= structTypeMd->getNumOperands())
      return {nullptr, nullptr};

    auto* fieldTypeMd = dyn_cast<MDNode>(structTypeMd->getOperand(baseIdx));
    auto* offsetConst = mdconst::dyn_extract_or_null<ConstantInt>(structTypeMd->getOperand(baseIdx + 1));
    auto* sizeConst   = mdconst::dyn_extract_or_null<ConstantInt>(structTypeMd->getOperand(baseIdx + 2));

    if (!fieldTypeMd || !offsetConst || !sizeConst)
      return {nullptr, nullptr};

    unsigned fieldOffset = offsetConst->getZExtValue();
    unsigned fieldSize   = sizeConst->getZExtValue();

    fieldOffsets.push_back(fieldOffset);
    fieldSizes.push_back(fieldSize);

    unsigned nextFieldOffset = 0;
    bool isLastField = (i + 1 == numFields);
    if (!isLastField) {
      if (baseIdx + 4 >= structTypeMd->getNumOperands())
        return {nullptr, nullptr};
      auto* nextOffsetConst = mdconst::dyn_extract_or_null<ConstantInt>(structTypeMd->getOperand(baseIdx + 4));
      if (!nextOffsetConst)
        return {nullptr, nullptr};
      nextFieldOffset = nextOffsetConst->getZExtValue();
    }
    foundAccess = (!foundAccess && isLastField) || (accessOffset >= fieldOffset && accessOffset < nextFieldOffset);

    if (isStructTypeDescriptor(fieldTypeMd)) {
      auto [fieldType, accessedTypeInField] =
        getPlaceholderStructTypes(fieldTypeMd, accessTypeMd, accessOffset - fieldOffset);
      if (foundAccess)
        accessedType = (accessTypeMd == fieldTypeMd) ? (fieldType ? fieldType->clone() : nullptr) : std::move(accessedTypeInField);
      if (fieldType)
        fieldTypes.push_back(std::move(fieldType));
      else
        fieldTypes.push_back(TransparentTypeFactory::createFromType(nullptr, 0));
    } else {
      fieldTypes.push_back(TransparentTypeFactory::createFromType(nullptr, 0));
    }
  }
  return {TransparentTypeFactory::createFromFields(fieldTypes, fieldOffsets, fieldSizes, 1), std::move(accessedType)};
}

std::unordered_map<StructType*, StructPaddingInfo> TBAAParser::getStructPaddingInfo(Module& module) {
  std::unordered_map<StructType*, StructPaddingInfo> structPaddingInfo;
  const DataLayout& dataLayout = module.getDataLayout();
  // TODO
  return structPaddingInfo;
}

bool TBAAParser::isStructTypeDescriptor(const MDNode* mdNode) { return mdNode->getNumOperands() >= 6; }
