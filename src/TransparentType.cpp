#include "TDAInfo/StructPaddingInfo.hpp"
#include "TDAInfo/TypeDeductionAnalysisInfo.hpp"
#include "TransparentType.hpp"

#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/Support/Casting.h>
#include <llvm/Support/ErrorHandling.h>

#include <deque>
#include <memory>
#include <sstream>

using namespace llvm;
using namespace tda;

bool containsPtrType(Type* type) {
  if (type->isSingleValueType() || type->isVoidTy())
    return type->isPointerTy();
  if (type->isArrayTy())
    return containsPtrType(type->getArrayElementType());
  if (auto* structType = dyn_cast<StructType>(type)) {
    for (Type* fieldType : structType->elements())
      if (containsPtrType(fieldType))
        return true;
    return false;
  }
  llvm_unreachable("Type not handled in containsPtrType");
}

std::unique_ptr<TransparentType> TransparentTypeFactory::createFromValue(const Value* value) {
  assert(value && "Cannot create type of null value");
  assert(!isa<BasicBlock>(value) && "BasicBlock cannot have a transparent type");
  if (auto* function = dyn_cast<Function>(value))
    return createFromType(function->getReturnType(), 0);
  if (auto* global = dyn_cast<GlobalValue>(value))
    return createFromType(global->getValueType(), 1);
  return createFromType(value->getType(), 0);
}

std::unique_ptr<TransparentType> TransparentTypeFactory::createFromType(Type* unwrappedType,
                                                                        const unsigned indirections) {
  std::unique_ptr<TransparentType> type = nullptr;
  if (auto* structType = dyn_cast_or_null<StructType>(unwrappedType))
    if (structType->hasName() && structType->getStructName().starts_with("union."))
      type = std::unique_ptr<TransparentType>(new TransparentType(nullptr, true));
    else
      type = std::unique_ptr<TransparentType>(new TransparentStructType(structType));
  else if (auto* arrayType = dyn_cast_or_null<ArrayType>(unwrappedType))
    type = std::unique_ptr<TransparentType>(new TransparentArrayType(arrayType));
  else if (auto* vectorType = dyn_cast_or_null<VectorType>(unwrappedType))
    type = std::unique_ptr<TransparentType>(new TransparentArrayType(vectorType));
  else if (auto* ptrType = dyn_cast_or_null<PointerType>(unwrappedType))
    type = std::unique_ptr<TransparentType>(new TransparentPointerType(ptrType));
  else
    type = std::unique_ptr<TransparentType>(new TransparentType(unwrappedType));
  return createFromExisting(type.get(), indirections);
}

std::unique_ptr<TransparentType> TransparentTypeFactory::createFromExisting(const TransparentType* unwrappedType,
                                                                            unsigned indirections) {
  if (indirections == 0)
    return unwrappedType->clone();

  Type* unwrappedLLVMType = unwrappedType->getLLVMType();
  PointerType* ptrLLVMType = nullptr;
  if (unwrappedLLVMType)
    ptrLLVMType = PointerType::get(unwrappedLLVMType->getContext(), 0);

  std::unique_ptr<TransparentType> type = unwrappedType->clone();
  for (unsigned i = 0; i < indirections; i++)
    type = std::unique_ptr<TransparentType>(new TransparentPointerType(ptrLLVMType, std::move(type)));
  return type;
}

std::unique_ptr<TransparentType>
TransparentTypeFactory::createFromFields(SmallVector<std::unique_ptr<TransparentType>>& fieldTypes,
                                         const SmallVector<unsigned>& fieldOffsets,
                                         const SmallVector<unsigned>& fieldSizes,
                                         const unsigned indirections) {
  std::unique_ptr<TransparentType> type =
    std::unique_ptr<TransparentStructType>(new TransparentStructType(fieldTypes, fieldOffsets, fieldSizes));
  return createFromExisting(type.get(), indirections);
}

TransparentType* TransparentType::getPointedType() const {
  assert(isPointerTT() && "Not a pointer type");
  return nullptr;
}

std::unique_ptr<TransparentType> TransparentType::getPointerToType() const {
  return TransparentTypeFactory::createFromExisting(this, 1);
}

SmallPtrSet<Type*, 4> TransparentType::getContainedLLVMTypes() const {
  if (llvmType)
    return {llvmType};
  return {};
}

std::unique_ptr<TransparentType> TransparentType::getIndexedType(const TransparentType* gepSrcElType,
                                                                 std::optional<iterator_range<Use*>> gepIndices) const {
  return getOrSetIndexedType(gepSrcElType, gepIndices);
}

std::unique_ptr<TransparentType>
TransparentType::cloneAndSetIndexedType(const TransparentType* setType,
                                        const TransparentType* gepSrcElType,
                                        std::optional<iterator_range<Use*>> gepIndices) const {
  if (setType && setType->isPointerTT() && setType->getFullyUnwrappedType()->isStructTT())
    return this->clone();
  return getOrSetIndexedType(gepSrcElType, gepIndices, setType, true);
}

bool TransparentType::isStructurallyEquivalent(const TransparentType* other) const {
  if (!other)
    return false;
  if (isPlaceholder() || other->isPlaceholder())
    return true;
  if (isPrimitiveTT() && other->isPrimitiveTT())
    return llvmType == other->llvmType;
  if (isPointerTT() && other->isPointerTT())
    return true;
  if (isArrayTT() && other->isArrayTT()) {
    const auto* thisArray = cast<TransparentArrayType>(this);
    const auto* otherArray = cast<TransparentArrayType>(other);
    return thisArray->getElementType()->isStructurallyEquivalent(otherArray->getElementType());
  }
  if (isStructTT() && other->isStructTT()) {
    const auto* thisStruct = cast<TransparentStructType>(this);
    const auto* otherStruct = cast<TransparentStructType>(other);
    if (thisStruct->getNumFieldTypes() != otherStruct->getNumFieldTypes())
      return false;
    for (auto&& [thisField, otherField] : zip(thisStruct->getFieldTypes(), otherStruct->getFieldTypes()))
      if (!thisField->isStructurallyEquivalent(otherField))
        return false;
    return true;
  }
  return false;
}

const TransparentType* TransparentType::findGepSrcElementType(const TransparentType* type) const {
  const TransparentType* curr = this->getPointedType();
  while (curr) {
    if (curr->isStructurallyEquivalent(type))
      return curr;
    if (curr->isArrayTT())
      curr = cast<TransparentArrayType>(curr)->getElementType();
    else if (curr->isStructTT())
      curr = cast<TransparentStructType>(curr)->getFieldType(0);
    else
      curr = nullptr;
  }
  return curr;
}

std::unique_ptr<TransparentType> TransparentType::getOrSetIndexedType(const TransparentType* gepSrcElType,
                                                                      std::optional<iterator_range<Use*>> gepIndices,
                                                                      const TransparentType* setType, bool set) const {
  std::list<const Value*> indices;
  if (gepIndices)
    for (const Value* index : *gepIndices)
      indices.push_back(index);
  else
    indices.emplace_back(nullptr);

  const TransparentType* thisPointed = this->getPointedType();
  if (!thisPointed)
    return nullptr;

  const TransparentType* startingPoint = nullptr;
  if (gepIndices && (gepSrcElType->isPrimitiveTT() || thisPointed->isPrimitiveTT()))
    startingPoint = thisPointed;
  else
    startingPoint = findGepSrcElementType(gepSrcElType);
  if (!startingPoint)
    return nullptr;

  std::unique_ptr<TransparentArrayType> gepSrcElArrayType = std::make_unique<TransparentArrayType>();
  gepSrcElArrayType->setElementType(gepSrcElType->clone());

  const auto startingPointArray = std::make_unique<TransparentArrayType>();
  startingPointArray->setElementType(startingPoint->clone());

  TransparentType* indexedType =
    getOrSetIndexedType(startingPointArray.get(), gepSrcElArrayType.get(), indices, setType);

  if (set)
    return startingPointArray->getElementType()->getPointerToType();
  return indexedType ? indexedType->clone() : nullptr;
}

TransparentType* TransparentType::getOrSetIndexedType(TransparentType* ptrOperandType,
                                                      const TransparentType* gepSrcElType,
                                                      std::list<const Value*>& gepIndices,
                                                      const TransparentType* setType) const {
  const Value* indexValue = gepIndices.front();
  gepIndices.pop_front();

  if (gepSrcElType->isArrayTT() && ptrOperandType->isArrayTT()) {
    // Both array
    TransparentType* ptrOpElementType = cast<TransparentArrayType>(ptrOperandType)->getElementType();
    TransparentType* gepSrcElElementType = cast<TransparentArrayType>(gepSrcElType)->getElementType();

    if (gepSrcElElementType->isPrimitiveTT()) {
      assert(gepIndices.empty());

      if (ptrOpElementType->isPrimitiveTT() || ptrOpElementType->isPointerTT()) {
        if (setType)
          cast<TransparentArrayType>(ptrOperandType)->setElementType(setType->clone());
        return ptrOpElementType;
      }

      if (ptrOpElementType->isArrayTT()) {
        if (setType)
          cast<TransparentArrayType>(ptrOpElementType)->setElementType(setType->clone());
        return cast<TransparentArrayType>(ptrOpElementType)->getElementType();
      }

      if (ptrOpElementType->isStructTT()) {
        const DataLayout* dataLayout = TypeDeductionAnalysisInfo::getInstance().getDataLayout();
        bool isZeroIndex = false;
        if (!indexValue) // nullptr used as 0 index for load and stores
          isZeroIndex = true;
        const auto* indexConst = dyn_cast_or_null<ConstantInt>(indexValue);
        if (!indexConst && !isZeroIndex)
          return nullptr;
        unsigned index = isZeroIndex ? 0 : indexConst->getZExtValue();
        auto* currStruct = cast<TransparentStructType>(ptrOpElementType);

        while (currStruct) {
          const StructLayout* structLayout = nullptr;
          if (Type* currStructLLVMType = currStruct->getLLVMType())
            structLayout = dataLayout->getStructLayout(cast<StructType>(currStructLLVMType));
          unsigned numFields = currStruct->getNumFieldTypes();
          for (unsigned i = 0; i < numFields; i++) {
            TransparentType* fieldType = currStruct->getFieldType(i);
            unsigned fieldOffset = structLayout ? structLayout->getElementOffset(i) : currStruct->getFieldOffset(i);
            unsigned nextFieldOffset = 0;
            if (i + 1 < numFields)
              nextFieldOffset =
                structLayout ? structLayout->getElementOffset(i + 1) : currStruct->getFieldOffset(i + 1);

            if (nextFieldOffset == 0 || (index >= fieldOffset && index < nextFieldOffset)) {
              if (index == fieldOffset) {
                if (setType)
                  currStruct->setFieldType(i, setType->clone());
                return fieldType;
              }
              if (currStruct->isArrayTT()) {
                if (setType)
                  cast<TransparentArrayType>(fieldType)->setElementType(setType->clone());
                return cast<TransparentArrayType>(fieldType)->getElementType();
              }
              currStruct = dyn_cast<TransparentStructType>(fieldType);
              break;
            }
          }
        }
        return nullptr;
      }

      llvm_unreachable("wtf");
    }

    if (gepIndices.empty()) {
      if (setType)
        cast<TransparentArrayType>(ptrOperandType)->setElementType(setType->clone());
      return ptrOpElementType;
    }

    return getOrSetIndexedType(ptrOpElementType, gepSrcElElementType, gepIndices, setType);
  }

  if (ptrOperandType->isArrayTT()) {
    // gepSrcElType not array and ptrOperandType array
    if (gepIndices.empty()) {
      if (setType)
        cast<TransparentArrayType>(ptrOperandType)->setElementType(setType->clone());
      return cast<TransparentArrayType>(ptrOperandType)->getElementType();
    }
    llvm_unreachable("wtf");
  }

  if (gepSrcElType->isArrayTT() && ptrOperandType->isPrimitiveTT())
    return nullptr;

  if (gepSrcElType->isStructTT() && ptrOperandType->isStructTT()) {
    // Both structs
    unsigned index = cast<ConstantInt>(indexValue)->getZExtValue();
    TransparentType* ptrOpFieldType = cast<TransparentStructType>(ptrOperandType)->getFieldType(index);
    TransparentType* gepSrcElFieldType = cast<TransparentStructType>(gepSrcElType)->getFieldType(index);

    if (gepIndices.empty()) {
      if (setType)
        cast<TransparentStructType>(ptrOperandType)->setFieldType(index, setType->clone());
      return ptrOpFieldType;
    }

    return getOrSetIndexedType(ptrOpFieldType, gepSrcElFieldType, gepIndices, setType);
  }

  if (gepSrcElType->isStructTT()) {
    // gepSrcElType struct and ptrOperandType not struct
    // This means that also ptrOperandType is a struct, but we still need to deduce it (or this is simply an alias)
    return nullptr;
  }

  llvm_unreachable("wtf");
}

bool TransparentType::operator==(const TransparentType& other) const {
  return getKind() == other.getKind() && llvmType == other.llvmType;
}

bool TransparentType::isCompatibleWith(const TransparentType* other) const {
  if (!other)
    return true;
  if (isPlaceholder() || other->isPlaceholder() || isUnion() || other->isUnion())
    return true;

  bool isPointer = isPointerTT();
  bool isOtherPointer = other->isPointerTT();
  if (isPointer || isOtherPointer) {
    if (!(isPointer && isOtherPointer))
      return false;
    if (containsOpaquePtr() || other->containsOpaquePtr())
      return true;
    const TransparentType* pointedType = getPointedType();
    const TransparentType* otherPointedType = other->getPointedType();
    return pointedType->isCompatibleWith(otherPointedType);
  }
  if (const auto* otherArray = dyn_cast<TransparentArrayType>(other))
    return otherArray->getElementType()->isCompatibleWith(this);
  if (isPrimitiveTT()) {
    if (!other->isPrimitiveTT())
      return false;
    return llvmType == other->llvmType;
  }
  return getKind() == other->getKind();
}

std::unique_ptr<TransparentType> TransparentType::mergeWith(const TransparentType* other) const {
  if (!other || other->isPlaceholder() || isUnion())
    return clone();
  if (isPlaceholder() || other->isUnion())
    return other->clone();

  assert(isCompatibleWith(other) && "mergeWith on incompatible types");
  if (isPointerTT() && other->isPointerTT()) {
    const bool opaque = containsOpaquePtr();
    const bool otherOpaque = other->containsOpaquePtr();
    if (!opaque && !otherOpaque) {
      const TransparentType* pointedType = getPointedType();
      const TransparentType* otherPointedType = other->getPointedType();
      const std::unique_ptr<TransparentType> mergedPointedType = pointedType->mergeWith(otherPointedType);
      return mergedPointedType->getPointerToType();
    }
    if (!otherOpaque)
      return other->clone();
    return clone();
  }
  if (const auto* otherArray = dyn_cast<TransparentArrayType>(other))
    return otherArray->mergeWith(this);
  if (isPrimitiveTT())
    return clone();
  llvm_unreachable("Not a pointer nor a scalar");
}

std::unique_ptr<TransparentType> TransparentType::clone() const {
  return std::unique_ptr<TransparentType>(new TransparentType(*this));
}

std::string TransparentType::toString() const {
  if (isUnion())
    return "U";
  if (isPlaceholder())
    return "_";
  return tda::toString(llvmType);
}

SmallPtrSet<Type*, 4> TransparentPointerType::getContainedLLVMTypes() const {
  SmallPtrSet<Type*, 4> containedTypes = TransparentType::getContainedLLVMTypes();
  if (pointedType) {
    SmallPtrSet<Type*, 4> pointedContainedTypes = pointedType->getContainedLLVMTypes();
    containedTypes.insert(pointedContainedTypes.begin(), pointedContainedTypes.end());
  }
  return containedTypes;
}

bool TransparentPointerType::containsFloatingPointType() const {
  return pointedType && pointedType->containsFloatingPointType();
}

bool TransparentPointerType::operator==(const TransparentType& other) const {
  if (this == &other)
    return true;
  if (getKind() != other.getKind())
    return false;
  const auto& o = cast<TransparentPointerType>(other);
  if (!pointedType && !o.pointedType)
    return true;
  if (!pointedType || !o.pointedType)
    return false;
  return *pointedType == *o.pointedType;
}

bool TransparentPointerType::isCompatibleWith(const TransparentType* other) const {
  if (!other || other->isPlaceholder() || other->isUnion())
    return true;

  if (!other->isPointerTT())
    return false;
  if (isOpaquePtr() || other->isOpaquePtr() || isByteTyOrPtrTo() || other->isByteTyOrPtrTo())
    return true;
  const TransparentType* pointedType = getPointedType();
  const TransparentType* otherPointedType = other->getPointedType();
  return pointedType && otherPointedType ? pointedType->isCompatibleWith(otherPointedType) : true;
}

std::unique_ptr<TransparentType> TransparentPointerType::mergeWith(const TransparentType* other) const {
  if (!other || other->isPlaceholder())
    return clone();
  if (other->isUnion())
    return other->clone();
  if (isByteTyOrPtrTo() && other->isByteTyOrPtrTo())
    return clone();

  const auto* otherPtr = cast<TransparentPointerType>(other);
  if ((!pointedType || isByteTyOrPtrTo()) && otherPtr->pointedType)
    return other->clone();
  if (pointedType && (!otherPtr->pointedType || otherPtr->isByteTyOrPtrTo()))
    return clone();
  if (!pointedType && !otherPtr->pointedType)
    return clone();
  std::unique_ptr<TransparentType> mergedPointed = pointedType->mergeWith(otherPtr->pointedType.get());
  return TransparentTypeFactory::createFromExisting(mergedPointed.get(), 1);
}

std::unique_ptr<TransparentType> TransparentPointerType::clone() const {
  return std::unique_ptr<TransparentType>(new TransparentPointerType(*this));
}

std::string TransparentPointerType::toString() const {
  if (!pointedType)
    return "ptr";
  return pointedType->toString() + "*";
}

bool TransparentArrayType::containsOpaquePtr() const {
  if (TransparentType::containsOpaquePtr())
    return true;
  return elementType->containsOpaquePtr();
}

SmallPtrSet<Type*, 4> TransparentArrayType::getContainedLLVMTypes() const {
  SmallPtrSet<Type*, 4> containedTypes = TransparentType::getContainedLLVMTypes();
  if (elementType) {
    SmallPtrSet<Type*, 4> elementContainedTypes = elementType->getContainedLLVMTypes();
    containedTypes.insert(elementContainedTypes.begin(), elementContainedTypes.end());
  }
  return containedTypes;
}

unsigned TransparentArrayType::getNumElements() const {
  if (!llvmType)
    return 0;
  if (isa<ArrayType>(llvmType))
    return llvmType->getArrayNumElements();
  if (auto* vectorType = dyn_cast<VectorType>(llvmType))
    return vectorType->getElementCount().getKnownMinValue();
  return 0;
}

bool TransparentArrayType::operator==(const TransparentType& other) const {
  if (this == &other)
    return true;
  if (getKind() != other.getKind())
    return false;

  const auto& otherArray = cast<TransparentArrayType>(other);
  if (!TransparentType::operator==(other))
    return false;

  if (!elementType && !otherArray.elementType)
    return true;
  if (!elementType || !otherArray.elementType)
    return false;
  return *elementType == *otherArray.elementType;
}

bool TransparentArrayType::isCompatibleWith(const TransparentType* other) const {
  if (!other || other->isUnion())
    return true;

  if (const auto* otherArray = dyn_cast<TransparentArrayType>(other)) {
    // TODO check lengths
    return getElementType()->isCompatibleWith(otherArray->getElementType());
  }
  return getElementType()->isCompatibleWith(other);
}

std::unique_ptr<TransparentType> TransparentArrayType::mergeWith(const TransparentType* other) const {
  if (!other)
    return clone();
  if (other->isUnion())
    return other->clone();

  std::unique_ptr<TransparentType> result = clone();
  std::unique_ptr<TransparentType> mergedElem;
  if (const auto* otherArray = dyn_cast<TransparentArrayType>(other))
    mergedElem = getElementType()->mergeWith(otherArray->getElementType());
  else
    mergedElem = getElementType()->mergeWith(other);
  cast<TransparentArrayType>(result.get())->setElementType(std::move(mergedElem));
  return result;
}

std::unique_ptr<TransparentType> TransparentArrayType::clone() const {
  return std::unique_ptr<TransparentType>(new TransparentArrayType(*this));
}

std::string TransparentArrayType::toString() const {
  if (!elementType)
    return "InvalidType";
  std::stringstream ss;
  if (!llvmType)
    ss << "[" << *elementType << "]";
  else if (isa<ArrayType>(llvmType))
    ss << "[" << llvmType->getArrayNumElements() << " x " << *elementType << "]";
  else if (auto* vectorType = dyn_cast<VectorType>(llvmType)) {
    ElementCount elementCount = vectorType->getElementCount();
    ss << "<";
    if (elementCount.isScalable())
      ss << "vscale x ";
    ss << elementCount.getKnownMinValue() << " x " << *elementType << ">";
  }
  return ss.str();
}

TransparentStructType::TransparentStructType(StructType* unwrappedType)
: TransparentType(unwrappedType) {
  auto& passInfo = TypeDeductionAnalysisInfo::getInstance();
  const DataLayout* dataLayout = passInfo.getDataLayout();
  const StructLayout* structLayout = dataLayout ? dataLayout->getStructLayout(unwrappedType) : nullptr;
  std::optional<StructPaddingInfo> structPaddingInfo = passInfo.getStructPaddingInfo(unwrappedType);
  ArrayRef<StructPaddingInfo::ByteRange> paddingRanges =
    structPaddingInfo ? structPaddingInfo->getPaddingRanges() : ArrayRef<StructPaddingInfo::ByteRange>();
  for (unsigned i = 0; i < unwrappedType->getNumElements(); i++) {
    bool isPadding = std::ranges::any_of(paddingRanges, [&structLayout, i](const StructPaddingInfo::ByteRange& range) {
      return structLayout ? structLayout->getElementOffset(i) == range.first : false;
    });
    if (isPadding)
      paddingFields.insert(i);
    Type* fieldType = unwrappedType->getElementType(i);
    fieldTypes.push_back(TransparentTypeFactory::createFromType(fieldType, 0));
  }
}

TransparentStructType::TransparentStructType(SmallVector<std::unique_ptr<TransparentType>>& fieldTypes,
                                             const SmallVector<unsigned>& fieldOffsets,
                                             const SmallVector<unsigned>& fieldSizes) {
  for (auto& fieldType : fieldTypes)
    this->fieldTypes.push_back(std::move(fieldType));
  for (const auto& fieldOffset : fieldOffsets)
    this->fieldOffsets.push_back(fieldOffset);
  // TODO use sizes to compute which fields are padding
}

bool TransparentStructType::containsOpaquePtr() const {
  if (TransparentType::containsOpaquePtr())
    return true;
  for (const std::unique_ptr<TransparentType>& field : fieldTypes)
    if (!field || field->containsOpaquePtr())
      return true;
  return false;
}

bool TransparentStructType::containsFloatingPointType() const {
  for (const TransparentType* fieldType : getFieldTypes())
    if (fieldType->containsFloatingPointType())
      return true;
  return false;
}

SmallPtrSet<Type*, 4> TransparentStructType::getContainedLLVMTypes() const {
  SmallPtrSet<Type*, 4> containedTypes = TransparentType::getContainedLLVMTypes();
  for (const TransparentType* field : getFieldTypes()) {
    SmallPtrSet<Type*, 4> elementContainedTypes = field->getContainedLLVMTypes();
    containedTypes.insert(elementContainedTypes.begin(), elementContainedTypes.end());
  }
  return containedTypes;
}

bool TransparentStructType::operator==(const TransparentType& other) const {
  if (this == &other)
    return true;
  if (getKind() != other.getKind())
    return false;
  auto& otherStructType = cast<TransparentStructType>(other);
  if (!TransparentType::operator==(other))
    return false;
  if (fieldTypes.size() != otherStructType.fieldTypes.size())
    return false;
  for (unsigned i = 0; i < fieldTypes.size(); i++) {
    if (!fieldTypes[i] && !otherStructType.fieldTypes[i])
      continue;
    if (!fieldTypes[i] || !otherStructType.fieldTypes[i] || *fieldTypes[i] != *otherStructType.fieldTypes[i])
      return false;
  }
  return true;
}

bool TransparentStructType::isCompatibleWith(const TransparentType* other) const {
  if (!other || other->isUnion())
    return true;

  if (const auto* otherArray = dyn_cast<TransparentArrayType>(other))
    return otherArray->getElementType()->isCompatibleWith(this);
  if (const auto* otherStruct = dyn_cast<TransparentStructType>(other)) {
    auto* structLLVMType = dyn_cast_or_null<StructType>(llvmType);
    auto* otherStructLLVMType = dyn_cast_or_null<StructType>(other->getLLVMType());
    if (structLLVMType && otherStructLLVMType && structLLVMType->hasName() && otherStructLLVMType->hasName())
      if (structLLVMType->getName() != otherStructLLVMType->getName())
        return false;
    if (getNumFieldTypes() != otherStruct->getNumFieldTypes())
      return false;
    for (auto&& [field, otherField] : zip(fieldTypes, otherStruct->fieldTypes))
      if (!field->isCompatibleWith(otherField.get()))
        return false;
    return true;
  }
  return false;
}

std::unique_ptr<TransparentType> TransparentStructType::mergeWith(const TransparentType* other) const {
  if (!other)
    return clone();
  if (other->isUnion())
    return other->clone();

  if (const auto* otherArray = dyn_cast<TransparentArrayType>(other))
    return mergeWith(otherArray->getElementType());

  const auto otherStruct = cast<TransparentStructType>(other);
  auto result = clone();
  auto* resultStruct = cast<TransparentStructType>(result.get());

  for (unsigned i = 0; i < fieldTypes.size(); i++) {
    std::unique_ptr<TransparentType> mergedField = getFieldType(i)->mergeWith(otherStruct->getFieldType(i));
    resultStruct->setFieldType(i, std::move(mergedField));

    if (isFieldPadding(i) || otherStruct->isFieldPadding(i))
      resultStruct->addFieldPadding(i);
  }

  Type* otherLLVMType = otherStruct->llvmType;
  if (llvmType || otherLLVMType) {
    if (llvmType && otherLLVMType) {
      bool isNamed = cast<StructType>(llvmType)->hasName();
      bool isOtherNamed = cast<StructType>(otherLLVMType)->hasName();
      if (isNamed && isOtherNamed)
        assert(llvmType == otherLLVMType);
      result->setLLVMType(isOtherNamed ? otherLLVMType : llvmType);
    }
    if (llvmType)
      resultStruct->setLLVMType(llvmType);
    else
      resultStruct->setLLVMType(otherLLVMType);
  }

  return result;
}

std::unique_ptr<TransparentType> TransparentStructType::clone() const {
  return std::unique_ptr<TransparentType>(new TransparentStructType(*this));
}

std::string TransparentStructType::toString() const {
  if (std::ranges::any_of(fieldTypes, [](const auto& field) -> bool { return field == nullptr; }))
    return "InvalidType";

  std::string typeString = llvmType ? tda::toString(llvmType) : "{}";
  std::stringstream ss;
  ss << typeString.substr(0, typeString.find('{') + 1) << " ";

  bool first = true;
  for (unsigned i = 0; i < fieldTypes.size(); i++) {
    const auto& fieldType = fieldTypes[i];
    if (!first)
      ss << ", ";
    else
      first = false;
    if (isFieldPadding(i))
      ss << "pad";
    ss << *fieldType;
  }

  ss << " }";
  if (llvmType && cast<StructType>(llvmType)->isPacked())
    ss << ">";
  return ss.str();
}
