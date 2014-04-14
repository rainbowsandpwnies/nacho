// Generated by the protocol buffer compiler.  DO NOT EDIT!
// source: queso.proto

#ifndef PROTOBUF_queso_2eproto__INCLUDED
#define PROTOBUF_queso_2eproto__INCLUDED

#include <string>

#include <google/protobuf/stubs/common.h>

#if GOOGLE_PROTOBUF_VERSION < 2004000
#error This file was generated by a newer version of protoc which is
#error incompatible with your Protocol Buffer headers.  Please update
#error your headers.
#endif
#if 2004001 < GOOGLE_PROTOBUF_MIN_PROTOC_VERSION
#error This file was generated by an older version of protoc which is
#error incompatible with your Protocol Buffer headers.  Please
#error regenerate this file with a newer version of protoc.
#endif

#include <google/protobuf/generated_message_util.h>
#include <google/protobuf/repeated_field.h>
#include <google/protobuf/extension_set.h>
#include <google/protobuf/generated_message_reflection.h>
// @@protoc_insertion_point(includes)

namespace queso {

// Internal implementation detail -- do not call these.
void  protobuf_AddDesc_queso_2eproto();
void protobuf_AssignDesc_queso_2eproto();
void protobuf_ShutdownFile_queso_2eproto();

class Variable;
class Instruction;
class Instructions;

enum VarType {
  VARIABLE = 1,
  CONSTANT = 2,
  ARRAY = 3
};
bool VarType_IsValid(int value);
const VarType VarType_MIN = VARIABLE;
const VarType VarType_MAX = ARRAY;
const int VarType_ARRAYSIZE = VarType_MAX + 1;

const ::google::protobuf::EnumDescriptor* VarType_descriptor();
inline const ::std::string& VarType_Name(VarType value) {
  return ::google::protobuf::internal::NameOfEnum(
    VarType_descriptor(), value);
}
inline bool VarType_Parse(
    const ::std::string& name, VarType* value) {
  return ::google::protobuf::internal::ParseNamedEnum<VarType>(
    VarType_descriptor(), name, value);
}
enum Opcode {
  COMMENT = 0,
  ASSIGN = 1,
  STORE = 2,
  LOAD = 3,
  ITE = 4,
  SIGNEXTEND = 5,
  ADD = 6,
  SUB = 7,
  MUL = 8,
  UDIV = 9,
  UMOD = 10,
  AND = 11,
  OR = 12,
  XOR = 13,
  SHR = 14,
  SHL = 15,
  CMPEQ = 16,
  CMPLTU = 17,
  CMPLEU = 18,
  CMPLTS = 19,
  CMPLES = 20
};
bool Opcode_IsValid(int value);
const Opcode Opcode_MIN = COMMENT;
const Opcode Opcode_MAX = CMPLES;
const int Opcode_ARRAYSIZE = Opcode_MAX + 1;

const ::google::protobuf::EnumDescriptor* Opcode_descriptor();
inline const ::std::string& Opcode_Name(Opcode value) {
  return ::google::protobuf::internal::NameOfEnum(
    Opcode_descriptor(), value);
}
inline bool Opcode_Parse(
    const ::std::string& name, Opcode* value) {
  return ::google::protobuf::internal::ParseNamedEnum<Opcode>(
    Opcode_descriptor(), name, value);
}
// ===================================================================

class Variable : public ::google::protobuf::Message {
 public:
  Variable();
  virtual ~Variable();
  
  Variable(const Variable& from);
  
  inline Variable& operator=(const Variable& from) {
    CopyFrom(from);
    return *this;
  }
  
  inline const ::google::protobuf::UnknownFieldSet& unknown_fields() const {
    return _unknown_fields_;
  }
  
  inline ::google::protobuf::UnknownFieldSet* mutable_unknown_fields() {
    return &_unknown_fields_;
  }
  
  static const ::google::protobuf::Descriptor* descriptor();
  static const Variable& default_instance();
  
  void Swap(Variable* other);
  
  // implements Message ----------------------------------------------
  
  Variable* New() const;
  void CopyFrom(const ::google::protobuf::Message& from);
  void MergeFrom(const ::google::protobuf::Message& from);
  void CopyFrom(const Variable& from);
  void MergeFrom(const Variable& from);
  void Clear();
  bool IsInitialized() const;
  
  int ByteSize() const;
  bool MergePartialFromCodedStream(
      ::google::protobuf::io::CodedInputStream* input);
  void SerializeWithCachedSizes(
      ::google::protobuf::io::CodedOutputStream* output) const;
  ::google::protobuf::uint8* SerializeWithCachedSizesToArray(::google::protobuf::uint8* output) const;
  int GetCachedSize() const { return _cached_size_; }
  private:
  void SharedCtor();
  void SharedDtor();
  void SetCachedSize(int size) const;
  public:
  
  ::google::protobuf::Metadata GetMetadata() const;
  
  // nested types ----------------------------------------------------
  
  // accessors -------------------------------------------------------
  
  // required .queso.VarType type = 1;
  inline bool has_type() const;
  inline void clear_type();
  static const int kTypeFieldNumber = 1;
  inline queso::VarType type() const;
  inline void set_type(queso::VarType value);
  
  // optional string name = 2;
  inline bool has_name() const;
  inline void clear_name();
  static const int kNameFieldNumber = 2;
  inline const ::std::string& name() const;
  inline void set_name(const ::std::string& value);
  inline void set_name(const char* value);
  inline void set_name(const char* value, size_t size);
  inline ::std::string* mutable_name();
  inline ::std::string* release_name();
  
  // required int32 bits = 3;
  inline bool has_bits() const;
  inline void clear_bits();
  static const int kBitsFieldNumber = 3;
  inline ::google::protobuf::int32 bits() const;
  inline void set_bits(::google::protobuf::int32 value);
  
  // optional uint32 addresses = 4;
  inline bool has_addresses() const;
  inline void clear_addresses();
  static const int kAddressesFieldNumber = 4;
  inline ::google::protobuf::uint32 addresses() const;
  inline void set_addresses(::google::protobuf::uint32 value);
  
  // optional uint64 lval = 5;
  inline bool has_lval() const;
  inline void clear_lval();
  static const int kLvalFieldNumber = 5;
  inline ::google::protobuf::uint64 lval() const;
  inline void set_lval(::google::protobuf::uint64 value);
  
  // required uint32 count = 6;
  inline bool has_count() const;
  inline void clear_count();
  static const int kCountFieldNumber = 6;
  inline ::google::protobuf::uint32 count() const;
  inline void set_count(::google::protobuf::uint32 value);
  
  // @@protoc_insertion_point(class_scope:queso.Variable)
 private:
  inline void set_has_type();
  inline void clear_has_type();
  inline void set_has_name();
  inline void clear_has_name();
  inline void set_has_bits();
  inline void clear_has_bits();
  inline void set_has_addresses();
  inline void clear_has_addresses();
  inline void set_has_lval();
  inline void clear_has_lval();
  inline void set_has_count();
  inline void clear_has_count();
  
  ::google::protobuf::UnknownFieldSet _unknown_fields_;
  
  ::std::string* name_;
  int type_;
  ::google::protobuf::int32 bits_;
  ::google::protobuf::uint64 lval_;
  ::google::protobuf::uint32 addresses_;
  ::google::protobuf::uint32 count_;
  
  mutable int _cached_size_;
  ::google::protobuf::uint32 _has_bits_[(6 + 31) / 32];
  
  friend void  protobuf_AddDesc_queso_2eproto();
  friend void protobuf_AssignDesc_queso_2eproto();
  friend void protobuf_ShutdownFile_queso_2eproto();
  
  void InitAsDefaultInstance();
  static Variable* default_instance_;
};
// -------------------------------------------------------------------

class Instruction : public ::google::protobuf::Message {
 public:
  Instruction();
  virtual ~Instruction();
  
  Instruction(const Instruction& from);
  
  inline Instruction& operator=(const Instruction& from) {
    CopyFrom(from);
    return *this;
  }
  
  inline const ::google::protobuf::UnknownFieldSet& unknown_fields() const {
    return _unknown_fields_;
  }
  
  inline ::google::protobuf::UnknownFieldSet* mutable_unknown_fields() {
    return &_unknown_fields_;
  }
  
  static const ::google::protobuf::Descriptor* descriptor();
  static const Instruction& default_instance();
  
  void Swap(Instruction* other);
  
  // implements Message ----------------------------------------------
  
  Instruction* New() const;
  void CopyFrom(const ::google::protobuf::Message& from);
  void MergeFrom(const ::google::protobuf::Message& from);
  void CopyFrom(const Instruction& from);
  void MergeFrom(const Instruction& from);
  void Clear();
  bool IsInitialized() const;
  
  int ByteSize() const;
  bool MergePartialFromCodedStream(
      ::google::protobuf::io::CodedInputStream* input);
  void SerializeWithCachedSizes(
      ::google::protobuf::io::CodedOutputStream* output) const;
  ::google::protobuf::uint8* SerializeWithCachedSizesToArray(::google::protobuf::uint8* output) const;
  int GetCachedSize() const { return _cached_size_; }
  private:
  void SharedCtor();
  void SharedDtor();
  void SetCachedSize(int size) const;
  public:
  
  ::google::protobuf::Metadata GetMetadata() const;
  
  // nested types ----------------------------------------------------
  
  // accessors -------------------------------------------------------
  
  // required .queso.Opcode opcode = 1;
  inline bool has_opcode() const;
  inline void clear_opcode();
  static const int kOpcodeFieldNumber = 1;
  inline queso::Opcode opcode() const;
  inline void set_opcode(queso::Opcode value);
  
  // optional .queso.Variable dst = 2;
  inline bool has_dst() const;
  inline void clear_dst();
  static const int kDstFieldNumber = 2;
  inline const ::queso::Variable& dst() const;
  inline ::queso::Variable* mutable_dst();
  inline ::queso::Variable* release_dst();
  
  // optional .queso.Variable lhs = 3;
  inline bool has_lhs() const;
  inline void clear_lhs();
  static const int kLhsFieldNumber = 3;
  inline const ::queso::Variable& lhs() const;
  inline ::queso::Variable* mutable_lhs();
  inline ::queso::Variable* release_lhs();
  
  // optional .queso.Variable rhs = 4;
  inline bool has_rhs() const;
  inline void clear_rhs();
  static const int kRhsFieldNumber = 4;
  inline const ::queso::Variable& rhs() const;
  inline ::queso::Variable* mutable_rhs();
  inline ::queso::Variable* release_rhs();
  
  // optional .queso.Variable src = 5;
  inline bool has_src() const;
  inline void clear_src();
  static const int kSrcFieldNumber = 5;
  inline const ::queso::Variable& src() const;
  inline ::queso::Variable* mutable_src();
  inline ::queso::Variable* release_src();
  
  // optional .queso.Variable condition = 6;
  inline bool has_condition() const;
  inline void clear_condition();
  static const int kConditionFieldNumber = 6;
  inline const ::queso::Variable& condition() const;
  inline ::queso::Variable* mutable_condition();
  inline ::queso::Variable* release_condition();
  
  // optional .queso.Variable t = 7;
  inline bool has_t() const;
  inline void clear_t();
  static const int kTFieldNumber = 7;
  inline const ::queso::Variable& t() const;
  inline ::queso::Variable* mutable_t();
  inline ::queso::Variable* release_t();
  
  // optional .queso.Variable e = 8;
  inline bool has_e() const;
  inline void clear_e();
  static const int kEFieldNumber = 8;
  inline const ::queso::Variable& e() const;
  inline ::queso::Variable* mutable_e();
  inline ::queso::Variable* release_e();
  
  // optional .queso.Variable address = 9;
  inline bool has_address() const;
  inline void clear_address();
  static const int kAddressFieldNumber = 9;
  inline const ::queso::Variable& address() const;
  inline ::queso::Variable* mutable_address();
  inline ::queso::Variable* release_address();
  
  // optional .queso.Variable mem = 10;
  inline bool has_mem() const;
  inline void clear_mem();
  static const int kMemFieldNumber = 10;
  inline const ::queso::Variable& mem() const;
  inline ::queso::Variable* mutable_mem();
  inline ::queso::Variable* release_mem();
  
  // optional .queso.Variable srcmem = 11;
  inline bool has_srcmem() const;
  inline void clear_srcmem();
  static const int kSrcmemFieldNumber = 11;
  inline const ::queso::Variable& srcmem() const;
  inline ::queso::Variable* mutable_srcmem();
  inline ::queso::Variable* release_srcmem();
  
  // optional .queso.Variable dstmem = 12;
  inline bool has_dstmem() const;
  inline void clear_dstmem();
  static const int kDstmemFieldNumber = 12;
  inline const ::queso::Variable& dstmem() const;
  inline ::queso::Variable* mutable_dstmem();
  inline ::queso::Variable* release_dstmem();
  
  // optional .queso.Variable value = 13;
  inline bool has_value() const;
  inline void clear_value();
  static const int kValueFieldNumber = 13;
  inline const ::queso::Variable& value() const;
  inline ::queso::Variable* mutable_value();
  inline ::queso::Variable* release_value();
  
  // optional string comment = 14;
  inline bool has_comment() const;
  inline void clear_comment();
  static const int kCommentFieldNumber = 14;
  inline const ::std::string& comment() const;
  inline void set_comment(const ::std::string& value);
  inline void set_comment(const char* value);
  inline void set_comment(const char* value, size_t size);
  inline ::std::string* mutable_comment();
  inline ::std::string* release_comment();
  
  // optional uint64 trace_address = 15;
  inline bool has_trace_address() const;
  inline void clear_trace_address();
  static const int kTraceAddressFieldNumber = 15;
  inline ::google::protobuf::uint64 trace_address() const;
  inline void set_trace_address(::google::protobuf::uint64 value);
  
  // @@protoc_insertion_point(class_scope:queso.Instruction)
 private:
  inline void set_has_opcode();
  inline void clear_has_opcode();
  inline void set_has_dst();
  inline void clear_has_dst();
  inline void set_has_lhs();
  inline void clear_has_lhs();
  inline void set_has_rhs();
  inline void clear_has_rhs();
  inline void set_has_src();
  inline void clear_has_src();
  inline void set_has_condition();
  inline void clear_has_condition();
  inline void set_has_t();
  inline void clear_has_t();
  inline void set_has_e();
  inline void clear_has_e();
  inline void set_has_address();
  inline void clear_has_address();
  inline void set_has_mem();
  inline void clear_has_mem();
  inline void set_has_srcmem();
  inline void clear_has_srcmem();
  inline void set_has_dstmem();
  inline void clear_has_dstmem();
  inline void set_has_value();
  inline void clear_has_value();
  inline void set_has_comment();
  inline void clear_has_comment();
  inline void set_has_trace_address();
  inline void clear_has_trace_address();
  
  ::google::protobuf::UnknownFieldSet _unknown_fields_;
  
  ::queso::Variable* dst_;
  ::queso::Variable* lhs_;
  ::queso::Variable* rhs_;
  ::queso::Variable* src_;
  ::queso::Variable* condition_;
  ::queso::Variable* t_;
  ::queso::Variable* e_;
  ::queso::Variable* address_;
  ::queso::Variable* mem_;
  ::queso::Variable* srcmem_;
  ::queso::Variable* dstmem_;
  ::queso::Variable* value_;
  ::std::string* comment_;
  ::google::protobuf::uint64 trace_address_;
  int opcode_;
  
  mutable int _cached_size_;
  ::google::protobuf::uint32 _has_bits_[(15 + 31) / 32];
  
  friend void  protobuf_AddDesc_queso_2eproto();
  friend void protobuf_AssignDesc_queso_2eproto();
  friend void protobuf_ShutdownFile_queso_2eproto();
  
  void InitAsDefaultInstance();
  static Instruction* default_instance_;
};
// -------------------------------------------------------------------

class Instructions : public ::google::protobuf::Message {
 public:
  Instructions();
  virtual ~Instructions();
  
  Instructions(const Instructions& from);
  
  inline Instructions& operator=(const Instructions& from) {
    CopyFrom(from);
    return *this;
  }
  
  inline const ::google::protobuf::UnknownFieldSet& unknown_fields() const {
    return _unknown_fields_;
  }
  
  inline ::google::protobuf::UnknownFieldSet* mutable_unknown_fields() {
    return &_unknown_fields_;
  }
  
  static const ::google::protobuf::Descriptor* descriptor();
  static const Instructions& default_instance();
  
  void Swap(Instructions* other);
  
  // implements Message ----------------------------------------------
  
  Instructions* New() const;
  void CopyFrom(const ::google::protobuf::Message& from);
  void MergeFrom(const ::google::protobuf::Message& from);
  void CopyFrom(const Instructions& from);
  void MergeFrom(const Instructions& from);
  void Clear();
  bool IsInitialized() const;
  
  int ByteSize() const;
  bool MergePartialFromCodedStream(
      ::google::protobuf::io::CodedInputStream* input);
  void SerializeWithCachedSizes(
      ::google::protobuf::io::CodedOutputStream* output) const;
  ::google::protobuf::uint8* SerializeWithCachedSizesToArray(::google::protobuf::uint8* output) const;
  int GetCachedSize() const { return _cached_size_; }
  private:
  void SharedCtor();
  void SharedDtor();
  void SetCachedSize(int size) const;
  public:
  
  ::google::protobuf::Metadata GetMetadata() const;
  
  // nested types ----------------------------------------------------
  
  // accessors -------------------------------------------------------
  
  // repeated .queso.Instruction instruction = 1;
  inline int instruction_size() const;
  inline void clear_instruction();
  static const int kInstructionFieldNumber = 1;
  inline const ::queso::Instruction& instruction(int index) const;
  inline ::queso::Instruction* mutable_instruction(int index);
  inline ::queso::Instruction* add_instruction();
  inline const ::google::protobuf::RepeatedPtrField< ::queso::Instruction >&
      instruction() const;
  inline ::google::protobuf::RepeatedPtrField< ::queso::Instruction >*
      mutable_instruction();
  
  // @@protoc_insertion_point(class_scope:queso.Instructions)
 private:
  
  ::google::protobuf::UnknownFieldSet _unknown_fields_;
  
  ::google::protobuf::RepeatedPtrField< ::queso::Instruction > instruction_;
  
  mutable int _cached_size_;
  ::google::protobuf::uint32 _has_bits_[(1 + 31) / 32];
  
  friend void  protobuf_AddDesc_queso_2eproto();
  friend void protobuf_AssignDesc_queso_2eproto();
  friend void protobuf_ShutdownFile_queso_2eproto();
  
  void InitAsDefaultInstance();
  static Instructions* default_instance_;
};
// ===================================================================


// ===================================================================

// Variable

// required .queso.VarType type = 1;
inline bool Variable::has_type() const {
  return (_has_bits_[0] & 0x00000001u) != 0;
}
inline void Variable::set_has_type() {
  _has_bits_[0] |= 0x00000001u;
}
inline void Variable::clear_has_type() {
  _has_bits_[0] &= ~0x00000001u;
}
inline void Variable::clear_type() {
  type_ = 1;
  clear_has_type();
}
inline queso::VarType Variable::type() const {
  return static_cast< queso::VarType >(type_);
}
inline void Variable::set_type(queso::VarType value) {
  GOOGLE_DCHECK(queso::VarType_IsValid(value));
  set_has_type();
  type_ = value;
}

// optional string name = 2;
inline bool Variable::has_name() const {
  return (_has_bits_[0] & 0x00000002u) != 0;
}
inline void Variable::set_has_name() {
  _has_bits_[0] |= 0x00000002u;
}
inline void Variable::clear_has_name() {
  _has_bits_[0] &= ~0x00000002u;
}
inline void Variable::clear_name() {
  if (name_ != &::google::protobuf::internal::kEmptyString) {
    name_->clear();
  }
  clear_has_name();
}
inline const ::std::string& Variable::name() const {
  return *name_;
}
inline void Variable::set_name(const ::std::string& value) {
  set_has_name();
  if (name_ == &::google::protobuf::internal::kEmptyString) {
    name_ = new ::std::string;
  }
  name_->assign(value);
}
inline void Variable::set_name(const char* value) {
  set_has_name();
  if (name_ == &::google::protobuf::internal::kEmptyString) {
    name_ = new ::std::string;
  }
  name_->assign(value);
}
inline void Variable::set_name(const char* value, size_t size) {
  set_has_name();
  if (name_ == &::google::protobuf::internal::kEmptyString) {
    name_ = new ::std::string;
  }
  name_->assign(reinterpret_cast<const char*>(value), size);
}
inline ::std::string* Variable::mutable_name() {
  set_has_name();
  if (name_ == &::google::protobuf::internal::kEmptyString) {
    name_ = new ::std::string;
  }
  return name_;
}
inline ::std::string* Variable::release_name() {
  clear_has_name();
  if (name_ == &::google::protobuf::internal::kEmptyString) {
    return NULL;
  } else {
    ::std::string* temp = name_;
    name_ = const_cast< ::std::string*>(&::google::protobuf::internal::kEmptyString);
    return temp;
  }
}

// required int32 bits = 3;
inline bool Variable::has_bits() const {
  return (_has_bits_[0] & 0x00000004u) != 0;
}
inline void Variable::set_has_bits() {
  _has_bits_[0] |= 0x00000004u;
}
inline void Variable::clear_has_bits() {
  _has_bits_[0] &= ~0x00000004u;
}
inline void Variable::clear_bits() {
  bits_ = 0;
  clear_has_bits();
}
inline ::google::protobuf::int32 Variable::bits() const {
  return bits_;
}
inline void Variable::set_bits(::google::protobuf::int32 value) {
  set_has_bits();
  bits_ = value;
}

// optional uint32 addresses = 4;
inline bool Variable::has_addresses() const {
  return (_has_bits_[0] & 0x00000008u) != 0;
}
inline void Variable::set_has_addresses() {
  _has_bits_[0] |= 0x00000008u;
}
inline void Variable::clear_has_addresses() {
  _has_bits_[0] &= ~0x00000008u;
}
inline void Variable::clear_addresses() {
  addresses_ = 0u;
  clear_has_addresses();
}
inline ::google::protobuf::uint32 Variable::addresses() const {
  return addresses_;
}
inline void Variable::set_addresses(::google::protobuf::uint32 value) {
  set_has_addresses();
  addresses_ = value;
}

// optional uint64 lval = 5;
inline bool Variable::has_lval() const {
  return (_has_bits_[0] & 0x00000010u) != 0;
}
inline void Variable::set_has_lval() {
  _has_bits_[0] |= 0x00000010u;
}
inline void Variable::clear_has_lval() {
  _has_bits_[0] &= ~0x00000010u;
}
inline void Variable::clear_lval() {
  lval_ = GOOGLE_ULONGLONG(0);
  clear_has_lval();
}
inline ::google::protobuf::uint64 Variable::lval() const {
  return lval_;
}
inline void Variable::set_lval(::google::protobuf::uint64 value) {
  set_has_lval();
  lval_ = value;
}

// required uint32 count = 6;
inline bool Variable::has_count() const {
  return (_has_bits_[0] & 0x00000020u) != 0;
}
inline void Variable::set_has_count() {
  _has_bits_[0] |= 0x00000020u;
}
inline void Variable::clear_has_count() {
  _has_bits_[0] &= ~0x00000020u;
}
inline void Variable::clear_count() {
  count_ = 0u;
  clear_has_count();
}
inline ::google::protobuf::uint32 Variable::count() const {
  return count_;
}
inline void Variable::set_count(::google::protobuf::uint32 value) {
  set_has_count();
  count_ = value;
}

// -------------------------------------------------------------------

// Instruction

// required .queso.Opcode opcode = 1;
inline bool Instruction::has_opcode() const {
  return (_has_bits_[0] & 0x00000001u) != 0;
}
inline void Instruction::set_has_opcode() {
  _has_bits_[0] |= 0x00000001u;
}
inline void Instruction::clear_has_opcode() {
  _has_bits_[0] &= ~0x00000001u;
}
inline void Instruction::clear_opcode() {
  opcode_ = 0;
  clear_has_opcode();
}
inline queso::Opcode Instruction::opcode() const {
  return static_cast< queso::Opcode >(opcode_);
}
inline void Instruction::set_opcode(queso::Opcode value) {
  GOOGLE_DCHECK(queso::Opcode_IsValid(value));
  set_has_opcode();
  opcode_ = value;
}

// optional .queso.Variable dst = 2;
inline bool Instruction::has_dst() const {
  return (_has_bits_[0] & 0x00000002u) != 0;
}
inline void Instruction::set_has_dst() {
  _has_bits_[0] |= 0x00000002u;
}
inline void Instruction::clear_has_dst() {
  _has_bits_[0] &= ~0x00000002u;
}
inline void Instruction::clear_dst() {
  if (dst_ != NULL) dst_->::queso::Variable::Clear();
  clear_has_dst();
}
inline const ::queso::Variable& Instruction::dst() const {
  return dst_ != NULL ? *dst_ : *default_instance_->dst_;
}
inline ::queso::Variable* Instruction::mutable_dst() {
  set_has_dst();
  if (dst_ == NULL) dst_ = new ::queso::Variable;
  return dst_;
}
inline ::queso::Variable* Instruction::release_dst() {
  clear_has_dst();
  ::queso::Variable* temp = dst_;
  dst_ = NULL;
  return temp;
}

// optional .queso.Variable lhs = 3;
inline bool Instruction::has_lhs() const {
  return (_has_bits_[0] & 0x00000004u) != 0;
}
inline void Instruction::set_has_lhs() {
  _has_bits_[0] |= 0x00000004u;
}
inline void Instruction::clear_has_lhs() {
  _has_bits_[0] &= ~0x00000004u;
}
inline void Instruction::clear_lhs() {
  if (lhs_ != NULL) lhs_->::queso::Variable::Clear();
  clear_has_lhs();
}
inline const ::queso::Variable& Instruction::lhs() const {
  return lhs_ != NULL ? *lhs_ : *default_instance_->lhs_;
}
inline ::queso::Variable* Instruction::mutable_lhs() {
  set_has_lhs();
  if (lhs_ == NULL) lhs_ = new ::queso::Variable;
  return lhs_;
}
inline ::queso::Variable* Instruction::release_lhs() {
  clear_has_lhs();
  ::queso::Variable* temp = lhs_;
  lhs_ = NULL;
  return temp;
}

// optional .queso.Variable rhs = 4;
inline bool Instruction::has_rhs() const {
  return (_has_bits_[0] & 0x00000008u) != 0;
}
inline void Instruction::set_has_rhs() {
  _has_bits_[0] |= 0x00000008u;
}
inline void Instruction::clear_has_rhs() {
  _has_bits_[0] &= ~0x00000008u;
}
inline void Instruction::clear_rhs() {
  if (rhs_ != NULL) rhs_->::queso::Variable::Clear();
  clear_has_rhs();
}
inline const ::queso::Variable& Instruction::rhs() const {
  return rhs_ != NULL ? *rhs_ : *default_instance_->rhs_;
}
inline ::queso::Variable* Instruction::mutable_rhs() {
  set_has_rhs();
  if (rhs_ == NULL) rhs_ = new ::queso::Variable;
  return rhs_;
}
inline ::queso::Variable* Instruction::release_rhs() {
  clear_has_rhs();
  ::queso::Variable* temp = rhs_;
  rhs_ = NULL;
  return temp;
}

// optional .queso.Variable src = 5;
inline bool Instruction::has_src() const {
  return (_has_bits_[0] & 0x00000010u) != 0;
}
inline void Instruction::set_has_src() {
  _has_bits_[0] |= 0x00000010u;
}
inline void Instruction::clear_has_src() {
  _has_bits_[0] &= ~0x00000010u;
}
inline void Instruction::clear_src() {
  if (src_ != NULL) src_->::queso::Variable::Clear();
  clear_has_src();
}
inline const ::queso::Variable& Instruction::src() const {
  return src_ != NULL ? *src_ : *default_instance_->src_;
}
inline ::queso::Variable* Instruction::mutable_src() {
  set_has_src();
  if (src_ == NULL) src_ = new ::queso::Variable;
  return src_;
}
inline ::queso::Variable* Instruction::release_src() {
  clear_has_src();
  ::queso::Variable* temp = src_;
  src_ = NULL;
  return temp;
}

// optional .queso.Variable condition = 6;
inline bool Instruction::has_condition() const {
  return (_has_bits_[0] & 0x00000020u) != 0;
}
inline void Instruction::set_has_condition() {
  _has_bits_[0] |= 0x00000020u;
}
inline void Instruction::clear_has_condition() {
  _has_bits_[0] &= ~0x00000020u;
}
inline void Instruction::clear_condition() {
  if (condition_ != NULL) condition_->::queso::Variable::Clear();
  clear_has_condition();
}
inline const ::queso::Variable& Instruction::condition() const {
  return condition_ != NULL ? *condition_ : *default_instance_->condition_;
}
inline ::queso::Variable* Instruction::mutable_condition() {
  set_has_condition();
  if (condition_ == NULL) condition_ = new ::queso::Variable;
  return condition_;
}
inline ::queso::Variable* Instruction::release_condition() {
  clear_has_condition();
  ::queso::Variable* temp = condition_;
  condition_ = NULL;
  return temp;
}

// optional .queso.Variable t = 7;
inline bool Instruction::has_t() const {
  return (_has_bits_[0] & 0x00000040u) != 0;
}
inline void Instruction::set_has_t() {
  _has_bits_[0] |= 0x00000040u;
}
inline void Instruction::clear_has_t() {
  _has_bits_[0] &= ~0x00000040u;
}
inline void Instruction::clear_t() {
  if (t_ != NULL) t_->::queso::Variable::Clear();
  clear_has_t();
}
inline const ::queso::Variable& Instruction::t() const {
  return t_ != NULL ? *t_ : *default_instance_->t_;
}
inline ::queso::Variable* Instruction::mutable_t() {
  set_has_t();
  if (t_ == NULL) t_ = new ::queso::Variable;
  return t_;
}
inline ::queso::Variable* Instruction::release_t() {
  clear_has_t();
  ::queso::Variable* temp = t_;
  t_ = NULL;
  return temp;
}

// optional .queso.Variable e = 8;
inline bool Instruction::has_e() const {
  return (_has_bits_[0] & 0x00000080u) != 0;
}
inline void Instruction::set_has_e() {
  _has_bits_[0] |= 0x00000080u;
}
inline void Instruction::clear_has_e() {
  _has_bits_[0] &= ~0x00000080u;
}
inline void Instruction::clear_e() {
  if (e_ != NULL) e_->::queso::Variable::Clear();
  clear_has_e();
}
inline const ::queso::Variable& Instruction::e() const {
  return e_ != NULL ? *e_ : *default_instance_->e_;
}
inline ::queso::Variable* Instruction::mutable_e() {
  set_has_e();
  if (e_ == NULL) e_ = new ::queso::Variable;
  return e_;
}
inline ::queso::Variable* Instruction::release_e() {
  clear_has_e();
  ::queso::Variable* temp = e_;
  e_ = NULL;
  return temp;
}

// optional .queso.Variable address = 9;
inline bool Instruction::has_address() const {
  return (_has_bits_[0] & 0x00000100u) != 0;
}
inline void Instruction::set_has_address() {
  _has_bits_[0] |= 0x00000100u;
}
inline void Instruction::clear_has_address() {
  _has_bits_[0] &= ~0x00000100u;
}
inline void Instruction::clear_address() {
  if (address_ != NULL) address_->::queso::Variable::Clear();
  clear_has_address();
}
inline const ::queso::Variable& Instruction::address() const {
  return address_ != NULL ? *address_ : *default_instance_->address_;
}
inline ::queso::Variable* Instruction::mutable_address() {
  set_has_address();
  if (address_ == NULL) address_ = new ::queso::Variable;
  return address_;
}
inline ::queso::Variable* Instruction::release_address() {
  clear_has_address();
  ::queso::Variable* temp = address_;
  address_ = NULL;
  return temp;
}

// optional .queso.Variable mem = 10;
inline bool Instruction::has_mem() const {
  return (_has_bits_[0] & 0x00000200u) != 0;
}
inline void Instruction::set_has_mem() {
  _has_bits_[0] |= 0x00000200u;
}
inline void Instruction::clear_has_mem() {
  _has_bits_[0] &= ~0x00000200u;
}
inline void Instruction::clear_mem() {
  if (mem_ != NULL) mem_->::queso::Variable::Clear();
  clear_has_mem();
}
inline const ::queso::Variable& Instruction::mem() const {
  return mem_ != NULL ? *mem_ : *default_instance_->mem_;
}
inline ::queso::Variable* Instruction::mutable_mem() {
  set_has_mem();
  if (mem_ == NULL) mem_ = new ::queso::Variable;
  return mem_;
}
inline ::queso::Variable* Instruction::release_mem() {
  clear_has_mem();
  ::queso::Variable* temp = mem_;
  mem_ = NULL;
  return temp;
}

// optional .queso.Variable srcmem = 11;
inline bool Instruction::has_srcmem() const {
  return (_has_bits_[0] & 0x00000400u) != 0;
}
inline void Instruction::set_has_srcmem() {
  _has_bits_[0] |= 0x00000400u;
}
inline void Instruction::clear_has_srcmem() {
  _has_bits_[0] &= ~0x00000400u;
}
inline void Instruction::clear_srcmem() {
  if (srcmem_ != NULL) srcmem_->::queso::Variable::Clear();
  clear_has_srcmem();
}
inline const ::queso::Variable& Instruction::srcmem() const {
  return srcmem_ != NULL ? *srcmem_ : *default_instance_->srcmem_;
}
inline ::queso::Variable* Instruction::mutable_srcmem() {
  set_has_srcmem();
  if (srcmem_ == NULL) srcmem_ = new ::queso::Variable;
  return srcmem_;
}
inline ::queso::Variable* Instruction::release_srcmem() {
  clear_has_srcmem();
  ::queso::Variable* temp = srcmem_;
  srcmem_ = NULL;
  return temp;
}

// optional .queso.Variable dstmem = 12;
inline bool Instruction::has_dstmem() const {
  return (_has_bits_[0] & 0x00000800u) != 0;
}
inline void Instruction::set_has_dstmem() {
  _has_bits_[0] |= 0x00000800u;
}
inline void Instruction::clear_has_dstmem() {
  _has_bits_[0] &= ~0x00000800u;
}
inline void Instruction::clear_dstmem() {
  if (dstmem_ != NULL) dstmem_->::queso::Variable::Clear();
  clear_has_dstmem();
}
inline const ::queso::Variable& Instruction::dstmem() const {
  return dstmem_ != NULL ? *dstmem_ : *default_instance_->dstmem_;
}
inline ::queso::Variable* Instruction::mutable_dstmem() {
  set_has_dstmem();
  if (dstmem_ == NULL) dstmem_ = new ::queso::Variable;
  return dstmem_;
}
inline ::queso::Variable* Instruction::release_dstmem() {
  clear_has_dstmem();
  ::queso::Variable* temp = dstmem_;
  dstmem_ = NULL;
  return temp;
}

// optional .queso.Variable value = 13;
inline bool Instruction::has_value() const {
  return (_has_bits_[0] & 0x00001000u) != 0;
}
inline void Instruction::set_has_value() {
  _has_bits_[0] |= 0x00001000u;
}
inline void Instruction::clear_has_value() {
  _has_bits_[0] &= ~0x00001000u;
}
inline void Instruction::clear_value() {
  if (value_ != NULL) value_->::queso::Variable::Clear();
  clear_has_value();
}
inline const ::queso::Variable& Instruction::value() const {
  return value_ != NULL ? *value_ : *default_instance_->value_;
}
inline ::queso::Variable* Instruction::mutable_value() {
  set_has_value();
  if (value_ == NULL) value_ = new ::queso::Variable;
  return value_;
}
inline ::queso::Variable* Instruction::release_value() {
  clear_has_value();
  ::queso::Variable* temp = value_;
  value_ = NULL;
  return temp;
}

// optional string comment = 14;
inline bool Instruction::has_comment() const {
  return (_has_bits_[0] & 0x00002000u) != 0;
}
inline void Instruction::set_has_comment() {
  _has_bits_[0] |= 0x00002000u;
}
inline void Instruction::clear_has_comment() {
  _has_bits_[0] &= ~0x00002000u;
}
inline void Instruction::clear_comment() {
  if (comment_ != &::google::protobuf::internal::kEmptyString) {
    comment_->clear();
  }
  clear_has_comment();
}
inline const ::std::string& Instruction::comment() const {
  return *comment_;
}
inline void Instruction::set_comment(const ::std::string& value) {
  set_has_comment();
  if (comment_ == &::google::protobuf::internal::kEmptyString) {
    comment_ = new ::std::string;
  }
  comment_->assign(value);
}
inline void Instruction::set_comment(const char* value) {
  set_has_comment();
  if (comment_ == &::google::protobuf::internal::kEmptyString) {
    comment_ = new ::std::string;
  }
  comment_->assign(value);
}
inline void Instruction::set_comment(const char* value, size_t size) {
  set_has_comment();
  if (comment_ == &::google::protobuf::internal::kEmptyString) {
    comment_ = new ::std::string;
  }
  comment_->assign(reinterpret_cast<const char*>(value), size);
}
inline ::std::string* Instruction::mutable_comment() {
  set_has_comment();
  if (comment_ == &::google::protobuf::internal::kEmptyString) {
    comment_ = new ::std::string;
  }
  return comment_;
}
inline ::std::string* Instruction::release_comment() {
  clear_has_comment();
  if (comment_ == &::google::protobuf::internal::kEmptyString) {
    return NULL;
  } else {
    ::std::string* temp = comment_;
    comment_ = const_cast< ::std::string*>(&::google::protobuf::internal::kEmptyString);
    return temp;
  }
}

// optional uint64 trace_address = 15;
inline bool Instruction::has_trace_address() const {
  return (_has_bits_[0] & 0x00004000u) != 0;
}
inline void Instruction::set_has_trace_address() {
  _has_bits_[0] |= 0x00004000u;
}
inline void Instruction::clear_has_trace_address() {
  _has_bits_[0] &= ~0x00004000u;
}
inline void Instruction::clear_trace_address() {
  trace_address_ = GOOGLE_ULONGLONG(0);
  clear_has_trace_address();
}
inline ::google::protobuf::uint64 Instruction::trace_address() const {
  return trace_address_;
}
inline void Instruction::set_trace_address(::google::protobuf::uint64 value) {
  set_has_trace_address();
  trace_address_ = value;
}

// -------------------------------------------------------------------

// Instructions

// repeated .queso.Instruction instruction = 1;
inline int Instructions::instruction_size() const {
  return instruction_.size();
}
inline void Instructions::clear_instruction() {
  instruction_.Clear();
}
inline const ::queso::Instruction& Instructions::instruction(int index) const {
  return instruction_.Get(index);
}
inline ::queso::Instruction* Instructions::mutable_instruction(int index) {
  return instruction_.Mutable(index);
}
inline ::queso::Instruction* Instructions::add_instruction() {
  return instruction_.Add();
}
inline const ::google::protobuf::RepeatedPtrField< ::queso::Instruction >&
Instructions::instruction() const {
  return instruction_;
}
inline ::google::protobuf::RepeatedPtrField< ::queso::Instruction >*
Instructions::mutable_instruction() {
  return &instruction_;
}


// @@protoc_insertion_point(namespace_scope)

}  // namespace queso

#ifndef SWIG
namespace google {
namespace protobuf {

template <>
inline const EnumDescriptor* GetEnumDescriptor< queso::VarType>() {
  return queso::VarType_descriptor();
}
template <>
inline const EnumDescriptor* GetEnumDescriptor< queso::Opcode>() {
  return queso::Opcode_descriptor();
}

}  // namespace google
}  // namespace protobuf
#endif  // SWIG

// @@protoc_insertion_point(global_scope)

#endif  // PROTOBUF_queso_2eproto__INCLUDED
