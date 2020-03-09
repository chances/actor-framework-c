import sys
import os
import re
from optparse import OptionParser
import ConfigParser


try:
    import pygccxml
except ImportError:
    print "You must instal pygccxml in-order to run this script."
    sys.exit(1)

from pygccxml.declarations.cpptypes import declarated_t, ellipsis_t, type_qualifiers_t, unknown_t, member_function_type_t, void_t
from pygccxml.declarations.type_traits import base_type, is_const, is_volatile, remove_volatile, is_calldef_pointer, is_pointer, remove_pointer, is_array, is_reference, remove_reference, is_bool, is_void, is_fundamental, remove_const
from pygccxml.declarations.type_traits_classes import has_trivial_constructor, has_public_constructor, has_public_destructor, has_copy_constructor, has_destructor, has_public_assign, is_enum, is_class
from pygccxml.declarations.calldef_members import constructor_t, destructor_t, member_function_t, member_operator_t
from pygccxml.declarations.calldef_types import VIRTUALITY_TYPES
from pygccxml.declarations.class_declaration import ACCESS_TYPES, class_declaration_t
from pygccxml.declarations.free_calldef import free_function_t, free_operator_t
from pygccxml.declarations.typedef import typedef_t
    
class UnsupportedError(NotImplementedError):
    """Exception for unsupported features."""
    pass

DEBUG = False

ARRAY_SIZE_VAR_NAME = 'arr_size'
RET_VAL_ON_EXCEPTION = 'NULL'
GENERATED_FILE_SUFFIX = "_C_Wrapper"

THIS_VAR_NAME = 'class_this'
RET_VAL_CLASS_NAME = 'ptr_ret_val_class'
WAS_EXCEPTION_ARG_NAME = 'ptr_was_exception'
C_BOOL_TYPE_NAME = 'BOOL_C'
C_TRUE_VAL = 'TRUE_C'
C_FALSE_VAL = 'FALSE_C'
# TODO: check whether those vars are in [arg_info.arg_name for arg_info in func_info.func_args_info_list], and if so - add a suffix.

PYGCCXML_DTOR_TOKEN = re.compile(r"._\d+")

PYGCCXML_FUNC_DECL_ARGS = re.compile(r".*\((.*?)\)")    # =The last ()'s contents.

OPERATOR_MAP = {
    '+': "plus",
    '-': "minus",
    '*': "multiply",
    '/': "division",
    '%': "mod",
    '^': "bitwise_xor",
    '&': "bitwise_and",
    '|': "bitwise_or",
    '~': "bitwise_not",
    '!': "not",
    '=': "assign",
    '<': "smaller",
    '>': "bigger",
    '+=': "plus_assign",
    '-=': "minus_assign",
    '*=': "multiply_assign",
    '/=': "division_assign",
    '%=': "mod_assign",
    '^=': "bitwise_xor_assign",
    '&=': "bitwise_and_assign",
    '|=': "bitwise_or_assign",
    '<<': "shift_left",
    '>>': "shift_right",
    '<<=': "shift_left_assign",
    '>>=': "shift_right_assign",
    '==': "equal",
    '!=': "not_assign",
    '<=': "smaller_or_equal",
    '>=': "bigger_or_equal",
    '&&': "and",
    '||': "or",
    '++': "plus_plus",
    '--': "minus_minus",
    ',': "comma",
    '->*': "pointer_redirect",
    '->': "redirect",
    '()': "function_call",
    '[]': "subscript",
    'new': "new",
    'new []': "new_array",
    'delete': "delete",
    'delete []': "delete_array"
}   # TODO: Check the function_call op.
    
OPERATORS_LIST_BY_LENGTH = sorted(OPERATOR_MAP.keys(), key=len, reverse=True)   # From the longest to the shortest, to check '+=' before '+' (or '=').

# Proxy funcs to shield from possible pygccxml implementation changes:

def is_declarated_type(arg):
    """Returns whether the argument is a declaration type."""
    return isinstance(arg, declarated_t)

def is_ellipsis(arg):
    """Returns whether the argument is ellipsis (...)."""
    return isinstance(arg, ellipsis_t)

def is_qualifier(arg):
    """Returns whether the argument is a qualifier."""
    return isinstance(arg, type_qualifiers_t)

def is_unknown_type(arg):
    """Returns whether the argument is an unknown type."""
    return isinstance(arg, unknown_t)

def is_member_function_type(arg):
    """Returns whether the argument is a member function type."""
    return isinstance(arg, member_function_type_t)
    
def is_typedef(arg):
    """Returns whether the argument is a typedef."""
    return isinstance(arg, typedef_t)

def get_public_default_ctor(cls):
    """Returns the class public default ctor, or None if one doesn't exist."""
    return has_trivial_constructor(cls)
    
def has_public_dtor(cls):
    """Returns whether the class has a public destructor."""
    return has_public_destructor(cls)
        
def is_abstract_class_declaration(arg):
    """Returns whether arg is a class declaration that is not a typedef - for example: typedef abstract_class_decl typedef_decl"""
    #return is_class_declaration(decl) and not is_typedef(decl)
    return isinstance(arg, class_declaration_t)

def get_full_name(decl, sub_seq=None):
    """Generates a C++ token's name, including namespaces."""
    #if is_abstract_class_declaration(decl):
    #    ns_name = get_full_name(decl.parent)
    #    if not ns_name.endswith("::"):  # True to every namespace except for the global namespace.
    #        ns_name += "::"
    #    return ns_name + decl.declaration.name
    full_name = pygccxml.declarations.full_name(decl)
    if sub_seq is not None:
        for old_token, new_token in sub_seq:
            full_name = full_name.replace(old_token, new_token)
    return full_name
    
    
def get_func_decl_str(func):
    """Return a func declaration string."""
    args_str = PYGCCXML_FUNC_DECL_ARGS.match(func.create_decl_string()).group(1).strip()
    return "%s(%s)" % (get_full_name(func), args_str)

def python_to_camel_case(decl_str):
    """Python to (Upper-)Camel Case naming convention, e.g.: "func_name" -> "FuncName" """
    words = decl_str.split("_")
    return "".join([word.capitalize() for word in words])

def strip_global_ns(decl_str):
    """Strip the global namespace ot a C++ declaration string."""
    return decl_str.lstrip(':')
    
def get_c_name(decl, is_full_name=True, c_sub_seq=None):
    """Generates a C token from a C++ token."""
    if is_full_name:
        cpp_name = get_full_name(decl)
    else:
        cpp_name = decl.name
    c_name = strip_global_ns(cpp_name).replace('::', '_').replace('~', "delete_").replace('>', '_').replace('<', '_').replace(' ', '').replace(',', '_').replace('*', "_ptr_").replace('&', "_ref_")
    # The first substitution is for namespaces. The second is for dtors. All others are for templates.
    if c_sub_seq is not None:
        for old_token, new_token in c_sub_seq:
            c_name = c_name.replace(old_token, new_token)
    return c_name

def get_class_ptr_name(class_c_name):
    """Generates a class pointer token from its C class token."""
    return "PTR_%s" % (class_c_name,)

def get_error_arg_str(is_c99):
    """Returns the type-name string of the error arg."""
    if is_c99:
        c_bool_type_str = "bool"
    else:
        c_bool_type_str = C_BOOL_TYPE_NAME
    return "%s *%s" % (c_bool_type_str, WAS_EXCEPTION_ARG_NAME)
    
def get_enum_c_name(enum):
    """Generates a C enum token from a C++ one."""
    enum_name = get_c_name(enum)
    if enum_name == enum.name:  # To prevent enum redefinition in the global scope. unlike typedef redefinition - it causes a compilation error.
        enum_name += "_C"   # TODO: Can (still) cause redefinition.
    return enum_name

def get_header_guard_name(generated_base_file_path):
    """Returns the header guard. for a specific header file name."""
    generated_header_file_name = os.path.basename(generated_base_file_path+".h")
    return generated_header_file_name.upper().replace('.', '_')

def is_public_concrete_func(member_func):
    """Returns whether a member function\operator is public and concrete."""
    return ((member_func.access_type == ACCESS_TYPES.PUBLIC) and (member_func.virtuality != VIRTUALITY_TYPES.PURE_VIRTUAL))

def get_class_by_decl(global_ns, class_decl, is_safe=True):
    """Returns the class for a class declaration."""
    try:
        return global_ns.class_(get_full_name(class_decl))
    except:
        if is_safe:
            raise UnsupportedError("No concrete class for class declaration %s. Possible reason: template instantiation is missing." % (str(class_decl),))
        else:
            raise
            
def exception_handling_str(generate_exception_handling_code, output_str, generate_error_arg, is_c99, is_void_ret_type, ret_type_c_str):
    """Generates exception handling wrapper around an implementation output string, with or without an error argument."""
    if not generate_exception_handling_code:
        return output_str
        
    if is_void_ret_type:
        on_exception_return_str = ""
    else:
        on_exception_return_str = "\treturn (%s) %s;\n" % (ret_type_c_str, RET_VAL_ON_EXCEPTION)
    if is_c99:
        c_false_str = "false"
        c_true_str = "true" 
    else:
        c_false_str = C_FALSE_VAL
        c_true_str = C_TRUE_VAL
    error_arg_no_exception_str = ""
    error_arg_was_exception_str = ""
    if generate_error_arg:
        error_arg_no_exception_str = "if((void *)%s != NULL) (*%s) = %s;\n" % (WAS_EXCEPTION_ARG_NAME, WAS_EXCEPTION_ARG_NAME, c_false_str)
        error_arg_was_exception_str = "if((void *)%s != NULL) (*%s) = %s;\n" % (WAS_EXCEPTION_ARG_NAME, WAS_EXCEPTION_ARG_NAME, c_true_str)
    return """    try {
        %s%s
    }
    catch(...) {
        %s\t%s
    }""" % (error_arg_no_exception_str, output_str, error_arg_was_exception_str, on_exception_return_str)


class MemoryFile(object):
    """A class to implement a file on the memory."""
    
    MARK_TOKEN = "@@@"
    def __init__(self, path):
        self.path = path
        self.lines = [self.MARK_TOKEN]
        
    def close(self):
        """Closes the memory file."""
        self.lines.remove(self.MARK_TOKEN)
        out_file = open(self.path, 'w')
        out_file.write("\n".join(self.lines))
        out_file.close()
        
    def write(self, str):
        """Writes a string to the memory file."""
        self.lines.append(str)
        
    def write_at_mark(self, str):
        """Writes a string at the mark position of the memory file."""
        self.lines.insert(self.lines.index(self.MARK_TOKEN), str)
        
    def set_mark(self):
        """Set the mark position in the memory file."""
        self.lines.remove(self.MARK_TOKEN)
        self.lines.append(self.MARK_TOKEN)
        
        
class BasicOutputClass(object):
    """A class to handle the files output."""
    
    def __init__(self, header_file_path, generate_dl):
        self.header_file_path = header_file_path
        header_file_name = os.path.basename(header_file_path)
        generated_base_file_name = header_file_name[:header_file_name.rindex(".h")]+GENERATED_FILE_SUFFIX
        # self.generated_base_file_path = os.path.join(os.path.dirname(header_file_path), generated_base_file_name)
        self.generated_base_file_path = os.path.join(os.getcwd(), generated_base_file_name)
        self.generate_dl = generate_dl
        self.cpp_file = MemoryFile(self.generated_base_file_path+".cpp")
        self.h_file = MemoryFile(self.generated_base_file_path+".h")
        if generate_dl:
            self.def_file = MemoryFile(self.generated_base_file_path+".def")
            
    def close(self):
        """Forces the output file creation."""
        self.cpp_file.close()
        self.h_file.close()
        if self.generate_dl:
            self.def_file.close()
            
    def write_to_cpp_file(self, output_str):
        """Write a string in the cpp file."""
        self.cpp_file.write(output_str+'\n')
        if DEBUG:
            print "CPP: %s" % (output_str,)
        
    def write_to_h_file(self, output_str):
        """Write a string in the header file."""
        self.h_file.write(output_str+'\n')
        if DEBUG:
            print "H: %s" % (output_str,)
    
    def write_at_h_file_mark(self, output_str):
        """Write a string in the header file's mark."""
        self.h_file.write_at_mark(output_str+'\n')
        if DEBUG:
            print "H (FRONT): %s" % (output_str,)
            
    def write_to_def_file(self, output_str):
        """Write a string in the def file, if this option is enabled."""
        if self.generate_dl:
            self.def_file.write(output_str+'\n')
            if DEBUG:
                print "DEF: %s" % (output_str,)
                
    def mark_h_file_front(self):
        """Mark the start of the header file, where the typedefs would be written."""
        self.h_file.set_mark()
                

class CodeOutputClass(BasicOutputClass):
    """A class to handle the code output."""
    
    def __init__(self, header_file_path, generate_exception_handling_code, generate_dl, is_compact_string, generate_operators, is_assume_copy, is_assume_assign, generate_error_arg, is_verbose, is_camel_case):
        super(CodeOutputClass, self).__init__(header_file_path, generate_dl)
        self.generate_exception_handling_code = generate_exception_handling_code
        self.is_compact_string = is_compact_string
        self.generate_operators = generate_operators
        self.is_assume_copy = is_assume_copy
        self.is_assume_assign = is_assume_assign
        self.generate_error_arg = generate_error_arg
        self.is_verbose = is_verbose
        self.is_camel_case = is_camel_case
    
    def output_class_typedef(self, cls, global_context, alternate_class_c_ptr_name=None):
        """Outputs a C class representation."""
        class_c_name, class_c_ptr_name = global_context.add_class(cls, alternate_class_c_ptr_name)
        verbose_str = ""
        if self.is_verbose:
            verbose_str = "\t/* A C wrapper for class %s */" % (get_full_name(cls),)
        self.write_at_h_file_mark("typedef struct _%s *%s;%s" % (class_c_name, class_c_ptr_name, verbose_str))
    
    def output_func(self, func, global_context, is_array_version=False, generate_min_args_ver_only=False):
        """Outputs a function C wrapper."""
        
        func_info = FuncInfo(func, global_context, self.generate_error_arg, generate_min_args_ver_only)
        c_func_name = func_info.c_func_name
        
        if (func_info.func_type == func_info.DTOR):
            # To fix the pygccxml dtor name of ~._<num> for declarated classes.
            c_func_name = PYGCCXML_DTOR_TOKEN.sub(get_c_name(func.parent, False), c_func_name)
        
        for used_def_vals_num in range(func_info.optional_args_num+1):  # Variations to handle default values.
            func_args_decl_list = [arg_c_str for arg_c_str in func_info.gen_func_args_c_strs()]
            func_args = func_args_decl_list[:len(func_args_decl_list)-used_def_vals_num]
            if is_array_version and (func_info.func_type == func_info.CTOR):
                func_args.append("size_t %s" % (ARRAY_SIZE_VAR_NAME,))  # Needed for new[].
            func_args_str = ", ".join(func_args)
            func_args_impl_list = []
            for arg_info in func_info.func_args_info_list[:len(func_info.func_args_info_list)-used_def_vals_num]:
                redirection_str = ""
                if arg_info.is_redirected:
                    redirection_str = "*"
                cast_str = ""
                if arg_info.cast_str:
                    cast_str = "(%s)" % (arg_info.cast_str,)
                arg_name = arg_info.arg_name
                func_args_impl_list.append((redirection_str, cast_str, arg_name))
            func_args_impl_str = ", ".join(["%s%s%s" % (redirection_str, cast_str, arg_name) for redirection_str, cast_str, arg_name in func_args_impl_list])
            
            if is_array_version:
                c_func_name = "%s_array" % (c_func_name,)
            unique_c_func_name = global_context.generate_unique_token(c_func_name)
            if self.is_camel_case:
                unique_c_func_name = python_to_camel_case(unique_c_func_name)
                
            self.write_to_def_file('\t'+unique_c_func_name)
            func_prototype = "%s %s(%s)" % (func_info.ret_type_info.arg_type_c_str, unique_c_func_name , func_args_str)
            verbose_str = ""
            if self.is_verbose:
                verbose_str = "\t/* A C wrapper for func %s */" % (get_func_decl_str(func),)
            self.write_to_h_file("%s;%s" % (func_prototype, verbose_str))
            self.write_to_cpp_file("%s {" % (func_prototype,))
            
            ret_val_c_str = "%s%s(%s)" % (func_info.class_redirection, func_info.full_name, func_args_impl_str)
            
            output_str = "\t\t"
            if (func_info.func_type == func_info.CTOR):
                if func_info.is_default_ctor():
                    ctor_args_str = ""
                else:
                    ctor_args_str = "(%s)" % (func_args_impl_str,)
                array_str = ""
                if is_array_version:
                    array_str = "[%s]" % (ARRAY_SIZE_VAR_NAME,)
                nothrow_str = ""
                if not self.generate_exception_handling_code:
                    nothrow_str = "(std::nothrow) "
                ret_val_c_str = "new %s%s%s%s" % (nothrow_str, func_info.ret_type_info.class_name, ctor_args_str, array_str)
            elif (func_info.func_type == func_info.DTOR):
                array_str = ""
                if is_array_version:
                    array_str = "[]"
                cast_str = "(%s*)" % (global_context.get_full_name(func.parent),)
                ret_val_c_str = "delete %s(%s%s)" % (array_str, cast_str, THIS_VAR_NAME)
            else:
                if (func_info.ret_type_info.is_class) and (func_info.ret_type_info.is_redirected):# and not(func_info.ret_type_info.is_ptr):
                    # Special case: a class should be returned by value. We'll try to return a pointer to a new instance, if possible.
                    nothrow_str = ""
                    if not self.generate_exception_handling_code:
                        nothrow_str = "(std::nothrow) "
                    if func_info.ret_type_info.can_create_with_copy_constructor or ((func_info.ret_type_info.can_create_with_copy_constructor is None) and self.is_assume_copy):
                        ret_val_c_str = "new %s%s(%s)" % (nothrow_str, func_info.ret_type_info.class_name, ret_val_c_str)
                    elif func_info.ret_type_info.can_create_with_default_constructor or ((func_info.ret_type_info.can_create_with_default_constructor is None) and self.is_assume_assign):
                        output_str += "%s *%s = new %s%s;\n" % (func_info.ret_type_info.class_name, RET_VAL_CLASS_NAME, nothrow_str, func_info.ret_type_info.class_name)
                        nothrow_null_check_str = ""
                        if not self.generate_exception_handling_code:
                            nothrow_null_check_str = "if((void*)%s != NULL) " % (RET_VAL_CLASS_NAME,)
                        output_str += "%s*%s = %s;\n" % (nothrow_null_check_str, RET_VAL_CLASS_NAME, ret_val_c_str)
                        ret_val_c_str = RET_VAL_CLASS_NAME
                    else:
                        raise UnsupportedError("Cannot handle a class return value without a public copy ctor or public default ctor an assignment operator in %s" % (func_info.full_name, ))
            if func_info.ret_type_info.is_void():
                return_str = ""
            else:
                return_str = "return "
            cast_str = ""
            if func_info.ret_type_info.cast_str:
                cast_str = "(%s)" % (func_info.ret_type_info.arg_type_c_str,)
            ref_str = ""
            if (func_info.ret_type_info.is_ref and not(func_info.ret_type_info.is_class)):
                ref_str = "&"
            output_str += "%s%s%s%s;" % (return_str, cast_str, ref_str, ret_val_c_str)
            output_str = exception_handling_str(self.generate_exception_handling_code, output_str, self.generate_error_arg, global_context.is_c99, func_info.ret_type_info.is_void(), func_info.ret_type_info.arg_type_c_str)
            self.write_to_cpp_file("%s" % (output_str,))
            self.write_to_cpp_file( "}")
            
    def output_std_string(self, string_typedef, global_context):
        """Outputs the std::(w)string C wrapper."""
        is_wstring, string_class, string_c_ptr_name = global_context.add_std_string(string_typedef)
        if self.is_compact_string:    # Otherwise, it would be outputed like other classes, recursively, as needed.
            self.output_class_typedef(string_class, global_context, string_c_ptr_name)
            public_default_ctor = get_public_default_ctor(string_class)
            self.output_func(public_default_ctor, global_context)
            self.output_func(public_default_ctor, global_context, True)
            
            if is_wstring:
                char_str = "wchar_t"
            else:
                char_str = "char"
            char_ptr_str = "const %s *" % (char_str,)
            for ctor in string_class.constructors():
                if (len(ctor.required_args) == 1) and (char_ptr_str == ctor.required_args[0].type.build_decl_string()):
                    self.output_func(ctor, global_context, False, True)    # Outputs the std::(w)string(char*) ctor. We don't generate the allocator<char_str> optional arg.
                    break
            
            string_dtor = has_destructor(string_class)
            self.output_func(string_dtor, global_context)
            self.output_func(string_dtor, global_context, True)
            c_str_func = string_class.member_function("c_str")
            self.output_func(c_str_func, global_context)
    
    def output_enum(self, enum, global_context):
        """Outputs an enum C version."""
        enum_name = get_enum_c_name(enum)
        verbose_str = ""
        if self.is_verbose:
            verbose_str = "\t/* A C wrapper for enum %s */" % (get_full_name(enum),) 
        self.write_at_h_file_mark("enum %s {" % (enum_name,))
        self.write_at_h_file_mark("%s" % (",\n".join(["\t%s=%s" % (global_context.generate_unique_token(key, True), val) for key, val in enum.values]),))    # Needed to handle 2 enums with same keys in different namespaces.
        self.write_at_h_file_mark("};%s" % (verbose_str,))
        global_context.add_enum(enum)
    
    def output_typedef(self, typedef, global_context):
        """Outputs a typedef C version."""
        typedef_info=ArgInfo(typedef.type, global_context, get_c_name(typedef))
        if typedef_info.is_c_decl:  # There is no support for typedefs that aren't C declerations - they'll be stripped to their raw C-type.
            verbose_str = ""
            if self.is_verbose:
                verbose_str = "\t/* A C wrapper for typedef %s */" % (get_full_name(typedef),)
            self.write_at_h_file_mark("typedef %s;%s" % (typedef_info.get_type_name_str(), verbose_str))
            global_context.add_typedef(typedef)
            # TODO: What about a typedef of an enum?
    
    def output_class_code(self, cls, global_context):
        """Output cls class code."""
        for ctor in cls.constructors(allow_empty=True):
            if (ctor.access_type == ACCESS_TYPES.PUBLIC):
                self.output_func(ctor, global_context)
    
        if has_public_dtor(cls):
            dtor = has_destructor(cls)
            self.output_func(dtor, global_context)
        
            public_default_ctor = get_public_default_ctor(cls)
            if public_default_ctor is not None:
                self.output_func(public_default_ctor, global_context, True)
                self.output_func(dtor, global_context, True)
        
        for member_func in cls.member_functions(allow_empty=True):
            if is_public_concrete_func(member_func):
                self.output_func(member_func, global_context)
        
        if self.generate_operators:        
            for member_op in cls.member_operators(allow_empty=True):
                if is_public_concrete_func(member_op):
                    self.output_func(member_op, global_context)
                    
    def output_prefix_code(self, is_c99):
        """Output the prefix code (includes, base typedefs, etc.)."""
        header_file_name = os.path.basename(self.header_file_path)
        generated_header_file_name = os.path.basename(self.generated_base_file_path+".h")
        generated_base_file_name = os.path.basename(self.generated_base_file_path)
        self.write_to_cpp_file("""#include "%s" """ % (header_file_name,))
        self.write_to_cpp_file("""#include "%s" """ % (generated_header_file_name,))
        self.write_to_def_file("""LIBRARY "%s"
EXPORTS""" % (generated_base_file_name,))
        
        header_guard = get_header_guard_name(self.generated_base_file_path)
        self.write_to_h_file("#ifndef %s" % (header_guard,))
        self.write_to_h_file("#define %s" % (header_guard,))
        
        self.write_to_h_file("""#ifdef __cplusplus
extern "C" {
#endif""")
        
        if not is_c99:
            self.write_to_h_file("#define %s 0" % (C_FALSE_VAL,))
            self.write_to_h_file("#define %s 1" % (C_TRUE_VAL,))
            self.write_to_h_file("typedef unsigned char %s;" % (C_BOOL_TYPE_NAME,))
        
        self.mark_h_file_front()
        
        if self.generate_dl:
            self.write_to_cpp_file("""#ifdef WIN32
#include <Windows.h>
extern "C" BOOL WINAPI DllMain(
    HINSTANCE hinstDLL,  // handle to DLL module
    DWORD fdwReason,     // reason for calling function
    LPVOID lpReserved )  // reserved
{
    // Perform actions based on the reason for calling.
    switch( fdwReason ) 
    { 
        case DLL_PROCESS_ATTACH:
         // Initialize once for each new process.
         // Return FALSE to fail DLL load.
            break;

        case DLL_THREAD_ATTACH:
         // Do thread-specific initialization.
            break;

        case DLL_THREAD_DETACH:
         // Do thread-specific cleanup.
            break;

        case DLL_PROCESS_DETACH:
         // Perform any necessary cleanup.
            break;
    }
    return TRUE;  // Successful DLL_PROCESS_ATTACH.
}
#endif  // WIN32""")
        
    def output_suffix_code(self):
        """Output the suffix code (header protectors, etc.)."""
        self.write_to_h_file("""#ifdef __cplusplus
}
#endif /* __cplusplus */""")
        generated_header_file_name = os.path.basename(self.generated_base_file_path+".h")
        self.write_to_h_file("#endif /* %s */" % (get_header_guard_name(self.generated_base_file_path),))


class CodeContext(object):
    """The code context (classes, typedefs, etc.) of the parsed header files."""
    
    CLASS = 0
    TYPEDEF = 1
    ENUM = 2
    
    def __init__(self, header_file_path, include_paths, compiler_type, is_c99):
        # Find the location of the xml generator (castxml or gccxml)
        generator_path, generator_name = pygccxml.utils.find_xml_generator()

        config = pygccxml.parser.xml_generator_configuration_t(xml_generator_path=generator_path, xml_generator=generator_name, include_paths=include_paths, compiler=compiler_type)
        decls = pygccxml.parser.parse([header_file_path], config)
        self.global_ns = pygccxml.declarations.get_global_namespace(decls)
        
        self.is_c99 = is_c99
        self.class_c_ptrs_map = {}
        self.token_freqs = {}
        self.typedefs_map = {}
        self.std_wstring_c_name = None
        self.std_string_c_name = None
        self.recursive_classes = []
        self.recursive_typedefs = []
        self.recursive_enums = []
        self.enums_map = {}
        
    def __getattr__(self, attr_name):
        """ CodeContext becomes a proxy to the global namespace attributes."""
        return getattr(self.global_ns, attr_name)
    
    def generate_unique_token(self, c_func_name, always_add_suffix=False):
        """Generates a unique C token."""
        # TODO: Use the args types instead, perhaps.
        if c_func_name in self.token_freqs:
            self.token_freqs[c_func_name] += 1
            return "%s%d" % (c_func_name, self.token_freqs[c_func_name])
        else:
            self.token_freqs[c_func_name] = 1
            if always_add_suffix:
                return "%s%d" % (c_func_name, self.token_freqs[c_func_name])
            else:
                return c_func_name
        
    def add_class(self, cls, alternate_class_c_ptr_name=None):
        """Add cls to the code context."""
        class_c_name = self.get_c_name(cls)
        if alternate_class_c_ptr_name is None:
            class_c_ptr_name = get_class_ptr_name(class_c_name)
        else:
            class_c_ptr_name = alternate_class_c_ptr_name
        self.class_c_ptrs_map[self.get_full_name(cls)] = class_c_ptr_name
        return (class_c_name, class_c_ptr_name)
        
    def add_typedef(self, typedef):
        """Add typedef to the code context."""
        self.typedefs_map[get_full_name(typedef)] = get_c_name(typedef)
        
    def add_enum(self, enum):
        """Add an enum to the code context."""
        self.enums_map[get_full_name(enum)] = get_enum_c_name(enum)
    
    def get_class_data(self, cls):
        """Get the class data for cls from the code context."""
        class_name = self.get_full_name(cls)
        if class_name not in self.class_c_ptrs_map:
            self.add_class(cls)
            if is_abstract_class_declaration(cls):
                cls = get_class_by_decl(self.global_ns, cls)
            if cls is not None:
                self.recursive_classes.append(cls)
        return (class_name, self.class_c_ptrs_map[class_name])
    
    def get_typedef_data(self, typedef):
        """Get the data for typedef from the code context."""
        typedef_name = get_full_name(typedef)
        if typedef_name not in self.typedefs_map:
            self.add_typedef(typedef)
            self.recursive_typedefs.append(typedef)
        return (typedef_name, self.typedefs_map[typedef_name])
    
    def get_enum_data(self, enum):
        """Get the data for enum from the code context."""
        enum_name = get_full_name(enum)
        if enum_name not in self.enums_map:
            self.add_enum(enum)
            self.recursive_enums.append(enum)
        return (enum_name, self.enums_map[enum_name])
        
    def add_std_string(self, string_typedef):
        """Add std::(w)string to the code context."""
        string_class = get_class_by_decl(self.global_ns, string_typedef.type.declaration, False)
        string_name = string_typedef.name
        is_wstring = ("wstring" in string_name)
        if is_wstring:
            self.wstring_ctor_name = get_public_default_ctor(string_class).name
            self.std_wstring_c_name = get_c_name(string_class)
            self.std_wstring_typedef_c_name = get_c_name(string_typedef)
            self.wstring_name = string_name
            self.wstring_full_name = get_full_name(string_class)
            self.wstring_full_typedef_name = get_full_name(string_typedef)
            string_c_ptr_name=get_class_ptr_name(self.std_wstring_typedef_c_name)    # We replace the ptr of the class with that of the typedef - more readable.
        else:
            self.string_ctor_name = get_public_default_ctor(string_class).name
            self.std_string_c_name = get_c_name(string_class)
            self.std_string_typedef_c_name = get_c_name(string_typedef)
            self.string_name = string_name
            self.string_full_name = get_full_name(string_class)
            self.string_full_typedef_name = get_full_name(string_typedef)
            string_c_ptr_name=get_class_ptr_name(self.std_string_typedef_c_name)    # We replace the ptr of the class with that of the typedef - more readable.
        self.add_typedef(string_typedef)
        return (is_wstring, string_class, string_c_ptr_name)
        
    def gen_recursive_elems(self):
        """Generates the elements gathered recursively that needs to be outputed."""
        while self.recursive_classes or self.recursive_typedefs or self.recursive_enums:
            # Not a for loop - since classes may get into self.recursive_classes during this loop (e.g.: std::string::allocator inside std::string methods). The same is true for typedefs.
            if self.recursive_enums:
                yield (self.ENUM, self.recursive_enums.pop(0))
            elif self.recursive_typedefs:
                yield (self.TYPEDEF, self.recursive_typedefs.pop(0))
            elif self.recursive_classes:
                yield (self.CLASS, self.recursive_classes.pop(0))
            
    def gen_sub_seq(self):
        """Generates a substitution sequence for C++ tokens."""
        if self.std_wstring_c_name is not None:
            yield (self.wstring_full_name, self.wstring_full_typedef_name) # Make the std::wstring declerations more readable.
        if self.std_string_c_name is not None:
            yield (self.string_full_name, self.string_full_typedef_name)  # Make the std::wstring declerations more readable.
            
    def gen_c_sub_seq(self):
        """Generates a substitution sequence for C tokens."""
        if self.std_wstring_c_name is not None:
            yield (self.std_wstring_c_name, self.std_wstring_typedef_c_name) # Make the std::wstring declerations more readable.
            yield (self.wstring_ctor_name, self.wstring_name)   # Replace basic_string() with wstring().
        if self.std_string_c_name is not None:
            yield (self.std_string_c_name, self.std_string_typedef_c_name) # Make the std::string declerations more readable.
            yield (self.string_ctor_name, self.string_name) # Replace basic_string() with string().
            
    def get_full_name(self, decl):
        """ Returns decl full name in the current code context."""
        return get_full_name(decl, self.gen_sub_seq())
    
    def get_c_name(self, decl):
        """ Returns decl C-name in the current code context."""
        return get_c_name(decl, True, self.gen_c_sub_seq())

class ArgInfo(object):
    """A class to parse a func argument."""
    
    def __init__(self, arg_type, global_context, arg_name=""):
        self.class_name = None
        self.is_const = False
        self.is_ref = False
        self.is_class = False
        self.arg_type_c_str = None
        self.is_ptr = False
        self.is_enum = False
        self.is_typedef = False
        self.arg_type = arg_type
        self.arg_name = arg_name
        self.cast_str = ""
        self.is_func_ptr = False
        
        ptrs_list=[]
        
        if "std::_Aux_cont" in str(arg_type):
            # Handle special case for MSVSC 2008, for example, when trying to instantiate vector<int>.
            # TODO: Handle the special case in a generic way.
            raise UnsupportedError("No support for std::_Aux_cont in: %s" % (str(arg_type),))
        
        curr_arg = arg_type
        while not(is_fundamental(curr_arg)) or is_typedef(curr_arg) or is_declarated_type(curr_arg) or is_enum(curr_arg):
            if is_abstract_class_declaration(curr_arg):
                self.is_class = True
                cls = get_class_by_decl(global_context.global_ns, curr_arg)
                break
            elif is_typedef(curr_arg):
                self.is_typedef = True
                typedef_name, typedef_c_name = global_context.get_typedef_data(curr_arg)
                curr_arg = curr_arg.type    # Don't use remove_alias() since this deletes ALL the typedefs - and we don't want that.
                #TODO: Is this good to classes, either?
            elif is_declarated_type(curr_arg):
                #curr_arg_decl_str = curr_arg.build_decl_string()
                #if pygccxml.declarations.templates.is_instantiation(curr_arg_decl_str) and not(is_std_string(curr_arg) or is_std_wstring(curr_arg)):
                 #   raise UnsupportedError("Currently templates are not supported.")
                 # TODO: Check STL contains, for example vector.
                #self.is_typedef, typedef_name, typedef_c_name = global_context.get_possible_typedef_data(curr_arg)
                curr_arg = curr_arg.declaration # And not remove_declarated(curr_arg) - since this would break a typedef completely, etc.
            elif is_const(curr_arg):
                self.is_const = True
                curr_arg = remove_const(curr_arg)
            elif is_ellipsis(curr_arg):
                raise UnsupportedError("Ellipsis arg types are not handeled.")
            elif is_qualifier(curr_arg):
                curr_arg = base_type(curr_arg)  # TODO: Is this correct?
            elif is_unknown_type(curr_arg):
                raise UnsupportedError("Unknown arg type: %s" % (str(curr_arg),))
            elif is_volatile(curr_arg):
                curr_arg = remove_volatile(curr_arg)    # Not being dealt.
            elif is_calldef_pointer(curr_arg):
                curr_arg = curr_arg.base    # remove_pointer() doesn't work here.
                if is_member_function_type(curr_arg):
                    raise UnsupportedError("Member function pointers are not supported: %s" % (str(arg_type),))
                self.is_func_ptr = True
                self.func_ptr_info = FuncPtrInfo(curr_arg, arg_name, global_context)
                break
            elif is_pointer(curr_arg) or is_array(curr_arg):
                ptrs_list.append(self.is_const)
                self.is_const = False
                curr_arg = remove_pointer(curr_arg)
            elif is_reference(curr_arg):
                self.is_ref = True   # Only the 1st ref is handeled
                curr_arg = remove_reference(curr_arg)
            elif is_enum(curr_arg):
                self.is_enum = True
                break
            elif is_class(curr_arg):
                self.is_class = True
                cls = curr_arg
                break
        
        self.is_c_bool = is_bool(curr_arg) and not global_context.is_c99    # This is redundant if the compiler is C99 compatible.
        self.is_c_decl = not(self.is_class or self.is_ref or self.is_c_bool)    #= A simple C decleration.
        self.is_redirected = (self.is_class or self.is_ref)
        
        if self.is_c_decl:
            self.arg_type_c_str = strip_global_ns(arg_type.build_decl_string())
            if self.is_typedef:
                stripped_typedef_name = strip_global_ns(typedef_name)
                if typedef_c_name != stripped_typedef_name:   # There is a namespace
                    self.cast_str = self.arg_type_c_str
                self.arg_type_c_str = self.arg_type_c_str.replace(typedef_name, typedef_c_name)
                # The following line is needed to handle the case where arg_type.build_decl_string() is a typedef -> we've stripped the global namespace, and the type won't be replaced with the last line.
                self.arg_type_c_str = self.arg_type_c_str.replace(stripped_typedef_name, typedef_c_name)
            elif self.is_enum:
                self.cast_str = self.arg_type_c_str
                enum_name, enum_c_name = global_context.get_enum_data(curr_arg)
                if "enum " not in enum_c_name:  # C++ style's enum
                    enum_c_name = "enum %s" % (enum_c_name,)
                self.arg_type_c_str = self.arg_type_c_str.replace(strip_global_ns(get_full_name(curr_arg)), enum_c_name)
        else:
            if self.is_class:
                if cls is not None:
                    self.can_create_with_copy_constructor = has_copy_constructor(cls)
                    self.can_create_with_default_constructor = (has_public_assign(cls) and has_trivial_constructor(cls))
                    self.class_name, base_arg_type_c_str = global_context.get_class_data(cls)
                else:   # For class declaration with no concrete classes.
                    self.can_create_with_copy_constructor = None
                    self.can_create_with_default_constructor = None
                    self.class_name, base_arg_type_c_str = global_context.get_class_data(curr_arg)
                if len(ptrs_list) > 0:
                    if ptrs_list.pop():  # The class ptr covers 1 redirection level...
                        base_arg_type_c_str = "const " + base_arg_type_c_str #...but we shouldn't forget the const correctness for the ptr we've just removed.
                    self.is_redirected = False
            else:
                base_arg_type_c_str = strip_global_ns(curr_arg.build_decl_string())
                if self.is_ref:  # The (is_class and is_ref) case is dealt in the is_class case.
                    ptrs_list.append(True) # We add a const indirection. Notice that self.is_const is about the contents - not about the ptr.
            curr_ptrs_list = []
            for is_ptr_const in reversed(ptrs_list):    # reversed - since ptrs are read from right-to-left.
                if is_ptr_const:
                    curr_ptrs_list.append('* const')
                else:
                    curr_ptrs_list.append('*')
            ptrs_str = ''.join(curr_ptrs_list)
            const_content_str = ""
            if self.is_const:
                const_content_str = "const "
            self.arg_type_c_str = "%s%s%s" % (const_content_str, base_arg_type_c_str, ptrs_str)
            if self.is_class:
                self.cast_str = self.arg_type_c_str.replace(global_context.get_class_data(curr_arg)[1], self.class_name+'*')
            if self.is_c_bool:
                self.cast_str = self.arg_type_c_str
                self.arg_type_c_str = self.arg_type_c_str.replace("bool", C_BOOL_TYPE_NAME)
        if self.is_func_ptr and not(self.is_typedef):  # TODO: Is this position covers all bases?
            self.arg_type_c_str = self.func_ptr_info.type_str
            
        if len(ptrs_list) > 0:
            self.is_ptr = True
    
    def is_void(self):
        """Returns whether the argument is void."""
        return is_void(self.arg_type)
        
    def get_type_name_str(self):
        """Returns the type and name argument string."""
        if self.is_func_ptr and not(self.is_typedef):   # TODO: What about if the typedef is stripped down?
            return self.arg_type_c_str.replace("(*)", "(*%s)" % (self.arg_name,))
        return "%s %s" % (self.arg_type_c_str, self.arg_name)

class FuncPtrInfo:
    """A class to parse a function pointer."""
    
    def __init__(self, func_type, name, global_context):
        self.func_args_info_list = []
        self.func_type = func_type
        self.name = name
        
        for arg in func_type.arguments_types:
            self.func_args_info_list.append(ArgInfo(arg, global_context))
            
        self.ret_type_info = ArgInfo(func_type.return_type, global_context)
        
        func_args_decl_list = [arg_info.arg_type_c_str for arg_info in self.func_args_info_list]
        func_args_str = ", ".join(func_args_decl_list)
        
        self.type_str = "%s (*%s)(%s)" % (self.ret_type_info.arg_type_c_str, name, func_args_str)
               
class FuncInfo:
    """A class to parse a function or a class method."""
    
    FREE_FUNC = 0
    FREE_OP = 1
    MEMBER_FUNC = 2
    MEMBER_OP = 3
    CTOR = 4
    DTOR = 5
    FUNC_TYPE_MAP = {free_function_t: FREE_FUNC,
                free_operator_t: FREE_OP,
                member_function_t: MEMBER_FUNC,
                member_operator_t: MEMBER_OP,
                constructor_t: CTOR,
                destructor_t: DTOR}
    
    def __init__(self, func, global_context, generate_error_arg, generate_min_args_ver_only=False):
        if func.has_ellipsis:
            raise UnsupportedError("Ellipsis arg types are not handeled.")
        
        self.func_args_info_list = []
        self.func = func
        self.full_name = global_context.get_full_name(func)
        self.c_func_name = global_context.get_c_name(func)
        
        self.func_type = self.FUNC_TYPE_MAP[type(func)]
        if (self.func_type == self.MEMBER_OP) or (self.func_type == self.FREE_OP):
            if not("operator_" in self.c_func_name):
                # Fix missing space in the func name ("operator+" -> "operator_+").
                self.c_func_name = self.c_func_name.replace("operator", "operator_")
            for op_name in OPERATORS_LIST_BY_LENGTH:
                self.c_func_name = self.c_func_name.replace(op_name, OPERATOR_MAP[op_name])
        
        self.generate_error_arg = generate_error_arg
        self.is_c99 = global_context.is_c99
        
        if generate_min_args_ver_only:
            self.optional_args_num = 0
        else:
            self.optional_args_num = len(func.optional_args)   # There are always len(func.optional_args) optional arguments, but we don't want to use them when we generate_min_args_ver_only.
        if generate_min_args_ver_only:
            arguments = func.required_args
        else:
            arguments = func.arguments
        for arg in arguments:
            self.func_args_info_list.append(ArgInfo(arg.type, global_context, arg.name))
            
        self.class_redirection = ""
        if (self.func_type == self.MEMBER_FUNC) or (self.func_type == self.DTOR) or (self.func_type == self.MEMBER_OP):
            self.class_name, class_c_ptr = global_context.get_class_data(func.parent)
            self.class_arg_c_str = "%s %s" % (class_c_ptr, THIS_VAR_NAME)
            
            if (self.func_type == self.MEMBER_FUNC) or (self.func_type == self.MEMBER_OP):
                self.is_static = func.has_static
                
                if self.is_static:
                    self.c_func_name += "_static"
                    self.class_redirection = ""
                    
                const_class_redirection_str = ""
                if func.has_const:
                    self.class_arg_c_str = "const " + self.class_arg_c_str
                    self.c_func_name += "_const"
                    const_class_redirection_str = "const "
            
                if not self.is_static:
                    self.class_redirection = "((%s%s*) %s)->" % (const_class_redirection_str, self.class_name, THIS_VAR_NAME,)
        
        if self.func_type == self.CTOR:
            self.ret_type_info = ArgInfo(func.parent, global_context)
            # TODO: The ctor returns a ptr to the class. Here we put the class_t and not pointer_t(class_t) - since it messes-up the ArgInfo's ctor.
            # The reason it works is that handling class and class-ptr is the same - but depending on it is very bad.
        elif (self.func_type == self.DTOR):
            self.ret_type_info = ArgInfo(void_t(), global_context)
        else:
            self.ret_type_info = ArgInfo(func.return_type, global_context)
        
    def gen_func_args_c_strs(self):
        """A generator to the func args types and names."""
        if self.generate_error_arg:
            yield get_error_arg_str(self.is_c99)
        if (self.func_type == self.DTOR) or (self.func_type == self.MEMBER_OP) or ((self.func_type == self.MEMBER_FUNC) and not self.is_static):
            yield self.class_arg_c_str
        for arg_info in self.func_args_info_list:
            yield arg_info.get_type_name_str()
            
    def is_default_ctor(self):
        """Returns whether the func is a default ctor."""
        if self.func_type == self.CTOR:
            return self.func.is_trivial_constructor
        return False


def unsupported_wrapper(func, ignore_unsupported_features=True):
    """A decorator to ignore unsupported features exception, if enabled."""
    def decorated(*args, **kws):
        try:
            func(*args, **kws)
        except UnsupportedError, ex:
            if ignore_unsupported_features:
                print ex.args[0]
            else:
                raise
    return decorated

                    
def generate_c_wrapper(header_file_path, generate_dl=True, generate_exception_handling_code=True, is_compact_string=True, is_assume_copy=False, is_assume_assign=False, generate_error_arg=True, is_verbose=False, generate_operators=True, ignore_unsupported_features=True, is_c99=False, is_camel_case=False, include_paths=None, compiler_type=None):
    """Outputs a C wrapper for header_file_path."""
    
    if generate_error_arg and not(generate_exception_handling_code):
        print "Ignoring error argument generation option, since the exception handling generation option is disabled"
        generate_error_arg = False
    
    header_file_path=os.path.abspath(header_file_path)
    
    output_class = CodeOutputClass(header_file_path, generate_exception_handling_code, generate_dl, is_compact_string, generate_operators, is_assume_copy, is_assume_assign, generate_error_arg, is_verbose, is_camel_case)
    global_context = CodeContext(header_file_path, include_paths, compiler_type, is_c99)
    
    output_class.output_prefix_code(global_context.is_c99)
    
    output_class.output_typedef=unsupported_wrapper(output_class.output_typedef, ignore_unsupported_features)
    output_class.output_func=unsupported_wrapper(output_class.output_func, ignore_unsupported_features)
    
    try:
        string_typedef = global_context.typedef(name="::std::string")
        output_class.output_std_string(string_typedef, global_context)
        string_typedef = global_context.typedef(name="::std::wstring")
        output_class.output_std_string(string_typedef, global_context)
    except:
        pass
    
    for cls in global_context.classes(header_file=header_file_path, allow_empty=True):
        output_class.output_class_typedef(cls, global_context)
       
    for typedef in global_context.typedefs(header_file=header_file_path, allow_empty=True):
        output_class.output_typedef(typedef, global_context)
              
    for enum in global_context.enums(header_file=header_file_path, allow_empty=True):
        output_class.output_enum(enum, global_context)
    
    for cls in global_context.classes(header_file=header_file_path, allow_empty=True):
        output_class.output_class_code(cls, global_context)
            
    for free_func in global_context.free_functions(header_file=header_file_path, allow_empty=True):
        output_class.output_func(free_func, global_context)
        
    if output_class.generate_operators:
        for free_op in global_context.free_operators(header_file=header_file_path, allow_empty=True):
            output_class.output_func(free_op, global_context)
        
    for elem_type, elem in global_context.gen_recursive_elems():
        if elem_type == global_context.CLASS:
            output_class.output_class_typedef(elem, global_context)
            output_class.output_class_code(elem, global_context)
        elif elem_type == global_context.TYPEDEF:
            output_class.output_typedef(elem, global_context)
        elif elem_type == global_context.ENUM:
            output_class.output_enum(elem, global_context)
    
    output_class.output_suffix_code()
    
    output_class.close()    # Forces the output file creation.


def safe_config_get_wrapper(config_get_func):
    """A decorator to mask ConfigParser methods from option not existing exception, returning a default value instead."""
    def decorated(section_name, key_name, def_val=None):
        try:
            return config_get_func(section_name, key_name)
        except ConfigParser.NoOptionError:
            return def_val
    return decorated

def get_option(options, option, def_val):
    """Returns a default value (other than None) when an optparse var option does not exist."""
    ret_val = getattr(options, option)
    if ret_val is None:
        return def_val
    return ret_val

def parse_option(config_get_func, section_name, option_name, options, def_val):
    """Parses one program option. The args parsing order is:
1. Command line args.
2. Config file options.
3. Default values."""
    option = def_val
    if config_get_func is not None:
        option = config_get_func(section_name, option_name, def_val)
    return get_option(options, option_name, option)

if __name__ == '__main__':
    
    cmd_line_parser = OptionParser("usage: %prog [options] <header_file_path>")
    cmd_line_parser.add_option("-g", "--gccxml", dest='gccxml_file_path', help="The gccxml file path")
    cmd_line_parser.add_option("-c", "--config", dest='config_file_path', help="The config file path")
    cmd_line_parser.add_option("-i", "--include", dest='include_paths', help="List of include paths to look for header files")
    cmd_line_parser.add_option("-t", "--compiler", dest='compiler_type', help="The compiler type")
    # cmd_line_parser.add_option("-i", "--ignore", action='store_false', dest='ignore_unsupported_features', help="Raise exception if an unsupported feature (like templates) is encountered.")
    cmd_line_parser.add_option("-d", "--dl", action='store_false', dest='generate_dl', help="Don't generate a def file (and a DllMain() function under Windows).")
    cmd_line_parser.add_option("-e", "--error", action='store_false', dest='generate_error_arg', help="Don't add error output args.")
    cmd_line_parser.add_option("-n", "--nothrow", action='store_false', dest='generate_exception_handling_code', help="Don't generate exception handling code.")
    cmd_line_parser.add_option("-v", "--verbose", action='store_false', dest='is_verbose', help="Don't generate verbose output.")
    cmd_line_parser.add_option("-9", "--c99", action='store_true', dest='is_c99', help="Compiler with C99 support.")
    cmd_line_parser.add_option("-o", "--operator", action='store_false', dest='generate_operators', help="Don't generate operators.")
    cmd_line_parser.add_option("-s", "--string", action='store_false', dest='is_compact_string', help="Output std::string in a compact format.")
    cmd_line_parser.add_option("--camel", action='store_true', dest='is_camel_case', help="The functions would be outputed in (Upper) Camel Case conventions, not Python conventions (e.g.: FuncName and not func_name).")
    cmd_line_parser.add_option("--copy", action='store_true', dest='is_assume_copy', help="Assume public copy constructor for class declarations with no concrete classes.")
    cmd_line_parser.add_option("--assign", action='store_true', dest='is_assume_assign', help="Assume public default constructor and assignment operator for class declarations with no concrete classes.")
    (options, args) = cmd_line_parser.parse_args()
    
    if len(args) != 1:
        cmd_line_parser.error("<header_file_path> is required")
    
    safe_config_get = None
    safe_config_get_bool = None
    if options.config_file_path is not None:
        config = ConfigParser.RawConfigParser()
        config.read(options.config_file_path)
        safe_config_get = safe_config_get_wrapper(config.get)
        safe_config_get_bool = safe_config_get_wrapper(config.getboolean)
        
    generate_dl = parse_option(safe_config_get_bool, 'Cpp2C Config', 'generate_dl', options, True)
    generate_error_arg = parse_option(safe_config_get_bool, 'Cpp2C Config', 'generate_error_arg', options, True)
    # ignore_unsupported_features = parse_option(safe_config_get_bool, 'Cpp2C Config', 'ignore_unsupported_features', options, True)
    ignore_unsupported_features = True
    generate_exception_handling_code = parse_option(safe_config_get_bool, 'Cpp2C Config', 'generate_exception_handling_code', options, True)
    gccxml_file_path = parse_option(safe_config_get, 'GccXml Config', 'gccxml_file_path', options, "")
    include_paths = parse_option(safe_config_get, 'GccXml Config', 'include_paths', options, None)
    compiler_type = parse_option(safe_config_get, 'GccXml Config', 'compiler_type', options, None)
    is_verbose = parse_option(safe_config_get_bool, 'Cpp2C Config', 'is_verbose', options, True)
    is_c99 = parse_option(safe_config_get_bool, 'Cpp2C Config', 'is_c99', options, False)
    generate_operators = parse_option(safe_config_get_bool, 'Cpp2C Config', 'generate_operators', options, True)
    is_compact_string = parse_option(safe_config_get_bool, 'Cpp2C Config', 'is_compact_string', options, True)
    is_camel_case = parse_option(safe_config_get_bool, 'Cpp2C Config', 'is_camel_case', options, False)
    is_assume_copy = parse_option(safe_config_get_bool, 'Cpp2C Config', 'is_assume_copy', options, False)
    is_assume_assign = parse_option(safe_config_get_bool, 'Cpp2C Config', 'is_assume_assign', options, False)

    if not include_paths == None:
        include_paths = include_paths.split(';')
    
    generate_c_wrapper(args[0], generate_dl, generate_exception_handling_code, is_compact_string, is_assume_copy, is_assume_assign, generate_error_arg, is_verbose, generate_operators, ignore_unsupported_features, is_c99, is_camel_case, include_paths, compiler_type)
    print "Done."