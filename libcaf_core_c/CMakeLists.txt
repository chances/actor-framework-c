# http://www.swig.org/Doc1.3/Introduction.html#Introduction_build_system

# https://github.com/vadz/swig/tree/C
# http://htmlpreview.github.io/?https://github.com/vadz/swig/blob/C/Doc/Manual/C.html

# https://github.com/swig/swig/issues/800
# https://github.com/swig/swig/issues?utf8=%E2%9C%93&q=is%3Aissue+%22gsoc2012-c%22

# Use latest UseSWIG module
cmake_minimum_required(VERSION 3.14)

# Get libcaf_core headers
file(GLOB_RECURSE LIBCAF_CORE_HEADERS "${PROJECT_SOURCE_DIR}/libcaf_core/caf/*.hpp")

find_package(SWIG 4.0 REQUIRED)
include(UseSWIG)

set(CMAKE_SWIG_FLAGS "")
# list(APPEND CMAKE_SWIG_FLAGS "-doxygen")
list(APPEND CMALE_SWIG_FLAGS "-c++")
list(APPEND CMALE_SWIG_FLAGS "-includeall")

set(SWIG_SOURCE_FILE_EXTENSIONS ".i" ".swg" ".hpp")
set(SWIG_USE_TARGET_INCLUDE_DIRECTORIES TRUE)

# set_source_files_properties("${CMAKE_CURRENT_LIST_DIR}/libcaf_core.i" PROPERTIES CPLUSPLUS ON)
# set_source_files_properties("${CMAKE_CURRENT_LIST_DIR}/libcaf_core.i" PROPERTIES SWIG_FLAGS "-includeall")
# swig_add_module(example python "${CMAKE_CURRENT_LIST_DIR}/libcaf_core.i" example.cxx)

set(SWIG_CORE_TARGET "libcaf_core")

swig_add_library(SWIG_CORE_TARGET
  TYPE USE_BUILD_SHARED_LIBS
  LANGUAGE c
  OUTPUT_DIR "${CMAKE_CURRENT_LIST_DIR}"
  SOURCES ${LIBCAF_CORE_HEADERS}
)

# set_property(TARGET ${SWIG_CORE_TARGET} PROPERTY SWIG_INCLUDE_DIRECTORIES ${INCLUDE_DIRECTORIES})
# set_property(TARGET ${SWIG_CORE_TARGET} PROPERTY SWIG_COMPILE_DEFINITIONS ${COMPILE_DEFINITIONS})
