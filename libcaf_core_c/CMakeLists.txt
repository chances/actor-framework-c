# https://cpp2c.webs.com/asimpleexample.htm
# https://sourceforge.net/projects/cpp2c/
#
# License unknown, other than "Copyright ©2010" on website

set(LIBCAF_C_TARGET "libcaf_c")

add_library(${LIBCAF_C_TARGET} STATIC)

# sh ./configure --libs-only --with-ccache --build-static

# Get libcaf_core headers
file(GLOB_RECURSE LIBCAF_CORE_HEADERS "${PROJECT_SOURCE_DIR}/libcaf_core/caf/*.hpp")

###

find_package(Python2 COMPONENTS Interpreter)
if(NOT Python2_FOUND)
  message(FATAL_ERROR "Cannot find Python 2 Interpreter")
endif()

print("${INCLUDE_DIRECTORIES}")

# TODO: Validate Python2_VERSION_MAJOR and Python2_VERSION_MINOR for Python 2.7?

# python cpp2c.py "C:\Projects\Test\Test.hpp" -g "C:\Program Files\gccxml 0.9\bin" -t msvc9
# python cpp2c.py ../libcaf_core/caf/actor.hpp --operator -t gcc --include=${workspaceFolder}/libcaf_core;${workspaceFolder}/build

foreach(LIBCAF_CORE_HEADER LIBCAF_CORE_HEADERS)
  message(${LIBCAF_CORE_HEADER})
  add_custom_command(TARGET ${LIBCAF_C_TARGET}
    PRE_BUILD
    COMMAND ${Python2_EXECUTABLE}
    ARGS cpp2c.py "${LIBCAF_CORE_HEADER}" --include "${CMAKE_CURRENT_SOURCE_DIR}/libcaf_core" --operator -t gcc # TODO: Use CMAKE_CXX_COMPILER or CMAKE_C_COMPILER for `compiler_type`?
    WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR}
  )
endforeach()
