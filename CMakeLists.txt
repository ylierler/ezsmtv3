cmake_minimum_required(VERSION 3.22)

project(ezsmt_plus)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED True)

include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/include)

add_executable(ezsmtPlus "")
add_subdirectory(src)

# target_include_directories("${PROJECT_BINARY_DIR}")
