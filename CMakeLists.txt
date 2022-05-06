cmake_minimum_required(VERSION 3.22)

project(ezsmt_plus)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED True)


find_package(Boost 1.78 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})

include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)

add_executable(ezsmtPlus "")
add_executable(test "")

add_subdirectory(src)
add_subdirectory(tests)
