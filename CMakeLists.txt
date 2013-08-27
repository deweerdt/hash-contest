cmake_minimum_required(VERSION 2.8)

add_definitions(-O3 -Wall -Wno-write-strings -fno-strict-aliasing)
add_executable(hash_contest hash_contest.cpp SpookyV2.cpp)
target_link_libraries(hash_contest z ssl rt crypto)
