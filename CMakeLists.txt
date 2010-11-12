add_definitions(-O3 -Wall)
add_executable(hash_contest hash_contest.cpp)
target_link_libraries(hash_contest z ssl rt)
