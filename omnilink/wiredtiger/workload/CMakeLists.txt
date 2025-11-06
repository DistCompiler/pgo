cmake_minimum_required(VERSION 4.1.1)
project(wiredtiger-stressor)

set(CMAKE_BUILD_TYPE Debug)

# Generate the `compile_commands.json` file.
set(CMAKE_EXPORT_COMPILE_COMMANDS ON CACHE INTERNAL "")

if(CMAKE_EXPORT_COMPILE_COMMANDS)
  set(CMAKE_CXX_STANDARD_INCLUDE_DIRECTORIES
    ${CMAKE_CXX_IMPLICIT_INCLUDE_DIRECTORIES})
endif()

find_package(OmniLink REQUIRED)
find_package(msgpack-cxx REQUIRED)

cmake_pkg_config(IMPORT wiredtiger REQUIRED)

add_executable(main main.cpp)
target_link_libraries(main OmniLink::OmniLink msgpack-cxx PkgConfig::wiredtiger)

install(DIRECTORY ${PROJECT_BINARY_DIR}/main
  DESTINATION bin
)
