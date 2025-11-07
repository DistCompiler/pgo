cmake_minimum_required(VERSION 4.1.1)
project(omnilink_reflocking_wrapper)

set(CMAKE_BUILD_TYPE Debug)

# Generate the `compile_commands.json` file.
set(CMAKE_EXPORT_COMPILE_COMMANDS ON CACHE INTERNAL "")

if(CMAKE_EXPORT_COMPILE_COMMANDS)
  set(CMAKE_CXX_STANDARD_INCLUDE_DIRECTORIES
    ${CMAKE_CXX_IMPLICIT_INCLUDE_DIRECTORIES})
endif()

SET(cmake_config_path "${CMAKE_INSTALL_LIBDIR}/cmake/omnilink_reflocking_wrapper")

find_package(OmniLink REQUIRED)
find_package(msgpack-cxx REQUIRED)

add_library(omnilink_reflocking_wrapper reflocking_wrapper.h reflocking_wrapper.cxx)
target_link_libraries(omnilink_reflocking_wrapper PUBLIC OmniLink::OmniLink msgpack-cxx)

set_property(TARGET omnilink_reflocking_wrapper PROPERTY CXX_STANDARD 17)
set_property(TARGET omnilink_reflocking_wrapper PROPERTY CXX_STANDARD_REQUIRED TRUE)

include(CMakePackageConfigHelpers)

configure_package_config_file(
  omnilink_reflocking_wrapper-config.cmake.in
  "${CMAKE_CURRENT_BINARY_DIR}/omnilink_reflocking_wrapper-config.cmake"
  INSTALL_DESTINATION "${cmake_config_path}"
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/omnilink_reflocking_wrapper-config.cmake"
    DESTINATION "${cmake_config_path}"
)

export(PACKAGE omnilink_reflocking_wrapper)

install(FILES ${PROJECT_SOURCE_DIR}/reflocking_wrapper.h DESTINATION include/omnilink/glue)
install(
  TARGETS omnilink_reflocking_wrapper
  EXPORT omnilink_reflocking_wrapper-targets
)

export(TARGETS omnilink_reflocking_wrapper
  FILE ${CMAKE_CURRENT_BINARY_DIR}/omnilink_reflocking_wrapper-targets.cmake
  NAMESPACE omnilink_reflocking_wrapper::)

install(EXPORT
    omnilink_reflocking_wrapper-targets
    FILE omnilink_reflocking_wrapper-targets.cmake
    DESTINATION "${cmake_config_path}"
    NAMESPACE omnilink_reflocking_wrapper::
)
