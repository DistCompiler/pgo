cmake_minimum_required(VERSION 4.1.1)

project(OmniLink LANGUAGES CXX)

# Generate the `compile_commands.json` file.
set(CMAKE_EXPORT_COMPILE_COMMANDS ON CACHE INTERNAL "")

if(CMAKE_EXPORT_COMPILE_COMMANDS)
  set(CMAKE_CXX_STANDARD_INCLUDE_DIRECTORIES
    ${CMAKE_CXX_IMPLICIT_INCLUDE_DIRECTORIES})
endif()

SET(cmake_config_path "${CMAKE_INSTALL_LIBDIR}/cmake/OmniLink")

find_package(msgpack-cxx REQUIRED)

add_library(OmniLink INTERFACE)

target_include_directories(OmniLink
  INTERFACE
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/include>
    $<INSTALL_INTERFACE:include>
)

target_link_libraries(OmniLink INTERFACE msgpack-cxx)

install(TARGETS OmniLink
  EXPORT OmniLink-targets
  COMPONENT OmniLink
  # This provides include directory in exported target
  # relative to prefix in single directory we've put everything in.
  INCLUDES DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}"
)

install(DIRECTORY include/
  DESTINATION include
  COMPONENT OmniLink
)

include(CMakePackageConfigHelpers)

configure_package_config_file(
  OmniLinkConfig.cmake.in
  "${CMAKE_CURRENT_BINARY_DIR}/OmniLinkConfig.cmake"
  INSTALL_DESTINATION "${cmake_config_path}"
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/OmniLinkConfig.cmake"
    DESTINATION "${cmake_config_path}"
    COMPONENT OmniLink
)

install(
    EXPORT OmniLink-targets
    FILE OmniLink-targets.cmake
    NAMESPACE OmniLink::
    DESTINATION "${cmake_config_path}"
    COMPONENT OmniLink
)

export(EXPORT OmniLink-targets
  FILE ${CMAKE_CURRENT_BINARY_DIR}/OmniLink-targets.cmake
  NAMESPACE OmniLink::)

# Register package in the User Package Registry
export(PACKAGE OmniLink)
