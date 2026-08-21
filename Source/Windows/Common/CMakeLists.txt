add_library(CommonWindowsRuntime STATIC LoadConfig.S)
if(CMAKE_HOST_APPLE)
  target_compile_definitions(CommonWindowsRuntime PRIVATE FEX_ON_WINE_APPLE=1)
endif()
add_subdirectory(CRT)
add_subdirectory(WinAPI)

target_link_libraries(CommonWindowsRuntime FEXCore_Base JemallocLibs)
target_compile_options(CommonWindowsRuntime PRIVATE -Wno-inconsistent-dllimport)
target_include_directories(CommonWindowsRuntime PRIVATE "${CMAKE_SOURCE_DIR}/Source/Windows/include/")

add_library(CommonWindows STATIC
  Allocator.cpp
  CPUFeatures.cpp
  EnvironmentVariablesHandling.cpp
  SHMStats.cpp
  InvalidationTracker.cpp
  ImageTracker.cpp
  Logging.cpp)

target_link_libraries(CommonWindows FEXCore_Base)
target_include_directories(CommonWindows PRIVATE "${CMAKE_SOURCE_DIR}/Source/Windows/include/")
if(CMAKE_HOST_APPLE)
  target_compile_definitions(CommonWindows PRIVATE FEX_ON_WINE_APPLE=1)
endif()
