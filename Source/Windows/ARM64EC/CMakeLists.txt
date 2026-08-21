add_library(arm64ecfex SHARED
  Module.cpp
  Module.S
  libarm64ecfex.def)

if(CMAKE_HOST_APPLE)
  # CMake expands $<TARGET_OBJECTS> first on the link line. Emit a rsp of
  # FEXCore objs and pass it after Module.S so .text growth cannot move EnterEC.
  file(GENERATE
    OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/fexcore-objs.rsp"
    CONTENT "$<JOIN:$<TARGET_OBJECTS:FEXCore_object>,\n>\n")
  add_dependencies(arm64ecfex FEXCore_object)
  target_link_options(arm64ecfex PRIVATE
    "SHELL:-Xlinker @${CMAKE_CURRENT_BINARY_DIR}/fexcore-objs.rsp")
else()
  target_sources(arm64ecfex PRIVATE $<TARGET_OBJECTS:FEXCore_object>)
endif()

patch_library_wine(arm64ecfex)

if(CMAKE_HOST_APPLE)
  target_compile_definitions(arm64ecfex PRIVATE FEX_ON_WINE_APPLE=1)
  target_compile_definitions(rpmalloc PRIVATE FEX_ON_WINE_APPLE=1)
  set_source_files_properties(Module.S PROPERTIES COMPILE_OPTIONS "-DFEX_ON_WINE_APPLE=1")
endif()
option(FEX_DEBUG_PROCESSINIT_STAGES "Return from ProcessInit immediately after InitSyscalls (Wine bring-up debug)" OFF)
if(FEX_DEBUG_PROCESSINIT_STAGES)
  target_compile_definitions(arm64ecfex PRIVATE FEX_DEBUG_PROCESSINIT_STAGES=1)
endif()

target_include_directories(arm64ecfex PRIVATE
  "${CMAKE_SOURCE_DIR}/Source/Windows/include/"
  "${CMAKE_SOURCE_DIR}/Source/"
  "${CMAKE_SOURCE_DIR}/Source/Windows/")

target_link_libraries(arm64ecfex PRIVATE
  FEXCore_Base
  Common
  CommonTools
  CommonWindows
  CommonWindowsRuntime
  ntdll_ex)

target_link_options(arm64ecfex PRIVATE -static -nostdlib -nostartfiles -nodefaultlibs -lc++ -lc++abi -lunwind)
target_link_libraries(arm64ecfex PRIVATE ${LIBGCC_PATH})
install(TARGETS arm64ecfex RUNTIME
  DESTINATION ${CMAKE_INSTALL_LIBDIR}
  COMPONENT Runtime)
