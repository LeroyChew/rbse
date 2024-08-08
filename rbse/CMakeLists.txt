# CMakeList.txt : CMake project for rbse, include source and define
# project specific logic here.
#

# Add source to this project's executable.
add_executable (rbse "rbse.cpp" "rbse.h" "Linked List.h" "Logic.h" "Test.h" "QBF.h" "Index.h" "Definitions.h" "QRAT.h" "Examples.h" "MultiLinear.h" "Connectivity.h" "Independence.h" "File.h" "Exp.h" "Circuits.h" "CircuitExtraction.h" "LocalExpansion.h")

if (CMAKE_VERSION VERSION_GREATER 3.12)
  set_property(TARGET rbse PROPERTY CXX_STANDARD 20)
endif()

# TODO: Add tests and install targets if needed.
