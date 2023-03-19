add_library(BlockExtractPass MODULE
    # List your source files here.
    pass.cpp
    utility.cpp
    abb.cpp
)

# Use C++11 to compile our pass (i.e., supply -std=c++11).
target_compile_features(BlockExtractPass PRIVATE cxx_range_for cxx_auto_type)

# LLVM is (typically) built with no C++ RTTI. We need to match that.
set_target_properties(BlockExtractPass PROPERTIES
    COMPILE_FLAGS "-fno-rtti"
)
