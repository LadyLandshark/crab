add_library(Crab ${CRAB_LIBS_TYPE}
  ##support
  debug.cpp
  stats.cpp
  os.cpp
  ##abstract domains
  abstract_domain_params.cpp
  array_adaptive_impl.cpp
  boolean.cpp
  congruence.cpp
  constant.cpp
  dis_interval.cpp
  interval.cpp
  interval_congruence.cpp
  region_info.cpp
  sign.cpp
  small_range.cpp
  term_operators.cpp
  types.cpp
  wrapped_interval.cpp
  ##numbers 
  bignums.cpp
  safeint.cpp
  wrapint.cpp
  ##variable factory
  varname_factory.cpp
  ##types
  tag.cpp
  )

target_include_directories(Crab PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_link_libraries(Crab ${GMP_LIB} ${GAPSTOP_LIBS})

install(TARGETS Crab
  LIBRARY DESTINATION crab/lib
  ARCHIVE DESTINATION crab/lib)

if (NOT TopLevel)
  ## This is ugly fix so that seahorn and crab-llvm can find Crab if
  ## dynamically linked. It has to do with how CMAKE_INSTALL_RPATH is
  ## handled by these tools.
  install(TARGETS Crab
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib)
endif()  



