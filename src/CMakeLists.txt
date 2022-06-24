add_subdirectory(include/glog)
target_link_libraries(ezsmtPlus PRIVATE glog::glog ${Boost_LIBRARIES})
target_link_libraries(test PRIVATE glog::glog ${Boost_LIBRARIES})


target_sources(ezsmtPlus
  PUBLIC
    ctable.cc
    rulebuilder.cc
    atomrule.cc
    read.cc
    timer.cc
    cmodels.cc
    program.cc
    interpret.cc
    graphscc.cc
    smtsolver.cc
    logics/QF_LIA_logic.cc
    main.cc
)

target_sources(test
  PUBLIC
    ctable.cc
    rulebuilder.cc
    atomrule.cc
    read.cc
    timer.cc
    cmodels.cc
    program.cc
    interpret.cc
    graphscc.cc
    smtsolver.cc
    logics/QF_LIA_logic.cc
    # main.cc
)
