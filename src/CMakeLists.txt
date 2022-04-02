add_library(ezsmtPlus_lib "")

target_sources(ezsmtPlus
  PUBLIC
    ctable.cc
    rulebuilder.cc
    atomrule.cc
    read.cc
    tree.cc
    timer.cc
    cmodels.cc
    program.cc
    interpret.cc
    graphscc.cc
    main.cc
)

target_sources(ezsmtPlus_lib
  PUBLIC
    ctable.cc
    rulebuilder.cc
    atomrule.cc
    read.cc
    tree.cc
    timer.cc
    cmodels.cc
    program.cc
    interpret.cc
    graphscc.cc
    # main.cc
)
