:!/bin/bash 

EZSMT_REPO_LOC=~/bitbucket/casp-to-smt-lib

EZSMT_MINGO_TESTS=$EZSMT_REPO_LOC/data/ez-benchmarks/mingo
EZSMT_THESIS_TESTS=$EZSMT_REPO_LOC/data/ez-benchmarks/thesis
EZSMT_NONTIGHT_TESTS=$EZSMT_REPO_LOC/data/ez-benchmarks/nontight

EZSMT_PROG=$EZSMT_REPO_LOC/code/ezcsp-dimacs-to-smt.py

EZCSP_BIN=$EZSMT_REPO_LOC/ezcsp-bins/linux/ezcsp

EZCSP_PARAMS_BLACK=

EZCSP_PARAMS_GREY=--cmodels-incremental

EZCSP_PARAMS_CLEAR=--cmodels-feedback


run_completion() {
    COMMAND=$1
    FILE_NAME=$2
 
    if [ -f $FILE_NAME.completion-command ]; then
        echo "File $FILE_NAME.completion-command exists. No benchmark run."
    else
        echo $COMMAND > $FILE_NAME.completion-command
    
        # Limit MEM to 4GB, Limit runtime to 30 min, Limit to one CPU core
        (ulimit -v 4194304; ( timeout 30m taskset -c 2 time $COMMAND ) 2> $FILE_NAME.completion-time)
        mv dimacs-completion*.out $FILE_NAME.dimacs
    fi
}

run_grounding() {
    COMMAND=$1
    FILE_NAME=$2
 
    if [ -f $FILE_NAME.grounding-command ]; then
        echo "File $FILE_NAME.grounding-command exists. No benchmark run."
    else
        echo $COMMAND > $FILE_NAME.grounding-command
    
        # Limit MEM to 4GB, Limit runtime to 30 min, Limit to one CPU core
        (ulimit -v 4194304; ( timeout 30m taskset -c 2 time $COMMAND > $FILE_NAME.grounding-output) 2> $FILE_NAME.grounding-time)
    fi
}

run_benchmark() {
    COMMAND=$1
    FILE_NAME=$2

    if [ -f $FILE_NAME.command ]; then
       echo "File $FILE_NAME.command exists. No benchmark run."
    else
        echo $COMMAND > $FILE_NAME.command
    
        # Limit MEM to 4GB, Limit runtime to 30 min, Limit to one CPU core
        (ulimit -v 4194304; ( timeout 30m taskset -c 2 time $COMMAND > $FILE_NAME.output) 2> $FILE_NAME.time)
    fi

    
}

run_preparse() {
    COMMAND=$1
    FILE_NAME=$2
    
    if [ -f $FILE_NAME.preparse-command ]; then
        echo "File $FILE_NAME.preparse-command exists. No benchmark run."
    else
        echo $COMMAND > $FILE_NAME.preparse-command
	
        (ulimit -v 4194304; ( timeout 30m taskset -c 2 time $COMMAND > $FILE_NAME.preparse-output) 2> $FILE_NAME.preparse-time)
    fi
}

run_conversion() {
    COMMAND=$1
    FILE_NAME=$2
    
    if [ -f $FILE_NAME.conversion-command ]; then
        echo "File $FILE_NAME.conversion-command exists. No benchmark run."
    else
        echo $COMMAND > $FILE_NAME.conversion-command

        (ulimit -v 4194304; ( timeout 30m taskset -c 2 time $COMMAND > $FILE_NAME.smt) 2> $FILE_NAME.conversion-time)
        #(ulimit -v 4194304; ( timeout 30m taskset -c 0 time $COMMAND difference-logic > $FILE_NAME.smt) 2> $FILE_NAME.conversion-time)
    fi
}

run_all_mingo_benchmarks() {
#    run_benchmarks mingo $EZSMT_MINGO_TESTS
#    run_benchmarks cmodels $EZSMT_MINGO_TESTS
#    run_benchmarks clingcon $EZSMT_MINGO_TESTS
#    run_benchmarks ezcsp $EZSMT_MINGO_TESTS
     run_benchmarks ezsmt $EZSMT_MINGO_TESTS
}

run_all_nontight_benchmarks() {
    #run_benchmarks clingo $EZSMT_NONTIGHT_TESTS
    #run_benchmarks cmodels $EZSMT_NONTIGHT_TESTS
    #run_benchmarks clingcon $EZSMT_NONTIGHT_TESTS
    #run_benchmarks ezcsp $EZSMT_NONTIGHT_TESTS
    #run_benchmarks ezsmt $EZSMT_NONTIGHT_TESTS
    run_benchmarks ezsmt_nontight_SCCLR_cvc4 $EZSMT_NONTIGHT_TESTS
    #run_benchmarks ezsmt_nontight_SCCLR_z3 $EZSMT_NONTIGHT_TESTS
    #run_benchmarks ezsmt_nontight_SCCLR_yices $EZSMT_NONTIGHT_TESTS
    #run_benchmarks ezsmt_nontight_LR_cvc4 $EZSMT_NONTIGHT_TESTS
    #run_benchmarks ezsmt_nontight_LR_z3 $EZSMT_NONTIGHT_TESTS
}

run_benchmarks() {
    BENCHMARK_TYPE=$1
    EZSMT_TESTS=$2

    echo "Running $BENCHMARK_TYPE benchmarks" 

    case $BENCHMARK_TYPE in 
    clingcon)
        SUFFIX=con
        ;;
    ezcsp)
        SUFFIX=ez
        ;;
    ezsmt)  
        SUFFIX=ez
        ;;
    ezsmt_nontight_LR_cvc4)  
        SUFFIX=ez
        ;;
    ezsmt_nontight_LR_z3)  
        SUFFIX=ez
        ;;
    ezsmt_nontight_SCCLR_cvc4)  
        SUFFIX=ez
        ;;
    ezsmt_nontight_SCCLR_z3)  
        SUFFIX=ez
        ;;
    ezsmt_nontight_SCCLR_yices)  
        SUFFIX=ez
        ;;
    cmodels)
        SUFFIX=asp
        ;;
    mingo)
        SUFFIX=mingo
        ;;
    clingo)  
        SUFFIX=asp
        ;; 
    *)
        echo $"Usage: $0 {clingcon|ezcsp|ezsmt}"
        ;;
    esac

    for ez_test in $( ls $EZSMT_TESTS); do
        EZSMT_INSTANCES=$EZSMT_TESTS/$ez_test/instances

        for ENCODING_NAME in $( ls $EZSMT_TESTS/$ez_test/encodings/*.$SUFFIX); do
            RESULTS_DIR=${ENCODING_NAME##*/}
            RESULTS_DIR=$EZSMT_TESTS/$ez_test/$BENCHMARK_TYPE-results-${RESULTS_DIR%.$SUFFIX}

            if [ ! -d "$RESULTS_DIR" ]; then
                echo $RESULTS_DIR
                mkdir $RESULTS_DIR
            fi

            case $BENCHMARK_TYPE in 
            clingcon)
                run_clingcon_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR
                ;;
            ezcsp)
                run_ezcsp_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR
                ;;
            ezsmt)  
                run_ezsmt_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR
                ;;
	    cmodels)
   		run_cmodels_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR
	        ;;
            ezsmt_nontight_LR_cvc4)  
                run_ezsmt_nontight_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR LR cvc4
                ;;
            ezsmt_nontight_LR_z3)  
                run_ezsmt_nontight_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR LR z3
                ;;
            ezsmt_nontight_SCCLR_cvc4)  
                run_ezsmt_nontight_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR SCCLR cvc4
                ;;
            ezsmt_nontight_SCCLR_z3)  
                run_ezsmt_nontight_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR SCCLR z3
                ;;
            ezsmt_nontight_SCCLR_yices)
                run_ezsmt_nontight_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR SCCLR yices
                ;;
       	    mingo)
                run_mingo_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR
                ;;
            clingo)
                run_clingo_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR
		;;
            *)
                echo $"Usage: $0 {cl|ez|smt}"
                ;;
            esac

        
        done 
    done   
}


#run_benchmarks() {
#    BENCHMARK_TYPE=$1
#
#    echo "Running $BENCHMARK_TYPE benchmarks" 
#
#    case $BENCHMARK_TYPE in 
#    clingcon)
#        SUFFIX=cl
#        ;;
#    ezcsp)
#        SUFFIX=ez
#        ;;
#    ezsmt)  
#        SUFFIX=ez
#        ;;
#    cmodels)
#        SUFFIX=asp
#        ;;
#    *)
#        echo $"Usage: $0 {clingcon|ezcsp|ezsmt}"
#        ;;
#    esac
#
#    EZSMT_TESTS=$EZSMT_THESIS_TESTS
#
#    for ez_test in $( ls $EZSMT_TESTS); do
#        EZSMT_INSTANCES=$EZSMT_TESTS/$ez_test/instances
#
#        for ENCODING_NAME in $( ls $EZSMT_TESTS/$ez_test/encodings/*.$SUFFIX); do
#            RESULTS_DIR=${ENCODING_NAME##*/}
#            RESULTS_DIR=$EZSMT_TESTS/$ez_test/$BENCHMARK_TYPE-results-${RESULTS_DIR%.$SUFFIX}
#            if [ ! -d "$RESULTS_DIR" ]; then
#                echo $RESULTS_DIR
#                mkdir $RESULTS_DIR
#            fi
#
#            case $BENCHMARK_TYPE in 
#            clingcon)
#                run_clingcon_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR
#                ;;
#            ezcsp)
#                run_ezcsp_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR
#                ;;
#            ezsmt)  
#                run_ezsmt_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR
#                ;;
#	    cmodels)
#   		run_cmodels_benchmarks $EZSMT_INSTANCES $ENCODING_NAME $RESULTS_DIR
#		;;
#            *)
#                echo $"Usage: $0 {cl|ez|smt}"
#                ;;
#            esac
#
#        
#        done 
#    done   
#}

run_clingcon_benchmarks() {
    EZSMT_INSTANCES=$1
    ENCODING_NAME=$2
    RESULTS_DIR=$3

    cd $RESULTS_DIR

    for INSTANCE in $( ls $EZSMT_INSTANCES); do
        echo $INSTANCE
        echo $ENCODING_NAME
        run_benchmark "clingcon $EZSMT_INSTANCES/$INSTANCE $ENCODING_NAME" ${INSTANCE%.asp}

    done
    
    cd -
}

run_cmodels_benchmarks() {
    EZSMT_INSTANCES=$1
    ENCODING_NAME=$2
    RESULTS_DIR=$3

    cd $RESULTS_DIR

    for INSTANCE in $( ls $EZSMT_INSTANCES); do
        echo $INSTANCE
        echo $ENCODING_NAME

	    FILE_NAME=${INSTANCE%.asp}

        run_grounding "../../../../../../../programs/gringo4/gringo $EZSMT_INSTANCES/$INSTANCE $ENCODING_NAME" $FILE_NAME
        run_benchmark "../../../../../../../cmodels/cmodels -file $FILE_NAME.grounding-output " $FILE_NAME

    done

    cd - 
}

run_clingo_benchmarks() {
    EZSMT_INSTANCES=$1
    ENCODING_NAME=$2
    RESULTS_DIR=$3

    cd $RESULTS_DIR

    for INSTANCE in $( ls $EZSMT_INSTANCES); do
        :echo $INSTANCE
        echo $ENCODING_NAME
        run_benchmark "clingo $EZSMT_INSTANCES/$INSTANCE $ENCODING_NAME" ${INSTANCE%.asp}

    done

    cd - 
}

run_mingo_benchmarks() {
    EZSMT_INSTANCES=$1
    ENCODING_NAME=$2
    RESULTS_DIR=$3

    cd $RESULTS_DIR

    for INSTANCE in $( ls $EZSMT_INSTANCES); do
        echo $INSTANCE
        echo $ENCODING_NAME

	    FILE_NAME=${INSTANCE%.mingo}

        run_benchmark "mingo $EZSMT_INSTANCES/$INSTANCE $ENCODING_NAME" $FILE_NAME

    done

    cd -
}

run_ezcsp_benchmarks() {
    EZSMT_INSTANCES=$1
    ENCODING_NAME=$2
    RESULTS_DIR=$3

    cd $RESULTS_DIR

    ENCODING_TYPE=${ENCODING_NAME##$EZSMT_THESIS_TESTS/}
    ENCODING_TYPE=${ENCODING_TYPE%%-*}
    echo $ENCODING_TYPE

    case $ENCODING_TYPE in 
        # reverse folding
        21)
            EZCSP_PARAMS=$EZCSP_PARAMS_GREY
            ;;
        # weighted sequence
        28)
            EZCSP_PARAMS=$EZCSP_PARAMS_CLEAR
            ;;
        # incremental scheduling
        35)  
            EZCSP_PARAMS=$EZCSP_PARAMS_GREY
            ;;
        *)
	        EZCSP_PRARMS=$EZCSP_PARAMS_BLACK
            echo $"Usage: $0 {21|28|35}"
            ;;
    esac

    EZCSP_PARAMS="$EZCSP_PARAMS --bprolog"
    
    echo $EZCSP_PARAMS

    for INSTANCE in $( ls $EZSMT_INSTANCES); do
        echo $INSTANCE
        echo $ENCODING_NAME
        #run_benchmark "$EZCSP_BIN $EZCSP_PARAMS $EZSMT_INSTANCES/$INSTANCE $ENCODING_NAME" ${INSTANCE%.asp}
        run_benchmark "../../../../../../../programs/ezcsp-2.0.0-r4116/ezcsp --swiprolog --cmodels-incremental --grounder ../../../../../../../programs/gringo4/gringo  $EZSMT_INSTANCES/$INSTANCE $ENCODING_NAME" ${INSTANCE%.asp} 
    done

    cd -
}

run_ezsmt_benchmarks() {
    EZSMT_INSTANCES=$1
    ENCODING_NAME=$2
    RESULTS_DIR=$3

    cd $RESULTS_DIR
    
    for INSTANCE in $( ls $EZSMT_INSTANCES); do
        FILE_NAME=${INSTANCE%.asp}
        echo $FILE_NAME
        echo $INSTANCE
        echo $ENCODING_NAME
        
        run_preparse "ezcsp --preparse-only $EZSMT_INSTANCES/$INSTANCE $ENCODING_NAME" $FILE_NAME
        run_grounding "../../../../../../../programs/gringo4/gringo $FILE_NAME.preparse-output" $FILE_NAME
        run_completion "cmodels -file $FILE_NAME.grounding-output -cdimacs" $FILE_NAME
        #run_completion "cmodels -cdimacs"
        
        #cat $FILE_NAME.preparse-output | gringo | cmodels -cdimacs # $FILE_NAME
        
        #ls -l dimacs-completion*.out


        run_conversion "python $EZSMT_PROG $FILE_NAME.dimacs" $FILE_NAME
        run_benchmark "cvc4 --lang smt $FILE_NAME.smt" $FILE_NAME 
    done

    cd -
}


run_ezsmt_nontight_benchmarks() {
    EZSMT_INSTANCES=$1
    ENCODING_NAME=$2
    RESULTS_DIR=$3
    LR=$4
    SMTSolver=$5

    cd $RESULTS_DIR
    
    for INSTANCE in $( ls $EZSMT_INSTANCES); do
        FILE_NAME=${INSTANCE%.asp}
        echo $FILE_NAME
        echo $INSTANCE
        echo $ENCODING_NAME
        
        #run_preparse "ezcsp --preparse-only $EZSMT_INSTANCES/$INSTANCE $ENCODING_NAME" $FILE_NAME
        #run_grounding "../../../../../../../programs/gringo4/gringo $FILE_NAME.preparse-output" $FILE_NAME
        


	#we do not need to do preparse for pure asp encoding
        run_grounding "../../../../../../../programs/gringo4/gringo $EZSMT_INSTANCES/$INSTANCE $ENCODING_NAME" $FILE_NAME


	case $LR in 
    	LR)
		run_completion "../../../../../../../cmodels/cmodels -file $FILE_NAME.grounding-output -levelRanking" $FILE_NAME
        	;;
    	SCCLR)  
		run_completion "../../../../../../../cmodels/cmodels -file $FILE_NAME.grounding-output -SCClevelRanking" $FILE_NAME
        	;; 
    	*)
    	esac

        #run_completion "cmodels -cdimacs"
        
        #cat $FILE_NAME.preparse-output | gringo | cmodels -cdimacs # $FILE_NAME
        
        #ls -l dimacs-completion*.out


        run_conversion "python $EZSMT_PROG $FILE_NAME.dimacs" $FILE_NAME
        #run_conversion "python $EZSMT_PROG $FILE_NAME.dimacs linear-real" $FILE_NAME
        #run_conversion "python $EZSMT_PROG $FILE_NAME.dimacs nontight-linear-real" $FILE_NAME
        #run_conversion "python $EZSMT_PROG $FILE_NAME.dimacs difference-logic" $FILE_NAME
	case $SMTSolver in
	cvc4)
        	run_benchmark "cvc4 --lang smt $FILE_NAME.smt" $FILE_NAME
		;;
	z3)
        	run_benchmark "../../../../../../../programs/z3/build/z3 -smt2 $FILE_NAME.smt" $FILE_NAME
		;;
	yices)
                run_benchmark "../../../../../../../programs/yices-2.5.4/bin/yices-smt2 $FILE_NAME.smt" $FILE_NAME
                ;;
        *)
	esac
 
    done

    cd -
}


#run_casp2smt

run_all_nontight_benchmarks


#EZSMT_INSTANCES=$EZSMT_REPO_LOC/21-ReverseFolding/instances
#EZSMT_ENCODING=$EZSMT_REPO_LOC/21-ReverseFolding/encodings/21.advanced


#ezcsp --swiprolog $EZSMT_INSTANCES/11-reverse_folding-0-0.asp $EZSMT_ENCODING > ezcsp-results.txt
