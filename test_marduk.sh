#! /bin/sh

pgm=$0

pgmdir=`dirname ${pgm}`

# from http://www.shelldorado.com/shelltips/script_programmer.html
abspgmdir="`cd \"${pgmdir}\" 2>/dev/null && pwd || echo \"${pgmdir}\"`"

PYTHONPATH="$PYTHONPATH:.:./nusmv:./spec_debug"
LD_LIBRARY_PATH="$LD_LIBRARY_PATH:$abspgmdir/../../NuSMV-game/NuSMVWrap/nusmv/clib"

export PYTHONPATH
export LD_LIBRARY_PATH

if [ ! -f ../specs/unrealizable/xml/amba_2_woef_a.xml ]
then
echo "Testfiles do not exist. Creating them ... (may take some time)"
cd ../specs/unrealizable/
./generate_all.sh > /dev/null
cd $abspgmdir
echo "Done!"
fi

echo "Performing some tests ... (may take some time)"
#echo "Testing with ../specs/unrealizable/xml/amba_2.xml ..."
python -u ${pgmdir}/marduk.py -d --r1 --r2 -i ../specs/unrealizable/xml/amba_2.xml 1>./check_out.txt

if ! grep -qF "Specification read within" ./check_out.txt; then
    echo 'FAIL: amba_2.xml: could not read spec!'
    exit -1
fi
if ! grep -qF "First reordering of bdd takes" ./check_out.txt; then
    echo 'FAIL: amba_2.xml: first reordering failed!'
    exit -1
fi
if ! grep -qF "Compute winning region within" ./check_out.txt; then
    echo 'FAIL: amba_2.xml: could not compute winning region!'
    exit -1
fi
if ! grep -qF "Compute strategy within" ./check_out.txt; then
    echo 'FAIL: amba_2.xml: could not compute winning strategy!'
    exit -1
fi
if ! grep -qF "Compute output functions within" ./check_out.txt; then
    echo 'FAIL: amba_2.xml: could not compute output function!'
    exit -1
fi
if ! grep -qF "Code generation takes" ./check_out.txt; then
    echo 'FAIL: amba_2.xml: could not generate code!'
    exit -1
fi
if ! grep -qF "FINISHED synthesis" ./check_out.txt; then
    echo 'FAIL: amba_2.xml: could not complete synthesis!'
    exit -1
fi


#echo "Testing with ../specs/unrealizable/xml/amba_2_woef_a.xml ..."
python ${pgmdir}/marduk.py -d --r1 --r2 -i ../specs/unrealizable/xml/amba_2_woef_a.xml --dm SMuvTuG 1>./check_out.txt

if ! grep -qF "The specification IS satisfiable" ./check_out.txt; then
    echo 'FAIL: amba_2_woef_a.xml is not reported as satisfiable!'
    exit -1
fi
if ! grep -qF "All in all: 80 formulas --reduced to--> 9 formulas" ./check_out.txt; then
    echo 'FAIL: amba_2_woef_a.xml: minimization failed!'
    exit -1
fi
if ! grep -qF "343 checks for realizability had to be done" ./check_out.txt; then
    echo 'FAIL: amba_2_woef_a.xml: minimization failed!'
    exit -1
fi

if ! grep -qF "Computing the counterstrategy took" ./check_out.txt; then
    echo 'FAIL: amba_2_woef_a.xml: could not compute counterstrategy!'
    exit -1
fi

if ! grep -qF " Countertrace FOUND" ./check_out.txt; then
    echo 'FAIL: amba_2_woef_a.xml: could not find a countertrace!'
    exit -1
fi

if ! grep -qF "Nr of states in graph: 5" ./check_out.txt; then
    echo 'FAIL: amba_2_woef_a.xml: graph computation did not succeed!'
    exit -1
fi

#echo "Testing with ../../ratsy/examples/demo/DemoGame2.rat"
python ${pgmdir}/marduk.py -d --r1 --r2 -i ../../ratsy/examples/demo/DemoGame2.rat --dm SMuvTuG 1>./check_out.txt

if ! grep -qF "The specification IS satisfiable" ./check_out.txt; then
    echo 'FAIL: DemoGame2.rat is not reported as satisfiable!'
    exit -1
fi
if ! grep -qF "All in all: 11 formulas --reduced to--> 7 formulas" ./check_out.txt; then
    echo 'FAIL: DemoGame2.rat: minimization failed!'
    exit -1
fi
if ! grep -qF "83 checks for realizability had to be done" ./check_out.txt; then
    echo 'FAIL:DemoGame2.rat: minimization failed!'
    exit -1
fi

if ! grep -qF "Computing the counterstrategy took" ./check_out.txt; then
    echo 'FAIL: DemoGame2.rat: could not compute counterstrategy!'
    exit -1
fi

if ! grep -qF " Countertrace FOUND" ./check_out.txt; then
    echo 'FAIL: DemoGame2.rat: could not find a countertrace!'
    exit -1
fi

if ! grep -qF "Nr of states in graph: 13" ./check_out.txt; then
    echo 'FAIL: DemoGame2.rat: graph computation did not succeed!'
    exit -1
fi

#echo "Testing with ../specs/misc/counter-5-gdl.rat"
python ${pgmdir}/marduk.py -d --r1 --r2 -i ../specs/misc/counter-5-gdl.rat 1>./check_out.txt

if ! grep -qF "Specification read within" ./check_out.txt; then
    echo 'FAIL: counter-5-gdl.rat: could not read spec!'
    exit -1
fi
if ! grep -qF "Encountered non-Boolean variable 'v'." ./check_out.txt; then
    echo 'FAIL: counter-5-gdl.rat: Did not encounter non-boolean variable!'
    exit -1
fi
if ! grep -qF "ADD corresponding to the encoding" ./check_out.txt; then
    echo 'FAIL: counter-5-gdl.rat: could not encode non-boolean variable!'
    exit -1
fi
if ! grep -qF "FINISHED synthesis" ./check_out.txt; then
    echo 'FAIL: counter-5-gdl.rat: could not complete synthesis!'
    exit -1
fi


rm ./check_out.txt
echo "ALL Tests PASSED"
