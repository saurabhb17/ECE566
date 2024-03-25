make clean
make all test
make EXTRA_SUFFIX=.NOCSE CUSTOMFLAGS="-no-cse -verbose" test
python3 ../../../../wolfbench/fullstats.py Instructions
python3 ../../../../wolfbench/timing.py
python3 ../../../../wolfbench/fullstats.py CSEDead
python3 ../../../../wolfbench/fullstats.py CSEElim
python3 ../../../../wolfbench/fullstats.py CSELdElim
