@echo off

:loop
    python generator.py
    datacheck_win -i datacheck_in.txt 
    java -Djava.ext.dirs=lib -classpath out/production/homework6-ALS-Elevator homeworkvi.Main < data.txt 

pause

goto loop