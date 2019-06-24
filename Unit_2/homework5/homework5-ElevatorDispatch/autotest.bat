@echo off

cd out/production/homework5-ElevatorDispatch/
::当main类依赖多个jar时，可以把多个jar打包到一个目录，然后用-Djava.ext.dirs指定该目录，引用依赖的多个jar，
::java -Djava.ext.dirs=lib com.test.HelloWordMain

:loop
    :: input
    ::set /p str=input: %1
    ::echo %str% > data.in 
    echo ------- output -------
    echo.

    java -Djava.ext.dirs=homeworkv homeworkv.Main < data.in

    echo.
    
pause

goto loop
