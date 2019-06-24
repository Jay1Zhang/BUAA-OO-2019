@echo off
cd C:/Users/94831/Desktop/课程中心/OO/MutualTest/homework2/SecondPro/src/Archer/src
javac Main.java
:loop
	del data.out
	java Main < data.in  > data.out
	fc data.out std.out

if not errorlevel 1 goto loop

pause

goto loop
