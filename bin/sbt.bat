@echo off
SetLocal EnableDelayedExpansion

REM ========== Setup ==========

set PATH=%PATH%;%ROOT_DIR%\lib
	REM /* Temporarily (due to SetLocal above, only tested on Win7) */

chcp 65001 > NUL
	REM Set console code page to Unicode. Might not work on Windows XP.

set ROOT_DIR=%~dp0\..
	REM This script is expected to be one level lower than the project root

pushd %ROOT_DIR%
	REM Sbt assumes that the current directory is the project root directory
	
set _SBT_OPTS=%SBT_OPTS%

REM ========== Coloured sbt output ==========

REM To see coloured SBT output on windows, install ansicon first
REM http://www.marioawad.com/2010/11/16/ansi-command-line-colors-under-windows/
REM http://groups.google.com/group/simple-build-tool/browse_thread/thread/ce23159caa0c742c

set ARCH=x32
if defined ProgramFiles(x86) set ARCH=x64
	REM See http://stackoverflow.com/questions/601089 for other options how to
	REM detect the OS architecture

set ANSICON_CMD=
set ANSICON_EXE=%ROOT_DIR%\tools\ansicon\%ARCH%\ansicon.exe

if exist %ANSICON_EXE% (
	set ANSICON_CMD=%ANSICON_EXE% -p ^&^&
	set _SBT_OPTS=-Djline.terminal=jline.UnsupportedTerminal %_SBT_OPTS%
)

REM ========== Java Options ==========

REM http://www.scalingbits.com/javaprimer
set _JAVA_OPTS=
set _JAVA_OPTS=%_JAVA_OPTS% -XX:MaxNewSize=120M
set _JAVA_OPTS=%_JAVA_OPTS% -XX:NewSize=120M
set _JAVA_OPTS=%_JAVA_OPTS% -XX:MaxPermSize=256M
set _JAVA_OPTS=%_JAVA_OPTS% -XX:+UseParNewGC
set _JAVA_OPTS=%_JAVA_OPTS% -XX:+UseConcMarkSweepGC
set _JAVA_OPTS=%_JAVA_OPTS% -XX:+CMSParallelRemarkEnabled
set _JAVA_OPTS=%_JAVA_OPTS% -XX:TargetSurvivorRatio=90
set _JAVA_OPTS=%_JAVA_OPTS% -XX:+CMSClassUnloadingEnabled
REM set _JAVA_OPTS=%_JAVA_OPTS% -Xms256m
set _JAVA_OPTS=%_JAVA_OPTS% -Xmx256M
set _JAVA_OPTS=%_JAVA_OPTS% -Xss16M
set _JAVA_OPTS=%_JAVA_OPTS% -Dfile.encoding=UTF-8

REM ========== Assemble final command ==========

set JAVA_CMD=java %_SBT_OPTS% %_JAVA_OPTS% -jar "%ROOT_DIR%\tools\sbt-launch.jar" %*
set CMD=!ANSICON_CMD! !JAVA_CMD!
	REM Must use delayed expansion here, otherwise the command will be executed
	REM immediately. This seems to be due to the '&&' added to ANSICON_CMD.


REM ========== Run ==========
	
REM echo.
REM echo !CMD!
	REM REM Must use delayed expansion here, see previous comment.
REM echo.

call %CMD%
	REM Must use non-delayed expansion here, otherwise nothing will be executed.
	
popd