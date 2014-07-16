@echo off
SetLocal EnableDelayedExpansion

REM ======== Basic configuration ========

set BASE_DIR=%~dp0
set FWD_ARGS=%*
set MAIN=viper.silicon.SiliconRunner

REM ======== Path-dependent configuration ========

set JAVA_EXE=java
set CP=%BASE_DIR%\silicon.jar

REM ======== Java ========

set JVM_OPTS=-Xss64m
set MAIN_OPTS=
set CMD=%JAVA_EXE% %JVM_OPTS% -cp "%CP%" %MAIN% %MAIN_OPTS% %FWD_ARGS%

REM ======== Executing  ========

REM echo.
REM echo %CMD%
REM echo.

call %CMD%

exit /B 0