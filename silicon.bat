@echo off
SetLocal EnableDelayedExpansion

chcp 65001 > NUL

REM TODO: It is bad that all verion numbers are hard coded, as is the list of
REM       dependencies.
REM       We should hook into Sbt's 'package' task in order to create this batch
REM       file automatically, e.g., by filling in a template.

REM ======== Basic configuration ========

REM
REM This file is expected to be in the root directory of Silicon.
REM
set BASE_DIR=%~dp0

set FWD_ARGS=%*

REM ======== Path-independent configuration ========


REM SVER = significant version (Scala versions might not be byte-code compatible)
REM RVER = revision version (should be byte-code compatible)
set SCALA_SVER=2.10
set SCALA_RVER=%SCALA_SVER%.1
set SILICON_VERSION=0.1-SNAPSHOT
set SILICON_MAIN=semper.silicon.SiliconRunner

REM ======== Path-dependent configuration ========

set JAVA_EXE=java

set LIBS_DIR=%BASE_DIR%\lib

set IVY_CACHE=%USERPROFILE%\.ivy2\cache
if not exist %IVY_CACHE% (
	echo Local Ivy cache not found at %IVY_CACHE%.
  echo Silicon tries to find jar-dependencies there.
	goto :EXIT_WITH_ERROR
)

set SBT_HOME=%USERPROFILE%\.sbt
if not exist %SBT_HOME% (
	echo Sbt's home directory could not be found %SBT_HOME%.
  echo Silicon tries to find Scala's core libraries there.
	goto :EXIT_WITH_ERROR
)

REM Set classpath elements

REM Scala
set __CP.SCALA_LIB="%SBT_HOME%\boot\scala-%SCALA_RVER%\lib\scala-library.jar"
set __CP.SCALA_REF="%SBT_HOME%\boot\scala-%SCALA_RVER%\lib\scala-reflect.jar"
REM Silicon
set __CP.SILICON_COMMON=%BASE_DIR%\common\target\scala-%SCALA_SVER%\silicon-common_%SCALA_SVER%-%SILICON_VERSION%.jar
set __CP.SILICON_JAR=%BASE_DIR%\target\scala-%SCALA_SVER%\silicon_%SCALA_SVER%-%SILICON_VERSION%.jar
)
REM Silicon's dependencies
set __CP.SCALLOP_LIB="%IVY_CACHE%\org.rogach\scallop_%SCALA_SVER%\jars\scallop_%SCALA_SVER%-0.9.4.jar"
set __CP.SLF4S=%IVY_CACHE%\com.weiglewilczek.slf4s\slf4s_2.9.1\jars\slf4s_2.9.1-1.0.7.jar
set __CP.SLF4J_API=%IVY_CACHE%\org.slf4j\slf4j-api\jars\slf4j-api-1.6.4.jar
set __CP.SLF4J_WRAPPER=%IVY_CACHE%\org.slf4j\slf4j-log4j12\jars\slf4j-log4j12-1.6.4.jar
set __CP.LOG4J=%IVY_CACHE%\log4j\log4j\bundles\log4j-1.2.16.jar
REM Sil and its additional dependencies
set __CP.SIL="%BASE_DIR%..\sil\target\scala-%SCALA_SVER%\classes"
set __CP.KIAMA_LIB="%IVY_CACHE%\com.googlecode.kiama\kiama_%SCALA_SVER%\jars\kiama_%SCALA_SVER%-1.5.1.jar"

REM Assemble classpath and check if all classpath elements exist

set CP=
for /f "tokens=2* delims=.=" %%A in ('set __CP.') do (
	if not exist %%B (
		echo Error: %%B does not exist.
		echo Run 'sbt package' in %BASE_DIR%. This should download all dependencies and compile and package Silicon.
		goto :EXIT_WITH_ERROR
	) else (
		if !CP!.==. (
			set CP=%%B
		) else (
			set CP=!CP!;%%B
		)
	)
)

set JVM_OPTS=-Dlog4j.configuration=file:%BASE_DIR%\src\test\resources\log4j.properties -Xss16m -Dfile.encoding=UTF-8

REM ======== Assembling final command  ========

set CMD=%JAVA_EXE% %JVM_OPTS% -cp "%CP%" %SILICON_MAIN% %FWD_ARGS%

REM ======== Running SILICON  ========

REM echo.
REM echo %CMD%
REM echo.

call %CMD%

exit /B 0

REM ======== Subroutines  ========

:EXIT_WITH_ERROR
	exit /B 1