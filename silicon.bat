@echo off

set CURR_DIR=%cd%
set BASE_DIR=%~dp0

:: switch to repository root to check for classpath file and possibly call sbt.
cd "%BASE_DIR%"

:: Only call sbt if the classpath file is missing.
if not exist silicon_classpath.txt (
	rem Read all lines of the sbt runtime classpath output and parse it against the regex supplied to findstr.
	rem The regex looks for lines not starting with '[' and ending in '.jar' as the classpath usually does
	rem (and log lines don't, since they are prefixed with [LOGLEVEL]).
	echo Generating missing silicon_classpath.txt file from sbt classpath
	for /f "tokens=*" %%i in ('sbt "export runtime:dependencyClasspath" ^| findstr "[^\[].*\.jar$"') do (
		echo |set /p=%%i > silicon_classpath.txt
	)
)

:: Read classpath file in rather cumbersome way to avoid the 1024 character buffer limit.
:: Note: this solutions breaks, once the classpath is longer than 8192 characters!
for /f "delims=" %%x in (silicon_classpath.txt) do set CP=%%x

:: switch back to original directory
cd "%CURR_DIR%"

set JVM_OPTS=-Xss16m -Dlogback.configurationFile="%BASE_DIR%\src\main\resources\logback.xml" -Dfile.encoding=UTF-8

call java %JVM_OPTS% -cp "%CP%" viper.silicon.SiliconRunner %*
