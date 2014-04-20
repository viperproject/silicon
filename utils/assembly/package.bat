@echo off
SetLocal

set THIS_DIR=%~dp0
set BASE_DIR=%THIS_DIR%\..\..
set SIL_DIR=%BASE_DIR%\..\sil
set ZIP_EXE=zip

pushd %THIS_DIR%

call assembly.bat

mkdir examples

xcopy /S %SIL_DIR%\src\test\resources\all examples
xcopy /S /I %SIL_DIR%\src\test\resources\quantifiedpermissions examples\quantifiedpermissions

REM http://www.info-zip.org/Zip.html
zip -r silicon.zip silicon.jar silicon.bat silicon.sh examples

del silicon.jar
rmdir /S /Q examples

popd
exit /B 0