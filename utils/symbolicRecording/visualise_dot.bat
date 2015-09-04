:: For instructions on usage, check out \utils\symbolicRecording\README_symbolicRecord.txt


:: Set the GRAPHVIZ_PATH variable to your installation folder:
::=====================================
SET GRAPHVIZ_PATH= <INSERT PATH TO GRAPHVIZ DIRECTORY>
::=====================================

"%graphvizpath%\bin\dot.exe" -Tpng "%cd%\dot_input.dot" > "%cd%\dot_output.png"

"%cd%\dot_output.png"