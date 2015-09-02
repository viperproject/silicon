:: For instructions on usage, check out \utils\symbolicRecording\README_symbolicRecord.txt


:: Set the GRAPHVIZ_PATH variable to your installation folder:
::=====================================
SET GRAPHVIZ_PATH= E:\Programme\GraphViz
::=====================================

"%graphvizpath%\bin\dot.exe" -Tpng "%cd%\utils\symbolicRecording\dot_input.dot" > "%cd%\utils\symbolicRecording\dot_output.png"

"%cd%\utils\symbolicRecording\dot_output.png"