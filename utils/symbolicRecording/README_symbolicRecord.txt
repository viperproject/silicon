
Chapters:
(i)  Usage of symbolic execution and or/visualiastion of the recording
(ii) TODO-List for SymbExLogger

=====================================
(i) Usage of symbolic execution recording and/or visualisation of the recording
=====================================

    If you want to visualise the recorded symbolic execution, follow these steps:

    1) Check that FLAG_WRITE_FILES in the SymbExLogger Object is set to true (src/main/scala/SymbExLogger.scala)
       (note: if you want to verify several files at once, e.g. with sbt>test, it is recommended
       to set this flag to false, otherwise File-I/O-overhead will increase runtime significantly)

    2) If you run your *.sil-file, SymbExLogger will write two files:
       \utils\symbolicRecording\dot_input.dot
       \utils\symbolicRecording\sedebuggertree\executionTree.js

    3) For DOT-Graph-Visualisation:
       a) Make sure you have GraphViz installed. www.graphviz.org
       b1) You use the created dot_input.dot file as input for one of the GraphViz-tools OR
       b2) you use the available batch-file \utils\symbolicRecording\visualise_dot.bat,
          which will automatically call dot and create a PNG-file with the graph.
          Make sure you have set the correct path to the GraphViz directory in the batchfile.

    4) For HTML-Visualisation:
       a1) Open \utils\symbolicRecording\sedebuggertree\example.html OR
       a2) use the batchfile \utils\symbolicRecording\visualise_HTML.bat

    Recommendation when using the batch-files: Open a 2nd Terminal in intelliJ (rightclick
    on Terminal -> New Session), use one Terminal for executing your files, use the other
    Terminal for the batch-files. Advantage: You dont need to exit SBT for executing the
    batch-files.


=====================================
TODO-List for SymbExLogger
=====================================

    1) Make it possible to disable logging, e.g. by making SymbExLogger-statements elidable.
       You might want to 'abuse' that everything logging-related is accessed via
       SymbExLogger-Object.

    2) Failed assertions: If tryAndFail is executed, stuff gets recorded twice. Add new record
       or provide further information in existing records to show the user
       what happened and why it happened.

    3) Implement commandline-parameters to decide whether or not recording is executed, and
       which visualisation is chosen. In short, get rid of SymbExLogger.FLAG_WRITE_FILES

    4) Unit-Testing currently only reports on which line of the files the first difference
       occurred, there might be more sophisticated ways to show differences

    5) Recording currently ignores or doesn't record in a very informative way:
       - Domains (ignored)
       - Magic Wands (?)
       - Quantified Permissions (?)

    6) Adding to 2): When Silicon aborts verification, recording is currently not really
       guaranteed to be sound. It 'makes sense' in most cases, but it would be nice to have concrete
       expectations on how stuff gets recorded when the verification aborts.

    7) It might be the case that identifiers upon insert/collapse are completly unnecessary.
       The problem that it solves was implemented primarily to make IfThenElse-Branching work,
       but it seems that the same approach that was taken for impure Branching (see: GlobalBranch-
       Record) could/should also work for IfThenElse.
       Sidenote: The identifiers turned out to be quite useful during debugging (for matching
       insert/collapse-pairs), getting rid of them has also its downsides.

    8) IfThenElse-Branching: Currently, the If-Branch and Else-Branch are recorded as part of the
       execution of a 'ConditionalBlock'. There's quite some code-duplication there, it might be possible
       to move the processing of the branches to another method or something similar which is then used
       twice, once for each branch, to reduce code-duplication.