# Preliminary steps for compiling to a GraalVM native image
This assumes a working *GraalVM Community Edition* installation with all the necessary environment variables (like `JAVA_HOME`) set correctly.

1. Prepare an empty directory `<CONFIG_OUT>` for the program trace
1. With the Silicon JAR and some non-trivial Viper file `<VIPER_FILE>` in the current working directory, run Silicon on `<VIPER_FILE>` using the *native image agent*:
`java -Xss256m -agentlib:native-image-agent=config-output-dir=<CONFIG_OUT> -jar silicon.jar <VIPER_FILE>`.
This is necessary because Silicon uses some dynamic JVM features (like loading the AdtPlugin at runtime) that cannot be statically inferred by the native image compiler.
1. Compile the Silicon JAR to a native image using the data gathered during the previous step:
`native-image -H:ConfigurationFileDirectories=<CONFIG_OUT> -jar silicon.jar`
