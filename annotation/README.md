# Flyweight ASTs

This directory contains the macro code to generate flyweight terms.

Flyweight ASTs are not used in the master branch as it did not increase performance as expected and thus is of no practical use. However the macro implementation may be used for different purposes in the future.

The file `Terms.example.scala` in this directory shows how the flyweight annotation can be used in practice.

If ever needed again, the `annotation` subproject  needs to be included in Silicon's `build.sbt` again:

```
lazy val annotation = project in file("annotation")
// ...

// Silicon specific project settings
lazy val silicon = (project in file("."))
  .dependsOn(annotation)
  // ...
```