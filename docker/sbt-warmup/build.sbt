ThisBuild / scalaVersion  := "2.13.14"

val chiselVersion = "6.5.0"

lazy val root = (project in file("."))
  .settings(
    name := "tile-riscv",
    addCompilerPlugin(
      "org.chipsalliance" % "chisel-plugin" % chiselVersion cross CrossVersion.full
    ),
    libraryDependencies ++= Seq(
      "org.chipsalliance" %% "chisel"     % chiselVersion,
      "edu.berkeley.cs"   %% "chiseltest" % "6.0.0" % Test,
    ),
  )