// build.sbt  ―  Tiled RISC-V Array (Chisel 6)

ThisBuild / scalaVersion  := "2.13.14"
ThisBuild / version       := "0.1.0"
ThisBuild / organization  := "com.example"

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
    scalacOptions ++= Seq(
      "-language:reflectiveCalls",
      "-deprecation",
      "-feature",
      "-Xcheckinit",
    ),
    // テストリソース（生成済み hex ファイル）のパスを参照できるようにする
    Test / resourceDirectory := baseDirectory.value / "tests" / "hex",
  )