package com.lge.metr

import java.io.File
import scala.Array.canBuildFrom
import spoon.AbstractLauncher
import spoon.reflect.Factory
import spoon.support.DefaultCoreFactory
import spoon.support.JavaOutputProcessor
import spoon.support.StandardEnvironment
import spoon.processing.Environment
import spoon.processing.Builder
import spoon.support.builder.SpoonBuildingManager

case class Config(src: Seq[File] = Seq(), deps: Seq[File] = Seq())

object AppMain extends AbstractLauncher with App {
  val parser = new scopt.OptionParser[Config]("metr") {
    head("metr", "1.0")

    opt[String]('s', "src") required () valueName ("<separated list of file or directory>") action { (x, c) =>
      c.copy(src = c.src ++ x.split(File.pathSeparator).map(new File(_)))
    } text ("src is a file to analyize or a directory which is a root of source files")
    opt[String]('d', "deps") optional () valueName (s"separated list of jar-files") action { (x, c) =>
      c.copy(deps = c.deps ++ x.split(File.pathSeparator).map(new File(_)))
    }
  }

  // parser.parse returns Option[C]
  parser.parse(args, Config()) map { config =>
    val factory = getFactory
    val builder = factory.getBuilder

    factory.getEnvironment.setComplianceLevel(6)

    config.src foreach (builder.addInputSource(_))
    println(builder.build)
  } getOrElse {
    // arguments are bad, error message will have been displayed
  }

  override def createFactory: Factory = {
    val env = new StandardEnvironment
    val factory = new Factory(new DefaultCoreFactory, env)

    env.setComplianceLevel(6)
    env.setVerbose(true)
    env.setTabulationSize(4)
    env.useTabulations(false)

    factory
  }

}