name := "atpl"

version := "1.0"

scalaVersion := "2.12.1"

scalacOptions := Seq("-unchecked", "-deprecation", "-encoding", "utf8")

//resolvers += "osc repository" at "http://maven.oschina.net/content/groups/public/"
resolvers += "main" at "http://repo1.maven.org/maven2"
resolvers += Resolver.mavenLocal
resolvers ++= Seq(
  Resolver.sonatypeRepo("releases"),
  Resolver.sonatypeRepo("snapshots")
)

externalResolvers := Resolver.withDefaultResolvers(resolvers.value, mavenCentral = false)