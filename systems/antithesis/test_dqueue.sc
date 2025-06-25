import common.{shell, showCmd, workspaceDir, configImg}

val dqueueWs = common.workspaceDir / "systems" / "dqueue"

try
  val img = "dqueue:antithesis"

  dqueueWs.shell("go", "test", "-c")
  workspaceDir.shell(
    "docker",
    "build",
    ".",
    "--platform",
    "linux/amd64",
    "--file",
    common.antithesisDir / "dqueue" / "Dockerfile.test",
    "-t",
    img,
  )
  workspaceDir.shell(
    "docker",
    "build",
    ".",
    "--platform",
    "linux/amd64",
    "--file",
    common.antithesisDir / "dqueue" / "Dockerfile.config",
    "-t",
    img.configImg,
  )

  common.loginDocker()
  common.pushToAntithesis(img)
  common.pushToAntithesis(img.configImg)

  common.launchAntithesis(img)
finally os.remove.all(dqueueWs / "dqueue.test")
