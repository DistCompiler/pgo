import common.{shell, showCmd, workspaceDir, configImg}

val dqueueWs = common.workspaceDir / "systems" / "dqueue"

try
  val dqueueImg = "dqueue:antithesis"

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
    dqueueImg,
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
    dqueueImg.configImg,
  )

  common.loginDocker()
  common.pushToAntithesis(dqueueImg)
  common.pushToAntithesis(dqueueImg.configImg)

  common.launchAntithesis(dqueueImg)
finally os.remove.all(dqueueWs / "dqueue.test")
