
import common.{shell, showCmd, workspaceDir, configImg}

val raftkvsWs = common.workspaceDir / "systems" / "raftkvs"

try
  val img = "raftkvs:antithesis"

  raftkvsWs.shell("go", "build", "./cmd/client")
  raftkvsWs.shell("go", "build", "./cmd/server")
  workspaceDir.shell(
    "docker",
    "build",
    ".",
    "--platform",
    "linux/amd64",
    "--file",
    common.antithesisDir / "raftkvs" / "Dockerfile.test",
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
    common.antithesisDir / "raftkvs" / "Dockerfile.config",
    "-t",
    img.configImg,
  )

  common.loginDocker()
  common.pushToAntithesis(img)
  common.pushToAntithesis(img.configImg)

  common.launchAntithesis(img)
finally
  os.remove.all(raftkvsWs / "client")
  os.remove.all(raftkvsWs / "server")
