//> using dependency "com.lihaoyi::os-lib:0.11.4"
//> using dependency "com.lihaoyi::requests:0.9.0"
//> using dependency "com.lihaoyi::upickle:4.2.1"

val workspaceDir = os.pwd / os.up / os.up
val antithesisDir = workspaceDir / "systems" / "antithesis"

val tenantName = "mongoresearch"
val keyFile = antithesisDir / s"$tenantName.key.json"
val userName = os.read(antithesisDir / s"$tenantName.user.txt").strip()
val password = os.read(antithesisDir / s"$tenantName.password.txt").strip()

def cmd(chunks: os.Shellable*): Unit =
  os.proc(chunks*)
    .showCmd
    .call(stdin = os.Inherit, stdout = os.Inherit, stderr = os.Inherit)

def loginDocker(): Unit =
  os.proc(
    "docker",
    "login",
    "-u",
    "_json_key",
    "https://us-central1-docker.pkg.dev",
    "--password-stdin",
  ).showCmd
    .call(
      stdin = os.read(common.keyFile),
      stdout = os.Inherit,
      stderr = os.Inherit,
    )

def pushToAntithesis(img: String): Unit =
  cmd(
    "docker",
    "tag",
    img,
    s"us-central1-docker.pkg.dev/molten-verve-216720/${tenantName}-repository/$img",
  )
  cmd(
    "docker",
    "push",
    s"us-central1-docker.pkg.dev/molten-verve-216720/${tenantName}-repository/$img",
  )

def launchAntithesis(img: String): Unit =
  val data = ujson.Obj(
    "params" -> ujson.Obj(
      "antithesis.description" -> "basic_test on main",
      "antithesis.duration" -> "10", // 30
      "antithesis.config_image" -> img.configImg,
      "antithesis.images" -> img,
      "antithesis.report.recipients" -> "finn.hackett@mongodb.com",
    ),
  )

  println(s"making request: $data")
  val resp = requests.post(
    s"https://$tenantName.antithesis.com/api/v1/launch/basic_test",
    auth = requests.RequestAuth.Basic(username = userName, password = password),
    data = data.toString,
  )
  println(s"CODE ${resp.statusCode}")
  println(resp.text())
end launchAntithesis

extension (proc: os.proc)
  def showCmd: proc.type =
    println(s"$$ ${proc.commandChunks.mkString(" ")}")
    proc

extension (img: String)
  def configImg: String =
    img match
      case s"$img:$tag" =>
        s"$img-config:$tag"

extension (path: os.Path)
  def shell(chunks: os.Shellable*): Unit =
    print(s"[$path]")
    os.proc(chunks*)
      .showCmd
      .call(
        cwd = path,
        stdout = os.Inherit,
        stdin = os.Inherit,
        stderr = os.Inherit,
      )
