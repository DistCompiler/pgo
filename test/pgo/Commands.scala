package pgo

import courier.Mailer
import mainargs.{ParserForMethods, arg, main}
import org.scalacheck.rng.Seed
import pgo.util.TLAExpressionFuzzTestUtils

import scala.concurrent.Await
import scala.concurrent.duration.Duration

object Commands extends TLAExpressionFuzzTestUtils {
  @main(doc = "run fuzz testing, starting from a given seed value. useful for debugging a known-problematic scenario")
  def fuzzWithSeed(@arg(doc = "the rng seed value, in base64 (can be found in fuzz test output folder)") seed: String): Unit = {
    val result = runExpressionFuzzTesting(seed = Seed.fromBase64(seed).get)
    if(result.success) {
      println("passed!")
    } else {
      println("failed!")
    }
    pprint.pprintln(result)
  }

  case class Stats(successCount: Int = 0, failCount: Int = 0, nodeFrequencies: Map[String,Long] = Map.empty, treeSizes: Map[Int,Long] = Map.empty)
  object Stats {
    import upickle.default._
    implicit val rw: ReadWriter[Stats] = macroRW
  }

  @main(doc = "run fuzz testing in a loop, stopping on failure and sending an e-mail to the ~~victim~~ person responsible")
  def fuzzIndefinitely(@arg(doc = "file in which to persist stats", name = "statsFile") statsFileStr: String,
                       @arg(doc = "user component of victim e-mail") victimUser: String,
                       @arg(doc = "domain component of victim's e-mail") victimDomain: String,
                       @arg(doc = "SMTP server for victim") victimSmtp: String = "mail.cs.ubc.ca",
                       @arg(doc = "SMTP port for victim") victimPort: Int = 465,
                       @arg(doc = "password for victim's e-mail account") victimPassword: String): Unit = {
    import upickle.default._

    var roundNum = 0
    var hasFailed = false
    while(!hasFailed) {
      roundNum += 1

      val statsFile = os.Path(statsFileStr, os.pwd)
      var statss: Map[String,Stats] = if(os.exists(statsFile)) {
        upickle.default.read[Map[String,Stats]](os.read.stream(statsFile))
      } else Map.empty
      val commitHash = os.proc("git", "rev-parse", "HEAD").call(cwd = os.pwd).out.text().trim

      println(s"beginning round $roundNum of current run, on commit $commitHash")

      val results = runExpressionFuzzTesting()

      statss = statss.updated(commitHash, {
        val orig = statss.getOrElse(commitHash, Stats())
        orig.copy(
          successCount = orig.successCount + results.result.succeeded,
          failCount = if(!results.success) orig.failCount + 1 else orig.failCount,
          nodeFrequencies = orig.nodeFrequencies ++ results.nodeFrequencies.view.map {
            case (id, freq) => (id, orig.nodeFrequencies.getOrElse(id, 0L) + freq)
          },
          treeSizes = orig.treeSizes ++ results.treeSizes.view.map {
            case (size, freq) => (size, orig.treeSizes.getOrElse(size, 0L) + freq)
          },
        )
      })
      os.write.over(statsFile, data = stream(statss))

      if(!results.success) {
        hasFailed = true
        val msgText = s"failure caught! seed was `${results.seed}`. counter-example stored at ${results.testOut}"
        println(msgText)

        // "fancy" mail support: send a failure notification, alongside a ZIP of the failing case
        import courier._, Defaults._

        val mailer = Mailer(victimSmtp, victimPort)
          .auth(true)
          .as(victimUser, victimPassword)
          .ssl(true)
          .apply()

        val sendFuture = mailer {
          Envelope.from(victimUser `@` victimDomain)
            .to(victimUser `@` victimDomain)
            .subject("fuzz test failure")
            .content {
              var mp = Multipart()
              if(results.testOut.nonEmpty) {
                os.remove.all(os.pwd / "counter_example.zip")
                os.proc("zip", "-r", os.pwd / "counter_example.zip", results.testOut.get.last).call(cwd = results.testOut.get / os.up)
                println(s"zipped counter-example file...")
                mp = mp.attach((os.pwd / "counter_example.zip").toIO)
              }
              mp = mp.text(msgText)
              mp
            }
        }

        sendFuture.failed

        Await.ready(sendFuture
          .map { _ =>
            println(s"sent e-mail notification.")
          }
          .recover { err =>
            println("failed to send e-mail notification.")
            err.printStackTrace()
          }, Duration.Inf)
        println("shutting down.")
      }
    }

  }

  def main(args: Array[String]): Unit =
    ParserForMethods(this).runOrExit(args = args)
}
