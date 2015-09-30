package reasonablypriced
import scala.language.higherKinds
import scala.language.implicitConversions
import scala.util.Try
import scalaz._
import scalaz.Scalaz._

object ReasonablyPriced extends App {

  // The following is based on Rúnar Bjarnasons brilliant talk: 
  //   Compositional Application Architecture With Reasonably Priced Monads

  // ---- SOME SET-UP: ----

  type Copro[F[_], G[_]] = { type f[x] = Coproduct[F, G, x] } // just for better readability

  // enhancing natural transformations with an or operator
  implicit class NaturalTransformationOrOps[F[_], H[_]](private val nt: F ~> H) extends AnyVal {
    // given F ~> H and G ~> H we derive Copro[F, G]#f ~> H
    def or[G[_]](f: G ~> H): Copro[F, G]#f ~> H =
      new (Copro[F, G]#f ~> H) {
        def apply[A](c: Coproduct[F, G, A]): H[A] = c.run match {
          case -\/(fa) => nt(fa)
          case \/-(ga) => f(ga)
        }
      }
  }

  type -~>[F[_], G[_]] = Inject[F, G] // alias for Inject to used infix

  object LiftImplicit {
    // lifting elments of a language into the Free-monad, this saves us from having a smart constructor for every element
    // in the language. Placed in object Implicits because it collides with implicit conversion ToFunctorOps.
    // Updated to use Free monad using the Coyoneda trait, which does not require the use of a map method
    implicit def lift[F[_], G[_], A](fa: F[A])(implicit I: F -~> G): Free.FreeC[G, A] = Free liftFC I.inj(fa)
  }


  // ---- LANGUAGES: ----
  // Languages are encoded as a case class per element/action in the language. Actions only describe what to do without 
  // inherent meaning how to do. It's members are the arguments to this action and the type parameter for the extended 
  // base trait encodes the return type of that action.
  // E.g. you can imagine a case class Create(key: Key, value: Value) extends Crud[Boolean] as a description of 
  // a function: (Key, Value) => Boolean

  // A simple language for interacting with the user
  sealed trait Interact[A]
  object Interact {
    case class Ask(prompt: String) extends Interact[String]
    case class Tell(msg: String)   extends Interact[Unit]
  }

  // A simple language for logging
  sealed trait Log[A]
  object Log {
    case class Info(txt: String) extends Log[Unit]
    case class Warn(txt: String) extends Log[Unit]
  }

  // Moved this out side of the trait. This caused major headaches for me
  sealed trait Crud[A]
  // A language for creating, reading, updating and deleting which is generic in the key and value type
  trait GenCrudCompanion {
    type Key
    type Value
    case class Create(key: Key, value: Value) extends Crud[Boolean]
    case class Read(key: Key)                 extends Crud[Option[Value]]
    case class Update(key: Key, value: Value) extends Crud[Boolean]
    case class Delete(key: Key)               extends Crud[Boolean]
  }

  // A concrete language with specific key and value type
  object Crud extends GenCrudCompanion {
    type Key = Int
    type Value = String
  }


  // ---- INTERPRETERS: ----
  // Languages can be interpreted to give meaning to the elements/actions in this language
  // This is done by NaturalTransformations (~>)

  // A side effect interpreter for interacting with the user 
  object Console extends (Interact ~> Id) {
    import Interact._
    def apply[A](i: Interact[A]): Id[A] = i match {
      case Ask(prompt) => { println(prompt); scala.io.StdIn.readLine() }
      case Tell(msg)   => println(msg)
    }
  }

  // A side effect interpreter for logging
  object Printer extends (Log ~> Id) {
    import Log._
    def apply[A](l: Log[A]): Id[A] = l match {
      case Info(txt) => println(txt)
      case Warn(txt) => System.err.println(txt)
    }
  }

  // An interpreter for the Crud language which uses an immutable map inside a scalaz.State
  type Store[A] = State[Map[Crud.Key, Crud.Value], A]
  object Crudinterpreter extends (Crud ~> Store) {
    import Crud._
    def apply[A](crud: Crud[A]): Store[A] = crud match {
      case Create(key, value) => State { m => (m + (key -> value), m contains key) }
      case Read(key)          => State { m => (m, m get key) }
      case Update(key, value) => State { m => (m + (key -> value), m contains key) }
      case Delete(key)        => State { m => (m - key, m contains key) }
    }
  }

  // A simple interpreter to chain with other interpreters 
  object Id2Store extends (Id ~> Store) {
    def apply[A](id: Id[A]): Store[A] = State { m => (m, id) }
  }

  // ---- PROGRAM: ----

  type R = Boolean
  // we don't know what kind of language F our program is written in but all we need is to be able 
  // to inject our three used languages into this language F
  def prg[F[_]](implicit I: Interact -~> F, C: Crud -~> F, L: Log -~> F): Free.FreeC[F, R] = {
    import LiftImplicit._ // needed to directly use language case classes instead of smart constructors
    import Interact._
    import Crud._
    import Log._
    def askFor[T](question: String)(extract: String => T): Free.FreeC[F, T] = {
      for {
        str <- Ask(question)
        t   <- Try(extract(str)).toOption.fold(askFor(question)(extract))(Free.pure[({type f[x]=Coyoneda[F,x]})#f, T](_))
      } yield t
    }
    for {
      key  <- askFor("Which key (Integer)?")(_.toInt)
      c    <- Create(key, "A")
      _    <- Info(s"created key $key which did${if (c) "" else "n't"} exist")
      vOpt <- Read(key)
      _    <- Info(s"read key $key : $vOpt")
      d1   <- Delete(key)
      _    <- Info(s"deleted key $key which did${if (d1) "" else "n't"} exist")
      d2   <- Delete(key)
      _    <- Info(s"deleted key $key which did${if (d2) "" else "n't"} exist")
      _    <- Create(key, "A") // just to have no empty map in the end
      _    <- Tell("finished roundtrip")
      passed = !c && vOpt.isDefined && d1 && !d2
    } yield passed: R
  }

  // we defined the type of our program language by stacking needed languages in Coproducts 
  type PRG0[A] = Coproduct[Interact, Crud, A]
  type PRG[A]  = Coproduct[Log, PRG0, A]
  val program: Free.FreeC[PRG, R] = prg[PRG]
  // we have to chain Console and Printer with Id2Store to bring all interpreters in line to be of the form ... ~> Store 
  // these two steps and type annotations are neccessary
  // This is Compose andThen Id2Store, becaus Scalaz 7.1.4 NaturalTransformation does not implement andThen
  val interpreter0: PRG0 ~> Store = (Id2Store compose Console) or Crudinterpreter
  val interpreter:  PRG  ~> Store = (Id2Store compose Printer) or interpreter0
  // Implements the Functor that maps it back to the interpreter...
  val coyoInterpreter = Coyoneda.liftTF(interpreter)
  // now that we have our program and a (combined) interpreter, we can run our program with this interpreter
  val result0: Store[R] = program.foldMap(coyoInterpreter)
  // result0 is a aggregated state function which we pass an initial state to run  
  val result: (Map[Crud.Key, Crud.Value], R) = result0.run(initial = Map.empty)
  println(result)

  // So what have we gained:
  //   Separated the description of what to do from the actual doing it in a certain way (interpreting it)
  //   Combined usage of serveral (> 2) languages 
  //   First steps into combining interpreters with different target domain
  //     (Console and Printer are interpretering into Id, but Crudinterpreter into Store)
  //   (Avoided smart constructors by implicit lift (may effect performance))

}
