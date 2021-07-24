package viper.silicon.annotation

import scala.annotation.{StaticAnnotation, compileTimeOnly}
import scala.language.experimental.macros
import scala.reflect.macros.whitebox

@compileTimeOnly("Could not expand macro.")
class flyweight(genCopy: Boolean = true) extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro flyweightMacro.impl
}

object flyweightMacro {
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*) = {
    import c.universe._

    // Check if copy method should be generated.
    val genCopy: Boolean = c.prefix.tree match {
      case q"new flyweight($b)" => c.eval[Boolean](c.Expr(b))
      case _ => true
    }

    val inputs = annottees.map(_.tree).toList

    // Get class declaration and companion object declaration if it exists.
    val (classDecl, companionDecl) = inputs match {
      case (head: ClassDef) :: Nil => (head, None)
      case (head: ClassDef) :: (tail: ModuleDef) :: Nil => (head, Some(tail))
      case _ => c.abort(c.enclosingPosition, "Annotation is only allowed on classes with optional companion object.")
    }

    // Extract information from class declaration.
    val (className, fields, bases, body) = try {
      val q"class $className $_(..$fields) extends ..$bases { ..$body }" = classDecl
      // TODO: Assert that class implements Term trait.
      (className, fields, bases, body)
    } catch {
      case _: MatchError => c.abort(c.enclosingPosition, "Could not parse class, is it a case class?")
    }

    // Get definitions from companion object, if any.
    // They are later inserted into the newly generated companion object.
    val companionDefns = companionDecl match {
      case Some(companionDecl) =>
        val q"object $_ extends ..$_ { ..$companionBody }" = companionDecl
        companionBody
      case None => List(q"")
    }

    // Define some helper values.
    val fieldTypes = fields.map(_.tpt).toList
    val fieldNames = fields.map(_.name).toList
    val termName = TermName(className.toString)

    // Check if an apply method already exists and rename it.
    var hasRenamedApplyMethod = false
    var hasUnapplyMethod = false
    var returnType = className
    val renamedCompanionDefns = companionDefns
      .map((elem) => try {
        val defn = elem.asInstanceOf[DefDef]
        val q"$_ def $methodName(...${methodFields}): $methodReturnType = $methodBody" = defn

        if (methodName.toString == "unapply") hasUnapplyMethod = true

        if (methodName.toString == "apply" && methodFields.head.length == fields.length && methodFields.head
          .zip(fields)
          .map({ case (mf, f) => mf.tpt.toString == f.tpt.toString })
          .foldLeft(true)(_ && _)
        ) {
          hasRenamedApplyMethod = true
          // TODO: Make it possible to use implicit return type. (Using context?)
          if (methodReturnType.toString == "<type ?>")
            c.abort(c.enclosingPosition, "Return type of non-compiler-generated apply method has to be explicit.")
          else
            returnType = TypeName(methodReturnType.toString)
          q"private def _apply (...${methodFields}): $methodReturnType = $methodBody"
        } else defn
      } catch {
        case _: ClassCastException => elem
      })

    // Create output from the extracted information.
    val output = q"""
      class $className private[terms] (..$fields) extends ..$bases {
        override lazy val hashCode = System.identityHashCode(this)

        ${
          if (genCopy)
            q"def copy(..${fieldNames.zip(fieldTypes).map({ case (name, ty) => q"val $name: $ty = $name"})}) = ${termName}(..${fieldNames})"
          else
            q""
        }
        ..$body
      }

      object ${termName} extends ((..${fieldTypes}) => $returnType) {
        import scala.collection.concurrent.TrieMap
        var pool = new TrieMap[(..${fieldTypes}), $returnType]

        def apply(..$fields) = {
          pool.get((..${fieldNames})) match {
            case None =>
              val term = ${
                // Use the now renamed apply method to create an instance of this object.
                if (hasRenamedApplyMethod)
                  q"${termName}._apply(..${fieldNames})"
                else
                  q"new $className(..${fieldNames})"
              }
              pool.addOne(((..${fieldNames}), term))
              term
            case Some(term) => term
          }
        }

        ${ // Create unapply method only if not already defined.
          if (!hasUnapplyMethod)
            q"""def unapply(t: $className) = {
                      ${
              // Turns out unapply on case classes without fields return true instead of an Option.
              if (fields.isEmpty)
                q"true"
              else
                q"Some((..${fieldNames.map(name => q"t.$name").toList}))"
            }
          }"""
          else q""
        }

        ..$renamedCompanionDefns
      }
    """

    output
  }
}
/*

*/