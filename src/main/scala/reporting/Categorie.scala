package ch.ethz.inf.pm.silicon.reporting

import ch.ethz.inf.pm.silicon
import silicon.interfaces.reporting.Categorie

case class DefaultCategorie(val name: String) extends Categorie

object Categories {
	val Error = DefaultCategorie("Error")
	val Warning = DefaultCategorie("Warning")
}