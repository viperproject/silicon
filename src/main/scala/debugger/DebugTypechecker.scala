package debugger

import viper.silver.parser.{NameAnalyser, PProgram, Resolver, TypeChecker}


class DebugResolver(override val p: PProgram) extends Resolver(p){
  override val typechecker: TypeChecker = new DebugTypeChecker(names)

}

class DebugTypeChecker(override val names: NameAnalyser) extends TypeChecker(names) {


}
