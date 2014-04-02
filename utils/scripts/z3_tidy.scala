import java.io.{BufferedWriter, OutputStreamWriter, FileOutputStream}
import scala.io.Source
import scala.collection.immutable.Stack

/* TODO: Move all Z3 declarations to the beginning of the output file */

if (args.length < 2) {
	println("Usage: z3_tidy <in.smt2> <out.smt2>")
	exit(1)
}

val inFile = args(0)
val outFile = args(1)

var stack = Stack.empty[List[String]]
var ls = List[String]()
	
var inCnt = 0
var outCnt = 0

Source.fromFile(inFile).getLines().foreach{l =>
	inCnt += 1
	val lt = l.trim
	
	if (lt.startsWith("(push")) {
		stack = stack.push(ls)
		ls = List[String]()
	} else if (lt.startsWith("(pop")) {
		ls = stack.head
		stack = stack.pop
	} else {
		ls = l :: ls
	}
}

val outWriter =
	new BufferedWriter(new OutputStreamWriter(new FileOutputStream(outFile)))

stack = stack.push(ls)
stack.reverse.map(_.reverse).flatten.foreach{l =>
	outCnt += 1
	outWriter.write(l)
	outWriter.newLine()
}

outWriter.close()

println("Read %s lines, wrote %s lines.".format(inCnt, outCnt))