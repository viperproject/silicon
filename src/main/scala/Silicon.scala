package ch.ethz.inf.pm.silicon

import java.util.Calendar
import java.text.SimpleDateFormat
import com.weiglewilczek.slf4s.Logging
import silAST.programs.Program

class Silicon extends Logging {
	def execute(program: Program) {
		val now = (new SimpleDateFormat("yyyy-MM-dd hh:mm:ss z")).format(Calendar.getInstance().getTime)
		
		val startTime = System.currentTimeMillis()
		
		logger.info("Silicon started on " + now)
		logger.info("Working on Program:")
		logger.info(program.toString)
	}
}