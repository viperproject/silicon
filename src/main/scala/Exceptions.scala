package semper.syxc

class VerificationException(val code: Int, val info: String)
		extends java.lang.RuntimeException {
	
	override val toString = info
}

class ASTConversionException(code: Int, info: String)
		extends VerificationException(code, info)