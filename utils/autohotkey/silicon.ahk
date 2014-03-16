; Make sure that this file is UTF-8 encoded with a BOM!
; AutoHotkey won't correctly recognise it otherwise.

; Control key		Ctrl-		^
; Alt key 			Alt- 		!
; Shift key 		Shift- 	+
; Windows key 	Win- 		#

SetKeyDelay -1 0

; Lambda l
^#l::send λ

; Gamma G,g
#+g::send Γ
#g::send γ

; Pi P, p
#+p::send Π
#p::send π

; Sigma S, s
#+s::send Σ
#s::send σ

; Phi p
#f::send f

; not equal, equal
#=::send ≠
+#=::send ≡

; empty set (actually a stroken-through letter O)
#0::Send Ø

; Tau t, Turnstyle / Right tack, Negation thereof
; #t::send τ
; ^#t::send ⊢
; ^#+t::Send ⊬