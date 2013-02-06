; Requires Z3 4.x

; ATTENTION: Continuing multi-line statements must be indented with at least
;            one tab or two spaces. All other lines must not start with tabs
;            or more than one space.

(set-option :print-success true) ; Boogie: false
; (set-option :print-warning false) ; Boogie: default
(set-option :global-decls true) ; Boogie: default

(set-option :AUTO_CONFIG false)
(set-option :MODEL_HIDE_UNUSED_PARTITIONS false)
(set-option :MODEL_V2 true)
(set-option :ASYNC_COMMANDS false)
(set-option :PHASE_SELECTION 0)
(set-option :RESTART_STRATEGY 0)
(set-option :RESTART_FACTOR |1.5|)
(set-option :ARITH_RANDOM_INITIAL_VALUE true)
(set-option :CASE_SPLIT 3)
(set-option :DELAY_UNITS true)
(set-option :DELAY_UNITS_THRESHOLD 16)
(set-option :NNF_SK_HACK true)
(set-option :MBQI false)
(set-option :QI_EAGER_THRESHOLD 100)
(set-option :QI_COST |"(+ weight generation)"|)
(set-option :TYPE_CHECK true)
(set-option :BV_REFLECT true)
; (set-option :QI_PROFILE true)
; (set-option :DEFAULT_QID true)

; (set-info :smt-lib-version 2.0)
; (set-info :category "industrial")

; (set-option :SOFT_TIMEOUT 5000)
; (set-option :soft-timeout 5000)

; --- Snapshots ---

; (declare-datatypes (($Snap ($combine ($combine.first Int) ($combine.second Int)))))
(declare-datatypes () (($Snap $Snap.unit ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))
; (declare-sort $Snap)

; (declare-const $unit $Snap)

; (declare-fun $combine ($Snap $Snap) $Snap)
(declare-fun $Snap.snapEq ($Snap $Snap) Bool)

; (assert (forall ((x1 $Snap) (x2 $Snap) (y1 $Snap) (y2 $Snap)) (!
	; (implies
		; ($snapEq ($combine x1 y1) ($combine x2 y2))
		; (and (= x1 x2) (= y1 y2)))
	; :qid |Combine|
	; :pattern (($snapEq ($combine x1 y1) ($combine x2 y2)))
	; )))
	
(assert (forall ((x $Snap) (y $Snap)) (!
	(implies
		($Snap.snapEq x y)
		(and (= x y)))
	:qid |$Snap.snapEq|
	:pattern (($Snap.snapEq x y))
	)))

; --- References ---

(declare-sort $Ref)

(declare-const $Ref.null $Ref)

(declare-const $thread $Ref)
 
; ; --- General math ---

; (declare-fun $Math.abs (Int) Int)

; (assert (forall ((i Int))
	; (and
		; (implies (< i 0) (= ($Math.abs i) (- 0 i)))
		; (implies (>= i 0) (= ($Math.abs i) i)))
	; ))

; --- Permissions ---

(define-sort $Perms () Real)
; (declare-const $Perms.Write $Perms)
(define-const $Perms.Write $Perms 1.0)
; (declare-const $Perms.Zero $Perms)
(define-const $Perms.Zero $Perms 0.0)
(declare-const $Perms.iRd $Perms) ; ???
(declare-const $Perms.pRd $Perms) ; Predicate read
(declare-const $Perms.mRd $Perms) ; Monitor read
(declare-const $Perms.cRd $Perms) ; Channel read

(define-fun $Perms.isValid ((p $Perms) (ub $Perms)) Bool
  (and (< $Perms.Zero p)
       (< p ub)))
       
(define-fun $Perms.isRead ((p $Perms) (ub $Perms)) Bool
  (and ($Perms.isValid p ub)
       (< (* 1000.0 p) $Perms.Write)))

; (assert (= $Perms.Zero 0.0))
; (assert (= $Perms.Write 1.0))
(assert ($Perms.isRead $Perms.iRd $Perms.Write))

(assert ($Perms.isRead $Perms.mRd $Perms.Write))
(assert
  (and
    (= $Perms.mRd $Perms.pRd )
    (= $Perms.pRd $Perms.cRd )))
; (assert ($Perms.isRead $Perms.pRd $Perms.Write))
; (assert ($Perms.isRead $Perms.cRd $Perms.Write))

; --- Credits ---
	
(declare-fun $Credits.credits ($Ref Int) Int)

; Macros
	
; (define ($Credits.allZero (x Int) (v Int))
	; (forall (r Int)
		; (= ($Credits.credits r v) 0)
	; ; :pat {($Credits.credits r v)})))
	; ))

; (define ($Credits.credits.updated (x Int) (v Int))
(define-fun $Credits.credits.updated ((x $Ref) (v Int)) Bool
	(forall ((r $Ref))
		(implies
			(not (= r x))
			(= ($Credits.credits r v) ($Credits.credits r (- v 1))))
	; :pat {($Credits.credits r v) ($Credits.credits r (- v 1))})))
	))

; --- Locks and locking order ---

(declare-datatypes ()
	(($Locks.mode $Locks.mode.none $Locks.mode.read $Locks.mode.write)))

(define-sort $Mu () Int)

(declare-fun $Locks.bottom () $Mu)
(declare-fun $Locks.initialMu ($Ref) $Mu)
(declare-fun $Locks.initialHolds ($Ref) $Locks.mode)
; (declare-fun $Locks.holds ($Ref Int) $Locks.mode)
(declare-fun $Locks.holds ($Ref $Locks.mode) $Locks.mode)
; (declare-fun $Locks.mu ($Ref Int) Int)
(declare-fun $Locks.less ($Mu $Mu) Bool)
; TODO: Use $Locks.eq instead of ==

(assert
  (= ($Locks.initialHolds $thread) $Locks.mode.write))

; Macros

; ; (define ($Locks.holds.updated (x Int) (v Int))
; (define-fun $Locks.holds.updated ((x $Ref) (v Int)) Bool
	; (forall ((r $Ref))
		; (implies
			; (not (= r x))
			; (= ($Locks.holds r v) ($Locks.holds r (- v 1))))
	; ; :pat {($Locks.holds x v p) ($Locks.holds r (- v 1))})))
	; ))
		
; ; (define ($Locks.mu.updated (x Int) (v Int))
; (define-fun $Locks.mu.updated ((x $Ref) (v Int)) Bool
	; (forall ((r $Ref))
		; (implies
			; (not (= r x))
			; (= ($Locks.mu r v) ($Locks.mu r (- v 1))))
	; ; :pat {($Locks.mu r v) ($Locks.mu r (- v 1))})))
	; ))

; ; (define ($Locks.maxlock.less (m Int) (v Int) (w Int) (c Int))
; (define-fun $Locks.maxlock.less ((m Int) (v Int) (w Int) (c Int)) Bool
	; (forall ((r $Ref))
		; (implies
			; ; (not (= ($Locks.holds r v) $Locks.mode.none))
      ; (and
        ; (not (= ($Locks.mu r w) m))
        ; ; true
        ; (or
          ; (not (= ($Locks.holds r v) $Locks.mode.none))
          ; (< ($Credits.credits r c) 0)))
			; ($Locks.less ($Locks.mu r w) m))))

; ; (define ($Locks.maxlock.atMost (m Int) (v Int) (w Int) (c Int))
; (define-fun $Locks.maxlock.atMost ((m Int) (v Int) (w Int) (c Int)) Bool
  ; (forall ((r $Ref))
    ; (implies
			; (or
				; (not (= ($Locks.holds r v) $Locks.mode.none))
				; (< ($Credits.credits r c) 0))
      ; (or
        ; ($Locks.less ($Locks.mu r w) m)
        ; (= ($Locks.mu r w) m)))))

; ; Axioms

(assert (forall ((t1 $Mu) (t2 $Mu)) (!
  (implies
    ($Locks.less t1 t2)
    (not (= t2 $Locks.bottom)))
  :pattern (($Locks.less t1 t2)))))
  ; ))

(assert (forall ((m $Mu)) (!
	(implies
		(not (= $Locks.bottom m))
		($Locks.less $Locks.bottom m))
	:pattern (($Locks.less $Locks.bottom m)))))
	; ))

(assert (forall ((t1 $Mu) (t2 $Mu)) (!
  (not (and ($Locks.less t1 t2) ($Locks.less t2 t1)))
  :pattern (($Locks.less t1 t2) ($Locks.less t2 t1)))))
  ; ))

(assert (forall ((m1 $Mu) (m2 $Mu) (m3 $Mu)) (!
	(implies
		(and ($Locks.less m1 m2) ($Locks.less m2 m3))
		($Locks.less m1 m3))
	:pattern (($Locks.less m1 m2) ($Locks.less m2 m3) ($Locks.less m1 m3)))))
	; ))

; (assert (forall ((r $Ref) (lm $Locks.mode)) (!
  ; (= ($Locks.holds r lm) lm)
  ; :pattern (($Locks.holds r lm)))))
  ; ; ))
  
; (assert (forall ((t $Ref) (m $Mu)) ; (!
	; (implies
		; (= m $Locks.bottom)
		; (= ($Locks.holds t m) $Locks.mode.none))
	; ; :pattern (($Locks.less $Locks.bottom m)))))
	; ))
  
; (assert (forall ((t1 $Ref) (t2 $Ref) (v Int) (w Int))
	; (implies
		; (and (not (= t1 t2))
		; (and (not (= ($Locks.holds t1 v) $Locks.mode.none))
				 ; (not (= ($Locks.holds t2 v) $Locks.mode.none))))
		; (not (= ($Locks.mu t1 w) ($Locks.mu t2 w))))
	; ; :pat {($Locks.holds t1 v) ($Locks.holds t2 v) ($Locks.mu t1) ($Locks.mu t2)}
	; ))
	
; --- Immutability	---

(declare-fun $Immutability.immutable ($Ref Int) Bool)
(declare-fun $Immutability.frozen ($Ref Int) Bool)

; --- Sort wrappers ---

(declare-fun $sorts.$SnapToInt ($Snap) Int)
(declare-fun $sorts.IntTo$Snap (Int) $Snap)

(assert (forall ((x Int))
	(= x ($sorts.$SnapToInt($sorts.IntTo$Snap x)))))

(assert (forall ((x $Snap))
	(= x ($sorts.IntTo$Snap($sorts.$SnapToInt x)))))

(declare-fun $sorts.$SnapTo$Ref ($Snap) $Ref)
(declare-fun $sorts.$RefTo$Snap ($Ref) $Snap)

(assert (forall ((x $Ref))
	(= x ($sorts.$SnapTo$Ref($sorts.$RefTo$Snap x)))))

(assert (forall ((x $Snap))
	(= x ($sorts.$RefTo$Snap($sorts.$SnapTo$Ref x)))))

(declare-fun $sorts.$SnapToBool ($Snap) Bool)
(declare-fun $sorts.BoolTo$Snap (Bool) $Snap)

(assert (forall ((x Bool))
	(= x ($sorts.$SnapToBool($sorts.BoolTo$Snap x)))))

(assert (forall ((x $Snap))
	(= x ($sorts.BoolTo$Snap($sorts.$SnapToBool x)))))

(declare-fun $sorts.$SnapTo$Mu ($Snap) $Mu)
(declare-fun $sorts.$MuTo$Snap ($Mu) $Snap)

(assert (forall ((x $Mu))
	(= x ($sorts.$SnapTo$Mu($sorts.$MuTo$Snap x)))))

(assert (forall ((x $Snap))
	(= x ($sorts.$MuTo$Snap($sorts.$SnapTo$Mu x)))))
  
; (declare-fun $sorts.$SnapToList<Int> ($Snap) (List Int))
; (declare-fun $sorts.List<Int>To$Snap ((List Int)) $Snap)

; (assert (forall ((x (List Int)))
	; (= x ($sorts.$SnapToList<Int>($sorts.List<Int>To$Snap x)))))

; (assert (forall ((x $Snap))
	; (= x ($sorts.List<Int>To$Snap($sorts.$SnapToList<Int> x)))))
  
; TODO: BoolToInt and BoolToRef are only needed when True is chosen as
;        the result value of dead branches. Either prune such branches, i.e.,
;        simplify an ite to a implication, or use a fresh term of the
;        appropriate sort instead of True.
(declare-fun $sorts.BoolToInt (Bool) Int)
(declare-fun $sorts.IntToBool (Int) Bool)

(assert (forall ((x Bool))
	(= x ($sorts.IntToBool($sorts.BoolToInt x)))))

(declare-fun $sorts.BoolTo$Ref (Bool) $Ref)
(declare-fun $sorts.$RefToBool ($Ref) Bool)

(assert (forall ((x Bool))
	(= x ($sorts.$RefToBool($sorts.BoolTo$Ref x)))))

; --- Setup	---

(assert (forall ((r $Ref))
		(= ($Credits.credits r 0) 0)
	; :pat {($Credits.credits r v)})))
	))

; (get-proof "stdout")
; (get-info statistics)

; (push)
; (check-sat)
; (pop)