;; Z3 SCRIPT BY MARIO, ASK IF CLARIFICATION OR MORE DETAILS ARE NEEDED
;;
;; HERE IS THE FINAL SMT SOLVER SCRIPT FOR PROVING SOUNDNESS OF OUR LATEST DIVISION CONSTRAINTS:
;; IN THE COMMENTS OF THE "SPECIFICATION" SECTION IT CONTAINS MANY VARIANTS
;; WHICH HAVE BEEN PROVEN EQUIVALENT TO THE ACTUAL SPEC (NOT IN COMMENTS)
;; AND A COUPLE OF VARIANTS WHICH CANNOT BE PROVEN EQUIVALENT WITHOUT FURTHER MASKING BUT ARE OF INTEREST
;; 
;; WARNING: IN THIS SCRIPT WE SIMPLY PROVE DIVISION BETWEEN SIGNED 8-BIT WORDS
;; THIS IS BECAUSE IT MAKES Z3 PROVING FASTER, AND BECAUSE IT IS EASILY EXTENDED
;; TO OUR REAL SCENARIO OF SIGNED 32-BIT DIVISION. ALSO, WE DO NOT SEPARATELY PROVE
;; CORRECTNESS OF THIS SCRIPT WHEN VARIABLES ARE WRAPPED IN OUR PRIME FIELD
;; SINCE WE MANUALLY CHECKED AND CAN ASSUME THAT WE DID NOT COMMIT ANY WRAPPING OR OTHER EMBEDDING 
;; MISTAKES IN OUR ACTUAL AIR CONSTRAINTS.
;;
;; NOTES:
;; - IT IS INTERESTING HOW MUCH SIMPLE MASKING CAN AFFECT DIVISION CONSTRAINTS:
;; IN OUR OPTIMISATION WE FIND THAT MANUALLY COMPUTING OUTPUTS' SIGN EXTENSIONS
;; GIVES US MORE CHEAPLY SATISFYING CONSTRAINTS, BECAUSE THROUGH EXPLICIT SIGN EXTENSIONS
;; WE ALSO IMPLICITLY FURTHER CONSTRAIN OF OUR DIVISION RELATION AND ITS INPUTS
;;
;; - AS EXAMPLE CONSIDER OUR OLD VERSION WHICH USED TO MASK DIVISION:
;; WHEN AN UNDERFLOW COULD OCCUR WE CHEAPLY MASKED DIVISOR FROM -1 TO 1
;; HOWEVER THIS ALSO CHANGED THE DYNAMIC OF THE MULTIPLICATION ARGUMENT
;; WHICH ACTUALLY BECAME MORE STRICT, SINCE MASKING IS LOGICALLY EQUIVALENT
;; TO FURTHER IMPLICIT OUTPUT CONSTRAINTS. THIS KIND OF PRE-EMPTIVE AND AGGRESSIVE
;; DIVISOR MASK ACTUALLY CONDITIONED DIVISION MORE THAN NECESSARY, THUS
;; ENFORCING THE NEED FOR CONSTRAINTS THAT WOULD OTHERWISE NOT BE REQUIRED
;; (SEE COMPLEXITY OF `quotientsignmask` in #4 VS SIMPLICITY OF `quotientsign` in #8)
;;
;; - AS FURTHER EXAMPLE AND CONCLUSION CONSIDER OUR OLD VERSION ROUNDING CONSTRAINT:
;; WHENEVER WE WOULD AUTOMATICALLY SIGN EXTEND QUOTIENT AND REMAINDER VARIABLES,
;; THE MULTIPLICATION WAS BY ITSELF NOT OPTINIONATED ENOUGH TO DISTINGUISH POSSIBLE
;; ROUNDING VARIANTS, AND SO FURTHER CONSTRAINTS WERE REQUIRED TO FIX THE REMAINDER'S 
;; SIGN AND ENFORCE ROUNDING-TOWARDS-ZERO DIVISION.
;; (SEE `(or (= (is_neg dividend) (is_neg remainder)) (= remainder #x00))` WHICH IS ABSENT IN #4 and #8)
;; FURTHERMORE, WE DISCOVERED THAT IT IS POSSIBLE TO SWAP THE OLD ROUNDING CONSTRAINT ON THE REMAINDER'S SIGN
;; FOR A MORE UNCONVENTIONAL (AND MORE EXPENSIVE) ROUNDING CONSTRAINT ON THE QUOTIENT'S SIGN
;; WHICH IMPLIES THAT THE SIGN OF THE QUOTIENT AND REMAINDER ARE NOT FREELY INDEPENDENT
;; BUT FURTHER INTERTWINED BY THE MULTIPLICATION THROUGH IMPLICIT CONSTRAINTS
;;
;; - THEREFORE, THIS OPTIMISATION REALISED THAT IT IS POSSIBLE TO SWAP OUR TRADITIONAL
;; ROUNDING AND MASKING CONSTRAINTS AND AUTOMATED QUOTIENT/REMAINDER SIGN EXTENSIONS
;; IN FAVOUR OF A MUCH CHEAPER MANUAL QUOTIENT/REMAINDER COMPUTATION, LETTING
;; OUR MULTIPLICATION CONSTRAINT TAKE CARE OF THE REST
;; (WE STILL MUST ENFORCE THE DIVISION-BY-ZERO CASE AS IT LEAVES QUOTIENT UNCONSTRAINED)


(define-fun is_neg ((x (_ BitVec 8))) Bool (= ((_ extract 7 7) x) #b1))
(define-fun neg ((x (_ BitVec 8))) (_ BitVec 8) (bvsub #x00 x))
(define-fun toext ((x (_ BitVec 8))) (_ BitVec 16) ((_ sign_extend 8) x))
(define-fun tomod ((x (_ BitVec 8))) (_ BitVec 16) ((_ zero_extend 8) (ite (is_neg x) (neg x) x)))

(declare-const dividend (_ BitVec 8))
(define-const dividendext (_ BitVec 16) (toext dividend))

(declare-const divisor (_ BitVec 8))
(define-const is_underflow Bool (and (= dividend #x80) (= divisor #xff)))
(define-const divisormod (_ BitVec 16) (tomod divisor))
(define-const divisorext (_ BitVec 16) (toext divisor))
(define-const divisorextmask (_ BitVec 16) (ite is_underflow #x0001 divisorext))

(declare-const quotient (_ BitVec 8))
(define-const quotientmod (_ BitVec 16) (tomod quotient))
(define-const quotientext (_ BitVec 16) (toext quotient))
(define-const quotientsignmask Bool (and (or (= divisor #x00) is_underflow (xor (is_neg dividend) (is_neg divisor))) (not (= quotient #x00))))
(define-const quotientsign Bool (and (xor (is_neg dividend) (is_neg divisor)) (not (= quotient #x00)) ))

(define-const dqmod (_ BitVec 16) (bvmul divisormod quotientmod))
(define-const dqsign Bool (xor (is_neg divisor) (is_neg quotient)))
(define-const dqneg (_ BitVec 16) (bvsub #x0000 dqmod))

(declare-const remainder (_ BitVec 8))
(define-const remaindermod (_ BitVec 16) (tomod remainder))
(define-const remaindersign Bool (and (is_neg dividend) (not (= remainder #x00))))
(define-const remainderext (_ BitVec 16) (toext remainder))

(define-const assumptions Bool (and
    true

    ;; special cases and testing
        ;; (not (and (= dividend #x80) (= divisor #xff)))
        ;; (not (= divisor #x00))
        ;; (= dividend #xf8)
        ;; (= divisor #x6c)
))

(define-const specification Bool (and
    (= quotient (ite (= divisor #x00) #xff
                (ite (and (= dividend #x80) (= divisor #xff)) #x80
                (bvsdiv dividend divisor) )))
    (= remainder (ite (= divisor #x00) dividend 
                (ite (and (= dividend #x80) (= divisor #xff)) #x00
                (bvsrem dividend divisor) )))
    
    ;; a bunch of constraints proven equivalent,
    ;; provided for the technical reader's interest
        ;; TYPICAL CONSTRAINTS
        ; constraint for expressing signed division as a multiplication+addition
        ; constraint for ensuring that the modulo of the remainder is always less than modulo of divisor
        ; constraint for ensuring rounding towards zero takes place
        ; constraint for handling edge cases (underflow, div-by-0)
        
        ;; MOCKUP MODULAR DIV PROVEN EQUIVALENT TO SPEC
        ;; (= (bvadd (ite (or is_underflow dqsign) dqneg dqmod) (concat (ite remaindersign #xff #x00) remainder)) ((_ sign_extend 8) dividend))
        ;; (or (= (is_neg dividend) (is_neg remainder)) (= remainder #x00))
        ;; (or (bvult remaindermod divisormod) (= divisor #x00))
        ;; ;; THEN THE MASKING!
        ;; (= quotient (ite (= divisor #x00) #xff quotient))
        
        ;; OUR OLD SIGNEXTENDED DIV PROVEN EQUIVALENT TO SPEC
        ;; (= (bvadd (bvmul divisorextmask quotientext) remainderext) dividendext)
        ;; (or (= (is_neg dividend) (is_neg remainder)) (= remainder #x00))
        ;; (or (bvult remaindermod divisormod) (= divisor #x00))
        ;; ;; MASK DIV-BY-0 QUOTIENT
        ;; (= quotient (ite (= divisor #x00) #xff quotient))
        
        ;; VARIANTS OF OUR SIGNEXTENDED DIV
        ;; OPTIMISED WITH VARYING DEGREES OF SIGN EXTENSION/COMPUTATION
        ;; 1-4 CONTAIN UNDERFLOW MASKED TO DIVISOR=1, 5-8 HAVE NO MASKING
        ;;
        ;;  1 - BOTH SIGNEXTENDED
        ;; (= (bvadd (bvmul divisorextmask ((_ sign_extend 8) quotient)) ((_ sign_extend 8) remainder)) dividendext)
        ;; (= (is_neg remainder) remaindersign) 
        ;; (or (bvult remaindermod divisormod) (= divisor #x00))
        ;; (= quotient (ite (= divisor #x00) #xff quotient))
        ;;
        ;;  2 - COMPUTE QUOTIENT EXTENSION
        ;; (= (bvadd (bvmul divisorextmask (concat (ite quotientsignmask #xff #x00) quotient)) ((_ sign_extend 8) remainder)) dividendext)
        ;; (= (is_neg remainder) remaindersign) 
        ;; (or (bvult remaindermod divisormod) (= divisor #x00))
        ;; (= quotient (ite (= divisor #x00) #xff quotient))
        ;;
        ;;  3a - COMPUTE REMAINDER EXTENSION (NORMAL ROUNDING CONSTRAINT)
        ;; (= (bvadd (bvmul divisorextmask ((_ sign_extend 8) quotient)) (concat (ite remaindersign #xff #x00) remainder)) dividendext)
        ;; (= (is_neg remainder) remaindersign) 
        ;; (or (bvult remaindermod divisormod) (= divisor #x00))
        ;; (= quotient (ite (= divisor #x00) #xff quotient))
        ;;
        ;;  3b - COMPUTE REMAINDER EXTENSION (DIFFERENT ROUNDING CONSTRAINT !!)
        ;; (= (bvadd (bvmul divisorextmask ((_ sign_extend 8) quotient)) (concat (ite remaindersign #xff #x00) remainder)) dividendext)
        ;; (= (is_neg quotient) quotientsignmask) 
        ;; (or (bvult remaindermod divisormod) (= divisor #x00))
        ;; (= quotient (ite (= divisor #x00) #xff quotient))
        ;;
        ;;  4 - COMPUTE BOTH QUOTIENT AND REMAINDER EXTENSION
        ;; (= (bvadd (bvmul divisorextmask (concat (ite quotientsignmask #xff #x00) quotient)) (concat (ite remaindersign #xff #x00) remainder)) dividendext)
        ;; (or (bvult remaindermod divisormod) (= divisor #x00))
        ;; (= quotient (ite (= divisor #x00) #xff quotient))
        ;;
        ;;
        ;; 5 - (BROKEN) BOTH SIGNEXTENDED
        ;; NOT PROVABLE FOR UNDERFLOW WITHOUT SOME FORM OF MASKING OF QUOTIENT/DIVIDEND SIGN OR DIVISOR !!
        ;; (= (bvadd (bvmul divisorext ((_ sign_extend 8) quotient)) ((_ sign_extend 8) remainder)) dividendext)
        ;; (= (is_neg remainder) remaindersign) 
        ;; (or (bvult remaindermod divisormod) (= divisor #x00))
        ;; (= quotient (ite (= divisor #x00) #xff quotient))
        ;;
        ;; 6 - COMPUTE QUOTIENT SIGN
        ;; (= (bvadd (bvmul divisorext (concat (ite quotientsign #xff #x00) quotient)) ((_ sign_extend 8) remainder)) dividendext)
        ;; (= (is_neg remainder) remaindersign) 
        ;; (or (bvult remaindermod divisormod) (= divisor #x00))
        ;; (= quotient (ite (= divisor #x00) #xff quotient))
        ;;
        ;; 7a - (BROKEN) COMPUTE REMAINDER SIGN (NORMAL ROUNDING CONSTRAINT)
        ;; NOT PROVABLE FOR UNDERFLOW WITHOUT SOME FORM OF MASKING OF QUOTIENT/DIVIDEND SIGN OR DIVISOR !!
        ;; (= (bvadd (bvmul divisorext ((_ sign_extend 8) quotient)) (concat (ite remaindersign #xff #x00) remainder)) dividendext)
        ;; (= (is_neg remainder) remaindersign) 
        ;; (or (bvult remaindermod divisormod) (= divisor #x00))
        ;; (= quotient (ite (= divisor #x00) #xff quotient))
        ;;
        ;; 7b - (BROKEN) COMPUTE REMAINDER SIGN (DIFFERENT ROUNDING CONSTRAINT !!)
        ;; NOT PROVABLE FOR UNDERFLOW WITHOUT SOME FORM OF MASKING OF QUOTIENT/DIVIDEND SIGN OR DIVISOR !!
        ;; (= (bvadd (bvmul divisorext ((_ sign_extend 8) quotient)) (concat (ite remaindersign #xff #x00) remainder)) dividendext)
        ;; (= (is_neg quotient) quotientsignmask) 
        ;; (or (bvult remaindermod divisormod) (= divisor #x00))
        ;; (= quotient (ite (= divisor #x00) #xff quotient))
        ;; 
        ;; 8 - COMPUTE BOTH SIGNS
        ;; (= (bvadd (bvmul divisorext (concat (ite quotientsign #xff #x00) quotient)) (concat (ite remaindersign #xff #x00) remainder)) dividendext)
        ;; (or (bvult remaindermod divisormod) (= divisor #x00))
        ;; (= quotient (ite (= divisor #x00) #xff quotient))
))

;; THE CONSTRAINTS CURRENTLY USED IN OUR CIRCUITS ARE FROM VERSION #8 DEFINED ABOVE
;; AND FOUND AGAIN HERE
(define-const constraints Bool (and
    ; constraint for expressing signed division as a multiplication+addition
    (= (bvadd (bvmul divisorext (concat (ite quotientsign #xff #x00) quotient)) (concat (ite remaindersign #xff #x00) remainder)) dividendext)
    
    ; constraint for ensuring rounding towards zero takes place
    ; (is_neg remainder) -> automatically in the remaindersign mask
    ; (is_neg quotient) -> automatically in the quotientsign mask
    ; explicit constraints no longer needed!
    ;(= (is_neg remainder) remaindersign) 
    ;(= (is_neg quotient) quotientsignmask) 
    ;(= (is_neg quotient) quotientsign) 
    
    ; constraint for ensuring that the modulo of the remainder is always less than modulo of divisor
    (or (bvult remaindermod divisormod) (= divisor #x00))
    
    ; constraint for handling edge cases (underflow, div-by-0)
    (= quotient (ite (= divisor #x00) #xff quotient))
))







;; THIS PART OF THE SOLVER SCRIPT ACTUALLY PROVES OUR CONSTRAINTS
;; IF Z3 OUTPUTS UNSAT, THAT IMPLIES IT WAS NOT ABLE TO PRODUCE
;; A SATISFYING MODEL THAT WOULD INVALIDATE OUR IFF. CONDITION
;; BETWEEN SPECIFICATION AND CONSTRAINTS. IF IT CANNOT FIND
;; SUCH A MODEL, THAT MEANS OUR REDUCTION IS FULLY SOUND
(assert assumptions)
(assert (not (= constraints specification))) ;; if and only if
(check-sat)

;; DEBUGGING
;; PRETTY PRINT much better than (get-model)
(define-fun i8 ((x (_ BitVec 8))) Int (ite (= ((_ extract 7 7) x) #b1) (- (bv2nat x) 256) (bv2nat x)))
(define-fun i16 ((x (_ BitVec 16))) Int (ite (= ((_ extract 15 15) x) #b1) (- (bv2nat x) 65536) (bv2nat x)))
(get-value ( 
    dividend (i8 dividend)  divisor (i8 divisor)  
    "---------------"
    (bvsdiv dividend divisor) (i8 (bvsdiv dividend divisor)) (bvsrem dividend divisor) (i8 (bvsrem dividend divisor)) 
    "---------------"
    quotient (i8 quotient) remainder (i8 remainder)
    "---------------"
    specification
    constraints
    "1"
    (= (bvadd (bvmul divisorextmask ((_ sign_extend 8) quotient)) ((_ sign_extend 8) remainder)) dividendext)
    (= (is_neg remainder) remaindersign) 
    "2"
    (= (bvadd (bvmul divisorextmask (concat (ite quotientsignmask #xff #x00) quotient)) ((_ sign_extend 8) remainder)) dividendext)
    (= (is_neg remainder) remaindersign) 
    "3a"
    (= (bvadd (bvmul divisorextmask ((_ sign_extend 8) quotient)) (concat (ite remaindersign #xff #x00) remainder)) dividendext)
    (= (is_neg remainder) remaindersign) 
    "3b"
    (= (bvadd (bvmul divisorextmask ((_ sign_extend 8) quotient)) (concat (ite remaindersign #xff #x00) remainder)) dividendext)
    (= (is_neg quotient) quotientsignmask) 
    "4"
    (= (bvadd (bvmul divisorextmask (concat (ite quotientsignmask #xff #x00) quotient)) (concat (ite remaindersign #xff #x00) remainder)) dividendext)
    "5 fake prophet"
    (= (bvadd (bvmul divisorext ((_ sign_extend 8) quotient)) ((_ sign_extend 8) remainder)) dividendext)
    "6"
    (= (bvadd (bvmul divisorext (concat (ite quotientsign #xff #x00) quotient)) ((_ sign_extend 8) remainder)) dividendext)
    "7"
    (= (bvadd (bvmul divisorext ((_ sign_extend 8) quotient)) (concat (ite remaindersign #xff #x00) remainder)) dividendext)
    divisorext
    "8"
    (= (bvadd (bvmul divisorext (concat (ite quotientsign #xff #x00) quotient)) (concat (ite remaindersign #xff #x00) remainder)) dividendext)
    divisorext
    (concat (ite quotientsign #xff #x00) quotient)
    (bvmul divisorext (concat (ite quotientsign #xff #x00) quotient))
    (concat (ite remaindersign #xff #x00) remainder)
    (bvadd (bvmul divisorext (concat (ite quotientsign #xff #x00) quotient)) (concat (ite remaindersign #xff #x00) remainder))
    dividendext
    "common"
    (or (bvult remaindermod divisormod) (= divisor #x00))
    (= quotient (ite (= divisor #x00) #xff quotient))
    (= (is_neg remainder) remaindersign) 
    (= (is_neg quotient) quotientsignmask) 
    (= (is_neg quotient) quotientsign) 
))