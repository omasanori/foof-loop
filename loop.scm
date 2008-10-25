;;; -*- Mode: Scheme -*-

;;;; Extensible Looping Macros, version 2

;;; This code is written by Taylor R. Campbell and placed in the Public
;;; Domain.  All warranties are disclaimed.

;;; This is a variation on Alex Shinn's looping macros described in
;;; message-id <1157562097.001179.11470@i42g2000cwa.googlegroups.com>.
;;; There are several differences:
;;;
;;;   (FOR variable ... (iterator argument ...))
;;;     instead of (variable ... <- iterator argument ...).
;;;   (=> variable update) instead of (variable <- update).
;;;   (LET variable initializer [stepper])
;;;     instead of (variable initializer [stepper]).
;;;   COLLECTING has support for conditional collection; see its page.
;;;   IN-LIST has an optional successor argument; CDR is the default.
;;;   IN-STRING-REVERSE is added to the set of vector-like iterators.
;;;   IN-RANGE's arguments are named, and extended; see its page.
;;;
;;; This file depends on sys-param.scm, also by Taylor R. Campbell, and
;;; SRFI 11 (LET-VALUES).

(define-syntax loop
  (syntax-rules ()
    ((LOOP ((loop-clause0 loop-clause1 ...) ...)
       body
       ...)
     (LOOP ANONYMOUS-LOOP ((loop-clause0 loop-clause1 ...) ...)
       body
       ...
       (ANONYMOUS-LOOP)))

    ((LOOP name ((loop-clause0 loop-clause1 ...) ...) body ...)
     (%LOOP START name ((loop-clause0 loop-clause1 ...) ...) (body ...)))))

;;; Use this definition of SYNTAX-ERROR if your favourite Scheme
;;; doesn't have one already.

;; (define-syntax syntax-error (syntax-rules ()))

(define-syntax %loop
  (syntax-rules (=> FOR LET START GO PARSE-FOR CONTINUE FINISH)

    ((%LOOP START name loop-clauses body)
     (%LOOP GO name (() () () () () ()) loop-clauses body))

    ;; Simple case of a single variable, for clarity.
    ((%LOOP GO name state
            ((FOR variable (looper argument ...))
             . loop-clauses)
            body)
     (looper (variable) (argument ...)
             %LOOP CONTINUE name state loop-clauses body))

    ;; FOR handler with tail patterns.  Unfortunately, tail patterns are non-
    ;; standard...
    ;; 
    ;; ((%LOOP GO name state
    ;;         ((FOR variable0 variable1 ... (looper argument ...))
    ;;          . loop-clauses)
    ;;         body)
    ;;  (looper (variable0 variable1 ...)
    ;;          (argument ...)
    ;;          %LOOP CONTINUE name state loop-clauses body))

    ((%LOOP GO name state
            ((FOR variable0 variable1 variable2 ...) . loop-clauses)
            body)
     (%LOOP PARSE-FOR (variable0 variable1 variable2 ...)
            ()
            name state loop-clauses body))

    ((%LOOP PARSE-FOR ((looper argument ...))
            variables
            name state loop-clauses body)
     (looper variables (argument ...)
             %LOOP CONTINUE name state loop-clauses body))

    ((%LOOP PARSE-FOR (next-variable more0 more1 ...)
            (variable ...)
            name state loop-clauses body)
     (%LOOP PARSE-FOR (more0 more1 ...)
            (variable ... next-variable)
            name state loop-clauses body))

    ((%LOOP PARSE-FOR (non-list)
            variables
            clause
            name state loop-clauses body)
     (SYNTAX-ERROR "Malformed FOR clause in LOOP:" 'clause))

    ((%LOOP ((outer-bvl outer-producer) ...)
            ((loop-variable loop-initializer loop-stepper) ...)
            ((entry-bvl entry-producer) ...)
            (termination-condition ...)
            ((body-bvl body-producer) ...)
            ((final-bvl final-producer) ...)
            CONTINUE
            name
            (outer-bindings
             loop-variables
             entry-bindings
             termination-conditions
             body-bindings
             final-bindings)
            loop-clauses
            body)
     (%LOOP GO name
            (((outer-bvl outer-producer) ... . outer-bindings)
             ((loop-variable loop-initializer loop-stepper) ...
              . loop-variables)
             ((entry-bvl entry-producer) ... . entry-bindings)
             (termination-condition ... . termination-conditions)
             ((body-bvl body-producer) ... . body-bindings)
             ((final-bvl final-producer) ... . final-bindings))
            loop-clauses
            body))

    ((%LOOP GO name state
            ((LET variable initializer) . loop-clauses)
            body)
     (%LOOP GO name state
            ((LET variable initializer variable) . loop-clauses)
            body))

    ((%LOOP GO name
            (outer-bindings (loop-variable ...) . more-state)
            ((LET variable initializer stepper) . loop-clauses)
            body)
     (%LOOP GO name
            (outer-bindings
             ;; Preserve ordering of the user's loop variables.
             (loop-variable ... (variable initializer stepper))
             . more-state)
            loop-clauses
            body))

    ((%LOOP GO name state (clause . loop-clauses) body)
     (SYNTAX-ERROR "Malformed LOOP clause:" 'clause))

    ((%LOOP GO name state () (=> result-form . body))
     (%LOOP FINISH name state result-form body))

    ((%LOOP GO name state () body)
     (%LOOP FINISH name state (IF #F #F) body))

    ((%LOOP FINISH name
            (((outer-bvl outer-producer) ...)
             ((loop-variable loop-initializer loop-stepper) ...)
             ((entry-bvl entry-producer) ...)
             (termination-condition ...)
             ((body-bvl body-producer) ...)
             ((final-bvl final-producer) ...))
            result-form
            body)
     (LET-VALUES ((outer-bvl outer-producer) ...)
       (DEFINE (LOOP-PROCEDURE loop-variable ...)
         (LET-VALUES ((entry-bvl entry-producer) ...)
           (IF (OR termination-condition ...)
               (LET-VALUES ((final-bvl final-producer) ...)
                 (WITH-EXTENDED-PARAMETER-OPERATORS
                     ((name
                       (LOOP-PROCEDURE (loop-variable . loop-stepper)
                                       ...)))
                   result-form))
               (LET-VALUES ((body-bvl body-producer) ...)
                 (WITH-EXTENDED-PARAMETER-OPERATORS
                     ((name
                       (LOOP-PROCEDURE (loop-variable . loop-stepper)
                                       ...)))
                   . body)))))
       (LOOP-PROCEDURE loop-initializer ...)))))

;;;; Collectors

;;; (FOR <list> (COLLECTING <generator>))
;;; (FOR <list> (COLLECTING <generator> (IF <condition>)))
;;; (FOR <list> (COLLECTING <generator> => <mapper>))           ;COND-style
;;; (FOR <list> (COLLECTING <generator> <tester> => <mapper))   ;SRFI-61-style

(define-syntax collecting
  (syntax-rules (IF =>)
    ((COLLECTING (list-variable) (generator) next . rest)
     (next ()                           ;Outer bindings
           ((ACCUMULATOR '()            ;Loop variables
                         (CONS generator ACCUMULATOR)))
           ()                           ;Entry bindings
           ()                           ;Termination conditions
           ()                           ;Body bindings
           (((list-variable)            ;Final bindings
             (REVERSE ACCUMULATOR)))
           . rest))

    ((COLLECTING (list-variable) (generator (IF condition)) next . rest)
     (next ()                           ;Outer bindings
           ((ACCUMULATOR '()            ;Loop variables
                         (IF condition
                             (CONS generator ACCUMULATOR)
                             ACCUMULATOR)))
           ()                           ;Entry bindings
           ()                           ;Termination conditions
           ()                           ;Body bindings
           (((list-variable)            ;Final bindings
             (REVERSE ACCUMULATOR)))
           . rest))

    ((COLLECTING (list-variable) (generator => mapper) next . rest)
     (next (((MAP) mapper))             ;Outer bindings
           ((ACCUMULATOR '()            ;Loop variables
                         (COND (generator
                                => (LAMBDA (DATUM)
                                     (CONS (MAP DATUM) ACCUMULATOR)))
                               (ELSE ACCUMULATOR))))
           ()                           ;Entry bindings
           ()                           ;Termination conditions
           ()                           ;Body bindings
           (((list-variable)            ;Final bindings
             (REVERSE ACCUMULATOR)))
           . rest))

    ((COLLECTING (list-variable) (generator tester => mapper) next . rest)
     (next (((TEST) tester)             ;Outer bindings
            ((MAP) mapper))
           ((ACCUMULATOR '()            ;Loop variables
                         (RECEIVE ARGS generator
                           (IF (APPLY TEST ARGS)
                               (CONS (APPLY MAP ARGS) ACCUMULATOR)
                               ACCUMULATOR))))
           ()                           ;Entry bindings
           ()                           ;Termination conditions
           ()                           ;Body bindings
           (((list-variable)            ;Final bindings
             (REVERSE accumulator)))
           . rest))

    ((COLLECTING (variable ...) arguments next . rest)
     (SYNTAX-ERROR "Malformed COLLECTING clause in LOOP:"
                   '(FOR variable ... (COLLECTING . arguments))))))

;;;; List Iteration

;;; (FOR <elt> [<pair>] (IN-LIST <list> [<successor>]))
;;;   Step across <list>, letting <pair> be each successive pair in
;;;   <list>, stepping by (<successor> <pair>), or (CDR <pair>) if no
;;;   successor procedure is explicitly provided.  Let <elt> be the car
;;;   of <pair> in the body of the loop.

(define-syntax in-list
  (syntax-rules ()
    ((IN-LIST (element-variable pair-variable) (list-expression successor)
              next . rest)
     (next (((LIST) list-expression))             ;Outer bindings
           ((pair-variable LIST                   ;Loop variables
                           (successor pair-variable)))
           ()                                     ;Entry bindings
           ((NOT (PAIR? pair-variable)))          ;Termination conditions
           (((element-variable)                   ;Body bindings
             (CAR pair-variable)))
           ()                                     ;Final bindings
           . rest))

    ((IN-LIST (element-variable pair-variable) (list-expression) next . rest)
     (IN-LIST (element-variable pair-variable) (list-expression CDR)
              next . rest))

    ((IN-LIST (element-variable) (list-expression successor) next . rest)
     (IN-LIST (element-variable PAIR) (list-expression successor) next . rest))

    ((IN-LIST (element-variable) (list-expression) next . rest)
     (IN-LIST (element-variable PAIR) (list-expression CDR) next . rest))

    ((IN-LIST (variable ...) arguments next . rest)
     (SYNTAX-ERROR "Malformed IN-LIST clause in LOOP:"
                   '(FOR variable ... (IN-LIST . arguments))))))

(define-syntax in-lists
  (syntax-rules ()
    ((IN-LISTS (elements-variable pairs-variable) (lists-expression)
               next . rest)
     (next (((LISTS) lists-expression))   ;Outer bindings
           ((pairs-variable LISTS CDRS))  ;Loop variables
           (((LOSE? CARS CDRS)            ;Entry bindings
             (%CARS&CDRS pairs-variable)))
           (LOSE?)                        ;Termination conditions
           (((elements-variable) CARS))   ;Body bindings
           ()                             ;Final bindings
           . rest))

    ((IN-LISTS (elements-variable) (lists) next . rest)
     (IN-LISTS (elements-variable PAIRS) (lists) next . rest))

    ((IN-LISTS (variable ...) arguments next . rest)
     (SYNTAX-ERROR "Malformed IN-LISTS clause in LOOP:"
                   '(FOR variable ... (IN-LIST . arguments))))))

(define (%cars&cdrs lists)
  (loop proceed ((for list (in-list lists))
                 (for cars (collecting (car list)))
                 (for cdrs (collecting (cdr list))))
    => (values #f cars cdrs)
    (if (pair? list)
        (proceed)
        (values #t #f #f))))

;;;; Vector and String Iteration

;;; (FOR <elt> [<index>] (IN-VECTOR <vector> [<start> [<end>]]))
;;;
;;; IN-VECTOR-REVERSE, IN-STRING, and IN-STRING-REVERSE all have the
;;; same syntax.
;;;
;;; The reverse iterators run from end to start; the bounds are still
;;; given in the same order as the forward iterators.

;++ These have the aesthetically displeasing property that the index
;++ variable is bound in the final expression to a bogus value (equal
;++ to the end bound).  Also, the reverse iterators will yield
;++ intermediate negative numbers.

(define-syntax in-vector
  (syntax-rules ()
    ((IN-VECTOR user-variables (vector-expression start/end ...) next . rest)
     (%IN-VECTOR (VECTOR 0 (VECTOR-LENGTH VECTOR))
                 (VECTOR-REF >= +)
                 (IN-VECTOR
                  "Malformed IN-VECTOR clause in LOOP:")
                 user-variables (vector-expression start/end ...)
                 user-variables (vector-expression start/end ...)
                 next . rest))))

(define-syntax in-vector-reverse
  (syntax-rules ()
    ((IN-VECTOR-REVERSE user-variables (vector-expression start/end ...)
                        next . rest)
     (%IN-VECTOR (VECTOR (- (VECTOR-LENGTH VECTOR) 1) 0)
                 (VECTOR-REF < -)
                 (IN-VECTOR-REVERSE
                  "Malformed IN-VECTOR-REVERSE clause in LOOP:")
                 user-variables (vector-expression start/end ...)
                 user-variables (vector-expression start/end ...)
                 next . rest))))

(define-syntax in-string
  (syntax-rules ()
    ((IN-STRING user-variables (vector-expression start/end ...) next . rest)
     (%IN-VECTOR (STRING 0 (STRING-LENGTH STRING))
                 (STRING-REF >= +)
                 (IN-STRING
                  "Malformed IN-STRING clause in LOOP:")
                 user-variables (vector-expression start/end ...)
                 user-variables (vector-expression start/end ...)
                 next . rest))))

(define-syntax in-string-reverse
  (syntax-rules ()
    ((IN-STRING-REVERSE user-variables (string-expression start/end ...)
                        next . rest)
     (%IN-VECTOR (STRING (- (STRING-LENGTH STRING) 1) 0)
                 (STRING-REF < -)
                 (IN-STRING-REVERSE
                  "Malformed IN-STRING-REVERSE clause in LOOP:")
                 user-variables (string-expression start/end ...)
                 user-variables (string-expression start/end ...)
                 next . rest))))

;;;;; Random-Access Sequence Generalization

(define-syntax %in-vector
  (syntax-rules ()
    ((%IN-VECTOR (vector-variable default-start default-end)
                 (vector-ref finished? step)
                 error-context
                 (element-variable index-variable)
                 (vector-expression start-expression end-expression)
                 original-variables original-arguments
                 next . rest)
     (next (((vector-variable START END)          ;Outer bindings
             (LET ((vector-variable vector-expression))
               (VALUES vector-variable start-expression end-expression))))
           ((index-variable START                 ;Loop variables
                            (step index-variable 1)))
           ()                                     ;Entry bindings
           ((finished? index-variable END))       ;Termination conditions
           (((element-variable)                   ;Body bindings
             (vector-ref vector-variable index-variable)))
           ()                                     ;Final bindings
           . rest))

    ;; Supply an index variable if absent.
    ((%IN-VECTOR default-values iteration-parameters error-context
                 (element-variable)
                 arguments
                 original-variables original-arguments
                 next . rest)
     (%IN-VECTOR default-values iteration-parameters error-context
                 (element-variable INDEX)
                 arguments
                 original-variables original-arguments
                 next . rest))

    ;; Supply the default start index if necessary.
    ((%IN-VECTOR (vector-variable default-start default-end)
                 iteration-parameters error-context user-variables
                 (vector-expression)
                 original-variables original-arguments
                 next . rest)
     (%IN-VECTOR (vector-variable default-start default-end)
                 iteration-parameters error-context user-variables
                 (vector-expression default-start)
                 original-variables original-arguments
                 next . rest))

    ;; Supply the default end index if necessary.
    ((%IN-VECTOR (vector-variable default-start default-end)
                 iteration-parameters error-context user-variables
                 (vector-expression start-expression)
                 original-variables original-arguments
                 next . rest)
     (%IN-VECTOR (vector-variable default-start default-end)
                 iteration-parameters error-context user-variables
                 (vector-expression start-expression default-end)
                 original-variables original-arguments
                 next . rest))

    ((%IN-VECTOR default-arguments iteration-parameters
                 (macro error-message)
                 modified-variables modified-arguments
                 (variable ...) arguments
                 next . rest)
     (SYNTAX-ERROR error-message '(FOR variable ... (macro . arguments))))))

;;;; Input

;;; (FOR <item> (IN-PORT <input-port> [<reader> [<eof?>]]))
;;;
;;; IN-FILE has the same syntax, but with a pathname in the place of
;;; the input port.

(define-syntax in-port
  (syntax-rules ()
    ((IN-PORT (datum-variable)
              (port-expression reader-expression eof-predicate)
              next . rest)
     (next (((PORT) port-expression)              ;Outer bindings
            ((READER) reader-expression)
            ((EOF?) eof-predicate))
           ()                                     ;Loop variables
           (((datum-variable) (READER PORT)))     ;Entry bindings
           ((EOF? datum-variable))                ;Termination conditions
           ()                                     ;Body bindings
           ()                                     ;Final bindings
           . rest))

    ;; Supply a reader if absent.
    ((IN-PORT (datum-variable) (port-expression) next . rest)
     (IN-PORT (datum-variable) (port-expression READ-CHAR) next . rest))

    ;; Supply an EOF predicate if absent.
    ((IN-PORT (datum-variable) (port-expression reader-expression) next . rest)
     (IN-PORT (datum-variable) (port-expression reader-expression EOF-OBJECT?)
              next . rest))

    ((IN-PORT (variable ...) arguments next . rest)
     (SYNTAX-ERROR "Malformed IN-PORT clause in LOOP:"
                   '(FOR variable ... (IN-FILE . arguments))))))

(define-syntax in-file
  (syntax-rules ()
    ((IN-FILE (datum-variable)
              (pathname-expression reader-expression eof-predicate)
              next . rest)
     (next (((PORT)                               ;Outer bindings
             (OPEN-INPUT-FILE pathname-expression))
            ((READER) reader-expression)
            ((EOF?) eof-predicate))
           ()                                     ;Loop variables
           (((datum-variable) (READER PORT)))     ;Entry bindings
           ((EOF? datum-variable))                ;Termination conditions
           ()                                     ;Body bindings
           ((()                                   ;Final bindings
             (BEGIN (CLOSE-INPUT-PORT PORT)
                    (VALUES))))
           . rest))

    ;; Supply a reader if absent.
    ((IN-FILE (datum-variable) (pathname-expression) next . rest)
     (IN-FILE (datum-variable) (pathname-expression READ-CHAR) next . rest))

    ;; Supply an EOF predicate if absent.
    ((IN-FILE (datum-variable) (pathname-expression reader) next . rest)
     (IN-FILE (datum-variable) (pathname-expression reader EOF-OBJECT?)
              next . rest))

    ((IN-FILE (variable ...) arguments next . rest)
     (SYNTAX-ERROR "Malformed IN-FILE clause in LOOP:"
                   '(FOR variable ... (IN-FILE . arguments))))))

;;;; Number Ranges

;;; (FOR <number>
;;;   (IN-RANGE [(FROM <start>)]
;;;             [({UP-TO | DOWN-TO} <end>)]
;;;             [(BY <step>)]))

;;; Because I am too lazy to do this properly, one must supply FROM,
;;; UP-TO / DOWN-TO, and BY in that order.  UP-TO or DOWN-TO is
;;; required; the others are optional.

(define-syntax in-range
  (syntax-rules (FROM UP-TO DOWN-TO BY)
    ((IN-RANGE (variable) ((FROM start-expression)
                           (UP-TO end-expression)
                           (BY step-expression))
               next . rest)
     (%IN-RANGE variable + >=
                start-expression end-expression step-expression
                next . rest))

    ((IN-RANGE (variable) ((FROM start-expression)
                           (DOWN-TO end-expression)
                           (BY step-expression))
               next . rest)
     (%IN-RANGE variable - <=
                start-expression end-expression step-expression
                next . rest))

    ;; Supply a default value of 1 for the step if absent.
    ((IN-RANGE (variable) ((FROM start-expression) (to end-expression))
               next . rest)
     (IN-RANGE (variable) ((FROM start-expression) (to end-expression) (BY 1))
               next . rest))

    ;; Supply a default value of 0 for the start if absent.
    ((IN-RANGE (variable) ((to end-expression) (BY step-expression))
               next . rest)
     (IN-RANGE (variable) ((FROM 0) (to end-expression) (BY step-expression))
               next . rest))

    ;; Supply default values for both start and step if both are absent.
    ((IN-RANGE (variable) ((to end-expression)) next . rest)
     (IN-RANGE (variable) ((FROM 0) (to end-expression) (BY 1)) next . rest))

    ((IN-RANGE (variable ...) arguments next . rest)
     (SYNTAX-ERROR "Malformed IN-RANGE clause in LOOP:"
                   '(FOR variable ... (IN-RANGE . arguments))))))

(define-syntax %in-range
  (syntax-rules ()
    ((%IN-RANGE variable stepper tester
                start-expression end-expression step-expression
                next . rest)
     (next (((START) start-expression)  ;Outer bindings
            ((END) end-expression)
            ((STEP) step-expression))
           ((variable START             ;Loop bindings
                      (stepper variable STEP)))
           ()                           ;Entry bindings
           ((tester variable end))      ;Termination conditions
           ()                           ;Body bindings
           ()                           ;Final bindings
           . rest))))
