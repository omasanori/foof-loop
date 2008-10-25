;;; -*- Mode: Scheme -*-

;;;; Extensible Looping Macros, version 5

;;; This code is written by Taylor R. Campbell and placed in the Public
;;; Domain.  All warranties are disclaimed.

;;; This is a variation on Alex Shinn's looping macros described in
;;; message-id <1157562097.001179.11470@i42g2000cwa.googlegroups.com>.
;;; There are a number of differences; among the most notable are
;;; - that the syntax for passing named arguments to the loop
;;;   dispatcher is `(=> name value)' rather than `name <- value';
;;; - that COLLECTING has been renamed LISTING, and there are many
;;;   other new accumulator macros as well, with extensions for initial
;;;   values and conditional accumulation;
;;; - that the parameters to IN-RANGE are now all named, with an option
;;;   of UP-TO or DOWN-TO to specify the direction of the range; and
;;; - that there are three new iterators: IN-LISTS, IN-NUMBERS, and
;;;   IN-STRINGS-REVERSE.
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

;;; Use this definition of SYNTACTIC-ERROR if your favourite Scheme
;;; doesn't have one already.  Note that this is distinct from a
;;; SYNTAX-ERROR procedure, since it must signal a compile-time error.
;;;
;;;   (define-syntax syntactic-error (syntax-rules ()))

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
            (FOR variable0 variable1 variable2 ...)   ;Copy for error message.
            name state loop-clauses body))

    ((%LOOP PARSE-FOR ((looper argument ...))
            variables
            original-clause name state loop-clauses body)
     (looper variables (argument ...)
             %LOOP CONTINUE name state loop-clauses body))

    ((%LOOP PARSE-FOR (next-variable more0 more1 ...)
            (variable ...)
            original-clause name state loop-clauses body)
     (%LOOP PARSE-FOR (more0 more1 ...)
            (variable ... next-variable)
            original-clause name state loop-clauses body))

    ((%LOOP PARSE-FOR (non-list)
            variables
            original-clause name state loop-clauses body)
     (SYNTACTIC-ERROR "Malformed FOR clause in LOOP:" original-clause))

    ((%LOOP ((outer-bvl outer-producer) ...)
            ((loop-variable loop-initializer loop-stepper) ...)
            ((entry-bvl entry-producer) ...)
            (termination-condition ...)
            ((body-bvl body-producer) ...)
            ((final-bvl final-producer) ...)
            CONTINUE
            name
            (outer-bindings
             (loop-variables ...)
             entry-bindings
             termination-conditions
             body-bindings
             final-bindings)
            loop-clauses
            body)
     (%LOOP GO name
            (((outer-bvl outer-producer) ... . outer-bindings)
             ;; Preserve the order of loop variables, so that the user
             ;; can put hers first and still use positional arguments.
             (loop-variables ...
                             (loop-variable loop-initializer loop-stepper) ...)
             ((entry-bvl entry-producer) ... . entry-bindings)
             (termination-condition ... . termination-conditions)
             ((body-bvl body-producer) ... . body-bindings)
             ((final-bvl final-producer) ... . final-bindings))
            loop-clauses
            body))

    ((%LOOP GO name state ((variable initializer) . loop-clauses) body)
     (%LOOP GO name state ((LET variable initializer) . loop-clauses) body))

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
     (SYNTACTIC-ERROR "Malformed LOOP clause:" clause))

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

;;;; Accumulators

;;; Accumulators have the following syntax:
;;;
;;;   (FOR <result> (ACCUMULATING <generator>))
;;;   (FOR <result> (ACCUMULATING <generator> (IF <condition>)))
;;;   (FOR <result> (ACCUMULATING <generator> => <mapper>))    ;COND-style
;;;   (FOR <result> (ACCUMULATING <generator> <tester>         ;SRFI-61-style
;;;                               => <mapper>))
;;;
;;; In addition, some of them support initial values, which are
;;; specified with an optional first argument of (INITIAL <initial
;;; value>).  For example, to accumulate a list starting with some tail
;;; <tail>, write
;;;
;;;   (FOR <result-list> (LISTING (INITIAL <tail>) <element>)).

(define-syntax listing
  (syntax-rules (INITIAL)
    ((LISTING variables ((INITIAL tail-expression) . arguments) next . rest)
     (%ACCUMULATING variables arguments (((TAIL) tail-expression))
                    ('() CONS (LAMBDA (RESULT)
                                (APPEND-REVERSE RESULT TAIL)))
                    (LISTING variables
                             ((INITIAL tail-expression) . arguments)
                             "Malformed LISTING clause in LOOP:")
                    next . rest))

    ((LISTING variables arguments next . rest)
     (%ACCUMULATING variables arguments ()
                    ('() CONS REVERSE)
                    (LISTING variables arguments
                             "Malformed LISTING clause in LOOP:")
                    next . rest))))

(define-syntax listing-reverse
  (syntax-rules (INITIAL)
    ((LISTING-REVERSE variables ((INITIAL tail-expression) . arguments)
                      next . rest)
     (%ACCUMULATING variables arguments (((TAIL) tail-expression))
                    (TAIL CONS)
                    (LISTING-REVERSE
                     variables ((INITIAL tail-expression) . arguments)
                     "Malformed LISTING-REVERSE clause in LOOP:")
                    next . rest))

    ((LISTING-REVERSE variables arguments next . rest)
     (%ACCUMULATING variables arguments ()
                    ('() CONS)
                    (LISTING-REVERSE
                     variables arguments
                     "Malformed LISTING-REVERSE clause in LOOP:")
                    next . rest))))

;;; This is non-reentrant but produces precisely one garbage cons cell.

(define-syntax listing!
  (syntax-rules ()
    ((LISTING! variables arguments next . rest)
     (%LISTING! variables arguments (CONS #F '())
                (LISTING! variables arguments
                          "Malformed LISTING clause in LOOP:")
                next . rest))))

(define-syntax listing-into!
  (syntax-rules ()
    ((LISTING-INTO! variables (first-expression . arguments) next . rest)
     (%LISTING! variables arguments first-expression
                (LISTING-INTO! variables
                               (first-expression . arguments)
                               "Malformed LISTING-INTO! clause in LOOP:")
                next . rest))))

(define-syntax %listing!
  (syntax-rules (INITIAL)
    ((%LISTING! variables ((INITIAL tail-expression) . arguments)
                first-expression
                error-context
                next . rest)
     (%ACCUMULATING variables arguments
                    (((FIRST TAIL)
                      (LET ((FIRST first-expression)
                            (TAIL tail-expression))
                        (SET-CDR! FIRST TAIL)
                        (VALUES FIRST TAIL))))
                    (FIRST (LAMBDA (DATUM PREVIOUS-CELL)
                             (LET ((NEXT-CELL (CONS DATUM TAIL)))
                               (SET-CDR! PREVIOUS-CELL NEXT-CELL)
                               NEXT-CELL))
                           (LAMBDA (CELL) CELL (CDR FIRST)))
                    error-context
                    next . rest))

    ((%LISTING! variables arguments first-expression error-context next . rest)
     (%LISTING! variables ((INITIAL '()) . arguments)
                first-expression
                error-context
                next . rest))))

;;;;; List Appending Accumulators

(define-syntax appending
  (syntax-rules (INITIAL)
    ((APPENDING variables ((INITIAL tail-expression) . arguments)
                next . rest)
     (%ACCUMULATING variables arguments (((TAIL) tail-expression))
                    ('() APPEND-REVERSE (LAMBDA (RESULT)
                                          (APPEND-REVERSE RESULT TAIL)))
                    (APPENDING variables
                               ((INITIAL tail-expression) . arguments)
                               "Malformed APPENDING clause in LOOP:")
                    next . rest))

    ((APPENDING variables arguments next . rest)
     (%ACCUMULATING variables arguments ()
                    ('() APPEND-REVERSE REVERSE)
                    (APPENDING variables arguments
                               "Malformed APPENDING clause in LOOP:")
                    next . rest))))

(define-syntax appending-reverse
  (syntax-rules (INITIAL)
    ((APPENDING-REVERSE variables ((INITIAL tail-expression) . arguments)
                        next . rest)
     (%ACCUMULATING variables arguments (((TAIL) tail-expression))
                    (TAIL APPEND-REVERSE)
                    (APPENDING-REVERSE
                     variables ((INITIAL tail-expression) . arguments)
                     "Malformed APPENDING-REVERSE clause in LOOP:")
                    next . rest))

    ((APPENDING-REVERSE variables arguments next . rest)
     (%ACCUMULATING variables arguments ()
                    ('() APPEND-REVERSE)
                    (APPENDING-REVERSE
                     variables arguments
                     "Malformed APPENDING-REVERSE clause in LOOP:")
                    next . rest))))

;; (define (append-reverse list tail)
;;   (loop ((FOR elt (IN-LIST list))
;;          (FOR result (LISTING-REVERSE (INITIAL tail) elt)))
;;     => result))

(define (append-reverse list tail)
  (if (pair? list)
      (append-reverse (cdr list) (cons (car list) tail))
      tail))

;;;;; Numerical Accumulators

;;; MULTIPLYING and SUMMING have no INITIAL parameter because you can
;;; just tack it on after the fact, which is not the case of most other
;;; accumulators.

(define-syntax summing
  (syntax-rules ()
    ((SUMMING variables arguments next . rest)
     (%ACCUMULATING variables arguments ()
                    (0 +)
                    (SUMMING variables arguments
                             "Malformed SUMMING clause in LOOP:")
                    next . rest))))

(define-syntax multiplying
  (syntax-rules ()
    ((MULTIPLYING variables arguments next . rest)
     (%ACCUMULATING variables arguments ()
                    (1 *)
                    (MULTIPLYING variables arguments
                                 "Malformed MULTIPLYING clause in LOOP:")
                    next . rest))))

(define-syntax maximizing
  (syntax-rules ()
    ((MAXIMIZING variables arguments next . rest)
     (%EXTREMIZING variables arguments MAX
                   (MAXIMIZING "Malformed MAXIMIZING clause in LOOP:")
                   next . rest))))

(define-syntax minimizing
  (syntax-rules ()
    ((MINIMIZING variables arguments next . rest)
     (%EXTREMIZING variables arguments MIN
                   (MINIMIZING "Malformed MINIMIZING clause in LOOP:")
                   next . rest))))

(define-syntax %extremizing
  (syntax-rules (INITIAL)
    ((%EXTREMIZING variables ((INITIAL init-expression) . arguments)
                   chooser
                   (macro message)
                   next . rest)
     (%ACCUMULATING variables arguments (((INIT) init-expression))
                    (INIT chooser)
                    (macro variables ((INITIAL init-expression) . arguments)
                           message)
                    next . rest))

    ((%EXTREMIZING variables arguments chooser (macro message) next . rest)
     (%ACCUMULATING variables arguments ()
                    (#F (LAMBDA (DATUM EXTREME)
                          (IF (AND DATUM EXTREME)
                              (chooser DATUM EXTREME)
                              (OR DATUM EXTREME))))
                    (macro variables arguments message)
                    next . rest))))

(define-syntax %accumulating
  (syntax-rules ()

    ;; There is a finalization step, so the result variable cannot be
    ;; the accumulator variable, and we must apply the finalizer at the
    ;; end.
    ((%ACCUMULATING (result-variable) arguments outer-bindings
                    (initializer combiner finalizer)
                    error-context
                    next . rest)
     (%%ACCUMULATING arguments (ACCUMULATOR initializer combiner)
                     outer-bindings
                     (((result-variable) (finalizer ACCUMULATOR)))
                     error-context
                     next . rest))

    ;; There is no finalizer step, so the accumulation is incremental,
    ;; and can be exploited; therefore, the result variable and the
    ;; accumulator variable are one and the same.
    ((%ACCUMULATING (accumulator-variable) arguments outer-bindings
                    (initializer combiner)
                    error-context
                    next . rest)
     (%%ACCUMULATING arguments (accumulator-variable initializer combiner)
                     outer-bindings
                     ()
                     error-context
                     next . rest))

    ;; The user supplied more than one variable.  Lose lose.
    ((%ACCUMULATING variables arguments outer-bindings parameters
                    (macro (variable ...) original-arguments message)
                    next . rest)
     (SYNTACTIC-ERROR message
                      (FOR variable ... (macro . original-arguments))))))

(define-syntax %%%accumulating
  (syntax-rules ()
    ((%%%ACCUMULATING outer-bindings loop-variable final-bindings next . rest)
     (next outer-bindings
           (loop-variable)
           ()                           ;Entry bindings
           ()                           ;Termination conditions
           ()                           ;Body bindings
           final-bindings
           . rest))))

(define-syntax %%accumulating
  (syntax-rules (IF =>)
    ((%%ACCUMULATING (generator)        ;No conditional
                     (accumulator initializer combiner)
                     outer-bindings final-bindings error-context next . rest)
     (%%%ACCUMULATING outer-bindings
                      (accumulator initializer       ;Loop variable
                                   (combiner generator accumulator))
                      final-bindings next . rest))

    ((%%ACCUMULATING (generator (IF condition))
                     (accumulator initializer combiner)
                     outer-bindings final-bindings error-context next . rest)
     (%%%ACCUMULATING outer-bindings
                      (accumulator initializer       ;Loop variable
                                   (IF condition
                                       (combiner generator accumulator)
                                       accumulator))
                      final-bindings next . rest))

    ((%%ACCUMULATING (generator => mapper)
                     (accumulator initializer combiner)
                     outer-bindings final-bindings error-context next . rest)
     (%%%ACCUMULATING (((MAP) mapper) . outer-bindings)
                      (accumulator initializer       ;Loop variable
                                   (COND (generator
                                          => (LAMBDA (DATUM)
                                               (combiner (MAP DATUM)
                                                         accumulator)))
                                         (ELSE accumulator)))
                      final-bindings next . rest))

    ((%%ACCUMULATING (generator tester => mapper)
                     (accumulator initializer combiner)
                     outer-bindings final-bindings error-context next . rest)
     (%%%ACCUMULATING (((TEST) tester)
                       ((MAP) mapper)
                       . outer-bindings)
                      (accumulator initializer       ;Loop variable
                                   (RECEIVE ARGS generator
                                     (IF (APPLY TEST ARGS)
                                         (combiner (APPLY MAP ARGS)
                                                   accumulator)
                                         accumulator)))
                      final-bindings next . rest))

    ((%%ACCUMULATING arguments parameters outer-bindings final-bindings
                     (macro (variable ...) original-arguments message)
                     next . rest)
     (SYNTACTIC-ERROR message
                      (FOR variable ... (macro . original-arguments))))))

;;;; List Iteration

;;; (FOR <elt> [<pair>] (IN-LIST <list> [<successor>]))
;;;   Step across <list>, letting <pair> be each successive pair in
;;;   <list>, stepping by (<successor> <pair>), or (CDR <pair>) if no
;;;   successor procedure is explicitly provided.  Let <elt> be the car
;;;   of <pair> in the body of the loop.

(define-syntax in-list
  (syntax-rules ()
    ((IN-LIST (element-variable pair-variable)
              (list-expression successor-expression)
              next . rest)
     (next (((LIST) list-expression)                  ;Outer bindings
            ((SUCCESSOR) successor-expression))
           ((pair-variable LIST TAIL))                ;Loop variables
           ()                                         ;Entry bindings
           ((NOT (PAIR? pair-variable)))              ;Termination conditions
           (((element-variable) (CAR pair-variable))  ;Body bindings
            ((TAIL)             (SUCCESSOR pair-variable)))
           ()                                         ;Final bindings
           . rest))

    ((IN-LIST (element-variable pair-variable) (list-expression) next . rest)
     (IN-LIST (element-variable pair-variable) (list-expression CDR)
              next . rest))

    ((IN-LIST (element-variable) (list-expression successor) next . rest)
     (IN-LIST (element-variable PAIR) (list-expression successor) next . rest))

    ((IN-LIST (element-variable) (list-expression) next . rest)
     (IN-LIST (element-variable PAIR) (list-expression CDR) next . rest))

    ((IN-LIST (variable ...) arguments next . rest)
     (SYNTACTIC-ERROR "Malformed IN-LIST clause in LOOP:"
                      (FOR variable ... (IN-LIST . arguments))))))

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
     (SYNTACTIC-ERROR "Malformed IN-LISTS clause in LOOP:"
                      (FOR variable ... (IN-LIST . arguments))))))

(define (%cars&cdrs lists)
  (loop proceed ((for list (in-list lists))
                 (for cars (listing (car list)))
                 (for cdrs (listing (cdr list))))
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
    ((IN-VECTOR variables (vector-expression start/end ...) next . rest)
     (%IN-VECTOR (FORWARD VECTOR-REF VECTOR 0 (VECTOR-LENGTH VECTOR))
                 variables (vector-expression start/end ...)
                 (IN-VECTOR variables (vector-expression start/end ...)
                            "Malformed IN-VECTOR clause in LOOP:")
                 next . rest))))

(define-syntax in-vector-reverse
  (syntax-rules ()
    ((IN-VECTOR-REVERSE variables (vector-expression start/end ...)
                        next . rest)
     (%IN-VECTOR (BACKWARD VECTOR-REF VECTOR (- (VECTOR-LENGTH VECTOR) 1) 0)
                 variables (vector-expression start/end ...)
                 (IN-VECTOR-REVERSE
                  variables (vector-expression start/end ...)
                  "Malformed IN-VECTOR-REVERSE clause in LOOP:")
                 next . rest))))

(define-syntax in-string
  (syntax-rules ()
    ((IN-STRING variables (vector-expression start/end ...) next . rest)
     (%IN-VECTOR (FORWARD STRING-REF STRING 0 (STRING-LENGTH STRING))
                 variables (vector-expression start/end ...)
                 (IN-STRING variables (vector-expression start/end ...)
                            "Malformed IN-STRING clause in LOOP:")
                 next . rest))))

(define-syntax in-string-reverse
  (syntax-rules ()
    ((IN-STRING-REVERSE variables (string-expression start/end ...)
                        next . rest)
     (%IN-VECTOR (BACKWARD STRING-REF STRING (- (STRING-LENGTH STRING) 1) 0)
                 variables (string-expression start/end ...)
                 (IN-STRING-REVERSE
                  variables (string-expression start/end ...)
                  "Malformed IN-STRING-REVERSE clause in LOOP:")
                 next . rest))))

;;;;; Random-Access Sequence Generalization

(define-syntax %in-vector
  (syntax-rules (FORWARD BACKWARD)
    ((%IN-VECTOR (FORWARD vector-ref vector-variable default-start default-end)
                 (element-variable index-variable)
                 (vector-expression start-expression end-expression)
                 error-context next . rest)
     (next (((vector-variable START END);Outer bindings
             (LET ((vector-variable vector-expression))
               (VALUES vector-variable start-expression end-expression))))
           ((index-variable START       ;Loop variables
                            (+ index-variable 1)))
           ()                           ;Entry bindings
           ((>= index-variable END))    ;Termination conditions
           (((element-variable)         ;Body bindings
             (vector-ref vector-variable index-variable)))
           ()                           ;Final bindings
           . rest))

    ((%IN-VECTOR (BACKWARD
                  vector-ref vector-variable default-start default-end)
                 (element-variable index-variabl)
                 (vector-expression start-expression end-expression)
                 error-context next . rest)
     (next (((vector-variable START END);Outer bindings
             (LET ((vector-variable vector-expression))
               (VALUES vector-variable start-expression end-expression))))
           ((index-variable START       ;Loop variables
                            index-variable))
           ()                           ;Entry bindings
           ((<= index-variable END))    ;Termination conditions
           (((index-variable)           ;Body bindings
             (- index-variable 1))
            ((element-variable)
             (vector-ref vector-variable (- index-variable 1))))
           ()                           ;Final bindings
           . rest))

    ;; Supply an index variable if absent.
    ((%IN-VECTOR iteration-parameters (element-variable) arguments
                 error-context next . rest)
     (%IN-VECTOR iteration-parameters (element-variable INDEX) arguments
                 error-context next . rest))

    ;; Supply the default start index if necessary.
    ((%IN-VECTOR (direction vector-ref variable default-start default-end)
                 variables (vector-expression)
                 error-context next . rest)
     (%IN-VECTOR (direction vector-ref variable default-start default-end)
                 variables (vector-expression default-start)
                 error-context next . rest))

    ;; Supply the default end index if necessary.
    ((%IN-VECTOR (direction vector-ref variable default-start default-end)
                 variables (vector-expression start-expression)
                 error-context next . rest)
     (%IN-VECTOR (direction vector-ref variable default-start default-end)
                 variables (vector-expression start-expression default-end)
                 error-context next . rest))

    ((%IN-VECTOR iteration-parameters modified-variables modified-arguments
                 (macro (variable ...) . arguments)
                 next . rest)
     (SYNTACTIC-ERROR error-message (FOR variable ... (macro . arguments))))))

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
     (SYNTACTIC-ERROR "Malformed IN-PORT clause in LOOP:"
                      (FOR variable ... (IN-FILE . arguments))))))

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
     (SYNTACTIC-ERROR "Malformed IN-FILE clause in LOOP:"
                      (FOR variable ... (IN-FILE . arguments))))))

;;;; Bounded Number Iteration

;;; (FOR <number>
;;;   (IN-RANGE [(FROM <start>)]
;;;             [({UP-TO | DOWN-TO} <end>)]
;;;             [(BY <step>)]))
;;;
;;; The bounds are consistently inclusive-lower and exclusive-upper.
;;;
;;; Because I am too lazy to do this properly, one must supply FROM,
;;; UP-TO / DOWN-TO, and BY in that order.  UP-TO or DOWN-TO is
;;; required; the others are optional.

(define-syntax in-range
  (syntax-rules (FROM UP-TO DOWN-TO BY)
    ((IN-RANGE (variable) ((FROM start-expression)
                           (UP-TO end-expression)
                           (BY step-expression))
               next . rest)
     (next (((START) start-expression)  ;Outer bindings
            ((END) end-expression)
            ((STEP) step-expression))
           ((variable START             ;Loop variables
                      (+ variable STEP)))
           ()                           ;Entry bindings
           ((>= variable END))          ;Termination conditions
           ()                           ;Body bindings
           ()                           ;Final bindings
           . rest))

    ((IN-RANGE (variable) ((FROM start-expression)
                           (DOWN-TO end-expression)
                           (BY step-expression))
               next . rest)
     (next (((START) start-expression)  ;Outer bindings
            ((END) end-expression)
            ((STEP) step-expression))
           ((variable START variable))  ;Loop variables
           ()                           ;Entry bindings
           ((<= variable END))          ;Termination conditions
           (((variable)                 ;Body bindings
             (- variable STEP)))
           ()                           ;Final bindings
           . rest))

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
     (SYNTACTIC-ERROR "Malformed IN-RANGE clause in LOOP:"
                      (FOR variable ... (IN-RANGE . arguments))))))

;;;; Unbounded Number Iteration

(define-syntax in-numbers
  (syntax-rules (UP-FROM DOWN-FROM BY)
    ((IN-NUMBERS (variable) ((UP-FROM lower-expression)
                             (BY step-expression))
                 next . rest)
     (next (((LOWER) lower-expression)        ;Outer bindings
            ((STEP) step-expression))
           ((variable LOWER                   ;Loop variables
                      (+ variable STEP)))
           ()                                 ;Entry bindings
           ()                                 ;Termination conditions
           ()                                 ;Body bindings
           ()                                 ;Final bindings
           . rest))

    ((IN-NUMBERS (variable) ((DOWN-FROM upper-expression)
                             (BY step-expression))
                 next . rest)
     (next (((UPPER) upper-expression)        ;Outer bindings
            ((STEP) step-expression))
           ((variable UPPER variable))        ;Loop variables
           (((variable) (- variable STEP)))   ;Entry bindings
           ()                                 ;Termination conditions
           ()                                 ;Body bindings
           ()                                 ;Final bindings
           . rest))

    ((IN-NUMBERS (variable) ((UP-FROM lower-expression)) next . rest)
     (IN-NUMBERS (variable) ((UP-FROM lower-expression) (BY 1)) next . rest))

    ((IN-NUMBERS (variable) ((DOWN-FROM lower-expression)) next . rest)
     (IN-NUMBERS (variable) ((DOWN-FROM lower-expression) (BY 1))
                 next . rest))

    ((IN-NUMBERS (variable) ((BY step-expression)) next . rest)
     (IN-NUMBERS (variable) ((UP-FROM 0) (BY step-expression)) next . rest))

    ((IN-NUMBERS (variable) () next . rest)
     (IN-NUMBERS (variable) ((UP-FROM 0) (BY 1)) next . rest))

    ((IN-NUMBERS (variable ...) arguments next . rest)
     (SYNTACTIC-ERROR "Malformed IN-NUMBERS clause in LOOP:"
		      (FOR variable ... (IN-NUMBERS . arguments))))))
