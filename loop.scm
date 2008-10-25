;;; -*- Mode: Scheme -*-

;;;; Extensible Looping Macros

;;; This code is written by Taylor R. Campbell and placed in the Public
;;; Domain.  All warranties are disclaimed.

;;; This is a variation on Alex Shinn's looping macros described in
;;; message-id <1157562097.001179.11470@i42g2000cwa.googlegroups.com>.
;;;
;;; This file depends on sys-param.scm, also by Taylor R. Campbell, and
;;; SRFI 11 (LET-VALUES).

(define-syntax loop
  (syntax-rules ()
    ((LOOP ((loop-specifier0 loop-specifier1 ...) ...)
       body
       ...)
     (LOOP ANONYMOUS-LOOP ((loop-specifier0 loop-specifier1 ...) ...)
       body
       ...
       (ANONYMOUS-LOOP)))

    ((LOOP name ((loop-specifier0 loop-specifier1 ...) ...)
       body
       ...)
     (%LOOP START name ((loop-specifier0 loop-specifier1 ...) ...)
            body ...))))

(define-syntax %loop
  (syntax-rules (=> <- START GO CONTINUE FINISH)

    ((%LOOP START name loop-specifiers . body)
     (%LOOP GO name (() () () () () ()) loop-specifiers . body))

    ((%LOOP GO name state
            ((variables <- looper argument ...) . loop-specifiers)
            . body)
     (looper (variables argument ...)
             %LOOP CONTINUE name state loop-specifiers . body))

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
            . body)
     (%LOOP GO name
            (((outer-bvl outer-producer) ... . outer-bindings)
             ((loop-variable loop-initializer loop-stepper) ...
              . loop-variables)
             ((entry-bvl entry-producer) ... . entry-bindings)
             (termination-condition ... . termination-conditions)
             ((body-bvl body-producer) ... . body-bindings)
             ((final-bvl final-producer) ... . final-bindings))
            . body))

    ((%LOOP GO name state
            ((variable initializer) . loop-specifiers)
            . body)
     (%LOOP GO name state
            ((variable initializer variable) . loop-specifiers)
            . body))

    ((%LOOP GO name
            (outer-bindings loop-variables . more-state)
            ((variable initializer stepper) . loop-specifiers)
            . body)
     (%LOOP GO name
            (outer-bindings
             ((variable initializer stepper) . loop-variables)
             . more-state)
            loop-specifiers
            . body))

    ((%LOOP GO name state () => result-form . body)
     (%LOOP FINISH name state result-form . body))

    ((%LOOP GO name state () . body)
     (%LOOP FINISH name state (IF #F #F) . body))

    ((%LOOP FINISH name
            (((outer-bvl outer-producer) ...)
             ((loop-variable loop-initializer loop-stepper) ...)
             ((entry-bvl entry-producer) ...)
             (termination-condition ...)
             ((body-bvl body-producer) ...)
             ((final-bvl final-producer) ...))
            result-form
            body ...)
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
                   body
                   ...)))))
       (LOOP-PROCEDURE loop-initializer ...)))))

;;;; Collectors

(define-syntax collecting
  (syntax-rules (IF =>)
    ((COLLECTING (list-variable generator) next . rest)
     (next ()                           ;Outer bindings
           ((ACCUMULATOR '()            ;Loop variables
                         (CONS generator ACCUMULATOR)))
           ()                           ;Entry bindings
           ()                           ;Termination conditions
           ()                           ;Body bindings
           (((list-variable)            ;Final bindings
             (REVERSE ACCUMULATOR)))
           . rest))

    ((COLLECTING (list-variable generator (IF condition)) next . rest)
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

    ;; => as in COND clauses.
    ((COLLECTING (list-variable generator => mapper) next . rest)
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

    ;; => as in SRFI 61 COND clauses.
    ((COLLECTING (list-variable generator tester => mapper) next . rest)
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
           . rest))))

;;;; List Iteration

;;; ((ELT PAIR) <- in-list LIST)   ELT is each successive element, and PAIR
;;;                                   is each successive cons cell, in LIST.
;;; ((PAIR) <- in-list LIST)       ELT is each successive element in LIST.
;;; (ELT <- in-list LIST)          PAIR is each successive cons cell in LIST.
;;; (() <- in-list LIST)           Walk to the end of LIST, binding nothing.
;;;
;;; Tack on (BY successor) after the list to make it iterate by the
;;; given successor procedure, rather than CDR.  For example, to walk
;;; down a property list (list of alternating keys and data):
;;;
;;;   (loop (((key tail) <- in-list plist (by cddr)))
;;;     (let ((datum (car tail)))
;;;       ...))
;;;
;++ This notation is suboptimal.  What we really want is
;++
;++   (loop (((key datum) <- in-list plist (by cddr)))
;++     ...),
;++
;++ but we'd need real pattern matching for that, and getting the *current*
;++ pair is syntactically tricky.

(define-syntax in-list
  (syntax-rules (BY)

    ;; Walk the list and bind the user's element variable.
    ((IN-LIST ((element-variable pair-variable)
               list-expression (BY successor)) next . rest)
     (next (((LIST) list-expression))             ;Outer bindings
           ((pair-variable LIST                   ;Loop variables
                           (successor pair-variable)))
           ()                                     ;Entry bindings
           ((NOT (PAIR? pair-variable)))          ;Termination conditions
           (((element-variable)                   ;Body bindings
             (CAR pair-variable)))
           ()                                     ;Final bindings
           . rest))

    ((IN-LIST ((element-variable pair-variable) list-expression) next . rest)
     (IN-LIST ((element-variable pair-variable)
               list-expression (BY CDR))
              next . rest))

    ;; Walk the list, but bind no element variable for the user.
    ((IN-LIST ((pair-variable) list-expression successor) next . rest)
     (next (((LIST) list-expression))             ;Outer bindings
           ((pair-variable LIST                   ;Loop variables
                           (CDR pair-variable)))
           ()                                     ;Entry bindings
           ((NOT (PAIR? pair-variable)))          ;Termination conditions
           ()                                     ;Body bindings
           ()                                     ;Final bindings
           . rest))

    ((IN-LIST ((pair-variable) list-expression) next . rest)
     (IN-LIST ((pair-variable) list-expression (BY CDR)) next . rest))

    ;; Walk the list with a generated, i.e. invisible to the user, pair
    ;; variable.
    ((IN-LIST (() list-expression successor ...) next . rest)
     (IN-LIST (PAIR list-expression successor ...) next . rest))

    ;; Walk the list with a generated pair variable, and also bind the
    ;; user's element variable.
    ((IN-LIST (element-variable list-expression successor ...) next . rest)
     (IN-LIST ((element-variable PAIR) list-expression) next . rest))))

;;;; List of Lists

(define-syntax in-lists
  (syntax-rules ()
    ((IN-LISTS ((elements-variable pairs-variable) lists-expression)
               next . rest)
     (next (((LISTS) lists-expression))   ;Outer bindings
           ((pairs-variable LISTS CDRS))  ;Loop variables
           (((LOSE? CARS CDRS)            ;Entry bindings
             (%CARS&CDRS pairs-variable)))
           (LOSE?)                        ;Termination conditions
           (((elements-variable) CARS))   ;Body bindings
           ()                             ;Final bindings
           . rest))

    ((IN-LISTS ((pairs-variable) lists-expression) next . rest)
     (next (((LISTS) lists-expression))   ;Outer bindings
           ((pairs-variable LISTS CDRS))  ;Loop variables
           (((LOSE? CARS CDRS)            ;Entry bindings
             (%CARS&CDRS pairs-variable)))
           (LOSE?)                        ;Termination conditions
           ()                             ;Body bindings
           ()                             ;Final bindings
           . rest))

    ((IN-LISTS (elements-variable lists) next . rest)
     (IN-LISTS ((elements-variable PAIRS) lists) next . rest))))

(define (%cars&cdrs lists)
  (loop proceed ((list <- in-list lists)
                 (cars <- collecting (car list))
                 (cdrs <- collecting (cdr list)))
    => (values #f cars cdrs)
    (if (pair? list)
        (proceed)
        (values #t #f #f))))

;;;; Vector and String Iteration

;;; These have the aesthetically displeasing property that the index
;;; variable is bound in the final expression to a bogus value (equal
;;; to the end bound).  Also, the reverse iterators will yield
;;; intermediate negative numbers.

(define-syntax in-vector
  (syntax-rules ()
    ((IN-VECTOR (user-variables vector-expression start/end ...) next . rest)
     (%IN-VECTOR (VECTOR 0 (VECTOR-LENGTH VECTOR))
                 (VECTOR-REF >= +)
                 (user-variables vector-expression start/end ...)
                 next . rest))))

(define-syntax in-vector-reverse
  (syntax-rules ()
    ((IN-VECTOR-REVERSE (user-variables vector-expression start/end ...)
                        next . rest)
     (%IN-VECTOR (VECTOR (- (VECTOR-LENGTH VECTOR) 1) 0)
                 (VECTOR-REF < -)
                 (user-variables vector-expression start/end ...)
                 next . rest))))

(define-syntax in-string
  (syntax-rules ()
    ((IN-STRING (user-variables vector-expression start/end ...) next . rest)
     (%IN-VECTOR (STRING 0 (STRING-LENGTH STRING))
                 (STRING-REF >= +)
                 (user-variables vector-expression start/end ...)
                 next . rest))))

(define-syntax in-string-reverse
  (syntax-rules ()
    ((IN-STRING-REVERSE (user-variables string-expression start/end ...)
                        next . rest)
     (%IN-VECTOR (STRING (- (STRING-LENGTH STRING) 1) 0)
                 (STRING-REF < -)
                 (user-variables string-expression start/end ...)
                 next . rest))))

;;;; Random-Access Sequence Generalization

(define-syntax %in-vector
  (syntax-rules ()
    ((%IN-VECTOR (vector-variable default-start default-end)
                 (vector-ref finished? step)
                 ((element-variable index-variable)
                  vector-expression start-expression end-expression)
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
    ((%IN-VECTOR (vector-variable default-start default-end)
                 (vector-ref finished? step)
                 (element-variable
                  vector-expression start-expression end-expression)
                 next . rest)
     (%IN-VECTOR (vector-variable default-start default-end)
                 (vector-ref finished? step)
                 ((element-variable INDEX)
                  vector-expression start-expression end-expression)
                 next . rest))

    ;; Supply the default end index if necessary.
    ((%IN-VECTOR (vector-variable default-start default-end)
                 (vector-ref finished? step)
                 (user-variables
                  vector-expression start-expression)
                 next . rest)
     (%IN-VECTOR (vector-variable default-start default-end)
                 (vector-ref finished? step)
                 (user-variables
                  vector-expression start-expression default-end)
                 next . rest))

    ;; Supply the default start index if necessary.
    ((%IN-VECTOR (vector-variable default-start default-end)
                 (vector-ref finished? step)
                 (user-variables vector-expression)
                 next . rest)
     (%IN-VECTOR (vector-variable default-start default-end)
                 (vector-ref finished? step)
                 (user-variables vector-expression default-start)
                 next . rest))))

;;;; Input

(define-syntax in-port
  (syntax-rules ()
    ((IN-PORT (datum-variable
               port-expression reader-expression eof-predicate) next . rest)
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
    ((IN-PORT (datum-variable port-expression) next . rest)
     (IN-PORT (datum-variable port-expression READ-CHAR) next . rest))

    ;; Supply an EOF predicate if absent.
    ((IN-PORT (datum-variable port-expression reader-expression) next . rest)
     (IN-PORT (datum-variable
               port-expression reader-expression EOF-OBJECT?)
              next . rest))))

(define-syntax in-file
  (syntax-rules ()
    ((IN-FILE (datum-variable
               pathname-expression reader-expression eof-predicate)
              next . rest)
     (next (((PORT)                               ;Outer bindings
             (OPEN-INPUT-FILE pathname-expression))
            ((READER) reader-expression)
            ((EOF?) eof-predicate))
           ()                                     ;Loop variables
           (((datum-variable) (READER PORT)))     ;Entry bindings
           ((EOF? datum-variable))                ;Termination conditions
           ()                                     ;Body bindings
           ()                                     ;Final bindings
           . rest))

    ;; Supply a reader if absent.
    ((IN-FILE (datum-variable pathname-expression) next . rest)
     (IN-FILE (datum-variable pathname-expression READ-CHAR)))

    ;; Supply an EOF predicate if absent.
    ((IN-FILE (datum-variable pathname-expression reader) next . rest)
     (IN-FILE (datum-variable pathname-expression reader EOF-OBJECT?)
              next . rest))))

;;; Because I am too lazy to do this properly, one must supply FROM,
;;; UP-TO / DOWN-TO, and BY in that order.  UP-TO or DOWN-TO is
;;; required; the others are optional.

(define-syntax in-range
  (syntax-rules (FROM UP-TO DOWN-TO BY)
    ((IN-RANGE (variable (FROM start-expression)
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

    ((IN-RANGE (variable (FROM start-expression)
                         (DOWN-TO end-expression)
                         (BY step-expression))
               next . rest)
     (next (((START) start-expression)  ;Outer bindings
            ((END) end-expression)
            ((STEP) step-expression))
           ((variable START             ;Loop variables
                      (- variable STEP)))
           ()                           ;Entry bindings
           ((<= variable END))          ;Termination conditions
           ()                           ;Body bindings
           ()                           ;Final bindings
           . rest))

    ((IN-RANGE (variable (FROM start-expression) (UP-TO end-expression))
               next . rest)
     (IN-RANGE (variable (FROM start-expression) (UP-TO end-expression) (BY 1))
               next . rest))

    ((IN-RANGE (variable (FROM start-expression) (DOWN-TO end-expression))
               next . rest)
     (IN-RANGE (variable
                (FROM start-expression) (DOWN-TO end-expression) (BY 1))
               next . rest))

    ((IN-RANGE (variable (UP-TO end-expression) (BY step-expression))
               next . rest)
     (IN-RANGE (variable (FROM 0) (UP-TO end-expression) (BY step-expression))
               next . rest))

    ((IN-RANGE (variable (DOWN-TO end-expression) (BY step-expression))
               next . rest)
     (IN-RANGE (variable
                (FROM 0) (DOWN-TO end-expression) (BY step-expression))
               next . rest))

    ((IN-RANGE (variable (UP-TO end-expression)) next . rest)
     (IN-RANGE (variable (FROM 0) (UP-TO end-expression))
               next . rest))

    ((IN-RANGE (variable (DOWN-TO end-expression)) next . rest)
     (IN-RANGE (variable (FROM 0) (DOWN-TO end-expression))
               next . rest))))
