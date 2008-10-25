;;; -*- Mode: Scheme -*-

;;;; Operators with Extended Parameter Syntax, Version 1

;;; This code is written by Taylor R. Campbell and placed in the Public
;;; Domain.  All warranties are disclaimed.

;;; Example:
;;;
;;;   (define (foo x y z) ...)
;;;
;;;   (with-extended-parameter-operators
;;;       ((foo* (foo (x . 0) (y . 0) (z . 0))))
;;;     (foo* 5 (=> z 3) (=> y 1)))
;;; <=>
;;;   (foo 5 1 3)

;;; I have *voluminously* commented this hideous macro of astonishing
;;; complexity in the hopes that it can be read by any other than
;;; macrological deities.  I use syntactic continuation-passing style
;;; in one small place, for a discussion of which the reader should see
;;; the Hilsdale paper; everything else is just mutually tail-recursive
;;; local macros.

;;; The question mark prefix indicates pattern variables.
;;; The number of question marks indicates the nesting depth
;;; of the macro which introduced the pattern variable.
;;; An asterisk marks a syntactic continuation's environment.

(define-syntax with-extended-parameter-operators
  (syntax-rules ()
    ((with-extended-parameter-operators
         ((?labelled-argument-macro-name
           (?positional-form-name (?parameter . ?default)
                                  ...))
          ...)
       ?body0
       ?body1
       ...)

     (letrec-syntax
         ((?labelled-argument-macro-name
           (syntax-rules ()
             ((?labelled-argument-macro-name . ??arguments)
              (letrec-syntax
                  ((apply-positional
                    (syntax-rules ()
                      ((apply-positional ???positionals)
                       (reverse-apply ?positional-form-name ???positionals))))

                   ;; Process all of the leading positional arguments.
                   ;; Once we reach a named argument, pass control on
                   ;; to PROCESS-NAMED.
                   ;;
                   ;; ???PARAMETERS is the list of remaining parameter
                   ;; specifiers (i.e. (parameter . default)) to
                   ;; process, in order.
                   ;;
                   ;; ???POSITIONALS is the current reversed list of
                   ;; positional argument expressions accumulated.
                   ;;
                   ;; ???ARGUMENTS is the list of remaining argument
                   ;; expressions in the input.
                   (process-positionals
                    (syntax-rules (=>)

                      ;; No more parameters -- ignore the remaining
                      ;; arguments (signal a syntax error?), and just
                      ;; do positional application.  There were no
                      ;; named arguments.
                      ((process-positionals () ???positionals . ???arguments)
                       (apply-positional ???positionals))

                      ;; No more positional arguments; fill in default
                      ;; values for the remaining parameters.
                      ((process-positionals ???parameters ???positionals)
                       (process-defaults ???parameters ???positionals))

                      ;; Named argument -- move on to
                      ;; PROCESS-NAMED.
                      ((process-positionals ???parameters
                                            ???positionals
                                            (=> ???parameter ???argument)
                                            . ???arguments)
                       (process-named ???parameters
                                      ???positionals
                                      (=> ???parameter ???argument)
                                      . ???arguments))

                      ;; Positional argument -- accumulate and
                      ;; proceed.
                      ((process-positionals (???parameter . ???parameters)
                                            ???positionals
                                            ???positional
                                            . ???arguments)
                       (process-positionals ???parameters
                                            (???positional . ???positionals)
                                            . ???arguments))))

                   ;; If we ran out of positional arguments, for each
                   ;; remaining parameter specifier, fill in its
                   ;; default expression.
                   (process-defaults
                    (syntax-rules ()

                      ((process-defaults () ???positionals)
                       (apply-positional ???positionals))

                      ((process-defaults ((???parameter . ???default)
                                          . ???parameters/defaults)
                                         ???positionals)
                       (process-defaults ???parameters/defaults
                                         (???default . ???positionals)))))

                   ;; Find the named argument corresponding with each
                   ;; parameter specifier, in order.
                   ;;
                   ;; ???PARAMETERS is the list of remaining parameter
                   ;; specifiers to process, in order.
                   ;;
                   ;; ???POSITIONALS is the currently accumulated list
                   ;; of positional argument expressions, in reverse
                   ;; order.
                   ;;
                   ;; ???ARGUMENTS is the list of remaining arguments
                   ;; to process.  No more positional arguments are
                   ;; allowed at this point in the game, and we never
                   ;; take anything off of this list.
                   (process-named
                    (syntax-rules ()

                      ;; No more pararmeters -- apply.
                      ((process-named () ???positionals . ???arguments)
                       (apply-positional ???positionals))

                      ;; No more arguments -- fill in defaults.
                      ((process-named ???parameters ???postionals)
                       (process-defaults ???parameters ???positionals))

                      ;; Match up this parameter with its argument
                      ;; expression; then go on with the remaining
                      ;; parameters, and all of the arguments.
                      ((process-named ((???parameter . ???default)
                                       . ???parameters)
                                      ???positionals
                                      . ???arguments)
                       (match-parameter-by-name
                        ???arguments
                        ???parameter
                        ???default
                        (process-named-continuation ???positionals
                                                    ???parameters
                                                    . ???arguments)))))

                   ;; Continuation for the named parameter matcher.
                   ;; When we get a value, add it to the saved list of
                   ;; positionals, and proceed with the saved list of
                   ;; remaining parameter specifiers, and the saved
                   ;; list of argument expressions.
                   (process-named-continuation
                    (syntax-rules ()
                      ((process-named-continuation ???value
                                                   ???positionals*
                                                   ???parameters*
                                                   . ???arguments*)
                       (process-named ???parameters*
                                      (???value . ???positionals*)
                                      . ???arguments*))))

                   ;; Find the named argument corresponding with a
                   ;; parameter specifier.  If none exists, use the
                   ;; default given.
                   (match-parameter-by-name
                    (syntax-rules (=> ?parameter ...)

                      ;; For each of the possible named parameters, if
                      ;; it matches this one, use it -- add the
                      ;; corresponding argument expression to the list
                      ;; of positionals.
                      ((match-parameter-by-name
                        ((=> ?parameter ???value) . ???arguments)
                        ?parameter
                        ???default
                        (???continuation . ???environment))
                       (???continuation ???value . ???environment))
                      ...               ;***

                      ;; Argument does not match -- skip it.
                      ((match-parameter-by-name (???argument . ???arguments)
                                                ???parameter
                                                ???default
                                                ???continuation)
                       (match-parameter-by-name ???arguments
                                                ???parameter
                                                ???default
                                                ???continuation))

                      ;; No more arguments -- use the default.
                      ((match-parameter-by-name
                        ()
                        ???parameter
                        ???default
                        (???continuation . ???environment))
                       (???continuation ???default . ???environment))))

                   ;; Apply ???OPERATOR to the reversal of the arguments.
                   (reverse-apply
                    (syntax-rules ()

                      ((reverse-apply ???operator ???reversed-arguments)
                       (reverse-apply ???operator ???reversed-arguments ()))

                      ((reverse-apply ???operator
                                      (???argument . ???more)
                                      ???arguments)
                       (reverse-apply ???operator
                                      ???more
                                      (???argument . ???arguments)))

                      ((reverse-apply ???operator () ???arguments)
                       (???operator . ???arguments)))))

                ;; Start the whole process.
                (process-positionals ((?parameter . ?default) ...)
                                     ()
                                     . ??arguments)))))
          ...)

       ?body0
       ?body1
       ...))))
