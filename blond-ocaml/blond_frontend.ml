(define blond
    (lambda ()
        ((_generate_toplevel-continuation initial-level
                                          (make-initial-environment))
             blond-banner (initial-meta-continuation initial-level))))


(define initial-level 0)
(define level-above add1)


(define initial-meta-continuation
    (lambda (level)
        (let ((an-initial-environment (make-initial-environment)))
            (lambda (selector)
                (case selector
                    ((env)
                        an-initial-environment)
                    ((cont)
                        (_generate_toplevel-continuation
                            (level-above level)
                            an-initial-environment))
                    ((meta-continuation)
                        (initial-meta-continuation (level-above level)))
                    (else
                       (_error foobarbaz)))))))



(define _generate_toplevel-continuation
    (lambda (my-level my-environment)
        (letrec ((elementary-loop
                    (lambda (iteration)
                        (lambda (val meta-continuation)
                            (begin
                                (_print my-level iteration val)
                                (_eval (read)
                                       my-environment
                                       (elementary-loop
                                            (next-iteration iteration))
                                       meta-continuation))))))
            (elementary-loop first-iteration))))

; The first iteration and how to manifest the following ones:
(define first-iteration 0)
(define next-iteration add1)



; A display mechanism for the prompts:
(define _print
    (lambda (l i v)
        (begin
            (display l)
            (display "-")
            (display i)
            (display ": ")
            (pretty-print v)
;           (newline)           ; in the case it was just (display v)
            (display l)
            (display "-")
            (display (next-iteration i))
            (display "> ")
            (flush-output-port))))
                          
