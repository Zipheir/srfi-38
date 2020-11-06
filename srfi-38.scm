;;;; srfi-38.scm - implementation of SRFI-38 for Chicken
;;
;; This code was written by Alex Shinn in 2009 and placed in the
;; Public Domain.  All warranties are disclaimed.

;; This attempts to utilize the native read/write as much as possible,
;; overriding just enough to enable shared reading and writing.

(module srfi-38
 (write-with-shared-structure write/ss
  read-with-shared-structure read/ss
  make-repl-support-shared-structure)

(import scheme)
(import (chicken base))
(import (chicken keyword))
(import (chicken port))


(define (interesting-object? x)
  (not (or (symbol? x) (number? x) (char? x) (boolean? x) (null? x)
           (port? x) (procedure? x) (eof-object? x) (eq? x (void)))))

(define (extract-shared-objects x . o)
  (let ((seen '())
        (interesting? (if (pair? o) (car o) interesting-object?)))
    (let find ((x x))
      (cond
       ((assq x seen)
        => (lambda (cell) (set-cdr! cell (+ (cdr cell) 1))))
       ((pair? x)
        (set! seen (cons (cons x 1) seen))
        (find (car x))
        (find (cdr x)))
       ((vector? x)
        (set! seen (cons (cons x 1) seen))
        (do ((i 0 (+ i 1)))
            ((= i (vector-length x)))
          (find (vector-ref x i))))
       ((interesting? x)
        (set! seen (cons (cons x 1) seen)))))
    (let extract ((ls seen) (res '()))
      (cond
       ((null? ls) res)
       ((> (cdar ls) 1) (extract (cdr ls) (cons (cons (caar ls) #f) res)))
       (else (extract (cdr ls) res))))))

(define (write-with-shared-structure x . o)
  (let* ((out (if (pair? o) (car o) (current-output-port)))
         (ignore-strings?
          (get-keyword ignore-strings: (if (pair? o) (cdr o) '())))
         (shared (extract-shared-objects
                  x
                  (if ignore-strings?
                      (lambda (x) (and (not (string? x)) (interesting-object? x)))
                      interesting-object?)))
         (count 0))
    (define (check-shared x prefix cont)
      (let ((cell (assq x shared)))
        (cond ((and cell (cdr cell))
               (display prefix out)
               (display "#" out)
               (write (cdr cell) out)
               (display "#" out))
              (else
               (cond (cell
                      (display prefix out)
                      (display "#" out)
                      (write count out)
                      (display "=" out)
                      (set-cdr! cell count)
                      (set! count (+ count 1))))
               (cont x (and cell #t))))))
    (cond
     ((null? shared)
      (write x out))
     (else
      (let wr ((x x))
        (check-shared
         x
         ""
         (lambda (x shared?)
           (cond
            ((pair? x)
             (display "(" out)
             (wr (car x))
             (let lp ((ls (cdr x)))
               (check-shared
                ls
                " . "
                (lambda (ls shared?)
                  (cond ((null? ls))
                        ((pair? ls)
                         (cond
                          (shared?
                           (display "(" out)
                           (wr (car ls))
                           (check-shared
                            (cdr ls)
                            " . "
                            (lambda (ls shared?) (lp ls)))
                           (display ")" out))
                          (else
                           (display " " out)
                           (wr (car ls))
                           (lp (cdr ls)))))
                        (else
                         (display " . " out)
                         (wr ls))))))
             (display ")" out))
            ((vector? x)
             (display "#(" out)
             (let ((len (vector-length x)))
               (cond ((> len 0)
                      (wr (vector-ref x 0))
                      (do ((i 1 (+ i 1)))
                          ((= i len))
                        (display " " out)
                        (wr (vector-ref x i))))))
             (display ")" out))
            (else
             (write x out))))))))))

(define write/ss write-with-shared-structure)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (skip-line in)
  (let ((c (read-char in)))
    (if (not (or (eof-object? c) (eqv? c #\newline)))
        (skip-line in))))

(define (skip-whitespace in)
  (case (peek-char in)
    ((#\space #\tab #\newline #\return)
     (read-char in)
     (skip-whitespace in))
    ((#\;)
     (skip-line in)
     (skip-whitespace in))))

(define (skip-comment in depth)
  (case (read-char in)
    ((#\#) (skip-comment in (if (eqv? #\| (peek-char in)) (+ depth 1) depth)))
    ((#\|) (if (eqv? #\# (peek-char in))
               (if (zero? depth) (read-char in) (skip-comment in (- depth 1)))
               (skip-comment in depth)))
    (else (if (eof-object? (peek-char in))
              (error "unterminated #| comment")
              (skip-comment in depth)))))

(define-constant delimiters
  '(#\( #\) #\[ #\] #\space #\tab #\newline #\return))

(define read-with-shared-structure
  (let ((read read))
    (lambda o
      (let ((in (if (pair? o) (car o) (current-input-port)))
            (shared '()))
        (define (read-label res)
          (let ((c (peek-char in)))
            (if (and (not (eof-object? c))
                     (or (char-numeric? c)
                         (memv (char-downcase c) '(#\a #\b #\c #\d #\e #\f))))
              (read-label (cons (read-char in) res))
              (list->string (reverse res)))))
        (define (read-number base)
          (let* ((str (read-label '()))
                 (n (string->number str base))
                 (c (peek-char in)))
            (if (or (not n) (not (or (eof-object? c) (memv c delimiters))))
                (error "read error: invalid number syntax" str c)
                n)))
        (define (read-name c in)
          (let lp ((ls (if (char? c) (list c) '())))
            (let ((c (peek-char in)))
              (cond ((or (eof-object? c) (memv c delimiters))
                     (list->string (reverse ls)))
                    (else (lp (cons (read-char in) ls)))))))
        (define (read-named-char c in)
          (let ((name (read-name c in)))
            (cond ((string-ci=? name "space") #\space)
                  ((string-ci=? name "newline") #\newline)
                  (else (error "unknown char name")))))
        (define (read-one)
          (skip-whitespace in)
          (case (peek-char in)
            ((#\#)
             (read-char in)
             (case (char-downcase (peek-char in))
               ((#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                (let ((n (string->number (read-label '()))))
                  (cond
                   ((not n)
                    (error "read error: invalid reference"))
                   ((eqv? #\= (peek-char in))
                    (read-char in)
                    (let* ((cell (list #f))
                           (thunk (lambda () (car cell))))
                      (set! shared (cons (cons n thunk) shared))
                      (let ((x (read-one)))
                        (set-car! cell x)
                        x)))
                   ((eqv? #\# (peek-char in))
                    (read-char in)
                    (cond ((assv n shared) => cdr)
                          (else (error "read error: unknown reference" n))))
                   (else
                    (error "read error: expected # or = after #n"
                           (read-char in))))))
               ((#\;)
                (read-char in)
                (read-one) ;; discard
                (read-one))
               ((#\|)
                (skip-comment in 0))
               ((#\() (list->vector (read-one)))
               ((#\') (read-char in) (list 'syntax (read-one)))
               ((#\`) (read-char in) (list 'quasisyntax (read-one)))
               ((#\!)
                (let ((name (read-name #f in)))
                  (cond
                   ((string-ci=? name "!fold-case")
                    (case-sensitive #t))
                   ((string-ci=? name "!no-fold-case")
                    (case-sensitive #f))
                   (else
                    (skip-line in)))))
               ((#\t) (let ((s (read-name #f in)))
                        (or (string-ci=? s "t") (string-ci=? s "true")
                            (error "bad # syntax" s))))
               ((#\f) (let ((s (read-name #f in)))
                        (if (or (string-ci=? s "f") (string-ci=? s "false"))
                            #f
                            (error "bad # syntax" s))))
               ((#\d) (read-char in) (read in))
               ((#\x) (read-char in) (read-number 16))
               ((#\o) (read-char in) (read-number 8))
               ((#\b) (read-char in) (read-number 2))
               ((#\i) (read-char in) (exact->inexact (read-one)))
               ((#\e) (read-char in) (inexact->exact (read-one)))
               ((#\c)
                (read-char in)
                (let ((c (read-char in)))
                  (case c
                    ((#\i) (parameterize ((case-sensitive #f)) (read-one)))
                    ((#\s) (parameterize ((case-sensitive #t)) (read-one)))
                    (else (error "unknown read syntax: #c" c)))))
               ((#\\)
                (read-char in)
                (read-named-char #f in))
               (else ; last resort
                (read (make-concatenated-port (open-input-string "#") in)))))
            ((#\()
             (read-char in)
             (let lp ((res '()))
               (skip-whitespace in)
               (case (peek-char in)
                 ((#\))
                  (read-char in)
                  (reverse res))
                 ((#\.)
                  (read-char in)
                  (if (memv (peek-char in) '(#\space #\tab #\newline #\())
                      (let ((tail (read-one)))
                        (skip-whitespace in)
                        (if (eqv? #\) (peek-char in))
                            (begin (read-char in) (append (reverse res) tail))
                            (error "expected end of list after dot")))
                      (read (make-concatenated-port (open-input-string ".") in))
                    ))
                 (else
                  (lp (cons (read-one) res))))))
            ((#\') (read-char in) (list 'quote (read-one)))
            ((#\`) (read-char in) (list 'quasiquote (read-one)))
            ((#\,)
             (read-char in)
             (list (if (eqv? #\@ (peek-char in))
                       (begin (read-char in) 'unquote-splicing)
                       'unquote)
                   (read-one)))
            (else
             (read in))))
        ;; body
        (let ((res (read-one)))
          (if (pair? shared)
              (patch res))
          res)))))

(define (hole? x) (procedure? x))
(define (fill-hole x) (if (hole? x) (fill-hole (x)) x))

(define (patch x)
  (cond
   ((pair? x)
    (if (hole? (car x)) (set-car! x (fill-hole (car x))) (patch (car x)))
    (if (hole? (cdr x)) (set-cdr! x (fill-hole (cdr x))) (patch (cdr x))))
   ((vector? x)
    (do ((i (- (vector-length x) 1) (- i 1)))
        ((< i 0))
      (let ((elt (vector-ref x i)))
        (if (hole? elt)
            (vector-set! x i (fill-hole elt))
            (patch elt)))))))

(define read/ss read-with-shared-structure)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (make-repl-support-shared-structure)
  ;;(set! ##sys#repl-read-hook read-with-shared-structure)
  (set! ##sys#repl-print-hook
        (lambda (x p) (write-with-shared-structure x p) (newline p)))
  (if #f #f))

)
