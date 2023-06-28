;;; init.scm
;;; Initial definitions that should be available for the compiler

(define (caar x) (car (car x)))
(define (cadr x) (car (cdr x)))
(define (cdar x) (cdr (car x)))
(define (cddr x) (cdr (cdr x)))
(define (caaar x) (car (caar x)))
(define (caadr x) (car (cadr x)))
(define (cadar x) (car (cdar x)))
(define (caddr x) (car (cddr x)))
(define (cdaar x) (cdr (caar x)))
(define (cdadr x) (cdr (cadr x)))
(define (cddar x) (cdr (cdar x)))
(define (cdddr x) (cdr (cddr x)))
(define (caaaar x) (caar (caar x)))
(define (caaadr x) (caar (cadr x)))
(define (caadar x) (caar (cdar x)))
(define (caaddr x) (caar (cddr x)))
(define (cadaar x) (cadr (caar x)))
(define (cadadr x) (cadr (cadr x)))
(define (caddar x) (cadr (cdar x)))
(define (cadddr x) (cadr (cddr x)))
(define (cdaaar x) (cdar (caar x)))
(define (cdaadr x) (cdar (cadr x)))
(define (cdadar x) (cdar (cdar x)))
(define (cdaddr x) (cdar (cddr x)))
(define (cddaar x) (cddr (caar x)))
(define (cddadr x) (cddr (cadr x)))
(define (cdddar x) (cddr (cdar x)))
(define (cddddr x) (cddr (cddr x)))

(define (list? e)
  (or (null? e)
      (and (pair? e)
           (list? (cdr e)))))

(define list (lambda args args))

(define (not x) (if x #f #t))

(define (fraction? q)
  (and (rational? q)
       (not (integer? q))))

(define list*
  (letrec ((run
             (lambda (a s)
               (if (null? s)
                   a
                   (cons a
                     (run (car s) (cdr s)))))))
    (lambda (a . s)
      (run a s))))

(define apply
  (letrec ((run
             (lambda (a s)
               (if (pair? s)
                   (cons a
                     (run (car s)
                       (cdr s)))
                   a))))
    (lambda (f . s)
      (__bin-apply f
        (run (car s)
          (cdr s))))))

(define ormap
  (lambda (f . s)
    (letrec ((loop
               (lambda (s)
                 (and (pair? (car s))
                      (or (apply f (map car s))
                          (loop (map cdr s)))))))
      (loop s))))

(define andmap
  (lambda (f . s)
    (letrec ((loop
               (lambda (s)
                 (or (null? (car s))
                     (and (apply f (map car s))
                          (loop (map cdr s)))))))
      (loop s))))  

(define map
  (letrec ((map1
             (lambda (f s)
               (if (null? s)
                   '()
                   (cons (f (car s))
                     (map1 f (cdr s))))))
           (map-list
             (lambda (f s)
               (if (null? (car s))
                   '()
                   (cons (apply f (map1 car s))
                     (map-list f
                       (map1 cdr s)))))))
    (lambda (f . s)
      (if (null? s)
          '()
          (map-list f s)))))

(define reverse
  (letrec ((run
             (lambda (s r)
               (if (null? s)
                   r
                   (run (cdr s)
                     (cons (car s) r))))))
    (lambda (s)
      (run s '()))))

(define append
  (letrec ((run-1
             (lambda (s1 sr)
               (if (null? sr)
                   s1
                   (run-2 s1
                     (run-1 (car sr)
                       (cdr sr))))))
           (run-2
             (lambda (s1 s2)
               (if (null? s1)
                   s2
                   (cons (car s1)
                     (run-2 (cdr s1) s2))))))
    (lambda s
      (if (null? s)
          '()
          (run-1 (car s)
            (cdr s))))))

(define fold-left
  (letrec ((run
             (lambda (f unit ss)
               (if (ormap null? ss)
                   unit
                   (run f
                     (apply f unit (map car ss))
                     (map cdr ss))))))
    (lambda (f unit . ss)
      (run f unit ss))))

;;; Please remember that the order here is as per Scheme, and 
;;; not the correct order, which is in Ocaml!
(define fold-right
  (letrec ((run
             (lambda (f unit ss)
               (if (ormap null? ss)
                   unit
                   (apply f
                     `(,@(map car ss)
                       ,(run f unit (map cdr ss))))))))
    (lambda (f unit . ss)
      (run f unit ss))))

(define +
  (let* ((error (lambda () (error '+ "all arguments need to be numbers")))
         (bin+
           (lambda (a b)
             (cond ((rational? a)
                    (cond ((rational? b) (__bin-add-qq a b))
                          ((real? b) (__bin-add-rr (rational->real a) b))
                          (else (error))))
                   ((real? a)
                    (cond ((rational? b) (__bin-add-rr a (rational->real b)))
                          ((real? b) (__bin-add-rr a b))
                          (else (error))))
                   (else (error))))))
    (lambda s (fold-left bin+ 0 s))))

(define -
  (let* ((error (lambda () (error '- "all arguments need to be numbers")))
         (bin-
           (lambda (a b)
             (cond ((rational? a)
                    (cond ((rational? b) (__bin-sub-qq a b))
                          ((real? b) (__bin-sub-rr (rational->real a) b))
                          (else (error))))
                   ((real? a)
                    (cond ((rational? b) (__bin-sub-rr a (rational->real b)))
                          ((real? b) (__bin-sub-rr a b))
                          (else (error))))
                   (else (error))))))
    (lambda (a . s)
      (if (null? s)
          (bin- 0 a)
          (let ((b (fold-left + 0 s)))
            (bin- a b))))))

(define *
  (let* ((error (lambda () (error '* "all arguments need to be numbers")))
         (bin*
           (lambda (a b)
             (cond ((rational? a)
                    (cond ((rational? b) (__bin-mul-qq a b))
                          ((real? b) (__bin-mul-rr (rational->real a) b))
                          (else (error))))
                   ((real? a)
                    (cond ((rational? b) (__bin-mul-rr a (rational->real b)))
                          ((real? b) (__bin-mul-rr a b))
                          (else (error))))
                   (else (error))))))
    (lambda s
      (fold-left bin* 1 s))))

(define /
  (let* ((error (lambda () (error '/ "all arguments need to be numbers")))
         (bin/
           (lambda (a b)
             (cond ((rational? a)
                    (cond ((rational? b) (__bin-div-qq a b))
                          ((real? b) (__bin-div-rr (rational->real a) b))
                          (else (error))))
                   ((real? a)
                    (cond ((rational? b) (__bin-div-rr a (rational->real b)))
                          ((real? b) (__bin-div-rr a b))
                          (else (error))))
                   (else (error))))))
    (lambda (a . s)
      (if (null? s)
          (bin/ 1 a)
          (let ((b (fold-left * 1 s)))
            (bin/ a b))))))

(define fact
  (lambda (n)
    (if (zero? n)
        1
        (* n (fact (- n 1))))))

(define < #void)
(define <= #void)
(define > #void)
(define >= #void)
(define = #void)

(let* ((exit
         (lambda ()
           (error 'generic-comparator
             "all the arguments must be numbers")))
       (make-bin-comparator
         (lambda (comparator-qq comparator-rr)
           (lambda (a b)
             (cond ((rational? a)
                    (cond ((rational? b) (comparator-qq a b))
                          ((real? b)
                           (comparator-rr (rational->real a) b))
                          (else (exit))))
                   ((real? a)
                    (cond ((rational? b)
                           (comparator-rr a (rational->real b)))
                          ((real? b) (comparator-rr a b))
                          (else (exit))))))))
       (bin<? (make-bin-comparator __bin-less-than-qq __bin-less-than-rr))
       (bin=? (make-bin-comparator __bin-equal-qq __bin-equal-rr))
       (bin>=? (lambda (a b) (not (bin<? a b))))
       (bin>? (lambda (a b) (bin<? b a)))
       (bin<=? (lambda (a b) (not (bin>? a b)))))
  (let ((make-run
          (lambda (bin-ordering)
            (letrec ((run
                       (lambda (a s)
                         (or (null? s)
                             (and (bin-ordering a (car s))
                                  (run (car s) (cdr s)))))))
              (lambda (a . s) (run a s))))))
    (set! < (make-run bin<?))
    (set! <= (make-run bin<=?))
    (set! > (make-run bin>?))
    (set! >= (make-run bin>=?))
    (set! = (make-run bin=?))))

(define make-list
  (letrec ((run
             (lambda (n ch)
               (if (zero? n)
                   '()
                   (cons ch
                     (run (- n 1) ch))))))
    (lambda (n . chs)
      (cond ((null? chs) (run n #\nul))
            ((and (pair? chs)
                  (null? (cdr chs))
                  (char? (car chs)))
             (run n (car chs)))
            (else (error 'make-list
                    "Usage: (make-list length ?optional-init-char)"))))))

(define char<? #void)
(define char<=? #void)
(define char=? #void)
(define char>? #void)
(define char>=? #void)

(let ((make-char-comparator
        (lambda (comparator)
          (lambda s
            (apply comparator
              (map char->integer s))))))
  (set! char<? (make-char-comparator <))
  (set! char<=? (make-char-comparator <=))
  (set! char=? (make-char-comparator =))
  (set! char>? (make-char-comparator >))
  (set! char>=? (make-char-comparator >=)))

(define char-downcase #void)
(define char-upcase #void)

(let ((delta
        (- (char->integer #\a)
          (char->integer #\A))))
  (set! char-downcase
    (lambda (ch)
      (if (char<=? #\A ch #\Z)
          (integer->char
            (+ (char->integer ch) delta))
          ch)))
  (set! char-upcase
    (lambda (ch)
      (if (char<=? #\a ch #\z)
          (integer->char
            (- (char->integer ch) delta))
          ch))))

(define char-ci<? #void)
(define char-ci<=? #void)
(define char-ci=? #void)
(define char-ci>? #void)
(define char-ci>=? #void)

(let ((make-char-ci-comparator
        (lambda (comparator)
          (lambda s
            (apply comparator
              (map (lambda (ch)
                     (char->integer
                       (char-downcase ch)))
                s))))))
  (set! char-ci<? (make-char-ci-comparator <))
  (set! char-ci<=? (make-char-ci-comparator <=))
  (set! char-ci=? (make-char-ci-comparator =))
  (set! char-ci>? (make-char-ci-comparator >))
  (set! char-ci>=? (make-char-ci-comparator >=)))

(define string-downcase #void)
(define string-upcase #void)

(let ((make-string-case-converter
        (lambda (char-case-converter)
          (lambda (str)
            (list->string
              (map char-case-converter
                (string->list str)))))))
  (set! string-downcase (make-string-case-converter char-downcase))
  (set! string-upcase (make-string-case-converter char-upcase)))

(define string<? #void)
(define string<=? #void)
(define string=? #void)
(define string>=? #void)
(define string>? #void)
(define string-ci<? #void)
(define string-ci<=? #void)
(define string-ci=? #void)
(define string-ci>=? #void)
(define string-ci>? #void)

(let ((make-string<?
        (lambda (char<? char=?)
          (letrec ((run
                     (lambda (i str1 len1 str2 len2)
                       (or (and (= i len1) (< len1 len2))
                           (and
                             (< i len1)
                             (or (char<?
                                   (string-ref str1 i)
                                   (string-ref str2 i))
                                 (and (char=?
                                        (string-ref str1 i)
                                        (string-ref str2 i))
                                      (run (+ i 1) str1 len1 str2 len2))))))))
            (let ((binary-string<?
                    (lambda (str1 str2)
                      (let ((len1 (string-length str1))
                            (len2 (string-length str2)))
                        (if (<= len1 len2)
                            (run 0 str1 len1 str2 len2)
                            (run 0 str2 len2 str1 len1))))))
              (letrec ((run
                         (lambda (str strs)
                           (or (null? strs)
                               (and (binary-string<? str (car strs))                                    (run (car strs) (cdr strs)))))))
                (lambda (str . strs)
                  (run str strs))))))))
  (set! string<? (make-string<? char<? char=?))
  (set! string-ci<? (make-string<? char-ci<? char-ci=?))
  (set! string>? (make-string<? char>? char=?))
  (set! string-ci>? (make-string<? char-ci>? char-ci=?)))

(let ((make-string<=?
        (lambda (char<? char=?)
          (letrec ((run
                     (lambda (i str1 len1 str2 len2)
                       (or (= i len1)
                           (char<?
                             (string-ref str1 i)
                             (string-ref str2 i))
                           (and (< i len1)
                                (char=?
                                  (string-ref str1 i)
                                  (string-ref str2 i))
                                (run (+ i 1) str1 len1 str2 len2))))))
            (let ((binary-string<=?
                    (lambda (str1 str2)
                      (let ((len1 (string-length str1))
                            (len2 (string-length str2)))
                        (if (<= len1 len2)
                            (run 0 str1 len1 str2 len2)
                            (run 0 str2 len2 str1 len1))))))
              (letrec ((run
                         (lambda (str strs)
                           (or (null? strs)
                               (and (binary-string<=? str (car strs))                                    (run (car strs) (cdr strs)))))))
                (lambda (str . strs)
                  (run str strs))))))))
  (set! string<=? (make-string<=? char<? char=?))
  (set! string-ci<=? (make-string<=? char<? char=?))
  (set! string>=? (make-string<=? char>? char=?))
  (set! string-ci>=? (make-string<=? char-ci>? char-ci=?)))

(let ((make-string=?
        (lambda (char=?)
          (letrec ((run
                     (lambda (i str1 str2 len)
                       (or (= i len)
                           (and (< i len)
                                (char=?
                                  (string-ref str1 i)
                                  (string-ref str2 i))
                                (run (+ i 1) str1 str2 len))))))
            (let ((binary-string=?
                    (lambda (str1 str2)
                      (let ((len1 (string-length str1))
                            (len2 (string-length str2)))
                        (and (= len1 len2)
                             (run 0 str1 str2 len1))))))
              (letrec ((run
                         (lambda (str strs)
                           (or (null? strs)
                               (and (binary-string=? str (car strs))                                    (run (car strs) (cdr strs)))))))
                (lambda (str . strs)
                  (run str strs))))))))
  (set! string=? (make-string=? char=?))
  (set! string-ci=? (make-string=? char-ci=?)))

(define length
  (lambda (s)
    (if (null? s)
        0
        (+ 1 (length (cdr s))))))

(define list?
  (lambda (e)
    (or (null? e)
        (and (pair? e)
             (list? (cdr e))))))

(define make-vector
  (let ((asm-make-vector make-vector))
    (lambda (n . xs)
      (let ((x
              (cond ((null? xs) #void)
                    ((and (pair? xs)
                          (null? (cdr xs)))
                     (car xs))
                    (else (error 'make-vector
                            "Usage: (make-vector size ?optional-default)")))))
        (asm-make-vector n x)))))

(define make-string
  (let ((asm-make-string make-string))
    (lambda (n . chs)
      (let ((ch
              (cond ((null? chs) #\nul)
                    ((and (pair? chs)
                          (null? (cdr chs)))
                     (car chs))
                    (else (error 'make-string
                            "Usage: (make-string size ?optional-default)")))))
        (asm-make-string n ch)))))

(define list->vector
  (letrec ((run
             (lambda (s i)
               (if (null? s)
                   (make-vector i #void)
                   (let ((v (run (cdr s) (+ i 1))))
                     (vector-set! v i (car s))
                     v)))))
    (lambda (s)
      (run s 0))))

(define list->string
  (letrec ((run
             (lambda (s i)
               (if (null? s)
                   (make-string i #\nul)
                   (let ((str (run (cdr s) (+ i 1))))
                     (string-set! str i (car s))
                     str)))))
    (lambda (s)
      (run s 0))))

(define vector (lambda s (list->vector s)))

(define string->list
  (letrec ((run
             (lambda (str i n)
               (if (< i n)
                   (cons (string-ref str i)
                     (run str (+ i 1) n))
                   '()))))
    (lambda (str)
      (run str 0 (string-length str)))))

(define vector->list
  (letrec ((run
             (lambda (v i n)
               (if (< i n)
                   (cons (vector-ref v i)
                     (run v (+ i 1) n))
                   '()))))
    (lambda (v)
      (run v 0 (vector-length v)))))

(define random (lambda (n) (remainder (trng) n)))

(define positive?
  (lambda (x)
    (< 0 x)))

(define negative? (lambda (x) (< x 0)))

(define even? (lambda (n) (zero? (remainder n 2))))

(define odd? (lambda (n) (not (even? n))))

(define abs (lambda (x) (if (negative? x) (- x) x)))

(define equal?
  (lambda (e1 e2)
    (cond ((and (pair? e1) (pair? e2))
           (and (equal? (car e1) (car e2))
                (equal? (cdr e1) (cdr e2))))
          ((and (vector? e1) (vector? e2)
                (= (vector-length e1) (vector-length e2)))
           (equal? (vector->list e1) (vector->list e2)))
          ((and (string? e1) (string? e2)
                (= (string-length e1) (string-length e2)))
           (string=? e1 e2))
          (else (eq? e1 e2)))))

(define assoc
  (lambda (a s)
    (cond ((null? s) #f)
          ((eq? (caar s) a) (car s))
          (else (assoc a (cdr s))))))

;;; end-of-input
