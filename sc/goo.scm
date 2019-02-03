((lambda (x . y) x) 1)

((lambda (x . y) y) 1 2)

((lambda (x . y) y) 1 2 3 4 5)

((lambda x x) 1)

(define foo 
	(lambda (f)
		(f 1 2 3)))

(define f 
	(lambda (x . y)
		y))

(define foo 
	(lambda (f)
		(lambda (x . y)
			(if (f y)
				'#(#t)
				'#(#f)))))

((foo pair?) 1 2 3 4)

(define foo2
	(lambda (f . x)
		(lambda ()
			(if (null? x)
				(f 1)
				(f x)))))

(define f2
	(lambda (x)
		(pair? x)))

((foo2 f2 1 2 3))

((foo2 f2))

(define foo3 
	(lambda (x . y)
		y))

(foo3 1)

(define foo4 (lambda (x y)
	(lambda (z . w)
		(lambda (a)
			(if (null? w)
				(+ (+ (+ x y) z) a)
				w)))))

(((foo4 1 2) 3 'alona) 4)

(((foo4 1 2) 3) 4)


(define foo5
 (lambda ()
	(lambda (z . w)
		(lambda (a)
			(if (null? w)
				(+ z a)
				w)))))


(((foo5) 3 'alona) 6)

(((foo5) 10) 2)




((lambda (f) (f 1)) (lambda (x) (+ 1 x)))

((lambda () (+ 1 2)))

((lambda () ((lambda (a) a) 'a)))

(define foo 
	(lambda (x)
		(lambda (y z)
			(or x (+ z y)))))

((foo #f) 1 2)

(define foo2
	(lambda (x . y)
		(lambda (z)
			(+ x z))))

((foo2 1) 4)

(define foo2
	(lambda (x . y)
		(lambda (z)
			(if (pair? y)
				y
				((lambda ()
					(+ z x)))))))

((foo2 1 '(2)) 3)

(define zero? 
  (let ((= =))
    (lambda (x) (= x 0))))

(define list (lambda x x))

(define list? 
  (let ((null? null?) (pair? pair?) (cdr cdr))
    (lambda (x)
      (or (null? x)
	  (and (pair? x) (list? (cdr x)))))))

(define length
  (let ((null? null?) (pair? pair?) (cdr cdr) (+ +))
    (lambda (x)
      (letrec ((count 0) (loop (lambda (lst count)
				 (cond ((null? lst) count)
				       ((pair? lst) (loop (cdr lst) (+ 1 count)))
				       (else "this should be an error, but you don't support exceptions")))))
	(loop x 0)))))

(define not
  (let ((eq? eq?))
    (lambda (x)
      (if (eq? x #t) #f #t))))

(define append
    (let ((null? null?) (car car) (cdr cdr) (cons cons))
      (lambda args
        ((letrec ((f (lambda (ls args)
                       (if (null? args)
                           ls
                           ((letrec ((g (lambda (ls)
                                          (if (null? ls)
                                              (f (car args) (cdr args))
                                              (cons (car ls) (g (cdr ls)))))))
                              g) ls)))))
           f) '() args))))

(append '(1 2) '(23))

(length '(1 2))