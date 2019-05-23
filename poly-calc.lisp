; Name: Keonho Lee
; UT EID: kl29758

; Implementation for a calculator for integer-coefficient polynomials

; Here are some examples for expressing polynomials in LISP list form
; Note that we are following ACL2 ordinal forms to express polynomials
; 3 is equivalent to 3
; 3x + 4 is equivalent to ((1 . 3) . 4)
; 3x^4 + 5x - 12 is equivalent to ((4 . 3) . ((1 . 5) . -12)) etc

; Some functions and theorems related to this expression

; Returns t if p is a constant, nil otherwise
(defun constp (p)
  (atom p))

; Returns the degree of the polynomial, i.e. the first exponent
(defun deg (p)
  (if (constp p)
    0
    (caar p)))

; Returns the leading coefficient of the polynomial, i.e. the first coefficient
(defun lead-coef (p)
  (if (constp p)
    p
    (cdar p)))

; Returns the leading term of the polynomial
(defun lead-term (p)
  (if (constp p)
    p
    (car p)))

; Returns the rest of the polynomial
(defun poly-rst (p)
  (if (constp p)
    0
    (cdr p)))

; Returns t if p is a right representation of a polynomial, nil otherwise
(defun polyp (p)
  (if (constp p)
    (integerp p)
    (and (consp (lead-term p))
	 (integerp (deg p))
	 (< 0 (deg p))
	 (integerp (lead-coef p))
	 (not (equal (lead-coef p) 0))
	 (polyp (poly-rst p))
	 (< (deg (poly-rst p))
	    (deg p)))))

; Rest of the polynomial other than the leading term is also a polynomial
(defthm poly-rst-polyp (implies (polyp p)
				(polyp (poly-rst p))))



; Now operations, +, -, and * for polynomials

; Helper function to make a polynomial, i.e. ((expn . coef) . rst)
(defun make-poly (expn coef rst)
  (declare (xargs :guard (and (integerp expn)
			      (< 0 expn)
			      (integerp coef)
			      (not (equal coef 0))
			      (polyp rst)
			      (< (deg rst) expn))
		  :verify-guards nil))
  (if (equal expn 0)
    coef
    (cons (cons expn coef)
	  rst)))

; Made polynomial is polynomial
(defthm make-poly-polyp (implies (and (integerp expn)
				      (< 0 expn)
				      (integerp coef)
				      (not (equal coef 0))
				      (polyp rst)
				      (< (deg rst) expn))
				 (polyp (make-poly expn coef rst))))

; Exponent of made polynomial is exponent itself
(defthm make-poly-expn-equal (implies (and (integerp expn)
					   (< 0 expn)
					   (integerp coef)
					   (not (equal coef 0))
					   (polyp rst)
					   (< (deg rst) expn))
				      (equal (deg (make-poly expn coef rst)) expn)))

; Leading coefficient of made polynomial is lead-coef itself
(defthm make-poly-coef-equal (implies (and (integerp expn)
					   (< 0 expn)
					   (integerp coef)
					   (not (equal coef 0))
					   (polyp rst)
					   (< (deg rst) expn))
				      (equal (lead-coef (make-poly expn coef rst)) coef)))

; Poly-rst of made polynomial is poly-rst itself
(defthm make-poly-rst-equal (implies (and (integerp expn)
					  (< 0 expn)
					  (integerp coef)
					  (not (equal coef 0))
					  (polyp rst)
					  (< (deg rst) expn))
				     (equal (poly-rst (make-poly expn coef rst)) rst)))



; Returns t if the polynomial is monomial, i.e. a polynomial with a single term
(defun monop (p)
  (declare (xargs :guard (polyp p)
                  :verify-guards nil))
  (and (polyp p)
       (or (constp p)
           (equal (poly-rst p) 0))))

; Addition
(defun poly+ (p q)
  (declare (xargs :guard (and (polyp p)
                              (polyp q))
                  :verify-guards nil
                  :measure (+ (acl2-count p) (acl2-count q))))
  (cond ((or (not (polyp p))
             (not (polyp q)))
	 nil)
	((and (constp p) (constp q))
	 (+ p q))
	((< (deg p) (deg q))
         (cons (lead-term q) (poly+ p (poly-rst q))))
        ((< (deg q) (deg p))
         (cons (lead-term p) (poly+ (poly-rst p) q)))
	((equal (+ (lead-coef p) (lead-coef q)) 0)
	 (poly+ (poly-rst p) (poly-rst q)))
	(t
	  (make-poly (deg p)
                      (+ (lead-coef p) (lead-coef q))
                      (poly+ (poly-rst p) (poly-rst q))))))

; Negation
(defun poly-neg (p)
  (declare (xargs :guard (polyp p)
                  :verify-guards nil))
  (if (constp p)
    (- p)
    (make-poly (deg p)
	       (- (lead-coef p))
	       (poly-neg (poly-rst p)))))

; Subtraction
(defun poly- (p q)
  (declare (xargs :guard (and (polyp p)
			      (polyp q))
		  :verify-guards nil))
  (poly+ p (poly-neg q)))

; Multiplication special case, (monomial) * (polynomial)
(defun poly*mono (p q)
  (declare (xargs :guard (and (monop p)
                              (polyp q))
                  :verify-guards nil
		  :measure (acl2-count q)))
  (cond ((or (not (monop p)) (not (polyp q)))
	 nil)
	((or (equal p 0) (equal q 0))
	 0)
	((and (constp p) (constp q))
	 (* p q))
	(t
	  (make-poly (+ (deg p) (deg q))
		     (* (lead-coef p) (lead-coef q))
		     (poly*mono p (poly-rst q))))))

; Multiplication
(defun poly* (p q)
  (declare (xargs :guard (and (polyp p)
			      (polyp q))
		  :verify-guards nil))
  (cond ((or (not (polyp p)) (not (polyp q)))
	 nil)
	((or (equal p 0) (equal q 0))
	 0)
	((and (constp p) (constp q))
	 (* p q))
	((constp p)
	 (poly*mono p q))
	(t
	  (poly+ (poly*mono (cons (lead-term p) 0) q)
		 (poly* (poly-rst p) q)))))

; Examples
(poly+ '3 '5)							; (3) + (5) = 8
(poly+ '((1 . 1) . 0) '7)					; (x) + (7) = x + 7
(poly+ '((3 . -1) (2 . 3) . -1) '((3 . 2) . 4))			; (-x^3 + 3x^2 - 1) + (2x^3 + 4) = x^3 + 3x^2 + 3
(poly+ '((3 . -1) (2 . 3) . -1) '((3 . 1) (2 . -3) . 1))	; (-x^3 + 3x^2 - 1) + (x^3 - 3x^2 + 1) = 0

(poly-neg '3)							; -(3) = -3
(poly-neg '((2 . 1) (1 . 5) . -3))				; -(x^2 + 5x - 3) = -x^2 - 5x + 3

(poly- '3 '5)							; (3) - (5) = -2
(poly- '((3 . -1) (2 . 3) . -1) '((3 . 2) . 4))			; (-x^3 + 3x^2 - 1) - (2x^3 + 4) = -3x^3 + 3x^2 - 5

(poly*mono '-3 '((3 . -1) (2 . 3) . -1))			; (-3) * (-x^3 + 3x^2 - 1) = 3x^3 - 9x^2 + 3
(poly*mono '((2 . 3) . 0) '((3 . -1) (2 . 3) . -1))		; (3x^2) * (-x^3 + 3x^2 - 1) = -3x^5 + 9x^4 - 3x^2

(poly* '((1 . 1) . 1) '((1 . 1) . 1))				; (x + 1) * (x + 1) = x^2 + 2x + 1
(poly* (poly* '((1 . 1) . 1) '((1 . 1) . 1)) '((1 . 1) . 1))	; (x + 1) * (x + 1) * (x + 1) = x^3 + 3x^2 + 3x + 1



; Now we prove some theorems related to these operations
(defthm poly*-mono-closure (implies (and (monop p)
					 (polyp q))
				    (polyp (poly*-mono p q))))

(defthm trivial-algebra1
	(implies (and (integerp x)
		      (integerp y)
		      (<= x y)
		      (<= y x))
		 (equal (equal x y) t)))

(defthm trivial-algebra2
        (implies (and (integerp x)
                      (integerp y)
                      (< x y))
                 (equal (<= x y) t)))

(defthm trivial-algebra3
        (implies (and (integerp x)
                      (integerp y)
                      (< x y))
                 (equal (< y x) nil)))

(defthm deg-lemma1
	(implies (and (polyp p)
		      (polyp q)
		      (constp p)
		      (equal (deg p) (deg q)))
		 (equal (constp q) t)))

(defthm deg-lemma2
	(implies (and (polyp p)
                      (polyp q)
                      (not (constp p))
                      (equal (deg p) (deg q)))
                 (equal (constp q) nil)))

(defthm deg-lemma3
        (implies (and (polyp p)
                      (polyp q)
                      (polyp r)
                      (< (deg q) (deg p))
                      (< (deg r) (deg p)))
                 (< (deg (poly+ q r))
                    (deg p))))

(defthm add-closure-lemma
	(implies (and (polyp p)
		      (integerp q))
		 (polyp (poly+ p q))))

(defthm mult-zero-product1
	(implies (and (polyp p)
		      (polyp p)
		      (not (equal p 0))
		      (not (equal q 0)))
		 (not (equal (poly* p q) 0))))

(defthm mult-zero-product2
	(implies (and (polyp p)
		      (polyp q)
		      (not (equal (poly* p q) 0)))
		 (and (not (equal p 0))
		      (not (equal q 0)))))

; Closure of addition
(defthm add-closure (implies (and (polyp p)
				  (polyp q))
			     (polyp (poly+ p q))))


; Associativity of addition
(defthm add-associative (implies (and (polyp p)
				      (polyp q)
				      (polyp r))
				 (equal (poly+ (poly+ p q) r)
					(poly+ p (poly+ q r)))))

; Commutativity of addition
(defthm add-commutative (implies (and (polyp p)
				      (polyp q))
				 (equal (poly+ p q)
					(poly+ q p))))

; Existence of identity of addition
(defthm add-identity (implies (polyp p)
			      (and (equal (poly+ p 0) p)
				   (equal (poly+ 0 p) p))))

; Inverse of addition
(defthm add-inverse (implies (polyp p)
			     (and (equal (poly+ p (poly-neg p)) 0)
				  (equal (poly+ (poly-neg p) p) 0))))

; Closure of mono-multiplication
(defthm poly*mono-closure (implies (and (monop p)
					(polyp q))
				   (polyp (poly*mono p q))))

; Closure of multiplication
(defthm mult-closure (implies (and (polyp p)
				   (polyp q))
			      (polyp (poly* p q))))

; Associativity of multiplication
(defthm mult-associative (implies (and (polyp p)
				       (polyp q)
				       (polyp r))
				  (equal (poly* (poly* p q) r)
					 (poly* p (poly* q r)))))

; Commutativity of multiplication
(defthm mult-commutative (implies (and (polyp p)
				       (polyp q))
				  (equal (poly* p q)
					 (poly* q p))))

; Existence of identity of multiplication
(defthm mult-identity (implies (polyp p)
			       (and (equal (poly* p 1) p)
				    (equal (poly* 1 p) p))))

; Distributivity of addition and mono-multiplication
(defthm poly*-mono-distributive
	(implies (and (monop p)
		      (polyp q)
		      (polyp r))
		 (equal (poly*mono p (poly+ q r))
			(poly+ (poly*mono p q) (poly*mono p r)))))

; Distributivity of addition and multiplication
(defthm distributive (implies (and (polyp p)
				   (polyp q)
				   (polyp r))
			      (equal (poly* p (poly+ q r))
				     (poly+ (poly* p q) (poly* p r)))))

; Degree of the product is equal to the sum of degrees
(defthm mult-deg (implies (and (polyp p)
			       (polyp q)
			       (not (equal p 0))
			       (not (equal q 0)))
			  (equal (deg (poly* p q))
				 (+ (deg p) (deg q)))))


; t if e is an element of x, nil otherwise
(defun mem (e x)
  (declare (xargs :guard (true-listp x)
                  :verify-guards nil))
  (if (atom x)
    nil
    (or (equal e (car x))
         (mem e (cdr x)))))

; Returns t if the given equation x is valid, where var is a list of variables
; If the equation x contains a variable that is not in the list var, then return nil
; The function should be written as the following examples:
; (eqp '(x y z) (+ 1 (* z 3) (- x y)))
; Yet, multivariable is not defined, hence only use '(x) for var parameter in the function
(defun eqp (var equation)
  (declare (xargs :guard (true-listp var)
		  :verify-guards nil))
  (if (atom equation)
    (or (integerp equation)
	(mem equation var))
    (let ((fn (car equation))
	  (args (cdr equation)))
      (and (true-listp args)
	   (case fn
	     (+ (and (consp args)					; need at least one parameter (+ x1 x2 ... xn)
		     (eqp var (car args))				; (eqp x1)
		     (or (null (cdr args))				; case with one argument (+ x1)
			 (and (consp (cdr args))			; case with more than one arguments (+ x1 x2 ... xn)
			      (eqp var (cons '+ (cdr args)))))))	; inductively check (eqp (+ x2 x3 ... xn))
	     (- (and (consp args)                               	; - case, only one or two parameters
                     (eqp var (car args))                           	; (eqp x1)
                     (or (null (cdr args))                      	; case (- x1)
                         (and (consp (cdr args))                	; case (- x1 x2)
                              (eqp var (cadr args))                  
                              (null (cddr args))))))
	     (* (and (consp args)					; need at least two parameters (* x1 x2 ... xn)
		     (eqp var (car args))				; (eqp x1)
		     (consp (cdr args))				
		     (or (and (null (cddr args))			; case with two arguments (* x1 x2)
			      (eqp var (cadr args)))
			 (and (consp (cddr args))			; case with more than two arguments (* x1 x2 ... xn)
			      (eqp var (cons '* (cdr args)))))))	; inductively check (eqp (* x2 x3 ... xn))
	     (otherwise nil))))))

; Returns the evaluated value of the equation
(defun evl (var equation)
  (declare (xargs :guard (eqp var equation)
		  :verify-guards nil))
  (if (atom equation)
    (if (integerp equation)
      equation
      '((1 . 1) . 0))
    (let ((fn (car equation))
	  (args (cdr equation)))
      (case fn
	(+ (if (null (cdr args))
	     (evl var (car args))				; (+ x1)
	     (poly+ (evl var (car args))			; inductively (+ x1 x2 .. xn)
		    (evl var (cons '+ (cdr args))))))
	(- (if (null (cdr args))
	     (poly-neg (evl var (car args)))			; (- x1)
	     (poly- (evl var (car args))			; (- x1 x2)
		    (evl var (cadr args)))))
	(* (if (null (cddr args))
	     (poly* (evl var (car args))			; (* x1 x2)
		    (evl var (cadr args)))
	     (poly* (evl var (car args))			; inductively (* x1 x2 ... xn)
		    (evl var (cons '* (cdr args))))))))))


; Examples
(eqp '(x) '7)
(eqp '(x) 'x)
(eqp '(x) 'y)
(eqp '(x) '(+ 1 2))
(eqp '(x) '(- 3 x))
(eqp '() '(* 1 4 (+ 3 5 7)))
(eqp '(x y z) '(+ (* (- 3 x) (+ 3 y z) 4) (- z x) (* 0 103)))

(evl '(x) '7)
(evl '(x) 'x)
(evl '(x) '(+ 1 2))
(evl '(x) '(- 3 x))
(evl '(x) '(+ (* (- 3 x) (+ 3 x x) 4) (+ x x) (- 0 103)))

(defthm polyp-evl (implies (eqp '(x) equation)
			   (polyp (evl '(x) equation))))
