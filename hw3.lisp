; Problem 102
(defun f1 (i j)
  (if (and (natp i)
	   (natp j)
	   (< i j))
    (f1 (+ 1 i) j)
    1))

; Measure for problem 102
(defun m102 (i j)
  (if (and (natp i)
	   (natp j)
	   (< i j))
    (- j i)
    0))

; xi = (equal (f1 i j) 1)
; m = (m102 i j)
; q1 = (and (natp i)
;	    (natp j)
;	    (< i j))
; sig1,1 = {i <- (+ 1 i), j <- j}

; Ordinal conjecture
(defthm oc102 (o-p (m102 i j)))

; Measure conjecture
(defthm mc102 (implies (and (natp i)
			    (natp j)
			    (< i j))
                       (o< (m102 (+ 1 i) j)
			   (m102 i j))))

; Base case trivially holds since
; (implies (not q1) xi)
; = (implies (not (and (natp i)
;  		       (natp j)
;		       (< i j)))
;	     (equal (f1 i j) 1))
; = t
; which follows by expanding the definition of f1

; Inductive step holds by the following:
; (implies (and q
; 	        xi/sig1,1)
; 	   xi)
; = (implies (and (natp i)
; 		  (natp j)
;		  (< i j)
;		  (equal (f1 (+ 1 i) j) 1))
;	     (equal (f1 i j) 1))
;
; Now expand (f1 i j)
;
; (f1 i j)
; = (f1 (+ 1 i) j)
; = 1
;
; Hence, (equal (f1 i j) 1) holds by induction


; Problem 103
(defun f2 (x)
  (if (equal x nil)
    2
    (and (f2 (car x))
	 (f2 (cdr x)))))

; Cons count function
(defun cc (x)
  (if (atom x)
    0
    (1+ (+ (cc (car x))
	   (cc (cdr x))))))

; Measure for problem 103
(defun m103 (x)
  (if (equal x nil)
    0
    (1+ (cc x))))

; xi = (equal (f2 x) 2)
; m = (m103 x)
; q1 = (not (equal x nil))
; sig1,1 = {x <- (car x)}
; sig1,2 = {x <- (cdr x)}

; Ordinal conjecture
(defthm oc103 (o-p (m103 x)))

; Measure conjecture
(defthm mc103 (implies (not (equal x nil))
		       (and (o< (m103 (car x))
				(m103 x))
			    (o< (m103 (cdr x))
				(m103 x)))))

; Base case trivially holds, since
; (implies (not q1) xi)
; = (implies (equal x nil) (equal (f2 x) 2))
; = (implies (equal x nil) (equal 2 2))
; = t

; Inductive step holds by the following:
; (implies (and q1
; 	        xi/sig1,1
; 	        xi/sig1,2)
; 	   xi)
; = (implies (and (not (equal x nil))
;		  ((equal (f2 (car x)) 2))
;		  ((equal (f2 (cdr x)) 2)))
;	     (equal (f2 x) 2))
;
; Now expand (f2 x)
;
; (f2 x)
; = (and (f2 (car x))
;        (f2 (cdr x)))
; = (if (f2 (car x))
;     (f2 (cdr x))
;     nil)
; = (if 2
;     2
;     nil)
; = 2
;
; Hence, (equal (f2 x) 2)) holds by induction


; Problem 104
(defun f3 (x y)
  (if (and (endp x)
	   (endp y))
    3
    (f3 (cdr x) (cdr y))))

; Measure for problem 104
(defun m104 (x y)
  (+ (m103 x) (m103 y)))

; xi = (equal (f3 x y) 3)
; m = (m104 x y)
; q1 = (not (and (endp x)
;		 (endp y)))
; sig1,1 = {x <- (cdr x), y <- (cdr y)}

; Ordinal conjecture
(defthm oc104 (o-p (m104 x y)))

; Measure conjecture
(defthm mc104 (implies (not (and (endp x)
				 (endp y)))
		       (o< (m104 (cdr x) (cdr y))
			   (m104 x y))))

; Base case trivially holds, since
; (implies (not q1)
;	   xi)
; = (implies (and (endp x)
;		  (endp y))
;	     (equal (f3 x y) 3))
; = t
; if we expand the definition of f3

; Inductive step holds by the following:
; (implies (and q1
;		xi/sig1,1)
;	   xi)
; = (implies (and (not (and (endp x)
;			    (endp y)))
;		  (equal (f3 (cdr x) (cdr y)) 3))
;	     (equal (f3 x y) 3))
; 
; Now expand (f3 x y)
; (f3 x y)
; = (f3 (cdr x) (cdr y))
; = 3
;
; Hence, (equal (f3 x y) 3) holds by induction


; Problem 105
(defun f4 (x y q)
  (if (p x)
    (if q
      (f4 y (dn x) (not q))
      (f4 y (up x) (not q)))
    4))
; which converts to
(defun f4 (x y q)
  (if (p x)
    (if q
      (if (p y)
	(if (not q)
	  (f4 (dn x) (dn y) q)
	  (f4 (dn x) (up y) q))
	4)
      (if (p y)
        (if (not q)
          (f4 (up x) (dn y) q)
          (f4 (up x) (up y) q))
        4))
    4))
; which is equivalent to
(defun f4 (x y q)
  (if (p x)
    (if q
      (if (p y)
	(f4 (dn x) (up y) q)
	4)
      (if (p y)
	(f4 (up x) (dn y) q)
	4))
    4))
; finally,
(defun f4 (x y q)
  (if (p x)
    (if (p y)
      (if q
	(f4 (dn x) (up y) q)
	(f4 (up x) (dn y) q))
      4)
    4))

; Measure for problem 105
(defun m105 (x y q)
  (if q
    (m x)
    (m y)))

; This was given in the previous problem
; Theorem dn-spec
; (and (o-p (m x))
;      (implies (p x)
; 	        (o< (m (dn x)) (m x))))

; xi = (equal (f4 x y q) 5)
; m = (m105 x y q)
; q1 = (and (p x)
;           (p y)
;	    q)
; q2 = (and (p x)
;	    (p y)
;	    (not q))
; sig1,1 = {x <- (dn x), y <- (up y), q <- q}
; sig2,1 = {x <- (up x), y <- (dn y), q <- q}

; Ordinal conjecture
; It is followed by the given theorem dn-spec

; Measure conjecture
(defthm mc105 (and (implies (and (p x)
				 (p y)
				 q)
			    (o< (m (dn x) (up y) q)
				(m x y q)))
		   (implies (and (p x)
				 (p y)
				 (not q))
			    (o< (m (up x) (dn y) q)
				(m x y q)))))

; Base case trivially holds, since
; (implies (and (not q1)
;		(not q2))
;          xi)
; = t
; by expanding the definition of f4

; Inductive step holds by the following:
; (implies (and q1
;               xi/sig1,1)
;          xi)
; = (implies (and (p x)
;                 (p y)
;		  q
;                 (equal (f4 (dn x) (up y) q) 4))
;            (equal (f4 x y q) 4))
; 
; Now expand (f4 x y)
; (f4 x y)
; = (f4 (dn x) (up y) q)
; = 4
;
; and,
; (implies (and q2
;               xi/sig2,1)
;          xi)
; = (implies (and (p x)
;                 (p y)
;                 (not q)
;                 (equal (f4 (up x) (dn y) q) 4))
;            (equal (f4 x y q) 4))
;
; Now expand (f4 x y)
; (f4 x y)
; = (f4 (up x) (dn y) q)
; = 4
;
; Hence, (equal (f4 x y q) 4) holds by induction
