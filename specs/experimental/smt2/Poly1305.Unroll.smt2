;(set-option :auto_config false)
;(set-option :produce-unsat-cores true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Poly1305: RFC 7539
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun pow2 (Int) Int)

;(assert (= (pow2 0) 1))
;(assert (forall ((m Int))
;		(! (=> (>= m 0) (= (pow2 (+ m 1)) (* 2 (pow2 m))))
;		:pattern ((pow2 (+ m 1)) (>= m 0)))))

;(assert (forall ((m Int) (n Int))
;     (! (=> (and (and (>= m 0) (>= n 0)) (< m n)) (< (pow2 m) (pow2 n)))
;     	   :pattern ((pow2 m) (pow2 n)))))
;(assert (= (pow2 1) 2))
;(assert (= (pow2 2) 4))
;(assert (= (pow2 63) 9223372036854775808))
;(assert (= (pow2 64) 18446744073709551616))
;(assert (= (pow2 128) 340282366920938463463374607431768211456))
;(assert (= (pow2 42) 4398046511104))
;(assert (= (pow2 44) 17592186044416))
;(assert (= (pow2 88) 309485009821345068724781056))
;(assert (= (pow2 44) (* 4 (pow2 42))))

;(assert (forall ((m Int) (n Int))
;	       (! (=> (and (>= m 0) (>= n 0)) (= (* (pow2 m) (pow2 n)) (pow2 (+ m n))))
;		:pattern ((* (pow2 m) (pow2 n))))))
;(assert (forall ((m Int) (n Int))
;	       (! (=> (>= m n) (= (div (pow2 m) (pow2 n)) (pow2 (- m n))))
;		:pattern ((div (pow2 m) (pow2 n))))))

(define-sort uint64 () Int)
(define-sort uint128 () Int)

(declare-datatypes () ((felem_limb (limb3 (l0 uint64) (l1 uint64) (l2 uint64)))))
(declare-datatypes () ((felem_wide (wide3 (l0 uint128) (l1 uint128) (l2 uint128)))))

(define-fun shl64 ((b uint64) (s uint64)) uint64
  (* b (pow2 s)))

(define-fun shr64 ((b uint64) (s uint64)) uint64
  (div b (pow2 s)))

(define-fun add64 ((a uint64) (b uint64)) uint64
  (mod (+ a b) (pow2 64)))

(define-fun mask64 ((b uint64) (s uint64)) uint64
  (mod b (pow2 s)))

(define-fun shl128 ((b uint128) (s uint64)) uint128
  (* b (pow2 s)))

(define-fun shr128 ((b uint128) (s uint64)) uint128
  (div b (pow2 s)))

(define-fun mask128 ((b uint128) (s uint64)) uint128
  (mod b (pow2 s)))

(define-fun add128 ((a uint64) (b uint64)) uint128
  (mod (+ a b) (pow2 128)))

(define-fun mul128 ((a uint64) (b uint64)) uint128
  (mod (* a b) (pow2 128)))

(define-fun reduce ((b felem_limb)) felem_limb
  (let ((b0 (l0 b))
	(b1 (l1 b))
	(b2 (l2 b)))
    (limb3 (add64 (shl64 b0 4) (shl64 b0 2)) b1 b2)))



(define-fun carry_top ((b felem_limb)) felem_limb
  (let ((b0 (l0 b))
	(b1 (l1 b))
	(b2 (l2 b)))
  (let ((b2_42 (shr64 b2 42)))
  (let ((b2 (mask64 b2 42)))
  (let ((b0 (add64 (add64 (shl64 b2_42 2) b2_42) b0)))
       (limb3 b0 b1 b2))))))      


(define-fun carry_top_wide ((b felem_wide)) felem_wide
  (let ((b0 (l0 b))
	(b1 (l1 b))
	(b2 (l2 b)))
  (let ((b2_42 (shr128 b2 42)))
  (let ((b2 (mask128 b2 42)))
  (let ((b0 (add128 (add128 (shl128 b2_42 2) b2_42) b0)))
      (wide3 b0 b1 b2))))))

(define-fun uint64_to_uint128 ((b uint64)) uint128
  b)

(define-fun uint128_to_uint64 ((b uint128)) uint64
  (mod b (pow2 64)))

(declare-const felem_limb0 felem_limb)
(declare-const felem_wide0 felem_wide)

(define-fun copy_from_wide ((b felem_wide)) felem_limb
  (let ((w0 (l0 b))
	(w1 (l1 b))
	(w2 (l2 b)))
  (let ((b0 (uint128_to_uint64 w0)))
  (let ((b1 (uint128_to_uint64 w1)))
  (let ((b2 (uint128_to_uint64 w2)))
     (limb3 b0 b1 b2))))))

(define-fun add_mul ((a uint128) (b uint64) (s uint64)) uint128
  (add128 a (mul128 (uint64_to_uint128 b) (uint64_to_uint128 s))))
		      
(define-fun sum_scalar_multiplication ((output felem_wide) (input felem_limb) (s uint64)) felem_wide
  (let ((o0 (l0 output))
	(o1 (l1 output))
	(o2 (l2 output))
	(i0 (l0 input))
	(i1 (l1 input))
	(i2 (l2 input)))
  (let ((o0 (add_mul o0 i0 s)))
  (let ((o1 (add_mul o1 i1 s)))
  (let ((o2 (add_mul o2 i2 s)))
      (wide3 o0 o1 o2))))))


(define-fun carry_wide ((tmp felem_wide)) felem_wide
  (let ((tmp0 (l0 tmp))
	(tmp1 (l1 tmp))
	(tmp2 (l2 tmp)))
  (let ((tmp0n (mask128 tmp0 44)))
  (let ((tmp1n (add128 tmp1 (shr128 tmp0 44))))
  (let ((tmp1nn (mask128 tmp1n 44)))
  (let ((tmp2n (add128 tmp2 (shr128 tmp1n 44))))
    (wide3 tmp0n tmp1nn tmp2n)))))))


(define-fun carry_limb ((tmp felem_limb)) felem_limb
  (let ((tmp0 (l0 tmp))
	(tmp1 (l1 tmp))
	(tmp2 (l2 tmp)))
  (let ((tmp0n (mask64 tmp0 44)))
  (let ((tmp1n (add64 tmp1 (shr64 tmp0 44))))
  (let ((tmp1nn (mask64 tmp1n 44)))
  (let ((tmp2n (add64 tmp2 (shr64 tmp1n 44))))
     (limb3 tmp0n tmp1nn tmp2n)))))))


(define-fun shift_reduce ((tmp felem_limb)) felem_limb
  (let ((tmp0 (l0 tmp))
	(tmp1 (l1 tmp))
	(tmp2 (l2 tmp)))
    (reduce (limb3 tmp1 tmp0 tmp2))))


(define-fun mul_shift_reduce ((output felem_wide) (input felem_limb) (input2 felem_limb)) felem_wide
  (let ((i20 (l0 input2))
	(i21 (l1 input2))
	(i22 (l2 input2)))
  (let ((output (sum_scalar_multiplication output input i20)))      
  (let ((input (shift_reduce input)))
  (let ((output (sum_scalar_multiplication output input i21)))      
  (let ((input (shift_reduce input)))
  (let ((output (sum_scalar_multiplication output input i22)))
       output)))))))

(define-fun fmul ((input felem_limb) (input2 felem_limb)) felem_limb
  (let ((tmp input))
  (let ((t (mul_shift_reduce felem_wide0 tmp input2)))
  (let ((t (carry_wide t)))
  (let ((t (carry_top_wide t)))
  (let ((output (copy_from_wide t)))
  (let ((o0 (l0 output)))
  (let ((o1 (l1 output)))
  (let ((o2 (l2 output)))
    (limb3 (mask64 o0 44) (add64 o1 (shr64 o0 44)) o2))))))))))


(define-fun fadd ((input felem_limb) (input2 felem_limb)) felem_limb
  (let ((x0 (l0 input))
	(x1 (l1 input))
	(x2 (l2 input)))
  (let ((y0 (l0 input2))
	(y1 (l1 input2))
	(y2 (l2 input2)))
  (let ((o0 (add64 x0 y0))
	  (o1 (add64 x1 y1))
	  (o2 (add64 x2 y2)))
    (limb3 o0 o1 o2)))))

(define-fun add_and_multiply ((acc felem_limb) (block felem_limb) (r felem_limb)) felem_limb
   (let ((acc (fadd acc block)))
     (fmul acc r)))

;; (define-fun update ((acc felem_limb) (len uint64) (block uint128) (r felem_limb)) felem_limb
;;   (let ((b0 (mask128 block 44)))
;;   (let ((b1 (mask128 (shr128 block 44) 44)))
;;   (let ((b2 (shr128 block 88)))
;;   (let ((b2 (+ b2 (pow2 42))))
    
;;   )
;; (define-fun poly1305 ((input uint64array) (len uint64) (key felem_limb)) uint64array
;;    (let ((k0 (select key #b00)))
;;    (let ((k1 (select key #b01)))
;;    (let ((k0 (bvand k0 #x0ffffffc0ffffffc)))
;;    (let ((k1 (bvand k1 #x0ffffffc0fffffff)))
;;    (let ((r0 (bvand k0 #x00000fffffffffff)))
;;    (let ((r1 (bvand (bvshl k1 #x0000000000000014) (bvlshr k0 #x000000000000002c))))
;;    (let ((r2 (bvlshr k0 #x0000000000000014)))
;;         input))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; POLY1305 SPECIFICATION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sort felem () Int)
(declare-const p1305 Int)
(assert (> p1305 1))

(define-fun felem_limb_eval ((input felem_limb)) felem
   (let ((f0 (l0 input)))
   (let ((f1 (l1 input)))
   (let ((f2 (l2 input)))
     (mod      
         (+ f0 (+
   	          (* f1 (pow2 44))
	          (* f2 (pow2 88))))
	       p1305)))))

(define-fun felem-add ((x felem) (y felem)) felem
     (mod       
       (+ x y)
	 p1305))


(define-fun felem-mul ((x felem) (y felem)) felem
     (mod       
       (* x y)
	 p1305))

(define-fun update ((acc felem) (len uint64) (block felem) (r felem)) felem
   (let ((e (add128 (pow2 (* 8 len)) block)))
     (felem-mul (felem-add acc e) r)))

(define-fun finish ((acc felem) (s felem)) felem
  (mod (felem-add acc s) (pow2 128)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-option :rlimit 54465600000)

;; (push)

;; (assert (= (pow2 63) 9223372036854775808))
;; (assert (= (pow2 64) 18446744073709551616))
;; (assert (forall ((x uint64) (y uint64)) 
;; 		(=>
;; 		 (and (>= x 0)
;; 		 (and (< x (pow2 63))
;; 		 (and (>= y 0)
;; 		 (and (< y (pow2 63))))))
;; 		 (not (= (add64 x y) (+ x y))))))
;; (check-sat)
;; ;(get-unsat-core)
;; (pop)

(push)

(assert (= (pow2 63) 9223372036854775808))
(assert (= (pow2 64) 18446744073709551616))
(assert (= (pow2 44) 17592186044416))
(assert (= (pow2 88) 309485009821345068724781056))
(assert (= p1305 1361129467683753853853498429727072845819))

;(assert (forall ((x uint64) (y uint64)) 
;	      (! (=>
;		 (and (>= x 0)
;		 (and (< x (pow2 63))
;		 (and (>= y 0)
;;		 (and (< y (pow2 63))))))
;		 (= (add64 x y) (+ x y)))
;		 :pattern ((add64 x y) (>= x 0) (< x (pow2 63)) (>= y 0) (< y (pow2 63))))))

;(assert (forall ((m Int) (n Int))
;	(! (= (mod (+ (mod m p1305) (mod n p1305)) p1305) (mod (+ m n) p1305))
;	   :pattern ((mod (+ (mod m p1305) (mod n p1305)) p1305)))))

(assert (forall ((x felem_limb) (y felem_limb))
		(let ((x0 (l0 x))
		      (y0 (l0 y))
		      (x1 (l1 x))
		      (y1 (l1 y))
		      (x2 (l2 x))
		      (y2 (l2 y)))
		(=>
		 (and (>= x0 0)
		 (and (<  x0 (pow2 63))
		 (and (>= y0 0)
  	         (and (<  y0 (pow2 63))
		 (and (>= x1 0)
		 (and (<  x1 (pow2 63))
	 	 (and (>= y1 0)
  	         (and (<  y1 (pow2 63))
		 (and (>= x2 0)
		 (and (<  x2 (pow2 63))
		 (and (>= y2 0)
  	         (and (<  y2 (pow2 63))))))))))))))
 		 (not (= (felem_limb_eval (fadd x y))
		  	 (felem-add (felem_limb_eval x) (felem_limb_eval y))))))))
;(check-sat-using simplify)
(check-sat)
(pop)

(push)

;; (assert (= p1305 1361129467683753853853498429727072845819))

;; (assert (= (pow2 0) 1))
;; (assert (= (pow2 1) 2))
;; (assert (= (pow2 4) 16))
;; (assert (= (pow2 42) 4398046511104))
;; (assert (= (pow2 44) 17592186044416))
;; (assert (= (pow2 63) 9223372036854775808))
;; (assert (= (pow2 64) 18446744073709551616))
;; (assert (= (pow2 88) 309485009821345068724781056))
(assert (> (pow2 42) 0))
(assert (= (pow2 44) (* 4 (pow2 42))))
(assert (= (pow2 63) (* 512 (pow2 44))))
(assert (= (pow2 64) (* 2 (pow2 63))))


(assert (forall ((x Int) (y Int))
	(! (= (* (pow2 x) (pow2 y)) (pow2 (+ x y)))
	   :pattern ((* (pow2 x) (pow2 y))))))
(assert (forall ((x Int) (y Int))
 	(! (= (/ (pow2 x) (pow2 y)) (pow2 (- x y)))
 	   :pattern ((/ (pow2 x) (pow2 y))))))
(assert (forall ((x Int) (y Int))
 		(! (= (mod (+ (* x (pow2 130)) y) p1305)
 		      (mod (+ (* x 5) y) p1305))
 		   :pattern ((mod (+ (* x (pow2 130)) y) p1305)))))

(assert (forall ((x felem_limb) (y felem_limb))
		(let ((x0 (l0 x))
		      (y0 (l0 y))
		      (x1 (l1 x))
		      (y1 (l1 y))
		      (x2 (l2 x))
		      (y2 (l2 y)))
		(=>
		 (and (>= x0 0)
		 (and (<  x0 (pow2 44))
		 (and (>= y0 0)
  	         (and (<  y0 (pow2 44))
		 (and (>= x1 0)
		 (and (<  x1 (pow2 44))
		 (and (>= y1 0)
  	         (and (<  y1 (pow2 44))
		 (and (>= x2 0)
		 (and (<  x2 (pow2 42))
		 (and (>= y2 0)
  	         (and (<  y2 (pow2 42))))))))))))))
 		 (not (= (felem_limb_eval (fmul x y))
 		   (felem-mul (felem_limb_eval x) (felem_limb_eval y))))))))
(check-sat)
(pop)

(push)
(assert (forall ((x felem_limb) (y felem_limb) (z felem_limb))
		(=>
		 (and (>= (select x #b00) 0)
		 (and (< (select x #b00) (pow2 44))
		 (and (>= (select y #b00) 0)
  	         (and (< (select y #b00) (pow2 44))
		 (and (>= (select z #b00) 0)
  	         (and (< (select z #b00) (pow2 44))
		 (and (>= (select x #b01) 0)
		 (and (< (select x #b01) (pow2 44))
		 (and (>= (select y #b01) 0)
  	         (and (< (select y #b01) (pow2 44))
		 (and (>= (select z #b01) 0)
  	         (and (< (select z #b01) (pow2 44))
		 (and (>= (select x #b10) 0)
		 (and (< (select x #b10) (pow2 42))
		 (and (>= (select z #b10) 0)
		 (and (< (select z #b10) (pow2 42))
		 (and (>= (select y #b10) 0)
  	         (and (< (select y #b10) (pow2 42))))))))))))))))))))
 		(not (= (felem_limb_eval (add_and_multiply x y z))
 		   (felem-mul (felem-add (felem_limb_eval x) (felem_limb_eval y)) (felem_limb_eval z)))))))

(check-sat)
(pop)
    
    
