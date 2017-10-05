(set-logic ALL)
(set-option :produce-models true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Poly1305: RFC 7539
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun pow2 (Int) Int)
(assert (= (pow2 0) 1))
(assert (= (pow2 1) 2))
;(assert (= (pow2 2) 4))
;(assert (= (pow2 63) 9223372036854775808))
;(assert (= (pow2 64) 18446744073709551616))
;(assert (= (pow2 128) 340282366920938463463374607431768211456))
;(assert (= (pow2 42) 4398046511104))
;(assert (= (pow2 44) 17592186044416))
;(assert (= (pow2 88) 309485009821345068724781056))
;(assert (= (pow2 44) (* 4 (pow2 42))))

;(assert (forall ((m Int))
;		(! (>= (pow2 m) 0)
;		:pattern ((pow2 m)))))   
(assert (forall ((m Int) (n Int))
	       (! (=> (and (>= m 0) (>= n 0)) (= (* (pow2 m) (pow2 n)) (pow2 (+ m n))))
		:pattern ((* (pow2 m) (pow2 n))))))
;(assert (forall ((m Int) (n Int))
;	       (! (=> (>= m n) (= (div (pow2 m) (pow2 n)) (pow2 (- m n))))
;		:pattern ((div (pow2 m) (pow2 n))))))

(check-sat) 
(define-sort idx () (_ BitVec 2))
(define-sort uint8 () (_ BitVec 8))
(define-sort uint64 () Int)
(define-sort uint64array () (Array idx uint64))
(define-sort uint128 () Int)
(define-sort felem_limb () (Array idx uint64))
(define-sort felem_wide () (Array idx uint128))

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
  (store b #b00 (add64 (shl64 (select b #b00) 4) (shl64 (select b #b00) 2))))

(define-fun carry_top ((b felem_limb)) felem_limb
  (let ((b2 (select b #b10)))
  (let ((b0 (select b #b00)))
  (let ((b2_42 (shr64 b2 42)))
  (let ((b (store b #b10 (mask64 b2 42))))
  (store b #b00 (add64 (add64 (shl64 b2_42 2) b2_42) b0)))))))


(define-fun carry_top_wide ((b felem_wide)) felem_wide
  (let ((b2 (select b #b10)))
  (let ((b0 (select b #b00)))
  (let ((b2_42 (shr128 b2 42)))
  (let ((b (store b #b10 (mask128 b2 42))))
  (store b #b00 (add128 (add128 (shl128 b2_42 2) b2_42) b0)))))))

(define-fun uint64_to_uint128 ((b uint64)) uint128
  b)

(define-fun uint128_to_uint64 ((b uint128)) uint64
  (mod b (pow2 64)))

(declare-const felem_limb0 felem_limb)
(declare-const felem_wide0 felem_wide)

(define-fun copy_from_wide ((b felem_wide)) felem_limb
  (let ((f (store felem_limb0 #b00 (uint128_to_uint64 (select b #b00)))))
  (let ((f (store f #b01 (uint128_to_uint64 (select b #b01)))))
  (let ((f (store f #b10 (uint128_to_uint64 (select b #b10)))))
     f))))

(define-fun add_mul ((a uint128) (b uint64) (s uint64)) uint128
  (add128 a (mul128 (uint64_to_uint128 b) (uint64_to_uint128 s))))
		      
(define-fun sum_scalar_multiplication ((output felem_wide) (input felem_limb) (s uint64)) felem_wide
  (let ((output (store output #b00 (add_mul (select output #b00) (select input #b00) s))))
  (let ((output (store output #b01 (add_mul (select output #b01) (select input #b01) s))))
  (let ((output (store output #b10 (add_mul (select output #b10) (select input #b10) s))))
      output))))

(define-fun carry_wide ((tmp felem_wide)) felem_wide
  (let ((tmp0 (select tmp #b00)))
  (let ((tmp1 (select tmp #b01)))
  (let ((tmp2 (select tmp #b10)))
  (let ((tmp0n (mask128 tmp0 44)))
  (let ((tmp1n (add128 tmp1 (shr128 tmp0 44))))
  (let ((tmp1nn (mask128 tmp1n 44)))
  (let ((tmp2n (add128 tmp2 (shr128 tmp1n 44))))
  (let ((tmp (store tmp #b00 tmp0n)))
  (let ((tmp (store tmp #b01 tmp1nn)))
  (let ((tmp (store tmp #b10 tmp2n)))
      tmp)))))))))))


(define-fun carry_limb ((tmp felem_limb)) felem_limb
  (let ((tmp0 (select tmp #b00)))
  (let ((tmp1 (select tmp #b01)))
  (let ((tmp2 (select tmp #b10)))
  (let ((tmp0n (mask64 tmp0 44)))
  (let ((tmp1n (add64 tmp1 (shr64 tmp0 44))))
  (let ((tmp1nn (mask64 tmp1n 44)))
  (let ((tmp2n (add64 tmp2 (shr64 tmp1n 44))))
  (let ((tmp (store tmp #b00 tmp0n)))
  (let ((tmp (store tmp #b01 tmp1nn)))
  (let ((tmp (store tmp #b10 tmp2n)))
    tmp)))))))))))


(define-fun shift_reduce ((tmp felem_limb)) felem_limb
  (let ((tmp0 (select tmp #b00)))
  (let ((tmp1 (select tmp #b01)))
  (let ((tmp2 (select tmp #b10)))
  (let ((tmp (store tmp #b10 tmp1)))
  (let ((tmp (store tmp #b01 tmp0)))
  (let ((tmp (store tmp #b00 tmp2)))
    (reduce tmp))))))))


(define-fun mul_shift_reduce ((output felem_wide) (input felem_limb) (input2 felem_limb)) felem_wide
  (let ((i20 (select input2 #b00)))
  (let ((i21 (select input2 #b01)))
  (let ((i22 (select input2 #b10)))
  (let ((output (sum_scalar_multiplication output input i20)))      
  (let ((input (shift_reduce input)))
  (let ((output (sum_scalar_multiplication output input i21)))      
  (let ((input (shift_reduce input)))
  (let ((output (sum_scalar_multiplication output input i22)))
       output)))))))))      

(define-fun fmul ((input felem_limb) (input2 felem_limb)) felem_limb
  (let ((tmp input))
  (let ((t (mul_shift_reduce felem_wide0 tmp input2)))
  (let ((t (carry_wide t)))
  (let ((t (carry_top_wide t)))
  (let ((output (copy_from_wide t)))
  (let ((o0 (select output #b00)))
  (let ((o1 (select output #b01)))
  (let ((o2 (select output #b10)))
  (let ((output (store output #b00 (mask64 o0 44))))
  (let ((output (store output #b01 (add64 o1 (shr64 o0 44)))))
       output)))))))))))

(define-fun fadd ((input felem_limb) (input2 felem_limb)) felem_limb
  (let ((acc (store felem_limb0 #b00 (add64 (select input #b00) (select input2 #b00)))))
  (let ((acc (store acc #b01 (add64 (select input #b01) (select input2 #b01)))))
  (let ((acc (store acc #b10 (add64 (select input #b10) (select input2 #b10)))))
       acc))))      

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

;; JUST FOR Z3:
;(define-fun bv2nat ((b uint64)) Int
;  (bv2int b))

(define-fun felem_limb_eval ((input felem_limb)) felem
   (let ((f0 (select input #b00)))
   (let ((f1 (select input #b01)))
   (let ((f2 (select input #b10)))
     (mod      
         (+ (+ f0
	       (* f1 (pow2 44)))
	       (* f2 (pow2 88)))
	 1361129467683753853853498429727072845819)))))

(define-fun felem-add ((x felem) (y felem)) felem
     (mod       
       (+ x y)
	 1361129467683753853853498429727072845819))


(define-fun felem-mul ((x felem) (y felem)) felem
     (mod       
       (* x y)
	 1361129467683753853853498429727072845819))

(define-fun update ((acc felem) (len uint64) (block felem) (r felem)) felem
   (let ((e (add128 (pow2 (* 8 len)) block)))
     (felem-mul (felem-add acc e) r)))

(define-fun finish ((acc felem) (s felem)) felem
  (mod (felem-add acc s) (pow2 128)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (forall ((x uint64) (y uint64)) 
		(=>
		 (and (>= x 0)
		 (and (< x (pow2 63))
		 (and (>= y 0)
		 (and (< y (pow2 63))))))
		 (= (add64 x y) (+ x y)))))

(check-sat)

(assert (forall ((x felem_limb) (y felem_limb))
		(=>
		 (and (>= (select x #b00) 0)
		 (and (< (select x #b00) (pow2 63))
		 (and (>= (select y #b00) 0)
  	         (and (< (select y #b00) (pow2 63))
		 (and (>= (select x #b01) 0)
		 (and (< (select x #b01) (pow2 63))
		 (and (>= (select y #b01) 0)
  	         (and (< (select y #b01) (pow2 63))
		 (and (>= (select x #b10) 0)
		 (and (< (select x #b10) (pow2 63))
		 (and (>= (select y #b10) 0)
  	         (and (< (select y #b10) (pow2 63))))))))))))))
 		(= (felem_limb_eval (fadd x y))
 		   (felem-add (felem_limb_eval x) (felem_limb_eval y))))))

(check-sat)

(assert (forall ((x felem_limb) (y felem_limb))
		(=>
		 (and (>= (select x #b00) 0)
		 (and (< (select x #b00) (pow2 44))
		 (and (>= (select y #b00) 0)
  	         (and (< (select y #b00) (pow2 44))
		 (and (>= (select x #b01) 0)
		 (and (< (select x #b01) (pow2 44))
		 (and (>= (select y #b01) 0)
  	         (and (< (select y #b01) (pow2 44))
		 (and (>= (select x #b10) 0)
		 (and (< (select x #b10) (pow2 42))
		 (and (>= (select y #b10) 0)
  	         (and (< (select y #b10) (pow2 42))))))))))))))
 		(= (felem_limb_eval (fmul x y))
 		   (felem-mul (felem_limb_eval x) (felem_limb_eval y))))))

(check-sat)

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
 		(= (felem_limb_eval (add_and_multiply x y z))
 		   (felem-mul (felem-add (felem_limb_eval x) (felem_limb_eval y)) (felem_limb_eval z))))))

(check-sat)

    
    
