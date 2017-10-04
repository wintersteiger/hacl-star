;(set-logic ABVNIA)
(set-option :produce-models true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Poly1305: RFC 7539
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sort idx () (_ BitVec 2))
(define-sort uint8 () (_ BitVec 8))
(define-sort uint64 () (_ BitVec 64))
(define-sort uint64array () (Array idx uint64))
(define-sort uint128 () (_ BitVec 128))
(define-sort felem_limb () (Array idx uint64))
(define-sort felem_wide () (Array idx uint128))

(define-fun reduce ((b felem_limb)) felem_limb
  (store b #b00 (bvadd (bvshl (select b #b00) #x0000000000000004) (bvshl (select b #b00) #x0000000000000002))))

(define-fun carry_top ((b felem_limb)) felem_limb
  (let ((b2 (select b #b10)))
  (let ((b0 (select b #b00)))
  (let ((b2_42 (bvlshr b2 #x000000000000002a)))
  (let ((b (store b #b10 (bvand b2 #x3fffffffffffffff))))
  (store b #b00 (bvadd (bvadd (bvshl b2_42 #x0000000000000002) b2_42) b0)))))))


(define-fun carry_top_wide ((b felem_wide)) felem_wide
  (let ((b2 (select b #b10)))
  (let ((b0 (select b #b00)))
  (let ((b2_42 (bvlshr b2 #x0000000000000000000000000000002a)))
  (let ((b (store b #b10 (bvand b2 #x00000000000000003fffffffffffffff))))
  (store b #b00 (bvadd (bvadd (bvshl b2_42 #x00000000000000000000000000000002) b2_42) b0)))))))

(define-fun uint64_to_uint128 ((b uint64)) uint128
  (concat #x0000000000000000 b))

(define-fun uint128_to_uint64 ((b uint128)) uint64
  ((_ extract 63 0) b))

(declare-const felem_limb0 felem_limb)
(declare-const felem_wide0 felem_wide)

(define-fun copy_from_wide ((b felem_wide)) felem_limb
  (let ((f (store felem_limb0 #b00 (uint128_to_uint64 (select b #b00)))))
  (let ((f (store f #b01 (uint128_to_uint64 (select b #b01)))))
  (let ((f (store f #b10 (uint128_to_uint64 (select b #b10)))))
     f))))

(define-fun add_mul ((a uint128) (b uint64) (s uint64)) uint128
  (bvadd a (bvmul (uint64_to_uint128 b) (uint64_to_uint128 s))))
		      
(define-fun sum_scalar_multiplication ((output felem_wide) (input felem_limb) (s uint64)) felem_wide
  (let ((output (store output #b00 (add_mul (select output #b00) (select input #b00) s))))
  (let ((output (store output #b01 (add_mul (select output #b01) (select input #b01) s))))
  (let ((output (store output #b10 (add_mul (select output #b10) (select input #b10) s))))
      output))))

(define-fun carry_wide ((tmp felem_wide)) felem_wide
  (let ((tmp0 (select tmp #b00)))
  (let ((tmp1 (select tmp #b01)))
  (let ((tmp2 (select tmp #b10)))
  (let ((tmp0n (bvand tmp0 #x000000000000000000000fffffffffff)))
  (let ((tmp1n (bvadd tmp1 (bvlshr tmp0 #x0000000000000000000000000000002c))))
  (let ((tmp1nn (bvand tmp1n #x000000000000000000000fffffffffff)))
  (let ((tmp2n (bvadd tmp2 (bvlshr tmp1n #x0000000000000000000000000000002c))))
  (let ((tmp (store tmp #b00 tmp0n)))
  (let ((tmp (store tmp #b01 tmp1nn)))
  (let ((tmp (store tmp #b10 tmp2n)))
      tmp)))))))))))


(define-fun carry_limb ((tmp felem_limb)) felem_limb
  (let ((tmp0 (select tmp #b00)))
  (let ((tmp1 (select tmp #b01)))
  (let ((tmp2 (select tmp #b10)))
  (let ((tmp0n (bvand tmp0 #x00000fffffffffff)))
  (let ((tmp1n (bvadd tmp1 (bvlshr tmp0 #x000000000000002c))))
  (let ((tmp1nn (bvand tmp1n #x00000fffffffffff)))
  (let ((tmp2n (bvadd tmp2 (bvlshr tmp1n #x000000000000002c))))
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

(define-fun fmul ((output felem_limb) (input felem_limb) (input2 felem_limb)) felem_limb
  (let ((tmp input))
  (let ((t (mul_shift_reduce felem_wide0 tmp input2)))
  (let ((t (carry_wide t)))
  (let ((t (carry_top_wide t)))
  (let ((output (copy_from_wide t)))
  (let ((o0 (select output #b00)))
  (let ((o1 (select output #b01)))
  (let ((o2 (select output #b10)))
  (let ((output (store output #b00 (bvand o0 #x00000fffffffffff))))
  (let ((output (store output #b01 (bvadd o1 (bvlshr o0 #x000000000000002c)))))
       output)))))))))))

(define-fun fadd ((input felem_limb) (input2 felem_limb)) felem_limb
  (let ((acc (store felem_limb0 #b00 (bvadd (select input #b00) (select input2 #b00)))))
  (let ((acc (store acc #b01 (bvadd (select input #b01) (select input2 #b01)))))
  (let ((acc (store acc #b10 (bvadd (select input #b10) (select input2 #b10)))))
       acc))))      

(define-fun add_and_multiply ((acc felem_limb) (block felem_limb) (r felem_limb)) felem_limb
  (let ((acc (fadd acc block)))
    (fmul acc acc r)))

(define-fun poly1305 ((input uint64array) (len uint64) (key felem_limb)) uint64array
  (let ((k0 (select key #b00)))
  (let ((k1 (select key #b01)))
  (let ((k0 (bvand k0 #x0ffffffc0ffffffc)))
  (let ((k1 (bvand k1 #x0ffffffc0fffffff)))
  (let ((r0 (bvand k0 #x00000fffffffffff)))
  (let ((r1 (bvand (bvshl k1 #x0000000000000014) (bvlshr k0 #x000000000000002c))))
  (let ((r2 (bvlshr k0 #x0000000000000014)))
       input))))))))

;; (define-sort felem () (_ BitVec 260))

;; (define-fun uint64_to_felem ((b uint64)) felem
;;   (concat #x0000000000000000000000000000000000000000000000000 b))

;; (define-fun felem_to_uint64 ((b felem)) uint64
;;   ((_ extract 63 0) b))

   
;; (define-fun felem_limb_eval ((input felem_limb)) felem
;;    (let ((f0 (select input #b00)))
;;    (let ((f1 (select input #b01)))
;;    (let ((f2 (select input #b10)))
;;      (bvurem       
;;      (bvadd
;;          (bvadd (uint64_to_felem f0)
;; 		(bvshl (uint64_to_felem f1) (uint64_to_felem #x000000000000002c)))
;; 	 (bvshl (uint64_to_felem f2) (uint64_to_felem #x0000000000000058)))
;;      #x000000000000000000000000000000003ffffffffffffffffffffffffffffffff)))))

;; (define-fun felem-add ((x felem) (y felem)) felem
;;      (bvurem       
;;        (bvadd x y)
;;        #x000000000000000000000000000000003ffffffffffffffffffffffffffffffff))

;; (define-fun felem-mul ((x felem) (y felem)) felem
;;      (bvurem       
;;        (bvmul x y)
;;        #x000000000000000000000000000000003ffffffffffffffffffffffffffffffff))

;; (assert (forall ((x felem_limb) (y felem_limb))
;; 		(=>
;; 		 (and
;; 		 (and
;; 		 (and (bvult (select x #b00) #x00000fffffffffff) (bvult (select y #b00) #x00000fffffffffff))
;; 		 (and (bvult (select x #b01) #x00000fffffffffff) (bvult (select y #b01) #x00000fffffffffff)))
;; 		 (and (bvult (select x #b10) #x00000fffffffffff) (bvult (select y #b10) #x00000fffffffffff)))
;; 		(= (felem_limb_eval (fadd x y))
;; 		   (felem-add (felem_limb_eval x) (felem_limb_eval y))))))

;; (check-sat)



(define-sort felem () Int)

;; JUST FOR Z3:
;(define-fun bv2nat ((b uint64)) Int
;  (bv2int b))

(declare-fun pow2 (Int) Int)
(assert (= (pow2 64) 18446744073709551616))
(declare-fun bv2natx (uint64) Int)
(declare-fun nat2bvx (Int) uint64)
(assert (forall ((b uint64))
		(= (nat2bvx (bv2natx b)) b)))
(assert (forall ((i Int))
	    (=> (< i (- (pow2 64) 1))
		(= (bv2natx (nat2bvx i)) i))))

(assert (forall ((x uint64) (y uint64))
		(= (bv2natx (bvadd x y)) (bv2natx (nat2bvx (+ (bv2natx x) (bv2natx y)))))))

		       
(define-fun uint64_to_felem ((b uint64)) felem
   (bv2natx b))
  
(define-fun felem_limb_eval ((input felem_limb)) felem
   (let ((f0 (select input #b00)))
   (let ((f1 (select input #b01)))
   (let ((f2 (select input #b10)))
     (mod      
         (+ (+ (uint64_to_felem f0)
	       (* (uint64_to_felem f1) 17592186044416))
	       (* (uint64_to_felem f2) 309485009821345068724781056))
	 1361129467683753853853498429727072845819)))))

(define-fun felem-add ((x felem) (y felem)) felem
     (mod       
       (+ x y)
	 1361129467683753853853498429727072845819))


(define-fun felem-mul ((x felem) (y felem)) felem
     (mod       
       (* x y)
	 1361129467683753853853498429727072845819))


(assert (forall ((x uint64) (y uint64))
		(=> 
 		 (and (< (bv2natx x) (- (pow2 64) 1)) (< (bv2natx y) (- (pow2 64) 1)))
		 (= (bv2natx (bvadd x y)) (+ (bv2natx x) (bv2natx y))))))

;; (assert (forall ((x felem_limb) (y felem_limb))
;; 		(=>
;; 		 (and
;; 		 (and
;; 		 (and (bvult (select x #b00) #x00000fffffffffff) (bvult (select y #b00) #x00000fffffffffff))
;; 		 (and (bvult (select x #b01) #x00000fffffffffff) (bvult (select y #b01) #x00000fffffffffff)))
;; 		 (and (bvult (select x #b10) #x00000fffffffffff) (bvult (select y #b10) #x00000fffffffffff)))
;; 		(= (felem_limb_eval (fadd x y))
;; 		   (felem-add (felem_limb_eval x) (felem_limb_eval y))))))

(check-sat)



    
    
