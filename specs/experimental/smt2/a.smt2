(define-sort uint64 () (_ BitVec 64))

(define-fun bv2nat ((x uint64)) Int
  (bv2int x))

(assert (forall ((x uint64) (y uint64))
		(=> 
 		 (and (bvult x #x7fffffffffffffff) (bvult y #x7fffffffffffffff))
		 (bvult (bvadd x y) #xffffffffffffffff))))

(check-sat)

(assert (forall ((x uint64) (y uint64))
		(=> 
 		 (and (bvult x #x7fffffffffffffff) (bvult y #x7fffffffffffffff))
		 (= (bv2nat (bvadd x y)) (+ (bv2nat x) (bv2nat y))))))
		 

(check-sat)


;; (declare-fun pow2 (Int) Int)
;; (assert (forall ((x Int) (y Int)) (= (* (pow2 x) (pow2 y)) (pow2 (+ x y)))))
;; (assert (forall ((x Int)) (>= (pow2 x) 0)))

;; (assert (=>
;;           (>= (pow2 64) 0)
;; 	  (= (mod (pow2 64) (pow2 64)) 1000)))

;; (check-sat)

;; (define-fun add64 ((a Int) (b Int)) Int
;;   (rem (+ a b) (pow2 64)))

;; (assert (=>
;;           (>= (pow2 64) 0)
;; 	  (= (add64 (pow2 64) 0) 1000)))

