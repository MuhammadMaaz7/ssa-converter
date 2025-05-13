; SMT-LIB translation of SSA code
(declare-const n Int)
(assert (> n 1))

(declare-const arr0 Int)
(declare-const arr1 Int)
(declare-const arr2 Int)
(declare-const arr3 Int)
; Initial array values
(assert (= arr0 4))
(assert (= arr1 3))
(assert (= arr2 2))
(assert (= arr3 1))

; Processing: i_1 = 1
; Iteration 1
(declare-const i_1 Int)
(assert (= i_1 1))
; Processing: φ1 = i_1 < n
; Phi condition φ1: (< i_1 n)
; Processing: key_1 = arr[i_1]
(declare-const key_1 Int)
(assert (= key_1 arr1))
; Processing: j_1 = i_1 - 1
(declare-const j_1 Int)
(assert (= j_1 (- i_1 1)))
; Processing: φ2 = j_1 >= 0 && arr[j_1] > key_1
; Phi condition φ2: (and (>= j_1 0) (> arr0 key_1))
; Processing: arr[j_1 + 1] = φ2 ? arr[j_1] : arr[j_1 + 1]
(declare-const arrj_1 + 1_1 Int)
(assert (= arrj_1 + 1_1 (ite (and (>= j_1 0) (> arr0 key_1)) arr0  (+ arrj1 1))))
; Processing: j_2 = φ2 ? j_1 - 1 : j_2
(declare-const j_2 Int)
(assert (= j_2 (ite (and (>= j_1 0) (> arr0 key_1)) j_1 - 1  j_2)))
; Processing: j_3 = φ2 ? j_2 : j_1
(declare-const j_3 Int)
(assert (= j_3 (ite (and (>= j_1 0) (> arr0 key_1)) j_2  j_1)))
; Processing: φ3 = j_3 >= 0 && arr[j_3] > key_1
; Phi condition φ3: (and (>= j_3 0) (> arrj3 key_1))
; Processing: arr[j_3 + 1] = φ3 ? arr[j_3] : arr[j_3 + 1]
(declare-const arrj_3 + 1_1 Int)
(assert (= arrj_3 + 1_1 (ite (and (>= j_3 0) (> arrj3 key_1)) arrj3  (+ arrj3 1))))
; Processing: j_4 = φ3 ? j_3 - 1 : j_4
(declare-const j_4 Int)
(assert (= j_4 (ite (and (>= j_3 0) (> arrj3 key_1)) j_3 - 1  j_4)))
; Processing: j_5 = φ3 ? j_4 : j_3
(declare-const j_5 Int)
(assert (= j_5 (ite (and (>= j_3 0) (> arrj3 key_1)) j_4  j_3)))
; Processing: arr[j_5 + 1] = φ1 ? key_1 : arr[j_5 + 1]
(declare-const arrj_5 + 1_1 Int)
(assert (= arrj_5 + 1_1 (ite (< i_1 n) key_1  (+ arrj5 1))))
; Processing: φ4 = i_1 < n
; Phi condition φ4: (< i_1 n)
; Processing: key_2 = arr[i_1]
(declare-const key_2 Int)
(assert (= key_2 arr1))
; Processing: j_6 = i_1 - 1
(declare-const j_6 Int)
(assert (= j_6 (- i_1 1)))
; Processing: φ5 = j_6 >= 0 && arr[j_6] > key_2
; Phi condition φ5: (and (>= j_6 0) (> arr0 key_2))
; Processing: arr[j_6 + 1] = φ5 ? arr[j_6] : arr[j_6 + 1]
(declare-const arrj_6 + 1_1 Int)
(assert (= arrj_6 + 1_1 (ite (and (>= j_6 0) (> arr0 key_2)) arr0  (+ arrj6 1))))
; Processing: j_7 = φ5 ? j_6 - 1 : j_7
(declare-const j_7 Int)
(assert (= j_7 (ite (and (>= j_6 0) (> arr0 key_2)) j_6 - 1  j_7)))
; Processing: j_8 = φ5 ? j_7 : j_6
(declare-const j_8 Int)
(assert (= j_8 (ite (and (>= j_6 0) (> arr0 key_2)) j_7  j_6)))
; Processing: φ6 = j_8 >= 0 && arr[j_8] > key_2
; Phi condition φ6: (and (>= j_8 0) (> arrj8 key_2))
; Processing: arr[j_8 + 1] = φ6 ? arr[j_8] : arr[j_8 + 1]
(declare-const arrj_8 + 1_1 Int)
(assert (= arrj_8 + 1_1 (ite (and (>= j_8 0) (> arrj8 key_2)) arrj8  (+ arrj8 1))))
; Processing: j_9 = φ6 ? j_8 - 1 : j_9
(declare-const j_9 Int)
(assert (= j_9 (ite (and (>= j_8 0) (> arrj8 key_2)) j_8 - 1  j_9)))
; Processing: j_10 = φ6 ? j_9 : j_8
(declare-const j_10 Int)
(assert (= j_10 (ite (and (>= j_8 0) (> arrj8 key_2)) j_9  j_8)))
; Processing: arr[j_10 + 1] = φ4 ? key_2 : arr[j_10 + 1]
(declare-const arrj_10 + 1_1 Int)
(assert (= arrj_10 + 1_1 (ite (< i_1 n) key_2  (+ arrj10 1))))
; Processing: key_3 = φ4 ? key_2 : key_1
(declare-const key_3 Int)
(assert (= key_3 (ite (< i_1 n) key_2  key_1)))
; Processing: j_11 = φ4 ? j_10 : j_5
(declare-const j_11 Int)
(assert (= j_11 (ite (< i_1 n) j_10  j_5)))

; Check that the final array is sorted
(assert (and (<= arr0 arr1) (<= arr1 arr2) (<= arr2 arr3)))

(check-sat)
(get-model)
