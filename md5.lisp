(defpackage :MD5 (:use :CL)
  (:export #:+md5-magic-a+ #:+md5-magic-b+ #:+md5-magic-c+ #:+md5-magic-d+
	   ;; Low-Level functions
	   #:md5sum-update #:md5sum-final #:md5sum-checksum
	   ;; Low-Level functions on character buffers
	   #:md5sum-update-char #:md5sum-final-char
	   ;; Mid-Level functions
	   #:make-md5-state #:update-md5-state #:finalize-md5-state
	   ;; High-Level functions on streams/files
	   #:md5sum-char-stream #:md5sum-byte-stream #:md5sum-file))

(in-package :MD5)

;;; Section 3.4:  Auxilliary functions

(deftype ub32 () `(unsigned-byte 32))
(deftype sb32 () `(signed-byte 32))

(declaim (inline f g h i)
	 (ftype (function (ub32 ub32 ub32) ub32) f g h i))

(defmacro the-usb32 (x)
  `(ext:truly-the sb32 (ext:truly-the ub32 ,x)))

(defmacro the-sb32 (x)
  `(ext:truly-the sb32 ,x))

(defmacro the-ub32 (x)
  `(ext:truly-the ub32 ,x))

(defun f (x y z)
  (declare (type ub32 x y z)
	   (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (the-ub32 (logior (the-sb32 (logand (the-usb32 x) (the-usb32 y)))
		    (the-sb32 (logandc1 (the-usb32 x) (the-usb32 z))))))

(defun g (x y z)
  (declare (type ub32 x y z)
	   (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (the-ub32 (logior (the-sb32 (logand (the-usb32 x) (the-usb32 z)))
		    (the-sb32 (logandc2 (the-usb32 y) (the-usb32 z))))))

(defun h (x y z)
  (declare (type ub32 x y z)
	   (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (the-ub32 (logxor (the-usb32 x) (the-usb32 y) (the-usb32 z))))

(defun i (x y z)
  (declare (type ub32 x y z)
	   (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (the-ub32 (logxor (the-usb32 y)
		    (the-sb32 (logorc2 (the-usb32 x) (the-usb32 z))))))

(declaim (inline mod32+ rol32)
	 (ftype (function (ub32 ub32) ub32) mod32+))
(defun mod32+ (a b)
  (declare (type ub32 a b) (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (ext:truly-the ub32 (+ a b)))

(declaim (ftype (function (ub32 (unsigned-byte 5)) ub32) rol32))
(defun rol32 (a s)
  (declare (type ub32 a) (type (unsigned-byte 5) s)
	   (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (ext:truly-the ub32 (logior (kernel:shift-towards-end a s)
			      (ash a (- s 32)))))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *t* (make-array 64 :element-type 'ub32
				:initial-contents
				(loop for i from 1 to 64
				      collect
				      (truncate
				       (* 4294967296
					  (abs (sin (float i 0.0d0)))))))))

(defmacro with-md5-round ((op block) &rest clauses)
  (loop for (a b c d k s i) in clauses
	collect
	`(setq ,a (mod32+ ,b (rol32 (mod32+ (mod32+ ,a (,op ,b ,c ,d))
					    (mod32+ (aref ,block ,k)
						    ,(aref *t* (1- i))))
			            ,s)))
	into result
	finally
	(return `(progn ,@result))))

(defun update-md5-block (a b c d block)
  (declare (type ub32 a b c d)
	   (type (simple-array ub32 (16)) block)
	   (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (let ((old-a a) (old-b b) (old-c c) (old-d d))
    (declare (type ub32 old-a old-b old-c old-d))
    ;; Round 1
    (with-md5-round (f block)
      (A B C D  0  7  1)(D A B C  1 12  2)(C D A B  2 17  3)(B C D A  3 22  4)
      (A B C D  4  7  5)(D A B C  5 12  6)(C D A B  6 17  7)(B C D A  7 22  8)
      (A B C D  8  7  9)(D A B C  9 12 10)(C D A B 10 17 11)(B C D A 11 22 12)
      (A B C D 12  7 13)(D A B C 13 12 14)(C D A B 14 17 15)(B C D A 15 22 16))
    ;; Round 2
    (with-md5-round (g block)
      (A B C D  1  5 17)(D A B C  6  9 18)(C D A B 11 14 19)(B C D A  0 20 20)
      (A B C D  5  5 21)(D A B C 10  9 22)(C D A B 15 14 23)(B C D A  4 20 24)
      (A B C D  9  5 25)(D A B C 14  9 26)(C D A B  3 14 27)(B C D A  8 20 28)
      (A B C D 13  5 29)(D A B C  2  9 30)(C D A B  7 14 31)(B C D A 12 20 32))
    ;; Round 3
    (with-md5-round (h block)
      (A B C D  5  4 33)(D A B C  8 11 34)(C D A B 11 16 35)(B C D A 14 23 36)
      (A B C D  1  4 37)(D A B C  4 11 38)(C D A B  7 16 39)(B C D A 10 23 40)
      (A B C D 13  4 41)(D A B C  0 11 42)(C D A B  3 16 43)(B C D A  6 23 44)
      (A B C D  9  4 45)(D A B C 12 11 46)(C D A B 15 16 47)(B C D A  2 23 48))
    ;; Round 4
    (with-md5-round (i block)
      (A B C D  0  6 49)(D A B C  7 10 50)(C D A B 14 15 51)(B C D A  5 21 52)
      (A B C D 12  6 53)(D A B C  3 10 54)(C D A B 10 15 55)(B C D A  1 21 56)
      (A B C D  8  6 57)(D A B C 15 10 58)(C D A B  6 15 59)(B C D A 13 21 60)
      (A B C D  4  6 61)(D A B C 11 10 62)(C D A B  2 15 63)(B C D A  9 21 64))
    ;; Update and return
    (values
     (mod32+ old-a a)
     (mod32+ old-b b)
     (mod32+ old-c c)
     (mod32+ old-d d))))

(defconstant +md5-magic-a+ #x67452301)
(defconstant +md5-magic-b+ #xefcdab89)
(defconstant +md5-magic-c+ #x98badcfe)
(defconstant +md5-magic-d+ #x10325476)

;; Low-level drivers

(declaim (inline fill-block fill-block-char))
(defun fill-block (block buffer offset)
  (declare (type (integer 0 #.(- most-positive-fixnum 64)) offset)
	   (type (simple-array ub32 (16)) block)
	   (type (simple-array (unsigned-byte 8) (*)) buffer)
	   (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  #+(and cmu x86)
  (kernel:bit-bash-copy
   buffer (+ (* vm:vector-data-offset vm:word-bits) (* offset vm:byte-bits))
   block (* vm:vector-data-offset vm:word-bits)
   (* 64 vm:byte-bits))
  #-(and cmu x86)
  (loop for i of-type (integer 0 16) from 0
	for j of-type (integer 0 #.most-positive-fixnum)
	from offset to (+ offset 63) by 4
	do
	(setf (aref block i)
	      (ext:truly-the ub32
			     (logior
			      (kernel:shift-towards-end
			       (aref buffer (+ j 3)) 24)
			      (kernel:shift-towards-end
			       (aref buffer (+ j 2)) 16)
			      (kernel:shift-towards-end
			       (aref buffer (+ j 1)) 8)
			      (aref buffer j)))
	      #+NIL
	      (dpb (aref buffer (+ j 3)) (byte 8 24)
		   (dpb (aref buffer (+ j 2)) (byte 8 16)
			(dpb (aref buffer (+ j 1)) (byte 8 8)
			     (aref buffer j)))))))

(defun fill-block-char (block buffer offset)
  (declare (type (integer 0 #.(- most-positive-fixnum 64)) offset)
	   (type (simple-array ub32 (16)) block)
	   (type simple-string buffer)
	   (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  #+(and cmu x86)
  (kernel:bit-bash-copy
   buffer (+ (* vm:vector-data-offset vm:word-bits) (* offset vm:byte-bits))
   block (* vm:vector-data-offset vm:word-bits)
   (* 64 vm:byte-bits))
  #-(and cmu x86)
  (loop for i of-type (integer 0 16) from 0
	for j of-type (integer 0 #.most-positive-fixnum)
	from offset to (+ offset 63) by 4
	do
	(setf (aref block i)
	      (ext:truly-the ub32
			     (logior
			      (kernel:shift-towards-end
			       (char-code (schar buffer (+ j 3))) 24)
			      (kernel:shift-towards-end
			       (char-code (schar buffer (+ j 2))) 16)
			      (kernel:shift-towards-end
			       (char-code (schar buffer (+ j 1))) 8)
			      (char-code (schar buffer j)))))))

(declaim (inline md5sum-update md5sum-final
		 md5sum-update-char md5sum-final-char))
(defun md5sum-update (a b c d block buffer offset)
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0))
	   (type ub32 a b c d)
	   (type (integer 0 #.(- most-positive-fixnum 64)) offset)
	   (type (simple-array ub32 (16)) block)
	   (type (simple-array (unsigned-byte 8) (*)) buffer))
  (fill-block block buffer offset)
  (update-md5-block a b c d block))

(defun md5sum-final (a b c d block buffer offset bytes total-length)
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0))
	   (type ub32 a b c d)
	   (type (unsigned-byte 29) total-length)
	   (type (integer 0 #.(- most-positive-fixnum 64)) offset)
	   (type (integer 0 63) bytes)
	   (type (simple-array ub32 (16)) block)
	   (type (simple-array (unsigned-byte 8) (*)) buffer))
  (setf (aref buffer (+ offset bytes)) #x80)
  (loop for index of-type (integer 0 #.most-positive-fixnum)
	from (+ offset bytes 1) to (+ offset 63)
	do (setf (aref buffer index) #x00))
  (fill-block block buffer offset)
  (when (< bytes 56)
    (setf (aref block 14) (* total-length 8)))
  (multiple-value-bind (a b c d)
      (update-md5-block a b c d block)
    (if (< 56 bytes 64)
	(progn
	  (loop for index of-type (integer 0 16) from 0 to 15
		do (setf (aref block index) #x00000000))
	  (setf (aref block 14) (* total-length 8))
	  (update-md5-block a b c d block))
	(values a b c d))))

(defun md5sum-update-char (a b c d block buffer offset)
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0))
	   (type ub32 a b c d)
	   (type (integer 0 #.(- most-positive-fixnum 64)) offset)
	   (type (simple-array ub32 (16)) block)
	   (type simple-string buffer))
  (fill-block-char block buffer offset)
  (update-md5-block a b c d block))

(defun md5sum-final-char (a b c d block buffer offset bytes total-length)
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0))
	   (type ub32 a b c d)
	   (type (unsigned-byte 29) total-length)
	   (type (integer 0 #.(- most-positive-fixnum 64)) offset)
	   (type (integer 0 63) bytes)
	   (type (simple-array ub32 (16)) block)
	   (type simple-string buffer))
  (setf (schar buffer (+ offset bytes)) (code-char #x80))
  (loop for index of-type (integer 0 #.most-positive-fixnum)
	from (+ offset bytes 1) to (+ offset 63)
	do (setf (schar buffer index) (code-char #x00)))
  (fill-block-char block buffer offset)
  (when (< bytes 56)
    (setf (aref block 14) (* total-length 8)))
  (multiple-value-bind (a b c d)
      (update-md5-block a b c d block)
    (if (< 56 bytes 64)
	(progn
	  (loop for index of-type (integer 0 16) from 0 to 15
		do (setf (aref block index) #x00000000))
	  (setf (aref block 14) (* total-length 8))
	  (update-md5-block a b c d block))
	(values a b c d))))

(defun md5sum-checksum (a b c d)
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0))
	   (type ub32 a b c d))
  (make-array 16 :element-type '(unsigned-byte 8)
	      :initial-contents
	      (list
	       (ldb (byte 8 0) a)
	       (ldb (byte 8 8) a)
	       (ldb (byte 8 16) a)
	       (ldb (byte 8 24) a)
	       (ldb (byte 8 0) b)
	       (ldb (byte 8 8) b)
	       (ldb (byte 8 16) b)
	       (ldb (byte 8 24) b)
	       (ldb (byte 8 0) c)
	       (ldb (byte 8 8) c)
	       (ldb (byte 8 16) c)
	       (ldb (byte 8 24) c)
	       (ldb (byte 8 0) d)
	       (ldb (byte 8 8) d)
	       (ldb (byte 8 16) d)
	       (ldb (byte 8 24) d))))

;; Mid-Level Drivers

(defstruct (md5-state
	     (:constructor make-md5-state ()))
  (a +md5-magic-a+ :type (unsigned-byte 32))
  (b +md5-magic-b+ :type (unsigned-byte 32))
  (c +md5-magic-c+ :type (unsigned-byte 32))
  (d +md5-magic-d+ :type (unsigned-byte 32))
  (amount 0 :type (unsigned-byte 29))
  (block (make-array 16 :element-type '(unsigned-byte 32)) :read-only t
	 :type (simple-array (unsigned-byte 32) (16)))
  (buffer (make-array 64 :element-type '(unsigned-byte 8)) :read-only t
	 :type (simple-array (unsigned-byte 8) (64)))
  (buffer-index 0 :type (integer 0 63))
  (finalized-p nil))

(declaim (inline copy-to-buffer))
(defun copy-to-buffer (from from-offset count buffer buffer-offset)
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0))
	   (type fixnum from-offset)
	   (type (integer 0 63) count buffer-offset)
	   (type (simple-array * (*)) from)
	   (type (simple-array (unsigned-byte 8) (64)) buffer))
  #+(and cmu x86)
  (kernel:bit-bash-copy
   from (+ (* vm:vector-data-offset vm:word-bits) (* from-offset vm:byte-bits))
   buffer (+ (* vm:vector-data-offset vm:word-bits)
	     (* buffer-offset vm:byte-bits))
   (* count vm:byte-bits))
  #-(and cmu x86)
  (if (typep from 'simple-string)
      (loop for buffer-index of-type (integer 0 64) from buffer-offset
	    for from-index of-type fixnum from from-offset
	    below (+ from-offset count)
	    do
	    (setf (aref buffer buffer-index)
		  (char-code (schar from from-index))))
      (loop for buffer-index of-type (integer 0 64) from buffer-offset
	    for from-index of-type fixnum from from-offset
	    below (+ from-offset count)
	    do
	    (setf (aref buffer buffer-index) (aref from from-index)))))

(defun update-md5-state (state sequence &key (start 0) (end (length sequence)))
  (declare (type md5-state state)
	   (type (simple-array * (*)) sequence)
	   (type fixnum start end)
	   (optimize (speed 3) (space 0) (debug 0)))
  (let ((a (md5-state-a state)) (b (md5-state-b state))
	(c (md5-state-c state)) (d (md5-state-d state))
	(block (md5-state-block state))
	(buffer (md5-state-buffer state))
	(buffer-index (md5-state-buffer-index state))
	(length (- end start)))
    (declare (type ub32 a b c d) (type fixnum length)
	     (type (integer 0 63) buffer-index)
	     (type (simple-array (unsigned-byte 32) (16)) block)
	     (type (simple-array (unsigned-byte 8) (64)) buffer))
    ;; Handle old rest
    (unless (zerop buffer-index)
      (let ((amount (min (- 64 buffer-index) length)))
	(declare (type (integer 0 63) amount))
	(copy-to-buffer sequence start amount buffer buffer-index)
	(setq start (the fixnum (+ start amount))))
      (multiple-value-setq (a b c d)
	(md5sum-update a b c d block buffer 0)))
    ;; Handle main-part and new-rest
    (etypecase sequence
      ((simple-array (unsigned-byte 8) (*))
       (locally
	   (declare (type (simple-array (unsigned-byte 8) (*)) sequence))
	 (loop for offset of-type (unsigned-byte 29) from start below end by 64
	       until (< (- end offset) 64)
	       do (multiple-value-setq (a b c d)
		    (md5sum-update a b c d block sequence offset))
	       finally
	       (let ((amount (- end offset)))
		 (unless (zerop amount)
		   (copy-to-buffer sequence offset amount buffer 0))
		 (setf (md5-state-buffer-index state) amount)))))
      (simple-string
       (locally
	   (declare (type simple-string sequence))
	 (loop for offset of-type (unsigned-byte 29) from start below end by 64
	       until (< (- end offset) 64)
	       do (multiple-value-setq (a b c d)
		    (md5sum-update-char a b c d block sequence offset))
	       finally
	       (let ((amount (- end offset)))
		 (unless (zerop amount)
		   (copy-to-buffer sequence offset amount buffer 0))
		 (setf (md5-state-buffer-index state) amount))))))
    (setf (md5-state-a state) a
	  (md5-state-b state) b
	  (md5-state-c state) c
	  (md5-state-d state) d
	  (md5-state-amount state) (+ (md5-state-amount state) length))
    state))

(defun finalize-md5-state (state)
  (declare (type md5-state state)
	   (optimize (speed 3) (space 0) (debug 0)))
  (or (md5-state-finalized-p state)
      (multiple-value-bind (a b c d)
	  (md5sum-final (md5-state-a state) (md5-state-b state)
			(md5-state-c state) (md5-state-d state)
			(md5-state-block state)
			(md5-state-buffer state)
			0 (md5-state-buffer-index state)
			(md5-state-amount state))
	(setf (md5-state-a state) a
	      (md5-state-b state) b
	      (md5-state-c state) c
	      (md5-state-d state) d
	      (md5-state-finalized-p state)
	      (md5sum-checksum a b c d)))))

;; High-Level Drivers

(defconstant +buffer-size+ (* 128 1024))

(deftype buffer-index () `(integer 0 ,+buffer-size+))

(defun md5sum-byte-stream (stream)
  (declare (type stream)
	   (optimize (speed 3) (space 0) (debug 0)))
  (let ((block (make-array 16 :element-type 'ub32))
	(buffer (make-array +buffer-size+ :element-type '(unsigned-byte 8)))
	(length 0)
	(a +md5-magic-a+) (b +md5-magic-b+)
	(c +md5-magic-c+) (d +md5-magic-d+))
    (declare (type ub32 a b c d length)
	     (type (simple-array ub32 (16)) block)
	     (type (simple-array (unsigned-byte 8) (*)) buffer))
    (loop for bytes of-type buffer-index = (read-sequence buffer stream)
	  do
	  (incf length bytes)
	  (loop for offset of-type buffer-index
		from 0 below +buffer-size+ by 64
		for rest-size of-type buffer-index = bytes
		then (- rest-size block-size)
		for block-size of-type (integer 0 64) = (min 64 rest-size)
		do
		(multiple-value-setq (a b c d)
		  (if (< block-size 64)
		      (md5sum-final a b c d block buffer offset
				    block-size length)
		      (md5sum-update a b c d block buffer offset)))
		until (< block-size 64))
	  until (< bytes +buffer-size+)
	  finally (return (md5sum-checksum a b c d)))))

(defun md5sum-char-stream (stream)
  (declare (type stream)
	   (optimize (speed 3) (space 0) (debug 0)))
  (let ((block (make-array 16 :element-type 'ub32))
	(buffer (make-string +buffer-size+))
	(length 0)
	(a +md5-magic-a+) (b +md5-magic-b+)
	(c +md5-magic-c+) (d +md5-magic-d+))
    (declare (type ub32 a b c d length)
	     (type (simple-array ub32 (16)) block)
	     (type simple-string buffer))
    (loop for bytes of-type buffer-index = (read-sequence buffer stream)
	  do
	  (incf length bytes)
	  (loop for offset of-type buffer-index
		from 0 below +buffer-size+ by 64
		for rest-size of-type buffer-index = bytes
		then (- rest-size block-size)
		for block-size of-type (integer 0 64) = (min 64 rest-size)
		do
		(multiple-value-setq (a b c d)
		  (if (< block-size 64)
		      (md5sum-final-char a b c d block buffer offset
					 block-size length)
		      (md5sum-update-char a b c d block buffer offset)))
		until (< block-size 64))
	  until (< bytes +buffer-size+)
	  finally (return (md5sum-checksum a b c d)))))

(defun md5sum-file (pathname)
  (declare (optimize (speed 3) (space 0) (debug 0)))
  (with-open-file (stream pathname :element-type '(unsigned-byte 8))
    (md5sum-byte-stream stream)))
