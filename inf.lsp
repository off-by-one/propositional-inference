;;;; Inference Machine
;;;; Author: Vlad

;;; Two data structures - a knowledge base list, and an inference set
;;; Both are conceptually a kb, as described below
;;; 
;;; <kb>     ::= '( <clause> ... )
;;; <clause> ::= '( <lit> ... )
;;; <lit>    ::= '( <var> ) | '(not <var>)
;;;
;;; To be interpreted as
;;; <kb> = <clause-0> ^ <clause-1> ^ <clause-2> ^ ...
;;; <clause-i> = <lit-1> v <lit-2> v <lit-3> v ...
;;;
;;; Knowledge base list represents kb as an actual list
;;; Inference set represents kb as a hash map with 't values
;;;
;;; Basic usage is (print-knowledge (make-inferences (read-kbdb "filename")))
;;; Knowledge base must have one clause per line, example:
;;;   ((not A) (B) (C))
;;;   ((not C) (D))
;;;   ((not D) (Q))
;;; 
;;; TODO: Read actual CNF files
;;;       Improve efficiency with an ordered set type, to avoid dup inferences
;;;       If possible improve loop constructs

(defun square (x) (* x x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hash set manipulators ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun putset (k s) (setf (gethash k s) 't) s)
(defun remset (k s) (setf (gethash k s) nil) s)
(defun getset (k s) (gethash k s))

(defun has-union-list-set (l s)
  (loop for i in l if (getset i s) return 't))

(defun insert-list-set (l s)
  (loop for i in l do (putset i s) finally (return s)))

(defun subtract-list-set (l s)
  (loop for i in l if (not (getset i s)) collect i))

(defun set-to-list (s)
  (loop for e being the hash-keys of s unless (equal e 'new-inf) collect e))

(defun list-to-set (l)
  (let ((s (make-hash-table :test #'equal :size (square (length l)))))
      (loop for e in l do (putset e s) finally (return s))))

;;;;;;;;;;;;;;;;;;;;;;;; CNF specification utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun negated (lit)
  (equal (car lit) 'not))

(defun negate (lit)
  (if (negated lit)
    (cdr lit)
    (cons 'not lit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;; CNF cleanup utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; compares literals, lit-a < lit-b
(defun literal-lessp (lit-a lit-b)
  (cond ((and (negated lit-a) (not (negated lit-b))) 0)
        ((and (not (negated lit-a)) (negated lit-b)) nil)
        ((and (negated lit-a) (negated lit-b))
           (string< (cadr lit-a) (cadr lit-b)))
        (t (string< (car  lit-a) (car  lit-b)))))

;; cleans duplicates and tautologies (~A v A) from a clause
(defun clean-clause (clause)
  (if (null clause) nil
    (let* ((fst (car clause))
           (rst (cdr clause))
           (is-fst #'(lambda (x) (equal x fst)))
           (is-neg #'(lambda (x) (equal x (negate fst))))
           (is-fst-or-neg #'(lambda (x) (or (equal x fst)
                                            (equal x (negate fst))))))
        (cond ((member-if is-neg (cdr clause))
                 (clean-clause (remove-if is-fst-or-neg clause)))
              ((member-if is-fst (cdr clause))
                 (cons fst (clean-clause (remove-if is-fst rst))))
              (t (cons (car clause) (clean-clause (cdr clause))))))))

;; standard form is ~A ^ ~B ^ ~C ^ .. X ^ Y ^ Z ^ ...
(defun standard-clausal-form (clause)
  (clean-clause (sort clause #'literal-lessp)))

(defun standard-knowledge-form (kb)
  (remove-duplicates (remove-if #'null kb) :test #'equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;; Start clause iterator ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; both left and right clauses are lists of literals
(defun infer-on-clauses (cl-l cl-r)
  (loop for sub-cl-l on cl-l
        for lft-iter from (length cl-l) downto 1
        append
          (remove-if #'null
            (loop for sub-cl-r on cl-r
                  for rgt-iter from (length cl-r) downto 1
                  if (equal (car sub-cl-l) (negate (car sub-cl-r)))
                  collect
                    (standard-clausal-form
                      (append (butlast cl-l lft-iter)
                              (butlast cl-r rgt-iter) 
                              (cdr sub-cl-l) (cdr sub-cl-r)))))))

;; kb is a list representation of a knowledge base, infs is a set of inferences
(defun infer-myopic (kb infs)
  (loop for cl in kb
        for new-infs =
          (loop for key being the hash-keys of infs
               for new-infs = (subtract-list-set (infer-on-clauses cl key) infs)
                unless (null new-infs)
                append new-infs into all-infs 
                finally (return all-infs))
        unless (null new-infs)
        append new-infs into all-infs
        finally (return all-infs)))

;; kb is a list representation of a knowledge base, infs is a set of inferences
(defun infer-complete (kb infs)
  (loop for new-infs = (infer-myopic kb infs)
        while new-infs
        do (insert-list-set new-infs infs)
        finally (return infs)))
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;; End clause Iterator ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; populate inference table, and then complete inferences
(defun make-inferences (kb)
  (let ((init-infs (list-to-set (infer-myopic kb (list-to-set kb)))))
    (set-to-list (infer-complete kb init-infs))))

;; read a database from a file
(defun read-kbdb (filename)
  (standard-knowledge-form
    (map 'list #'standard-clausal-form
      (with-open-file (stream filename)
        (loop for line = (read stream nil 'foo)
              until (eq line 'foo) collect line)))))

(defun print-knowledge (l)
  (length (map 'list #'(lambda (l) (format T "~{~a ~}~C" l #\newline)) l)))

