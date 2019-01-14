#lang plait

(define-type Exp
  (numE [n : Number])
  (plusE [lhs : Exp]
         [rhs : Exp])
  (multE [lhs : Exp]
         [rhs : Exp])
  (argE)
  (thisE)
  (newE [class-name : Symbol]
        [args : (Listof Exp)])
  (getE [obj-expr : Exp]
        [field-name : Symbol])
  (castE [class-name : Symbol]
         [exp : Exp])
  (if0E [cnd : Exp]
        [thn : Exp]
        [els :  Exp])
  (sendE [obj-expr : Exp]
         [method-name : Symbol]
         [arg-expr : Exp])
  (ssendE [obj-expr : Exp]
          [class-name : Symbol]
          [method-name : Symbol]
          [arg-expr : Exp])
  (newarrayE [type-name : Symbol]
             [size : Exp]
             [initial : Exp])
  (arrayrefE [array : Exp]
             [index : Exp])
  (arraysetE [array : Exp]
             [index : Exp]
             [arg : Exp])
  (nullE))

(define-type Class
  (classC [class-name : Symbol]
          [super : Symbol]
          [field-names : (Listof Symbol)]
          [methods : (Listof (Symbol * Exp))]))

(define-type Value
  (numV [n : Number])
  (objV [class-name : Symbol]
        [field-values : (Listof Value)])
  (nullV)
  (arrayV [type-name : Symbol]
          [value-list : (Listof (Boxof Value))]))

(define-type Type
  (numT)
  (objT (class-name : Symbol))
  (arrayT (type : Type))
  (nullT))



(module+ test
  (print-only-errors #t))

;; ----------------------------------------
(define (find [l : (Listof (Symbol * 'a))] [name : Symbol]) : 'a
  (type-case (Listof (Symbol * 'a)) l
    [empty
     (error 'find (string-append "not found: " (symbol->string name)))]
    [(cons p rst-l)
     (if (symbol=? (fst p) name)
         (snd p)
         (find rst-l name))]))


(define (find-class [l : (Listof (Symbol * 'a))] [name : Symbol])
  (find l name))


(module+ test
  (test (find (list (values 'a 1)) 'a)
        1)
  (test (find (list (values 'a 1) (values 'b 2)) 'b)
        2)
  (test/exn (find empty 'a)
            "not found: a")
  (test/exn (find (list (values 'a 1)) 'x)
            "not found: x"))


;; ----------------------------------------

(define interp : (Exp (Listof (Symbol * Class)) Value Value -> Value)
  (lambda (a classes this-val arg-val)
    (local [(define (apply-array array-expr index-expr function)
              (type-case Value (recur index-expr)
                [(numV num) (cond
                              [(< num 0) (error 'interp "index can't be negative")]
                              [else
                               (local [(define array-value (recur array-expr))]
                                 (type-case Value array-value
                                   [(arrayV type-name value-list) (function type-name value-list num)]
                                   [else (error 'interp "must be array")]))])]
                [else (error 'interp "not a number")]))
                
            (define (recur expr)
              (interp expr classes this-val arg-val))]
      (type-case Exp a
        [(numE n) (numV n)]
        [(plusE l r) (num+ (recur l) (recur r))]
        [(multE l r) (num* (recur l) (recur r))]
        [(thisE) this-val]
        [(argE) arg-val]
        [(newE class-name field-exprs)
         (local [(define c (find-class classes class-name))
                 (define vals (map recur field-exprs))]
           (if (= (length vals) (length (classC-field-names c)))
               (objV class-name vals)
               (error 'interp "wrong field count")))]
        [(getE obj-expr field-name)
         (type-case Value (recur obj-expr)
           [(objV class-name field-vals)
            (type-case Class (find classes class-name)
              [(classC cls-name super field-names methods)
               (find (map2 (lambda (n v) (values n v))
                           field-names
                           field-vals)
                     field-name)])]
           [else (error 'interp "not an object")])]
        [(sendE obj-expr method-name arg-expr)
         (local [(define obj (recur obj-expr))
                 (define arg-val (recur arg-expr))]
           (type-case Value obj
             [(objV class-name field-vals)
              (call-method class-name method-name classes
                           obj arg-val)]
             [else (error 'interp "not an object")]))]
        [(ssendE obj-expr class-name method-name arg-expr)
         (local [(define obj (recur obj-expr))
                 (define arg-val (recur arg-expr))]
           (call-method class-name method-name classes
                        obj arg-val))]
        [(castE class-name arg-expr)
         (let ([value (recur arg-expr)])
           (type-case Value value
             [(objV class-name2 field-values)
              (cond
                [(instance-of? class-name2 class-name classes)
                 value]
                [else (error 'interp "not an instance")])]
             [(nullV) value]
             [else (error 'interp "not an object")]))]
        [(if0E cnd thn els)
         (let ([num-value (recur cnd)])
           (type-case Value num-value
             [(numV num)
              (cond
                [(= 0 num) (recur thn)]
                [else (recur els)])]
             [else (error 'interp "not a number")]))]
        [(nullE) (nullV)]
        [(newarrayE type-name size-expr initial-expr)
         (type-case Value (recur size-expr)
           [(numV num) (cond
                         [(< num 0) (error 'interp "size can't be negative")]
                         [else (arrayV type-name (initial-array num (recur initial-expr)))])]
           [else (error 'interp "not a number")])]
        [(arrayrefE array-expr index-expr)
         (apply-array array-expr index-expr
                      (lambda (type-name values index-expr) (get-array values index-expr)))]
        [(arraysetE array-expr index-expr exp)
         (apply-array array-expr index-expr
                      (lambda (type-name values index) (local [(define value (recur exp))]
                                                         (type-case Value value
                                                           [(objV class-name field-values)
                                                            (cond
                                                              [(instance-of? class-name type-name classes)
                                                               (begin
                                                                 (set-array values index value)
                                                                 (numV 0))]
                                                              [else (error 'interp "array")])]
                                                           [else (error 'interp "not an object")]))))]))))

(define (search-array values index function)
  (cond
    [(empty? values) (error 'interp "array")]
    [(equal? index 0) (function (first values))]
    [else (search-array (rest values) (- index 1) function)]))


(define (get-array values index)
  (search-array values index (lambda (a) (unbox a))))


(define (set-array values index set-val)
  (search-array values index (lambda (b) (set-box! b set-val))))

(define (initial-array size initial-value)
  (cond
    [(equal? size 0) empty]
    [else (cons (box initial-value) (initial-array (- size 1) initial-value))]))

(define (find* [get-name : ('a -> Symbol)])
  (lambda ([name : Symbol] [val-list : (Listof 'a)])
    (cond
      [(empty? val-list)
       (error 'find "not found")]
      [else (if (equal? name (get-name (first val-list)))
                (first val-list)
                ((find* get-name) name (rest val-list)))])))


                          
;; -----------------#2 Change---------------------        
(define (instance-of? [class-name : Symbol]
                      [parent-name : Symbol]
                      [classes : (Listof (Symbol * Class))])
  (cond
    [(equal? class-name parent-name) #t]
    [else
     (type-case Class (find classes class-name)
       [(classC cls-name super field-names methods)
        (instance-of? super parent-name classes)])]))
           
(define (call-method class-name method-name classes
                     obj arg-val)
  (type-case Class (find-class classes class-name)
    [(classC cls-name super field-names methods)
     (let ([body-expr (find methods method-name)])
       (interp body-expr
               classes
               obj
               arg-val))]))

(define (num-op [op : (Number Number -> Number)]
                [op-name : Symbol] 
                [x : Value]
                [y : Value]) : Value
  (cond
    [(and (numV? x) (numV? y))
     (numV (op (numV-n x) (numV-n y)))]
    [else (error 'interp "not a number")]))

(define (num+ x y) (num-op + '+ x y))
(define (num* x y) (num-op * '* x y))

;; ----------------------------------------
;; Examples



(module+ test
  (define object
    (values 'Null
            (classC
             'Object
             'b
             empty
             empty)))
  
  (define posn-class 
    (values 'Posn
            (classC
             'Posn
             'Object
             (list 'x 'y)
             (list (values 'mdist
                           (plusE (getE (thisE) 'x) (getE (thisE) 'y)))
                   (values 'addDist
                           (plusE (sendE (thisE) 'mdist (numE 0))
                                  (sendE (argE) 'mdist (numE 0))))
                   (values 'addX
                           (plusE (getE (thisE) 'x) (argE)))
                   (values 'multY (multE (argE) (getE (thisE) 'y)))
                   (values 'factory12 (newE 'Posn (list (numE 1) (numE 2))))))))
    
  (define posn3D-class
    (values 'Posn3D
            (classC
             'Posn3D
             'Posn
             (list 'x 'y 'z)
             (list (values 'mdist (plusE (getE (thisE) 'z)
                                         (ssendE (thisE) 'Posn 'mdist (argE))))
                   (values 'addDist (ssendE (thisE) 'Posn 'addDist (argE)))))))

  (define object-class
    (values 'Object
            (classC
             'Object
             'b
             empty
             empty)))

  (define posn27 (newE 'Posn (list (numE 2) (numE 7))))
  (define posn531 (newE 'Posn3D (list (numE 5) (numE 3) (numE 1))))
  (define posn828 (newE 'Posn (list (numE 8) (numE 28))))
  (define posn42432 (newE 'Posn3D (list (numE 4) (numE 24) (numE 32))))

  (define (interp-posn a)
    (interp a (list posn-class posn3D-class) (numV -1) (numV -1))))

;; ----------------------------------------

(module+ test

  
  (test/exn (interp-posn (newarrayE 'Posn posn27 (numE 9)))
            "not a number")
  (test (interp-posn (newarrayE 'Posn (numE 2) posn27))
        (arrayV 'Posn (list (box (objV 'Posn (list (numV 2) (numV 7)))) (box (objV 'Posn (list (numV 2) (numV 7)))))))
  (test (interp-posn (newarrayE 'Posn (numE 2) posn27))
        (arrayV 'Posn (list (box (objV 'Posn (list (numV 2) (numV 7)))) (box (objV 'Posn (list (numV 2) (numV 7)))))))
  (test (interp-posn (arrayrefE (newarrayE 'Posn (numE 2) posn27) (numE 0)))
        (interp-posn posn27))
  (test/exn (interp-posn (arrayrefE (newarrayE 'Posn (numE 0) posn27) (numE 0)))
            "array")

  (test/exn (interp-posn (arrayrefE (newarrayE 'Posn (numE 2) posn27) posn828))
        "not a number")
  (test/exn (interp-posn (arraysetE posn27 posn828 posn828))
            "not a number")
  (test/exn (interp-posn (arraysetE posn27 posn828 (numE 0)))
            "not a number") 
  (test/exn (interp-posn (arrayrefE (newarrayE 'Posn (numE 2) posn27) (numE -1)))
        "negative")
  ; Need here to show is imperative
  (test (interp-posn (arraysetE (newarrayE 'Posn (numE 2) posn27) (numE 0) posn828))
        (numV 0))
  (test/exn (interp-posn (arraysetE posn27 (numE 0) posn828))
        "array") 
  (test/exn (interp-posn (newarrayE 'Posn (numE -1) posn27))
            "can't be negative")
  (test/exn (interp-posn (arraysetE (newarrayE 'Posn (numE 2) posn27) (numE 0) (numE 0)))
            "not an object")
  
  (test (interp (numE 10) 
                empty (objV 'Object empty) (numV 0))
        (numV 10))
  
  (test (interp (nullE) 
                empty (objV 'Object empty) (numV 0))
        (nullV))
  (test/exn (interp-posn (getE (nullE) 'x))
            "not an object")
;  (test/exn (interp-posn (arraysetE (newarrayE 'Posn3D (numE 2) posn42432) (numE 3) posn27))
;            "not an instance")

  (test (interp (if0E (numE 0) posn828 posn27)
                (list posn-class posn3D-class) (objV 'Object empty) (numV 0))
        (interp-posn posn828))
  (test (interp (if0E (numE 1) posn828 posn27)
                (list posn-class posn3D-class) (objV 'Object empty) (numV 0))
        (interp-posn posn27))
  (test/exn (interp (if0E posn828 posn828 posn27)
                 (list posn-class posn3D-class) (objV 'Object empty) (numV 0))
         "not a number")
        

  (test (interp-posn (castE 'Posn posn531))
        (objV 'Posn3D (list (numV 5) (numV 3) (numV 1))))
  (test (interp-posn (castE 'Posn posn27))
        (objV 'Posn (list (numV 2) (numV 7))))
  (test/exn (interp-posn (castE 'Posn3D posn27))
              "not")
  (test/exn (interp-posn (castE 'Number (numE 1)))
            "not an object")
  (test (interp-posn (castE 'Posn (nullE)))
        (nullV))
  
  (test (interp (plusE (numE 10) (numE 17))
                empty (objV 'Object empty) (numV 0))
        (numV 27))
  (test (interp (multE (numE 10) (numE 7))
                empty (objV 'Object empty) (numV 0))
        (numV 70))

  (test (interp-posn (newE 'Posn (list (numE 2) (numE 7))))
        (objV 'Posn (list (numV 2) (numV 7))))

  (test (interp-posn (sendE posn27 'mdist (numE 0)))
        (numV 9))
  
  (test (interp-posn (sendE posn27 'addX (numE 10)))
        (numV 12))

  (test (interp-posn (sendE (ssendE posn27 'Posn 'factory12 (numE 0))
                            'multY
                            (numE 15)))
        (numV 30))

  (test (interp-posn (sendE posn531 'addDist posn27))
        (numV 18))
  
  (test/exn (interp-posn (plusE (numE 1) posn27))
            "not a number")
  (test/exn (interp-posn (getE (numE 1) 'x))
            "not an object")

  (test/exn (interp-posn (sendE (numE 1) 'mdist (numE 0)))
            "not an object")
  (test/exn (interp-posn (ssendE (numE 1) 'Posn 'mdist (numE 0)))
            "not an object")
  (test/exn (interp-posn (newE 'Posn (list (numE 0))))
            "wrong field count")
    (test (interp (newarrayE 'num (numE 3) (numE 1)) empty (numV -1) (numV -1))
        (arrayV 'num (list (box (numV 1)) (box (numV 1)) (box (numV 1)))))
  (test/exn (interp (newarrayE 'num (numE -1) (numE 1)) empty (numV -1) (numV -1))
            "negative")

  (test (interp (newarrayE 'NumType (numE 1) (numE 2)) empty (numV -1) (numV -1))
        (arrayV 'NumType (list (box (numV 2)))))

  
  (test (interp (arrayrefE (newarrayE 'num (numE 3) (numE 1)) (numE 1)) empty (numV -1) (numV -1))
        (numV 1))
  (test (interp (arrayrefE (newarrayE 'num (numE 3) (numE 1)) (numE 2)) empty (numV -1) (numV -1))
        (numV 1))
  (test/exn (interp (newarrayE 'num (numE -1) (numE 1)) empty (numV -1) (numV -1))
            "negative")
  

  (test (interp-posn (arraysetE (newarrayE 'Posn (numE 2) posn27) (numE 1) posn27))
        (numV 0))
  )
