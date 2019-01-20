#lang plait

;; Make all "class.rkt" definitions available here, where
;; the "class.rkt" file must be in the same directory
;; as this one:
(require "class.rkt")

(define-type ExpI
  (numI [n : Number])
  (plusI [lhs : ExpI]
         [rhs : ExpI])
  (multI [lhs : ExpI]
         [rhs : ExpI])
  (argI)
  (thisI)
  (newI [class-name : Symbol]
        [args : (Listof ExpI)])
  (getI [obj-expr : ExpI]
        [field-name : Symbol])
  (castI [class-name : Symbol]
         [exp : ExpI])
  (if0I [cnd : ExpI]
        [thn : ExpI]
        [els : ExpI])
  (sendI [obj-expr : ExpI]
         [method-name : Symbol]
         [arg-expr : ExpI])
  (superI [method-name : Symbol]
          [arg-expr : ExpI])
  (nullI)
  (newarrayI (type-name : Symbol)
             (size-expr : ExpI)
             (init-expr : ExpI))
  (arrayrefI (array-expr : ExpI)
             (index-expr : ExpI))
  (arraysetI (array-expr : ExpI)
             (index-expr : ExpI)
             (set-expr : ExpI)))

(define-type ClassI
  (classI [class-name : Symbol]
          [super-name : Symbol]
          [field-names : (Listof Symbol)]
          [methods : (Listof (Symbol * ExpI))]))

(module+ test
  (print-only-errors #t))

;; ----------------------------------------

(define (exp-i->c [a : ExpI] [super-name : Symbol]) : Exp
  (local [(define (recur expr)
            (exp-i->c expr super-name))]
    (type-case ExpI a
      [(numI n) (numE n)]
      [(plusI l r) (plusE (recur l) (recur r))]
      [(multI l r) (multE (recur l) (recur r))]
      [(argI) (argE)]
      [(thisI) (thisE)]
      [(newI class-name field-exprs)
       (newE class-name (map recur field-exprs))]
      [(getI expr field-name)
       (getE (recur expr) field-name)]
      ;; -----------------#2 Change---------------------
      [(castI class-name exp)
       (castE class-name (recur exp))]
      [(if0I cnd thn els)
       (if0E (recur cnd) (recur thn) (recur els))]
      [(nullI) (nullE)]
      [(sendI expr method-name arg-expr)
       (sendE (recur expr)
              method-name
              (recur arg-expr))]
      [(superI method-name arg-expr)
       (ssendE (thisE)
               super-name
               method-name
               (recur arg-expr))]
      [(newarrayI type-name size-expr initial-expr)
       (newarrayE type-name
                  (recur size-expr)
                  (recur initial-expr))]
      [(arrayrefI array-expr index-expr)
       (arrayrefE (recur array-expr)
                  (recur index-expr))]
      [(arraysetI array-expr index-expr set-expr)
       (arraysetE (recur array-expr)
                  (recur index-expr)
                  (recur set-expr))])))



;; ----------------------------------------

(define (class-i->c-not-flat [c : ClassI]) : Class
  (type-case ClassI c
    [(classI class-name super-name field-names methods)
     (classC
      class-name
      super-name
      field-names
      (map (lambda (m)
             (values (fst m)
                     (exp-i->c (snd m) super-name)))
           methods))]))

(module+ test
  (define posn3d-mdist-i-method
    (values 'mdist
            (plusI (getI (thisI) 'z)
                   (superI 'mdist (argI)))))
  (define posn3d-mdist-c-method
    (values 'mdist
            (plusE (getE (thisE) 'z)
                   (ssendE (thisE) 'Posn 'mdist (argE)))))

  (define posn3d-i-class 
    (values 'Posn3D
            (classI
             'Posn3D
             'Posn
             (list 'z)
             (list posn3d-mdist-i-method))))
  (define posn3d-c-class-not-flat
    (values 'Posn3D
            (classC 'Posn3D
                    'Posn
                    (list 'z)
                    (list posn3d-mdist-c-method))))

  (test (class-i->c-not-flat (snd posn3d-i-class))
        (snd posn3d-c-class-not-flat)))

;; ----------------------------------------

(define (flatten-class [name : Symbol]
                       [classes-not-flat : (Listof (Symbol * Class))] 
                       [i-classes : (Listof (Symbol * ClassI))]) : Class
  (type-case Class (find classes-not-flat name)
    [(classC cls-name1 super1 field-names methods)
     (type-case Class (flatten-super name classes-not-flat i-classes)
       [(classC cls-name2 super2 super-field-names super-methods)
        (classC
         cls-name1
         super1
         (add-fields super-field-names field-names)
         (add/replace-methods super-methods methods))])]))

(define (flatten-super [name : Symbol]
                       [classes-not-flat : (Listof (Symbol * Class))] 
                       [i-classes : (Listof (Symbol * ClassI))]) : Class
  (type-case ClassI (find i-classes name)
    [(classI cls-name super-name field-names i-methods)
     (if (equal? super-name 'Object)
         (classC cls-name super-name empty empty)
         (flatten-class super-name
                        classes-not-flat
                        i-classes))]))

(module+ test
  (define posn-i-class
    (values
     'Posn
     (classI 'Posn
             'Object
             (list 'x 'y)
             (list (values 'mdist
                           (plusI (getI (thisI) 'x)
                                  (getI (thisI) 'y)))
                   (values 'addDist
                            (plusI (sendI (thisI) 'mdist (numI 0))
                                   (sendI (argI) 'mdist (numI 0))))))))
  (define addDist-c-method
    (values 'addDist
            (plusE (sendE (thisE) 'mdist (numE 0))
                   (sendE (argE) 'mdist (numE 0)))))
  (define posn-c-class-not-flat
    (values
     'Posn
     (classC 'Posn
             'Object
            (list 'x 'y)
            (list (values 'mdist
                          (plusE (getE (thisE) 'x)
                                 (getE (thisE) 'y)))
                  addDist-c-method))))
  (define posn3d-c-class
    (values 'Posn3D
            (classC 'Posn3D
                    'Posn
                    (list 'x 'y 'z)
                    (list posn3d-mdist-c-method
                          addDist-c-method))))

  (test (flatten-class 'Posn3D
                       (list posn-c-class-not-flat
                             posn3d-c-class-not-flat)
                       (list posn-i-class
                             posn3d-i-class))
        (snd posn3d-c-class)))

;; ----------------------------------------

(define add-fields append)

(define (add/replace-methods [methods : (Listof (Symbol * Exp))]
                             [new-methods : (Listof (Symbol * Exp))])
  : (Listof (Symbol * Exp))
  (cond
    [(empty? new-methods) methods]
    [else (add/replace-methods
           (add/replace-method methods (first new-methods))
           (rest new-methods))]))

(define (add/replace-method [methods : (Listof (Symbol * Exp))] 
                            [new-method : (Symbol * Exp)])
  : (Listof (Symbol * Exp))
  (cond
    [(empty? methods) (list new-method)]
    [else
     (if (equal? (fst (first methods))
                 (fst new-method))
         (cons new-method (rest methods))
         (cons (first methods) 
               (add/replace-method (rest methods)
                                   new-method)))]))
(module+ test
  ;cast
  (test (exp-i->c (castI 'Object (numI 0)) 'Object)
        (castE 'Object (numE 0)))
  ;if0
  (test (exp-i->c (if0I (numI 0) (numI 1) (numI 2)) 'Object)
        (if0E (numE 0) (numE 1) (numE 2)))
  ;null
  (test (exp-i->c (nullI) 'Posn)
        (nullE))
  ;array
  (test (exp-i->c (newarrayI 'Array (numI 0) (numI 1)) 'Object)
        (newarrayE 'Array (numE 0) (numE 1)))
  (test (exp-i->c (arrayrefI (numI 0) (numI 1)) 'Object)
        (arrayrefE (numE 0) (numE 1)))
  (test (exp-i->c (arraysetI (numI 0) (numI 1) (numI 2)) 'Object)
        (arraysetE (numE 0) (numE 1) (numE 2)))
  (test (exp-i->c (numI 10) 'Object)
        (numE 10))
  (test (exp-i->c (newarrayI 'Posn (numI 0) (numI 1)) 'Object)
        (newarrayE 'Posn (numE 0) (numE 1)))
  (test (exp-i->c (arrayrefI (numI 0) (numI 1)) 'Object)
        (arrayrefE (numE 0) (numE 1)))
  (test (exp-i->c (arraysetI (numI 0) (numI 1) (numI 2)) 'Object)
        (arraysetE (numE 0) (numE 1) (numE 2)))
  ;rest
  (test (exp-i->c (plusI (numI 10) (numI 2)) 'Object)
        (plusE (numE 10) (numE 2)))
  (test (exp-i->c (multI (numI 10) (numI 2)) 'Object)
        (multE (numE 10) (numE 2)))
  (test (exp-i->c (argI) 'Object)
        (argE))
  (test (exp-i->c (thisI) 'Object)
        (thisE))
  (test (exp-i->c (newI 'Object (list (numI 1))) 'Object)
        (newE 'Object (list (numE 1))))
  (test (exp-i->c (getI (numI 1) 'x) 'Object)
        (getE (numE 1) 'x))
  (test (exp-i->c (sendI (numI 1) 'mdist (numI 2)) 'Object)
        (sendE (numE 1) 'mdist (numE 2)))
  (test (exp-i->c (superI 'mdist (numI 2)) 'Posn)
        (ssendE (thisE) 'Posn 'mdist (numE 2)))
  (test (add-fields (list 'x 'y) (list 'z))
        (list 'x 'y 'z))

  (test (add/replace-methods empty empty)
        empty)
  (test (add/replace-methods empty (list (values 'm (numE 0))))
        (list (values 'm (numE 0))))
  (test (add/replace-methods (list (values 'm (numE 0))) empty)
        (list (values 'm (numE 0))))
  (test (add/replace-methods (list (values 'm (numE 0)))
                             (list (values 'm (numE 1))))
        (list (values 'm (numE 1))))
  (test (add/replace-methods (list (values 'm (numE 0))
                                   (values 'n (numE 2)))
                             (list (values 'm (numE 1))))
        (list (values 'm (numE 1))
              (values 'n (numE 2))))
  (test (add/replace-methods (list (values 'm (numE 0)))
                             (list (values 'm (numE 1))
                                   (values 'n (numE 2))))
        (list (values 'm (numE 1))
              (values 'n (numE 2))))

  (test (add/replace-method (list (values 'm (numE 0)))
                            (values 'm (numE 1)))
        (list (values 'm (numE 1))))
  (test (add/replace-method (list (values 'm (numE 0)))
                            (values 'n (numE 2)))
        (list (values 'm (numE 0))
              (values 'n (numE 2))))
  
)

;; ----------------------------------------

(define (interp-i [i-a : ExpI] [i-classes : (Listof (Symbol * ClassI))]) : Value
  (local [(define a (exp-i->c i-a 'Object))
          (define classes-not-flat
            (map (lambda (i)
                   (values (fst i)
                           (class-i->c-not-flat (snd i))))
                 i-classes))
          (define classes
            (map (lambda (c)
                   (let ([name (fst c)])
                     (values name
                             (flatten-class name classes-not-flat i-classes))))
                 classes-not-flat))]
    (interp a classes (objV 'Object empty) (numV 0))))

(module+ test
  (test (interp-i (numI 0) empty)
        (numV 0))

  (test (interp-i
         (sendI (newI 'Posn3D (list (numI 5) (numI 3) (numI 1)))
                'addDist
                (newI 'Posn (list (numI 2) (numI 7))))
         (list posn-i-class
               posn3d-i-class))
        (numV 18)))
