#lang racket

; протип:
; правете всичките си ламбди с един аргумент

; примери за естествени числа, кодирани чрез ламбда функции
; (чърч кодиране/нумерали на чърч)

; ще симулираме пеанови естествени числа, т.е. ето тази "дефиниция" на естествените числа

; 0. има нещо което се казва z и нещо което се казва s
; 1. z е естествено число
; 1. ако <нещо> е естествено число, то и (s <нещо>) също е естествено число

; с други думи искаме z да съответства на 0, а s на събиране с 1
; и всички останали естествени числа да представим като голям брой пъти 1 + 1 + 1 + 1 + ... 1 + 0
; (s брои колко пъти прибавяме 1)

; същото нещо ще направим и тук - броенето ни (s) ще е колко пъти сме приложили функция към аргумент
; а самият аргумент ще е "нулата"
; по конвенция винаги f ще ни е функцията която пролагаме а v ще кръщаваме константата която съответства на нула

; нула
(define czero
  (lambda (f)
    (lambda (v)
      v)))

; едно
(define cone
  (lambda (f)
    (lambda (v)
      (f v))))

; две
(define ctwo
  (lambda (f)
    (lambda (v)
      (f (f v)))))


; ПРИМЕРИ
(define 1+ (lambda (n) (+ 1 n)))

; разписване

; обръщане от и до
(define (nat-to-scm n)
  ((n 1+) 0))

; разписване

(define csucc
  (lambda (n)
    (lambda (f)
      (lambda (v)
        (f ((n f) v))))))

; разписване

; забележете че трябва два пъти да извикаме `n`, щото все пак са два ламбди и в скийм има разлика между
; A x A -> A
; и
; A -> (A -> A)

; грешно нарочно?
(define (nat-from-scm n)
  (if (= 0 n)
      czero
      (csucc (nat-from-scm (- n 1)))))

; "директен" vs "недиректен" подход
(define cplus
  (lambda (n)
    (lambda (m)
      (lambda (f)
        (lambda (v)
          ((n f) ((m f) v)))))))

; (nat-to-scm ((cplus ctwo) ctwo))
;n = cone = \f.\v. (f v)
;m = ctwo = \f.\v. (f (f v))
;cplus n m
;->
;\f.\v. cone f ctwo ->
;\f.\v. f ctwo ->
;
;\f.\v. f (f (f v))


; разписване?

(define cplus-another
  (lambda (n)
    (lambda (m)
      ((n csucc) m))))

; (nat-to-scm ((cplus (nat-from-scm 5)) (nat-from-scm 15)))
; (nat-to-scm ((cplus-another (nat-from-scm 5)) (nat-from-scm 15)))

; =====================
; foldr кодирани списъци (foldr-али???)

; show lists as a parallel with natural numbers
; in haskell
; data Nat = Zero | Succ Nat
;
; Zero
;
; (lambda (f)
;   (lambda (v)
;     v))
;
;
;  (Succ (Succ (Succ Zero)))
;
;  (lambda (f)
;    (lambda (v)
;      (f (f (f v)))))
;
;
;data List = Nil | Cons Int List
;
; Nil
;
; k*
; (lambda (f)
;   (lambda (v)
;     v))
;
; Succ Zero
;
; (Cons 0 Nil)

; (lambda (f)
;   (lambda (v)
;     (f czero v)))
;
;
;(Cons 0 (Cons 1 (Cons 2 Nil)))

; (lambda (f)
;   (lambda (v)
;     ((f 0) ((f 1) ((f 2) v)))))

(define cnil
  (lambda (f)
    (lambda (v)
      v)))

; (ccons cnil 1 ->
(lambda (f)
  (lambda (v)
    ((f 1) v)))
; ((ccons 2) ((ccons 1) nil)) ->
(lambda (f)
  (lambda (v)
    ((f 2) ((f 1) v))))

(define ccons
  (lambda (x)
    (lambda (xs)
      (lambda (f)
        (lambda (v)
          ((f x) ((xs f) v)))))))

; 1 2 3 -> 6
; '(1 2 3)

; ((+) 1 ((+) 2 ((+) 3 0)))
; (f   1 (f   2 (f   3 v)))
; f -> cplus
; v -> czero

(define csum
  (lambda (xs)
    ((xs cplus) czero)))


; =====================
; Нумерали на Чърч
;(nat-to-scm
;  (csum ((ccons 5) cnil)))
; УПРАЖНЕНИЕ: Умножение
; ПРИМЕРИ:
(define cmult
  (lambda(m)
    (lambda(n)
      ((m (cplus n)) czero))))

;(nat-to-scm ((cmult (nat-from-scm 1)) (nat-from-scm 3))) ;-- 3
;(nat-to-scm ((cmult (nat-from-scm 1)) (nat-from-scm 0))) ;-- 0
;(nat-to-scm ((cmult (nat-from-scm 23)) (nat-from-scm 3)));-- 69
;(nat-to-scm ((cmult (nat-from-scm 21)) (nat-from-scm 2))) ;-- 42


; УПРАЖНЕНИЕ: Повдигане на степен
; ПРИМЕРИ:
(define cexp
  (lambda(m)
    (lambda (n)
      ((n (cmult m)) cone))))

;(nat-to-scm ((cexp (nat-from-scm 3)) (nat-from-scm 1))) ; -- 3
;(nat-to-scm ((cexp (nat-from-scm 2)) (nat-from-scm 10))); -- 1024
;(nat-to-scm ((cexp (nat-from-scm 0)) (nat-from-scm 10))); -- 0
;(nat-to-scm ((cexp (nat-from-scm 30)) (nat-from-scm 0))); -- 0

; =====================
; Чърч кодирани булеви стойности (бинерали на Чърч?)

; true
(define ctt
  (lambda (t)
    (lambda (f)
      t)))

; false
(define cff
  (lambda (t)
    (lambda (f)
      f)))

; if
(define cif
  (lambda (b)
    (lambda (t)
      (lambda (e)
        ((b t) e)))))

; УПРАЖНЕНИЕ: Конвертиране от бинерали към булеви стойности на скийм
; ПРИМЕРИ:
; (bool-to-scm ctt) -- #t
; (bool-to-scm cff) -- #f
(define (bool-to-scm b)
  (((cif b) #t) #f))

; УПРАЖНЕНИЕ: Конвертиране от булеви стойности на скийм към бинерали
; ПРИМЕРИ:
; (((bool-from-scm #t) 5) 3) -- 5
; (((bool-from-scm #f) 5) 3) -- 3
(define (bool-from-scm b)
  (if b
       ctt
       cff))

;(((bool-from-scm #t) 5) 3)
;(((bool-from-scm #f) 5) 3)
; УПРАЖНЕНИЕ: Отрицание на булеан
; ПРИМЕРИ:
; (bool-to-scm (cnot ctt)) -- #f
; (bool-to-scm (cnot (cnot ctt))) -- #t
(define cnot
  (lambda (b) (((cif b) cff) ctt)))

;(bool-to-scm (cnot ctt)) 
;(bool-to-scm (cnot (cnot ctt)))

; УПРАЖНЕНИЕ: Четност
; ПРИМЕРИ:
; (bool-to-scm (ceven (nat-from-scm 0))) -- #t
; (bool-to-scm (ceven (nat-from-scm 1337))) -- #f
; (bool-to-scm (ceven (nat-from-scm 8))) -- #t
(define ceven
  (lambda (n)
    ((n cnot) ctt)))

;(bool-to-scm (ceven (nat-from-scm 0)))
;(bool-to-scm (ceven (nat-from-scm 1337)))
;(bool-to-scm (ceven (nat-from-scm 8)))

; =====================
; СПИСЪЦИ
; тук можете да ползвате и скиймски стойности вътре в списъците!
; по-лесно е за тестване понякога

; УПРАЖНЕНИЕ: Произведението на числата в списък
; ПРИМЕРИ:
; (nat-to-scm (cprod cnil)) -- 1
; (nat-to-scm (cprod ((ccons ctwo) ((ccons ctwo) cnil)))) -- 4
; (nat-to-scm (cprod ((ccons ctwo) ((ccons ctwo) ((ccons ctwo) cnil))))) -- 8
(define cprod
  (lambda (l)
    ((l cmult) cone)))

;(nat-to-scm (cprod cnil))
;(nat-to-scm (cprod ((ccons ctwo) ((ccons ctwo) cnil))))
;(nat-to-scm (cprod ((ccons ctwo) ((ccons ctwo) ((ccons ctwo) cnil)))))


; HINT: Откраднете вдъхновение от csum

; Полезно за после:
; Функция която взима три аргумента и връща първия.
(define k3
  (lambda (x)
    (lambda (y)
      (lambda (z)
        x))))

; УПРАЖНЕНИЕ: Проверка за празен списък
; Проверете дали подаденият списък е празен.
; Имайте предвид колко аргумента взимат функциите в нашето представяне на списъци.
; ПРИМЕРИ:
;(bool-to-scm (cnil? cnil)) -- #t
;(bool-to-scm (cnil? ((ccons cnil) cnil))) -- #f
(define cnil?
  (lambda(xs)    ;(f 1 (f 2 (f 3 ((f 5) ctt))))
    ((xs (lambda (x) (lambda (y) cff))) ctt))) 

;(bool-to-scm (cnil? cnil))
;(bool-to-scm (cnil? ((ccons cnil) cnil))) 
; Полезно за после:
; Скиймският `cons`, но curry-нат.
(define curried-cons
  (lambda (x) (lambda (y) (cons x y))))

; УПРАЖНЕНИЕ: Конвертирайте foldr-ал към скиймски списък
; ПРИМЕРИ:
; (list-to-scm cnil) -- '()
; (list-to-scm ((ccons 6) cnil)) -- '(6)
; (list-to-scm ((ccons 6) ((ccons 9) cnil))) -- '(6 9)
(define (list-to-scm xs)
  ((xs curried-cons) '()))

;(list-to-scm cnil)
;(list-to-scm ((ccons 6) cnil))
;(list-to-scm ((ccons 6) ((ccons 9) cnil))) 

; HINT:
; Възползвайте се от структурата на foldr-алите, както се възползвахме от
; структурата при естествените числа за съответната ѝ функция!

; УПРАЖНЕНИЕ: Конвертирайте от скийсмки списък към foldr-ал
; ПРИМЕРИ:
(define (list-from-scm xs)
  (if(equal? xs '())
    cnil
    ((ccons (car xs)) (list-from-scm (cdr xs)))))

;(list-to-scm (list-from-scm '(0))); -- '(0)
;(list-to-scm (list-from-scm '(1)));-- '(1)
;(list-to-scm (list-from-scm '(1 3 3 7))); -- '(1 3 3 7)
;
; HINT:
; Използвайте cnil и ccons

; УПРАЖНЕНИЕ: Дължина на foldr-ал
; ПРИМЕРИ:

;Idea eat the element and put a function that does 1+ whith th next
(define clength
  (lambda (xs)
    ((xs (lambda(x) (cplus cone))) czero)))

;(nat-to-scm (clength (list-from-scm '()))) ;-- 0
;(nat-to-scm (clength (list-from-scm '(1 2)))); -- 2

; УПРАЖНЕНИЕ: Генериране на списък с нумералите от подадения нумерал до cnil
; (редът не е задължително да е нарастващ или намаляващ)
; ПРИМЕРИ: (f (f (f (f (lambda(v) (ccons (clength v)) v)))))
;(nat-to-scm (clength (cto-zero (nat-from-scm 13)))) ;-- 13
;(map nat-to-scm (list-to-scm (cto-zero (nat-from-scm 10)))) ;-- '(10 9 8 7 6 5 4 3 2 1)
;(map nat-to-scm (list-to-scm (cto-zero (nat-from-scm 0)))) ;-- '()

; The example is wrong. This implementation is correct
(define cto-zero
  (lambda (x)
    ((x (lambda(v) ((ccons (clength v)) v))) cnil)))

;(define cto-zero
;  (lambda (x)
;    ((x (lambda(v) ((ccons ((cplus cone)(clength v))) v))) cnil)))

;(nat-to-scm (clength (cto-zero (nat-from-scm 13))))
;(map nat-to-scm (list-to-scm (cto-zero (nat-from-scm 10))));
;(map nat-to-scm (list-to-scm (cto-zero (nat-from-scm 0)))) 


; HINT:
; Помислете как да да използвате "резултата от рекурсивното извикване",
; което ви предоставя нумералът n като аргумент, за да разберете "на кое естествено число сте в момента".

; УПРАЖНЕНИЕ: Факториел
; Възползвайте се от cto-zero и cprod
; ПРИМЕРИ:
;(nat-to-scm (cfact (nat-from-scm 0))) -- 1
;(nat-to-scm (cfact (nat-from-scm 5))) -- 120
;(nat-to-scm (cfact (nat-from-scm 10))) -- 3628800

(define cfact
  (lambda (x)
    (((cto-zero x) (lambda(v)(cmult((cplus cone) v)))) cone)))

;(nat-to-scm (cfact (nat-from-scm 0)))
;(nat-to-scm (cfact (nat-from-scm 5)))
;(nat-to-scm (cfact (nat-from-scm 10))) 
; УПРАЖНЕНИЕ: foldr за foldr-али
; ПРИМЕР:
(define cfoldr
  (lambda (x) ;cplus
    (lambda (y) ;czero
      (lambda (l) ((l x) y))))) ;list 

; (nat-to-scm (((cfoldr cplus) czero) ((ccons ctwo) ((ccons (csucc ctwo)) cnil)))) ; -- 5
; HINT: Откраднете вдъхновение от това как cif се отнася към бинералите.

; Може би полезно за после.
(define (compose f) (lambda (g) (lambda (x) (f (g x)))))

; УПРАЖНЕНИЕ: map за foldr-али
; ПРИМЕРИ:
; (list-to-scm ((cmap 1+) (list-from-scm '(1 2 3)))) -- '(2 3 4)
; (map nat-to-scm (list-to-scm ((cmap csucc) (list-from-scm (map nat-from-scm '(41 68)))))) -- '(42 69)
(define cmap 
  (lambda (f)
    ((cfoldr (lambda(v) (lambda(xs) ((ccons (f v)) xs)))) cnil)))
; HINT: Помислете как да реализирате map използвайки foldr
;(list-to-scm ((cmap 1+) (list-from-scm '(1 2 3)))) ; -- '(2 3 4)
;(map nat-to-scm (list-to-scm ((cmap csucc) (list-from-scm (map nat-from-scm '(41 68)))))) 

(define i (lambda (x) x))

; УПРАЖНЕНИЕ: filter за foldr-али
; Приемете че подадената функция връща бинерал.
; ПРИМЕР:
; (map nat-to-scm (list-to-scm ((cfilter ceven) (cto-zero (nat-from-scm 10))))) -- '(10 8 6 4 2)
(define cfilter
  (lambda (p?)
    ((cfoldr (lambda(v) (lambda(xs) (((cif (p? v)) ((ccons v) xs)) xs)))) cnil)))

; (map nat-to-scm (list-to-scm ((cfilter ceven) (cto-zero (nat-from-scm 10))))) 
; HINT: Помислете как да реализирате filter използвайки foldr.

; УПРАЖНЕНИЕ: foldl за foldr-али (uh-oh)
; Помислете как да имплементиранте foldl чрез foldr, използвайки композиция на функции като операцията за сгъване.
; (f 0 ( f 2 ( f 5 ((f 6) cnil))))
; (6 (cnil x))) (0 (...) x) (x (0 (..)))
; (f (g x))
(define cfoldl
 (lambda (f)
   (lambda (x)
     (cfoldr ((compose (f x)))))))
 
;(nat-to-scm (((cfoldl cplus) czero) ((ccons ctwo) ((ccons (csucc ctwo)) cnil)))) ; --5
; УПРАЖНЕНИЕ: reverse за foldr-али (uh-oh)
; Помислете как да имплементиранте reverse чрез foldl
(define creverse
  void)


;chyp for homework
(define chyp 
  (lambda (m)
    (lambda (n)
      ((n m) m))))

(define c0
  (lambda (f)
    (lambda (v) v)))

(define cs
  (lambda (n)
    (lambda (f)
      (lambda (x)
        (f ((n f) x))))))

(define ctrue
  (lambda (x)
    (lambda (y) x)))

(define cfalse
  (lambda (x)
    (lambda (y) y)))

(define cconsT
  (lambda (x)
    (lambda (y)
      (lambda (z)
        ((z x) y)))))

(define ccar
  (lambda (p) (p ctrue)))

(define ccdr
  (lambda (p) (p cfalse)))

(define cp
  (lambda (n)
    (ccdr
     ((n
       (lambda (p)
         ((cconsT
           (cs (ccar p)))
          (ccar p))))
      ((cconsT c0) c0)))))

(define c=0
  (lambda n
    (n (lambda(k) cff) ctt)))

(define id 
  (lambda (x) x))

(define myG
  (lambda (y)
    (lambda (prev)
      (lambda (x)
        ((cmult y) prev))))) 

(define (h y . xs)
  (lambda (f)
    (lambda (g)
      (((c=0 y) (f xs))
               (((g (cp y)) (((h (cp y) xs) f) g)) xs)))))
