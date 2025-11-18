(= (traceid $x) (let $reduced $x (trace! $reduced $reduced)))

(= (map-flat $f ()) ())
(= (map-flat $f (cons $x $xs)) (cons ($f $x) (map-flat $f $xs)))

!(test (map-flat (+ 1) (1 2 3)) (2 3 4))

(= (traceid $in) (trace! $in $in))

(= (map-nested $f ()) ())
(= (map-nested $f (cons $x $xs))
     (if (is-expr $x)
         (cons (map-nested $f $x) (map-nested $f $xs))
         (cons ($f $x) (map-nested $f $xs))))

!(test (map-nested (+ 1) (1 (2 3))) (2 (3 4)))

;(: fold-flat (-> (-> $init $a $init) $init $lista $init))
(= (fold-flat $f $init ()) $init)
(= (fold-flat $f $init (cons $x $xs)) (fold-flat $f ($f $init $x) $xs))

!(test (fold-flat + 0 (1 2 3)) 6)

;(: foldr-flat (-> (-> $a $init $init) $init $lista $init))
(= (foldr-flat $f $init ()) $init)
(= (foldr-flat $f $init (cons $x $xs)) ($f $x (foldr-flat $f $init $xs)))

!(test (foldr-flat cons () (1 (2 3) 4)) (1 (2 3) 4))

(= (fold-nested $f $init ()) $init)
(= (fold-nested $f $init (cons $x $xs))
      (if (is-expr $x)
        (fold-nested $f (fold-nested $f $init $x) $xs)
        (fold-nested $f ($f $init $x) $xs)))

!(test (fold-nested + 0 (1 (2 3))) 6)

;Intersection
(= (/?\ $pred () $b) ())
(= (/?\ $pred (cons $a $as) $bs)
      (if (fold-flat or False (map-flat ($pred $a) $bs))
         (cons $a (/?\ $pred $as $bs))
         (/?\ $pred $as $bs)))

(= (/=\ $a $b) (/?\ = $a $b))
(= (/==\ $a $b) (/?\ == $a $b))
(= (/=@=\ $a $b) (/?\ =alpha $a $b))

!(test (/==\ (1 2 3) (2 3 4)) (2 3))

;Subtraction
(= (\? $pred () $bs) ())
(= (\? $pred (cons $a $as) $bs)
  (if (fold-flat or False (map-flat ($pred $a) $bs))
    (\? $pred $as $bs)
    (cons $a (\? $pred $as $bs))))

(= (\= $a $b) (\? = $a $b))
(= (\== $a $b) (\? == $a $b))
(= (\=a $a $b) (\? =alpha $a $b))

!(test (\== (1 2 3) (2 3 4)) (1))

(= (@ $a $b) (let $a $b $a))

(= (. $f1 $f2 $arg) ($f2 ($f1 $arg)))

(= (&&& $f1 $f2 $arg) (($f1 $arg) ($f2 $arg)))

(= (&^& $f1 $f2 $arg) (superpose (($f1 $arg) ($f2 $arg))))

(= (mfail $x) (empty))

!(test (collapse (&^& (+ 1) (mfail) 1)) (2))

(= (head $x) (cons $x $xs))
(= (tail $xs) (cons $x $xs))

!(test (let (head $x) (1 2 3) $x) 1)
!(test (let (tail $xs) (1 2 3) $xs) (2 3))

(= (mylast $x) (union-atom $xs ($x)))
(= (init $xs) (union-atom $xs ($x)))

!(test (let (mylast $x) (1 2 3) $x) 3)
!(test (let (init $xs) (1 2 3) $xs) (1 2))
