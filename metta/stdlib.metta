(= (traceid $x) (trace! $x $x))

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

(= (fold-flat $f $init ()) $init)
(= (fold-flat $f $init (cons $x $xs)) (fold-flat $f ($f $init $x) $xs))

!(test (fold-flat + 0 (1 2 3)) 6)

(= (foldr-flat $f $init ()) $init)
(= (foldr-flat $f $init (cons $x $xs)) ($f $x (foldr-flat $f $init $xs)))

!(test (foldr-flat cons () (1 (2 3) 4)) (1 (2 3) 4))

(= (fold-nested $f $init ()) $init)
(= (fold-nested $f $init (cons $x $xs))
      (if (is-expr $x)
        (fold-nested $f (fold-nested $f $init $x) $xs)
        (fold-nested $f ($f $init $x) $xs)))

!(test (fold-nested + 0 (1 (2 3))) 6)

(= (ueq $a $b) (= $a $b))
(= (eq $a $b) (== $a $b))
(= (aeq $a $b) (=@= $a $b))

;Intersection
(= (/?\ $pred () $b) ())
(= (/?\ $pred (cons $a $as) $bs)
      (if (fold-flat or False (map-flat ($pred $a) $bs))
         (cons $a (/?\ $pred $as $bs))
         (/?\ $pred $as $bs)))

!(test (/?\ eq (1 2 3) (2 3 4)) (2 3))

(= (/=\ $a $b) (/?\ ueq $a $b))
(= (/==\ $a $b) (/?\ eq $a $b))
(= (/=@=\ $a $b) (/?\ aeq $a $b))

;Subtraction
(= (\? $pred () $bs) ())
(= (\? $pred (cons $a $as) $bs)
  (if (fold-flat or False (map-flat ($pred $a) $bs))
    (\? $pred $as $bs)
    (cons $a (\? $pred $as $bs))))

(= (\= $a $b) (\? ueq $a $b))
(= (\== $a $b) (\? eq $a $b))
(= (\=@= $a $b) (\? aeq $a $b))

!(test (\== (1 2 3) (2 3 4)) (1))
