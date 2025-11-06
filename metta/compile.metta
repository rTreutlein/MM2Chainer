!(import! &self stdlib)

(= (collectvars $accum $arg) (if (is-var $arg) (cons $arg $accum) $accum))

(= (seff ($idx $atom $vars) $elem) (let $elem (exists $idx $vars) ((+ 1 $idx) $atom $vars)))

(= (skolemize $expra $exprb)
   (if (or (is-var $exprb) (is-var $expra))
     $exprb
     (let* (($avars (list_to_set (fold-nested collectvars () $expra )))
            ($bvars (list_to_set (fold-nested collectvars () $exprb )))
            ($onlyb (\== $bvars $avars))
            (($_ $res $avars) (sealed $onlyb (fold-nested seff (0 $exprb $avars) $onlyb)))
           )
      $res
     )
    )
)

!(test (skolemize (PlayedTennis $x) (PlayedTennis $x $t)) (PlayedTennis $x (exists 0 ($x))))

(= (addidx $expr $idx)
    (let ($head $tail) (decons $expr)
     (let $ntail (addidx $tail (+ $idx 1))
      (cons ($head $idx) $ntail))))
(= (addidx () $idx) ())

!(test (addidx (a b c) 0) ((a 0) (b 1) (c 2)))

(= (out_and_ff $type ($elem $idx))
   (((: $prf $type (STV $tvs $tvc)) (CPU sqrt ($tvs) $ntvs)) |- ((: (proj $idx $prf) $elem (STV $ntvs $tvc)))))
(= (out_and_ff $_ ($elem $idx)
   (compile-outputs (: $prf $elem $tv))))

(= (out_or_ff $type ($elem $idx))
   (((: $prf $type $tv)) |- ((: (proj $idx $prf) $elem $tv))))
(= (out_or_ff $type ($elem $idx))
   (compile-outputs (: $prf $elem $tv)))

(= (compile-outputs (: $NNprf $type $NNtv))
  (let ($head $tail) (decons $type)
    (if (not (is-var $head))
      (case $head
        ((And
          (let $idtail (addidx $tail 0)
          (out_and_ff $type (superpose $idtail)))
         )
         (Or
          (let $idtail (addidx $tail 0)
          (out_or_ff $type (superpose $idtail)))
         )
        ))
      Empty)
    ))

!(test (collapse (compile-outputs (: prf (And A B) (STV 1.0 1.0))))
       ((((: $_129424 (And A B) (STV $_129466 $_129472)) (CPU sqrt ($_129466) $_129508)) |- ((: (proj 0 $_129424) A (STV $_129508 $_129472)))) (((: $_129232 (And A B) (STV $_129274 $_129280)) (CPU sqrt ($_129274) $_129316)) |- ((: (proj 1 $_129232) B (STV $_129316 $_129280))))))

(= (in_map $elem) (: $prf $elem $tv))

(= (in_fold ($formula $premises (: $cclprf $ccltype $ccltv))
            (: $prfelem $elem $tve))
   (let (($NN1 $NN2 $NN3 $tv) $NNr) (decons $premises)
        ($formula
         (union-atom ((CPU $formula ($tv $tve) $ntv) (: $prfelem $elem $tve)) $premises)
         (: (cons $prfelem $cclprf) (cons $elem $ccltype) $ntv))))

(= (inTemplate $formula $head $tail)
 (let* (((cons (: $fstprf $fstelem $fsttv) $rst) (map-flat in_map $tail))
        (($formula $resNNprms (: $cclprf $ccltype $ccltv)) (fold-flat in_fold ($formula ((: $fstprf $fstelem $fsttv)) (: ($fstprf) ($fstelem) $fsttv)) $rst))
        (($rcclprf $rccltype) ((reverse $cclprf) (reverse $ccltype)))
       )
     ((reverse $resNNprms) |- ((: (cons conjunction $rcclprf) (cons $head $rccltype) $ccltv)))))

!(test (inTemplate testformula And (A B))
       (((: $_137384 A $_137396) (: $_137414 B $_137426) (CPU testformula ($_137396 $_137426) $_137468)) |- ((: (conjunction $_137384 $_137414) (And A B) $_137468))))

(= (compile-inputs (: $prf $type $tv))
   (let (cons $head $tail) $type
     (if (not (is-var $head))
       (case $head
         ((And (superpose ((inTemplate and-formula $head $tail) (compile-inputs (: $prf (superpose $tail) $tv)))))
          (Or (superpose ((inTemplate or-formula $head $tail) (compile-inputs (: $prf (superpose $tail) $tv)))))
         ))
         Empty)))

!(test (collapse (compile-inputs (: $prf (And (Or X Y) B) (STV $s $c))))
       ((((: $_141576 (Or X Y) $_141606) (: $_141624 B $_141636) (CPU and-formula ($_141606 $_141636) $_141678)) |- ((: (conjunction $_141576 $_141624) (And (Or X Y) B) $_141678))) (((: $_141384 X $_141396) (: $_141414 Y $_141426) (CPU or-formula ($_141396 $_141426) $_141468)) |- ((: (conjunction $_141384 $_141414) (Or X Y) $_141468)))))

(= (uPmapf1 $elem)
   (if (= $elem (: $prf ($rel $a $b) $itv))
       (if (and (== $rel Implication) (not (is-var $rel)))
           (CPU bc (kb depth ((: $prfa $a (STV 1.0 1.0)) |- (: $prfb $b $itv))) $res)
           $elem)
       $elem))

(= (uPmapf2 $elem $accum)
   (if (= $elem (: $prfa ($rel $a) (STV $nas $nac)))
       (if (and (not (is-var $rel)) (== $rel Not))
           (cons (: $prfa $a (STV $as $ac)) (cons (CPU - (1.0 $as) $nas) $accum))
           (cons $elem $accum))
       (cons $elem $accum)))

(= (updatePremises $premises) (foldr-flat uPmapf2 () (map-flat uPmapf1 $premises)))

(= (postImpGuard $relation) (== $relation Implication))
(= (postQueryImpGuard $relation) (and (not (is-var $relation)) (== $relation Implication)))

(= (postNotGuard $relation) (== $relation Not))
(= (postQueryNotGuard $relation) (and (== $relation Not) (not (is-var $relation))))

(= (postCore $premises $conclusions $impGuard $notGuard $actionB $actionA)
  (let $npremises (updatePremises $premises)
  (case $conclusions
    ((((: $prf ($relation $a $b) $tv))
       (if ($impGuard $relation)
         (superpose ( (post ((union-atom $npremises ((: $prfa $a $atv) (CPU mp-formula ($atv $tv) $btv))) |- ((: ($prf $prfa) $b $btv))))
                      ($actionB $b)
                      ($actionA $a)
                    ))
         ($npremises |- $conclusions))
     )
     (((: $prf ($relation $a) (STV $strength $confidence)))
       (if ($notGuard $relation)
          (post ($npremises |- ((: $prf $a (STV (- 1.0 $strength) $confidence)))))
          ($npremises |- $conclusions))
     )
     ($conclusions
      ($npremises |- $conclusions))))))

(= (post ($premises |- $conclusions))
  (postCore $premises $conclusions postImpGuard postNotGuard compile-outputs compile-inputs))

(= (compile $stmt)
    (let (: $prf $Type $tv) $stmt
    (if (is-var $Type)
      Empty
      (case $stmt
        (((: $prf ($relation $a $b) $itv)
          (if (== $relation Implication)
            (let* ( ($nb (skolemize $a $b))
                    ($na (skolemize $b $a))
                  )
            (post (superpose ((((: $prfa $a $atv) (CPU mp-formula ($itv $atv) $btv))
                                |-
                                ((: ($prf $prfa) $nb $btv)))
                              (if (is-var $nb) Empty (compile-outputs (: ($prf $prfa) $nb $btv)))
                              (if (is-var $a) Empty (compile-inputs (: $prfa $a $atv)))

                               ;(((: $prfsb (substitute $b) $btv1)
                               ;  (: $prfb $b $btv2)
                               ;  (CPU stv< ($btv1 $btv2) True)
                               ;  (: $pa (substitute $na) $atv)
                               ;  (CPU inversion-formula ($atv $btv1 $itv) $nitv)
                               ;  (CPU mp-formula ($btv2 $nitv) $natv)
                               ; )
                               ; |-
                               ; ((: ((inverted $prf $pa $prfsb) $prfb) $na $natv)))
                               ;(if (is-var $na) Empty (compile-outputs (: ((inverted $prf $pa $pb1) $pb2) $na $natv)))
                               ;(if (is-var $b) Empty (compile-inputs (: $pb2 $b $btv2)))
                             ))))
            (post (superpose ( (() |- ($stmt))
                  (compile-outputs $stmt))))
            ))
         ($stmt
          (post (superpose ( (() |- ($stmt))
                             (compile-outputs $stmt)
         )))))))))


(= (postQuery Empty) Empty)
(= (postQuery ($premises |- $conclusions))
  (postCore $premises $conclusions postQueryImpGuard postQueryNotGuard compile-inputs compile-outputs))

(= (compileQuery $stmt)
 (let (: $prf $Type $tv) $stmt
  (if (is-var $Type)
   ( (() |- ((: $prf $Type $tv))) ())
   (if (= $Type ($relation $a $b))
    (if (== $relation Implication)
     ((postQuery (((: $prfa $a (STV 1.0 1.0))) |- ((: $prfb $b $itv))))
      (collapse (postQuery (superpose ( (compile-inputs (: $prfb $b $btv)) (compile-outputs (: $prfa $a $atv)) ))))
     )
     ((postQuery (() |- ((: $prf $Type $tv))))
      (collapse (postQuery (compile-inputs (: $prf $Type $tv))))))
    ((postQuery (() |- ((: $prf $Type $tv))))
     (collapse (postQuery (compile-inputs (: $prf $Type $tv))))))
  )))

(= (nested ()) Nil)
(= (nested (cons $head $tail))
   ($head (nested $tail)))

(= (mm2compile $kb $stmt)
  (mm2stmt $kb (compile $stmt)))

(= (mm2stmt $kb $stmt)
 (case $stmt
   ( ((() |- ($ccl)) ($kb $ccl))
     (($prms |- ($ccl)) ($kb ((nested $prms) |- $ccl)))
   )))

(= (mm2compileQuery $kb $stmt)
   (case (compileQuery $stmt)
    ( ( ( (() |- ($ccl)) $adds) (let $tail (collapse (mm2stmt $kb (superpose $adds))) (let $lst (cons (goal $kb Nil $ccl) $tail) (superpose $lst))))
      ( ( ($prms |- ($ccl)) $adds) (let $tail (collapse (mm2stmt $kb (superpose $adds))) (let $lst (cons (goal $kb $prms $ccl) $tail) (superpose $lst))))
    )
   ))

!(test (collapse (mm2compile kb (: prf (Implication (Or A B) (And C D)) (STV 1.0 1.0))))
       ((kb (((: $_179922 (Or A B) $_179952) ((CPU mp-formula ((STV 1.0 1.0) $_179952) $_180030) Nil)) |- (: (prf $_179922) (And C D) $_180030)))
        (kb (((: $_179712 (And C D) (STV $_179754 $_179760)) ((CPU sqrt ($_179754) $_179802) Nil)) |- (: (proj 0 $_179712) C (STV $_179802 $_179760))))
        (kb (((: $_179502 (And C D) (STV $_179544 $_179550)) ((CPU sqrt ($_179544) $_179592) Nil)) |- (: (proj 1 $_179502) D (STV $_179592 $_179550))))
        (kb (((: $_179286 A $_179298) ((: $_179322 B $_179334) ((CPU or-formula ($_179298 $_179334) $_179382) Nil))) |- (: (conjunction $_179286 $_179322) (Or A B) $_179382)))))
