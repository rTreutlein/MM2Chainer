(= (traceid $x) (trace! $x $x))

(= (collectvars $accum $arg) (if (is-var $arg) (let ($arg $accum) (decons $res) $res) $accum))

(= (seff ($idx $atom $vars) $elem) (let $elem (exists $idx $vars) ((+ 1 $idx) $atom $vars)))

(= (skolemize $expra $exprb)
   (if (or (is-var $exprb) (is-var $expra))
     $exprb
     (let* (($avars (fold-nested $expra () collectvars))
            ($bvars (fold-nested $exprb () collectvars))
            ($onlyb (subtract == $bvars $avars))
            (($_ $res $avars) (sealed $onlyb (fold-nested $onlyb (0 $exprb $avars) seff)))
           )
      $res
     )
    )
)

(= (addidx $expr $idx)
    (let ($head $tail) (decons $expr)
     (let $ntail (addidx $tail (+ $idx 1))
      (cons ($head $idx) $ntail))))
(= (addidx () $idx) ())

;!(test (addidx (a b c) 0) ((a 0) (b 1) (c 2)))

(= (out_and_ff $type ($elem $idx))
   (((: $prf $type (STV $tvs $tvc)) (CPU sqrt ($tvs) $ntvs)) |- ((: (proj $idx $prf) $elem (STV $ntvs $tvc)))))
(= (out_and_ff $_ ($elem $idx)
   (out (: $prf $elem $tv))))

(= (out_or_ff $type ($elem $idx))
   (((: $prf $type $tv)) |- ((: (proj $idx $prf) $elem $tv))))
(= (out_or_ff $type ($elem $idx))
   (out (: $prf $elem $tv)))

(= (out (: $NNprf $type $NNtv))
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

(= (in_map $elem) (: $prf $elem $tv))

(= (in_fold ($formula $premises (: $cclprf $ccltype $ccltv))
            (: $prfelem $elem $tve))
   (let (($NN1 $NN2 $NN3 $tv) $NNr) (decons $premises)
        ($formula
         (concat ((CPU $formula ($tv $tve) $ntv) (: $prfelem $elem $tve)) $premises)
         (: (cons $prfelem $cclprf) (cons $elem $ccltype) $ntv))))

(= (inTemplate $formula $head $tail)
 (let* (($prms (map-flat $tail in_map))
        (((: $fstprf $fstelem $fsttv) $rst) (decons $prms))
        (($formula $resNNprms (: $cclprf $ccltype $ccltv)) (fold-flat $rst ($formula ((: $fstprf $fstelem $fsttv)) (: ($fstprf) ($fstelem) $fsttv)) in_fold))
        (($rcclprf $rccltype) ((reverse $cclprf) (reverse $ccltype)))
       )
     ((reverse $resNNprms) |- ((: (cons conjunction $rcclprf) (cons $head $rccltype) $ccltv)))))

(= (in (: $prf $type $tv))
   (let ($head $tail) (decons $type)
     (if (not (is-var $head))
       (case $head
         ((And (superpose ((inTemplate and-formula $head $tail) (in (: $prf (superpose $tail) $tv)))))
          (Or (superpose ((inTemplate or-formula $head $tail) (in (: $prf (superpose $tail) $tv)))))
         ))
         Empty)))

(= (uPmapf1 $elem)
   (if (=? $elem (: $prf ($rel $a $b) $itv))
       (if (and (== $rel Implication) (not (is-var $rel)))
           (CPU bc (kb depth ((: $prfa $a (STV 1.0 1.0)) |- (: $prfb $b $itv))) $res)
           $elem)
       $elem))

(= (uPmapf2 $elem)
   (if (=? $elem (: $prfa ($rel $a) (STV $nas $nac)))
       (if (and (not (is-var $rel)) (== $rel !))
           (∧ (: $prfa $a (STV $as $ac)) (CPU - (1.0 $as) $nas))
           $elem)
       $elem))

(= (updatePremises $premises) (map-flat (map-flat $premises uPmapf1) uPmapf2))

(= (post ($premises |- $conclusions))
  (let $npremises (updatePremises $premises)
  (case $conclusions
    ((((: $prf ($relation $a $b) $tv))
       (if (== $relation Implication)
         (superpose ( (post ((concat $npremises ((: $prfa $a $atv) (CPU mp-formula ($atv $tv) $btv))) |- ((: ($prf $prfa) $b $btv))))
                      (out $b)
                      (in $a)
                    ))
         ($npremises |- $conclusions))
     )
     (((: $prf ($relation $a) (STV $strength $confidence)))
       (if (== $relation Not)
          (post ($npremises |- ((: $prf $a (STV (- 1.0 $strength) $confidence)))))
          ($npremises |- $conclusions))
     )
     ($conclusions
      ($npremises |- $conclusions))))))

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
                               (if (is-var $nb) Empty (out (: ($prf $prfa) $nb $btv)))
                               (if (is-var $a) Empty (in (: $prfa $a $atv)))

                               (((: $prfsb (substitute $b) $btv1)
                                 (: $prfb $b $btv2)
                                 (CPU stv< ($btv1 $btv2) True)
                                 (: $pa (substitute $na) $atv)
                                 (CPU inversion-formula ($atv $btv1 $itv) $nitv)
                                 (CPU mp-formula ($btv2 $nitv) $natv)
                                )
                                |-
                                ((: ((inverted $prf $pa $prfsb) $prfb) $na $natv)))
                               (if (is-var $na) Empty (out (: ((inverted $prf $pa $pb1) $pb2) $na $natv)))
                               (if (is-var $b) Empty (in (: $pb2 $b $btv2)))
                             ))))
            (post (superpose ( (() |- ($stmt))
                  (out $stmt))))
            ))
         ($stmt
          (post (superpose ( (() |- ($stmt))
                             (out $stmt)
         )))))))))


(= (postQuery Empty) Empty)
(= (postQuery ($premises |- $conclusions))
  (let $npremises (updatePremises $premises)
  (case $conclusions
    ((((: $prf ($relation $a $b) $tv))
       (if (and (not (is-var $relation)) (== $relation Implication))
         (superpose ( (post ((concat $npremises ((: $prfa $a $atv) (CPU mp-formula ($atv $tv) $btv))) |- ((: ($prf $prfa) $b $btv))))
                      (in $b)
                      (out $a)
                    ))
         ($npremises |- $conclusions))
     )
     (((: $prf ($relation $a) (STV $strength $confidence)))
       (if (and (== $relation Not) (not (is-var $relation)))
          (post ($npremises |- ((: $prf $a (STV (- 1.0 $strength) $confidence)))))
          ($npremises |- $conclusions))
     )
     ($conclusions
      ($npremises |- $conclusions))))))

(= (compileQuery $stmt)
 (let (: $prf $Type $tv) $stmt
  (if (is-var $Type)
   ( (() |- ((: $prf $Type $tv))) ())
   (if (= $Type ($relation $a $b))
    (if (== $relation Implication)
     ((postQuery (((: $prfa $a (STV 1.0 1.0))) |- ((: $prfb $b $itv))))
      (collapse (postQuery (superpose ( (in (: $prfb $b $btv)) (out (: $prfa $a $atv)) ))))
     )
     ((postQuery (() |- ((: $prf $Type $tv))))
      (collapse (postQuery (in (: $prf $Type $tv))))))
    ((postQuery (() |- ((: $prf $Type $tv))))
     (collapse (postQuery (in (: $prf $Type $tv))))))
  )))

(= (nested ()) Nil)
(= (nested $stmt)
 (let ($head $tail) (decons $stmt)
   ($head (nested $tail))))

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

!(mm2compile kb (: extract_any_from_and (Implication (And $item $others) $item) (STV 1.0 1.0)))
