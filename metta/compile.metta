!(import! &self stdlib)

!(change-state! ctxid 0)

(= (nextctx) (let $n (get-state ctxid) (let $_ (change-state! ctxid (+ $n 1)) $n)))

(= (extract-vars $expr)
  (if (is-expr $expr)
    (let $collect-vars (|-> ($accum $arg) (if (is-var $arg) (cons $arg $accum) $accum))
    (fold-nested $collect-vars () $expr))
   ()))

(= (skolemize $expra $exprb)
   (if (or (is-var $exprb) (is-var $expra))
     $exprb
     (let* (($avars (list_to_set (extract-vars $expra)))
            ($bvars (list_to_set (extract-vars $exprb)))
            ($onlyb (\== $bvars $avars))
            ($substitute (|-> (($idx $atom) $elem) (let $elem (exists $idx $avars) ((+ 1 $idx) $atom))))
            (($_ $res) (sealed $onlyb (fold-nested $substitute (0 $exprb) $onlyb)))
           )
      $res)))

!(test (skolemize (PlayedTennis $x) (PlayedTennis $x $t)) (PlayedTennis $x (exists 0 ($x))))

(= (addidx (cons $head $tail) $idx)
      (cons ($head $idx) (addidx $tail (+ $idx 1))))
(= (addidx () $idx) ())

!(test (addidx (a b c) 0) ((a 0) (b 1) (c 2)))

(= (compile-outputs (: $kb $NNprf (@ $type (cons $head $tail)) $NNtv))
    (if (and (not (is-var $head)) (is-member $head (And Or)))
      (let $to-proj (|-> (($elem $idx)) (((: $kb $prf $type $tvin) (CPU (atom_concat $head -projection) ($tvin) $tvout)) |- ((: $kb (proj $idx $prf) $elem $tvout))))
      (let $cmp-out (|-> (($elem $_)) (compile-outputs (: $kb $prfn $elem $tvn)))
      (let $idtail (addidx $tail 0)
        (&^& $to-proj $cmp-out (superpose $idtail)))))
      Empty))

!(test (collapse (compile-outputs (: kb prf (And A B) (STV 1.0 1.0))))
       ((((: kb $_18502 (And A B) $_18532) (CPU And-projection ($_18532) $_18568)) |- ((: kb (proj 0 $_18502) A $_18568)))
        (((: kb $_18346 (And A B) $_18376) (CPU And-projection ($_18376) $_18412)) |- ((: kb (proj 1 $_18346) B $_18412)))))

(= (in_map $kb $elem) (: $kb $prf $elem $tv))

(= (tv $tv) (: $kb $prf $elem $tv))
(= (tv $tv) (CPU $formula $args $tv))

!(test (let (head (tv $tv)) ((: kb prf elem tv)) $tv) tv)
!(test (let (head (tv $tv)) ((CPU formula args tv)) $tv) tv)

(= (in_fold $formula
            (: $kb $prfelem $elem $tve)
            ((@ $premises (head (tv $tv))) (: $kb $cclprf $ccltype $ccltv)))
         ((cons (CPU $formula ($tv $tve) $ntv) (cons (: $kb $prfelem $elem $tve) $premises))
          (: $kb (cons $prfelem $cclprf) (cons $elem $ccltype) $ntv)))

(= (inTemplate $kb $formula $head $tail)
 (let* (((cons (@ $fst (: $kb $fstprf $fstelem $fsttv)) $rst) (map-flat (in_map $kb) $tail))
        ($init (($fst) (: $kb ($fstprf) ($fstelem) $fsttv)))
        (($resNNprms (: $kb $cclprf $ccltype $ccltv)) (foldr-flat (in_fold $formula) $init $rst))
        (($rcclprf $rccltype) ((reverse $cclprf) (reverse $ccltype)))
       )
     ((reverse $resNNprms) |- ((: $kb (cons conjunction $rcclprf) (cons $head $rccltype) $ccltv)))))

!(test (inTemplate $kb test-formula And (A B))
       (((: $kb $_137384 A $_137396) (: $kb $_137414 B $_137426) (CPU test-formula ($_137396 $_137426) $_137468)) |- ((: $kb (conjunction $_137384 $_137414) (And A B) $_137468))))

(= (compile-inputs (: $kb $prf (cons $head $tail) $tv))
     (if (and (not (is-var $head)) (is-member $head (Or And)))
         (superpose ((inTemplate $kb (atom_concat $head -formula) $head $tail)
                     (compile-inputs (: $kb $prf (superpose $tail) $tv))))
         Empty))

!(test (collapse (compile-inputs (: kb $prf (And (Or X Y) B) (STV $s $c))))
       ((((: kb $_141576 (Or X Y) $_141606)    (: kb $_141624 B $_141636) (CPU And-formula ($_141606 $_141636) $_141678)) |- ((: kb (conjunction $_141576 $_141624) (And (Or X Y) B) $_141678)))
        (((: kb $_141384 X $_141396) (: kb $_141414 Y $_141426) (CPU Or-formula ($_141396 $_141426) $_141468)) |- ((: kb (conjunction $_141384 $_141414) (Or X Y) $_141468)))))

(= (uPmapf1 $elem)
   (if (= $elem (: $kb $prf ($rel $a $b) $tv))
       (if (and (== $rel Implication) (not (is-var $rel)))
           (let $vars (extract-vars $a)
           (let $ctx  (nextctx)
           (let $_ (add-atom ctx (($kb $ctx $vars) $a))
                  (: ($kb $ctx $vars) $prf $b $tv))))
           $elem)
       $elem))

(= (uPmapf2 $elem $accum)
   (if (= $elem (: $kb $prfa ($rel $a) $tv))
       (if (and (not (is-var $rel)) (== $rel Not))
           (cons (: $kb $prfa $a $tv_a) (cons (CPU not-formula ($tv_a) $tv) $accum))
           (cons $elem $accum))
       (cons $elem $accum)))

(= (updatePremises $premises) (foldr-flat uPmapf2 () (map-flat uPmapf1 $premises)))

!(test (updatePremises ((: $kb $prf (Implication (Dog $x) (Animal $x)) $tv))) ((: ($_8644 0 ($_8680)) $_8650 (Animal $_8680) $_8704)))

!(test (updatePremises ((: $kb $prf (Not (Dog $x)) $tv))) ((: $_9054 $_9060 (Dog $_9090) $tv) (CPU not-formula ($tv) $ntv)))

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

(= (postQuery Empty) Empty)
(= (postQuery ($premises |- $conclusions))
  (postCore $premises $conclusions postQueryImpGuard postQueryNotGuard compile-inputs compile-outputs))

(= (compile $kb (@ $stmt (: $prf $Type $tv)))
    (if (is-var $Type)
      Empty
      (case $stmt
        (((: $prf ($relation $a $b) $itv)
          (if (== $relation Implication)
            (let* ( ($nb (skolemize $a $b))
                    ($na (skolemize $b $a))
                  )
            (post (superpose ((((: $kbr $prfa $a $atv) (CPU mp-formula ($itv $atv) $btv))
                                |-
                                ((: $kbr ($prf $prfa) $nb $btv)))
                              (if (is-var $nb) Empty (compile-outputs (: $kbr ($prf $prfa) $nb $btv)))
                              (if (is-var $a) Empty (compile-inputs (: $kbr $prfa $a $atv)))

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
            (post (superpose ( (() |- ((: $kb $prf $Type $tv)))
                               (compile-outputs (: $kb $prf $Type $tv)))))
            ))
         ($stmt
          (post (superpose ( (() |- ((: $kb $prf $Type $tv)))
                             (compile-outputs (: $kb $prf $Type $tv))
         ))))))))


(= (compileQuery $kb (: $prf $Type $tv))
  (if (is-var $Type)
   ( (() |- ((: $kb $prf $Type $tv))) ())
   (if (= $Type ($relation $a $b))
    (if (== $relation Implication)
     ((postQuery (((: $kb $prfa $a (STV 1.0 1.0))) |- ((: $kb $prfb $b $itv))))
      (collapse (postQuery (superpose ( (compile-inputs (: $kb $prfb $b $btv)) (compile-outputs (: $kb $prfa $a $atv)) ))))
     )
     ((postQuery (() |- ((: $kb $prf $Type $tv))))
      (collapse (postQuery (compile-inputs (: $kb $prf $Type $tv))))))
    ((postQuery (() |- ((: $kb $prf $Type $tv))))
     (collapse (postQuery (compile-inputs (: $kb $prf $Type $tv))))))
  ))

(= (nested ()) Nil)
(= (nested (cons $head $tail))
   ($head (nested $tail)))

(= (mm2compile $kb $stmt)
  (mm2stmt (compile $kb $stmt)))

(= (mm2stmt $stmt)
 (case $stmt
   ( ((() |- ($ccl)) $ccl)
     (($prms |- ($ccl)) (rules ((nested $prms) |- $ccl)))
   )))

(= (mm2compileQuery $kb $stmt)
   (case (compileQuery $kb $stmt) 
   (
     ( ( (() |- ($ccl)) $adds)
          (let $tail (map-flat mm2stmt $adds) (let $lst (cons (goal $ccl) $tail) (superpose $lst))))
     ( ( (((: $kb $prf $type $tv)) |- ((: $kb $prf1 $type1 $tv1))) $adds) 
          (let $vars (extract-vars $type)
          (let $mvars (if (== $vars ()) Nil $vars)
          (let $ctx  (nextctx)
          (let $ctxatom (: ($kb $ctx $mvars) (ctx proof $ctx) $type $tv)
          (let $goalatom (goal (: ($kb $ctx $mvars) $prf1 $type1 $tv1))
          (let $tail (map-flat mm2stmt $adds)
          (let $lst (union-atom ($goalatom $ctxatom) $tail) (superpose $lst)))))))))
     ( $a (notsupported mm2compileQuery $kb $stmt $a))
   )))

!(test (mm2compile kb (: prf (Dog doggy) (STV 1.0 1.0))) (: kb prf (Dog doggy) (STV 1.0 1.0)))

!(test (collapse (mm2compile kb (: prf (Implication (Or A B) (And C D)) (STV 1.0 1.0))))
       ((rules (((: $kb1 $_75390 (Or A B) $_75420) ((CPU mp-formula ((STV 1.0 1.0) $_75420) $_75498) Nil)) |- (: $kb1 (prf $_75390) (And C D) $_75498)))
        (rules (((: $kb2 $_75216 (And C D) $_75246) ((CPU And-projection ($_75246) $_75288) Nil)) |- (: $kb2 (proj 0 $_75216) C $_75288)))
        (rules (((: $kb3 $_75042 (And C D) $_75072) ((CPU And-projection ($_75072) $_75114) Nil)) |- (: $kb3 (proj 1 $_75042) D $_75114)))
        (rules (((: $kb4 $_74826 A $_74838) ((: $kb4 $_74862 B $_74874) ((CPU Or-formula ($_74838 $_74874) $_74922) Nil))) |- (: $kb4 (conjunction $_74826 $_74862) (Or A B) $_74922)))))


!(test (mm2compile kb (: prf (Implication (Not A) B) (STV 1.0 1.0))) 
       (rules (((: $_24104 $_24110 A $_24828) ((CPU not-formula ($_24828) $_24122) ((CPU mp-formula ((STV 1.0 1.0) $_24122) $_24152) Nil))) |- (: $_24104 (prf $_24110) B $_24152))))

!(test (mm2compileQuery kb (: $prf B $tv)) (goal (: kb $_14174 B $_14186)))
