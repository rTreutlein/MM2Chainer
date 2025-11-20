!(import! &self stdlib)

!(change-state! ctxid 0)

(= (nextctx) (let $n (get-state ctxid) (let $_ (change-state! ctxid (+ $n 1)) $n)))

(= (extract-vars $expr)
  (if (is-var $expr)
    ($expr)
    (if (is-expr $expr)
      (let $collect-vars (|-> ($accum $arg) (if (is-var $arg) (cons $arg $accum) $accum))
           (fold-nested $collect-vars () $expr))
      ())))

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
      (empty)))

!(test (collapse (compile-outputs (: kb prf (And A B) (STV 1.0 1.0))))
       ((((: kb $_18502 (And A B) $_18532) (CPU And-projection ($_18532) $_18568)) |- ((: kb (proj 0 $_18502) A $_18568)))
        (((: kb $_18346 (And A B) $_18376) (CPU And-projection ($_18376) $_18412)) |- ((: kb (proj 1 $_18346) B $_18412)))))


(= (in_map $kb $elem) (: $kb $prf $elem $tv))

(= (tv $tv) (: $kb $prf $elem $tv))
(= (tv $tv) (CPU $formula $args $tv))

!(test (let (head (tv $tv)) ((: kb prf elem tv)) $tv) tv)
!(test (let (head (tv $tv)) ((CPU formula args tv)) $tv) tv)

(= (in_fold $formula
            ((@ $premises (head (tv $tv))) (: $kb $cclprf $ccltype $ccltv))
            (: $kb $prfelem $elem $tve))
         ((cons (CPU $formula ($tv $tve) $ntv) (cons (: $kb $prfelem $elem $tve) $premises))
          (: $kb (cons $prfelem $cclprf) (cons $elem $ccltype) $ntv)))

(= (inTemplate $kb $formula $head $tail)
 (let* (((cons (@ $fst (: $kb $fstprf $fstelem $fsttv)) $rst) (map-flat (in_map $kb) $tail))
        ($init (($fst) (: $kb ($fstprf) ($fstelem) $fsttv)))
        (($resNNprms (: $kb $cclprf $ccltype $ccltv)) (fold-flat (in_fold $formula) $init $rst))
        (($rcclprf $rccltype) ((reverse $cclprf) (reverse $ccltype)))
       )
     ((reverse $resNNprms) |- ((: $kb (cons conjunction $rcclprf) (cons $head $rccltype) $ccltv)))))

!(test (inTemplate $kb test-formula And (A B))
       (((: $kb $_137384 A $_137396) (: $kb $_137414 B $_137426) (CPU test-formula ($_137396 $_137426) $_137468)) |- ((: $kb (conjunction $_137384 $_137414) (And A B) $_137468))))

(= (compile-inputs (: $kb $prf (cons $head $tail) $tv))
     (if (and (not (is-var $head)) (is-member $head (Or And)))
         (superpose ((inTemplate $kb (atom_concat $head -formula) $head $tail)
                     (compile-inputs (: $kb $prf (superpose $tail) $tv))))
         (empty)))

!(test (collapse (compile-inputs (: kb $prf (And (Or X Y) B) (STV $s $c))))
       ((((: kb $_141576 (Or X Y) $_141606)    (: kb $_141624 B $_141636) (CPU And-formula ($_141606 $_141636) $_141678)) |- ((: kb (conjunction $_141576 $_141624) (And (Or X Y) B) $_141678)))
        (((: kb $_141384 X $_141396) (: kb $_141414 Y $_141426) (CPU Or-formula ($_141396 $_141426) $_141468)) |- ((: kb (conjunction $_141384 $_141414) (Or X Y) $_141468)))))

(= (uPmapf1 $elem)
   (if (= $elem (: $kb $prf ($rel $a $b) $tv))
       (if (and (== $rel Implication) (not (is-var $rel)))
           (let $vars (extract-vars $a)
           (let $mvars (if (== $vars ()) Nil $vars)
           (let $ctx  (nextctx)
           (let $_ (add-atom ctx (: ($kb $ctx $mvars) (ctx proof $ctx) $a (STV 1.0 1.0)))
                  (: ($kb $ctx $mvars) $prf $b $tv)))))
           $elem)
       $elem))

(= (uPmapf2 $elem $accum)
   (if (and (= $elem (: $kb $prfa $type $tv)) (not (is-var $type)))
       (if (and (= $type ($rel $a))
           (and (not (is-var $rel)) 
                (== $rel Not)))
           (cons (: $kb $prfa $a $tv_a) (cons (CPU Not-formula ($tv_a) $tv) $accum))
           (cons $elem $accum))
       (cons $elem $accum)))

(= (updatePremises $premises) (foldr-flat uPmapf2 () (map-flat uPmapf1 $premises)))

!(test (updatePremises ((: $kb $prf (Implication (Dog $x) (Animal $x)) $tv))) ((: ($_8644 0 ($_8680)) $_8650 (Animal $_8680) $_8704)))

!(test (updatePremises ((: $kb $prf (Not (Dog $x)) $tv))) ((: $_9054 $_9060 (Dog $_9090) $tv) (CPU Not-formula ($tv) $ntv)))

(= (postImpGuard $relation) (== $relation Implication))
(= (postQueryImpGuard $relation) (and (not (is-var $relation)) (== $relation Implication)))

(= (postNotGuard $relation) (== $relation Not))
(= (postQueryNotGuard $relation) (and (== $relation Not) (not (is-var $relation))))

(= (postCore $premises $conclusions $impGuard $notGuard $actionB $actionA)
  (let $npremises (updatePremises $premises)
  (case $conclusions
    ((((: $prf ($relation $a $b) $tv))
       (if ($impGuard $relation)
         (superpose ( (post ((union-atom $npremises ((: $prfa $a $atv) (CPU Mp-formula ($atv $tv) $btv))) |- ((: ($prf $prfa) $b $btv))))
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

(= (postQuery ($premises |- $conclusions))
  (postCore $premises $conclusions postQueryImpGuard postQueryNotGuard compile-inputs compile-outputs))

(= (compile $kb (@ $stmt (: $prf $Type $tv)))
    (if (is-var $Type)
      (empty)
      (case $stmt
        (((: $prf ($relation $a $b) $itv)
          (if (== $relation Implication)
            (let* ( ($nb (skolemize $a $b))
                    ($na (skolemize $b $a))
                  )
            (post (superpose ((((: $kbr $prfa $a $atv) (CPU Mp-formula ($itv $atv) $btv))
                                |-
                                ((: $kbr ($prf $prfa) $nb $btv)))
                              (if (is-var $nb) (empty) (compile-outputs (: $kbr ($prf $prfa) $nb $btv)))
                              (if (is-var $a) (empty) (compile-inputs (: $kbr $prfa $a $atv)))

                               ;(((: $prfsb (substitute $b) $btv1)
                               ;  (: $prfb $b $btv2)
                               ;  (CPU stv< ($btv1 $btv2) True)
                               ;  (: $pa (substitute $na) $atv)
                               ;  (CPU inversion-formula ($atv $btv1 $itv) $nitv)
                               ;  (CPU mp-formula ($btv2 $nitv) $natv)
                               ; )
                               ; |-
                               ; ((: ((inverted $prf $pa $prfsb) $prfb) $na $natv)))
                               ;(if (is-var $na) (empty) (compile-outputs (: ((inverted $prf $pa $pb1) $pb2) $na $natv)))
                               ;(if (is-var $b) (empty) (compile-inputs (: $pb2 $b $btv2)))
                             ))))
            (post (superpose ( (() |- ((: $kb $prf $Type $tv)))
                               (compile-outputs (: $kb $prf $Type $tv)))))
            ))
         ($stmt
          (post (superpose ( (() |- ((: $kb $prf $Type $tv)))
                             (compile-outputs (: $kb $prf $Type $tv)
         )))))))))


(= (compileQuery $kb (: $prf $Type $tv))
  (if (is-var $Type)
   ( (() |- ((: $kb $prf $Type $tv))) ())
   (if (and (= $Type ($relation $a $b)) (== $relation Implication))
     ((postQuery (((: $kb $prfa $a (STV 1.0 1.0))) |- ((: $kb $prfb $b $itv))))
      (collapse (postQuery (superpose ( (compile-inputs (: $kb $prfb $b $btv)) (compile-outputs (: $kb $prfa $a $atv)) ))))
     )
     ((postQuery (() |- ((: $kb $prf $Type $tv))))
      (collapse (postQuery (compile-inputs (: $kb $prf $Type $tv))))))
  ))

(= (nested ()) Nil)
(= (nested (cons $head $tail))
   ($head (nested $tail)))

(= (mm2compile $kb $stmt)
  (let $_ (clear-space ctx)
        (superpose ((mm2stmt (compile $kb $stmt)) (get-atoms ctx)))))

(= (mm2stmt $stmt)
 (case $stmt
   ( ((() |- ($ccl)) $ccl)
     (($prms |- ($ccl)) (rules ((nested $prms) |- $ccl)))
   )))

(= (mm2compileQuery $kb $stmt)
   (case (compileQuery $kb $stmt) 
   (
     ( ( (() |- ($ccl)) $adds)
          (let $tail (map-flat mm2stmt $adds)
          (let $lst (cons (goal $ccl) $tail) (superpose $lst))))
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
       ((rules (((: $kb1 $_75390 (Or A B) $_75420) ((CPU Mp-formula ((STV 1.0 1.0) $_75420) $_75498) Nil)) |- (: $kb1 (prf $_75390) (And C D) $_75498)))
        (rules (((: $kb2 $_75216 (And C D) $_75246) ((CPU And-projection ($_75246) $_75288) Nil)) |- (: $kb2 (proj 0 $_75216) C $_75288)))
        (rules (((: $kb3 $_75042 (And C D) $_75072) ((CPU And-projection ($_75072) $_75114) Nil)) |- (: $kb3 (proj 1 $_75042) D $_75114)))
        (rules (((: $kb4 $_74826 A $_74838) ((: $kb4 $_74862 B $_74874) ((CPU Or-formula ($_74838 $_74874) $_74922) Nil))) |- (: $kb4 (conjunction $_74826 $_74862) (Or A B) $_74922)))))

!(test (mm2compile kb (: prf (Implication (Not A) B) (STV 1.0 1.0))) 
       (rules (((: $_24104 $_24110 A $_24828) ((CPU Not-formula ($_24828) $_24122) ((CPU Mp-formula ((STV 1.0 1.0) $_24122) $_24152) Nil))) |- (: $_24104 (prf $_24110) B $_24152))))

!(test (mm2compileQuery kb (: $prf B $tv)) (goal (: kb $_14174 B $_14186)))

!(test (collapse (mm2compileQuery kb (: $q_whom_did_she_see (And (See $e) (Agent $e she_2) (Person she_2) (Patient $e $whom) (Person $whom) (Tense $e past_tense)) $tv)))
       ((goal (: kb $_25686 (And (See $_25716) (Agent $_25716 she_2) (Person she_2) (Patient $_25716 $_25782) (Person $_25782) (Tense $_25716 past_tense)) $_25830))
        (rules (((: kb $_35502 (See $_35520) $_35526) ((: kb $_35556 (Agent $_35520 she_2) $_35586) ((CPU And-formula ($_35526 $_35586) $_35634) ((: kb $_35664 (Person she_2) $_35688) ((CPU And-formula ($_35634 $_35688) $_35736) ((: kb $_35766 (Patient $_35520 $_35790) $_35796) ((CPU And-formula ($_35736 $_35796) $_35844) ((: kb $_35874 (Person $_35790) $_35898) ((CPU And-formula ($_35844 $_35898) $_35946) ((: kb $_35976 (Tense $_35520 past_tense) $_36006) ((CPU And-formula ($_35946 $_36006) $_36054) Nil))))))))))) |- (: kb (conjunction $_35502 $_35556 $_35664 $_35766 $_35874 $_35976) (And (See $_35520) (Agent $_35520 she_2) (Person she_2) (Patient $_35520 $_35790) (Person $_35790) (Tense $_35520 past_tense)) $_36054)))))

!(test (mm2compile kb (: boy_implies_person (Implication (Boy $x) (Person $x)) (STV 0.9 0.9)))
       (rules (((: $_38502 $_38508 (Boy $_38526) $_38532) ((CPU Mp-formula ((STV 0.9 0.9) $_38532) $_38610) Nil)) |- (: $_38502 (boy_implies_person $_38508) (Person $_38526) $_38610))))

!(test (collapse (mm2compileQuery kb (: $prf (And A B C) $tv)))
       ((goal (: kb $_37162 (And A B C) $_37198))
        (rules (((: kb $_37246 A $_37258) ((: kb $_37288 B $_37300) ((CPU And-formula ($_37258 $_37300) $_37348) ((: kb $_37378 C $_37390) ((CPU And-formula ($_37348 $_37390) $_37438) Nil))))) |- (: kb (conjunction $_37246 $_37288 $_37378) (And A B C) $_37438)))))

!(test (mm2compile kb (: a_b_c (Implication (Implication A B) C) (STV 1.0 1.0)))
       ((rules (((: ($_40530 1 Nil) $_40548 B $_40560) ((CPU Mp-formula ((STV 1.0 1.0) $_40560) $_40638) Nil)) |- (: $_40530 (a_b_c $_40548) C $_40638)))
        (: ($_40404 1 Nil) (ctx proof 1) A (STV 1.0 1.0))))

!(test (mm2compile kb (: at_time_transfer (Implication (And (AtTime $what $when) (Implication $what $else)) (AtTime $else $when)) (STV 1.0 1.0)))
       ((rules (((: $_44010 $_44016 (And (AtTime $_44046 $_44052) (Implication $_44046 $_44076)) $_44082) ((CPU Mp-formula ((STV 1.0 1.0) $_44082) $_44160) Nil)) |- (: $_44010 (at_time_transfer $_44016) (AtTime $_44076 $_44052) $_44160)))
        (rules (((: $_43716 $_43722 (AtTime $_43740 $_43746) $_43752) ((: ($_43716 2 ($_43740)) $_43806 $_43812 $_43818) ((CPU And-formula ($_43752 $_43818) $_43866) Nil))) |- (: $_43716 (conjunction $_43722 $_43806) (And (AtTime $_43740 $_43746) (Implication $_43740 $_43812)) $_43866))) (: ($_43590 2 ($_43608)) (ctx proof 2) $_43608 (STV 1.0 1.0))))
