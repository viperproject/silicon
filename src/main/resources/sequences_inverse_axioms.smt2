; Parameters:
;  - $S$ is the sort of the sequence elements

(assert (forall ((i Int) (xs $Seq<$S$>)) (!
    (= ($Seq.at_inv xs ($Seq.at xs i)) i)
    :pattern (($Seq.at_inv xs ($Seq.at xs i)))
    )))
