(assert (forall ((i Int) (xs $Seq<$Ref>)) (!
    (= ($Fun.inv<Int> ($Seq.at xs i)) i)
    :pattern (($Fun.inv<Int> ($Seq.at xs i)))
    )))
