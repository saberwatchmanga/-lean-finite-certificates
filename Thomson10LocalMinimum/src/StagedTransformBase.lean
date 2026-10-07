import CoordinateTransformReplayBase

noncomputable section
open scoped BigOperators
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag Thomson10CoordinateChange Thomson10Stability
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def intermediateProgramNode (i j : Fin 17) : Nat :=
  match i.val with
  | 0 => match j.val with
    | 0 => 1603
    | 1 => 1604
    | 2 => 1609
    | 3 => 1617
    | 4 => 1619
    | 5 => 1629
    | 6 => 1645
    | 7 => 1660
    | 8 => 1679
    | 9 => 1702
    | 10 => 1728
    | 11 => 1756
    | 12 => 1788
    | 13 => 1822
    | 14 => 1856
    | 15 => 1897
    | _ => 1941
  | 1 => match j.val with
    | 0 => 1604
    | 1 => 1942
    | 2 => 1943
    | 3 => 1944
    | 4 => 1947
    | 5 => 1952
    | 6 => 1959
    | 7 => 1968
    | 8 => 1977
    | 9 => 1987
    | 10 => 1999
    | 11 => 2013
    | 12 => 2029
    | 13 => 2047
    | 14 => 2067
    | 15 => 2088
    | _ => 2111
  | 2 => match j.val with
    | 0 => 2112
    | 1 => 0
    | 2 => 2115
    | 3 => 2120
    | 4 => 0
    | 5 => 2125
    | 6 => 2134
    | 7 => 2145
    | 8 => 2158
    | 9 => 2173
    | 10 => 2190
    | 11 => 2209
    | 12 => 2230
    | 13 => 2253
    | 14 => 2276
    | 15 => 2303
    | _ => 2332
  | 3 => match j.val with
    | 0 => 2333
    | 1 => 0
    | 2 => 2336
    | 3 => 2341
    | 4 => 2342
    | 5 => 2348
    | 6 => 2359
    | 7 => 2371
    | 8 => 2386
    | 9 => 2403
    | 10 => 2422
    | 11 => 2443
    | 12 => 2466
    | 13 => 2491
    | 14 => 2517
    | 15 => 2546
    | _ => 2577
  | 4 => match j.val with
    | 0 => 0
    | 1 => 2578
    | 2 => 0
    | 3 => 2579
    | 4 => 2582
    | 5 => 2589
    | 6 => 2598
    | 7 => 2609
    | 8 => 2622
    | 9 => 2637
    | 10 => 2654
    | 11 => 2673
    | 12 => 2694
    | 13 => 2717
    | 14 => 2742
    | 15 => 2769
    | _ => 2798
  | 5 => match j.val with
    | 0 => 0
    | 1 => 2112
    | 2 => 2799
    | 3 => 2802
    | 4 => 2805
    | 5 => 2814
    | 6 => 2825
    | 7 => 2838
    | 8 => 2851
    | 9 => 2865
    | 10 => 2881
    | 11 => 2899
    | 12 => 2919
    | 13 => 2941
    | 14 => 2964
    | 15 => 2989
    | _ => 3016
  | 6 => match j.val with
    | 0 => 2578
    | 1 => 0
    | 2 => 3019
    | 3 => 3024
    | 4 => 3025
    | 5 => 3032
    | 6 => 3043
    | 7 => 3054
    | 8 => 3067
    | 9 => 3082
    | 10 => 3099
    | 11 => 3118
    | 12 => 3139
    | 13 => 3162
    | 14 => 3186
    | 15 => 3213
    | _ => 3242
  | 7 => match j.val with
    | 0 => 0
    | 1 => 2333
    | 2 => 3243
    | 3 => 3246
    | 4 => 3249
    | 5 => 3257
    | 6 => 3266
    | 7 => 3276
    | 8 => 3289
    | 9 => 3303
    | 10 => 3319
    | 11 => 3337
    | 12 => 3357
    | 13 => 3379
    | 14 => 3402
    | 15 => 3427
    | _ => 3454
  | 8 => match j.val with
    | 0 => 3455
    | 1 => 0
    | 2 => 3458
    | 3 => 3463
    | 4 => 3464
    | 5 => 3469
    | 6 => 3478
    | 7 => 3489
    | 8 => 3502
    | 9 => 3517
    | 10 => 3534
    | 11 => 3553
    | 12 => 3574
    | 13 => 3597
    | 14 => 3621
    | 15 => 3648
    | _ => 3677
  | 9 => match j.val with
    | 0 => 3678
    | 1 => 3678
    | 2 => 3681
    | 3 => 3686
    | 4 => 3689
    | 5 => 3698
    | 6 => 3711
    | 7 => 3726
    | 8 => 3743
    | 9 => 3762
    | 10 => 3783
    | 11 => 3806
    | 12 => 3831
    | 13 => 3858
    | 14 => 3886
    | 15 => 3917
    | _ => 3950
  | 10 => match j.val with
    | 0 => 3951
    | 1 => 3952
    | 2 => 3955
    | 3 => 3960
    | 4 => 3963
    | 5 => 3972
    | 6 => 3985
    | 7 => 4000
    | 8 => 4017
    | 9 => 4036
    | 10 => 4056
    | 11 => 4079
    | 12 => 4104
    | 13 => 4131
    | 14 => 4159
    | 15 => 4190
    | _ => 4223
  | 11 => match j.val with
    | 0 => 4224
    | 1 => 4225
    | 2 => 4228
    | 3 => 4233
    | 4 => 4236
    | 5 => 4245
    | 6 => 4258
    | 7 => 4273
    | 8 => 4290
    | 9 => 4309
    | 10 => 4330
    | 11 => 4353
    | 12 => 4378
    | 13 => 4405
    | 14 => 4433
    | 15 => 4464
    | _ => 4497
  | 12 => match j.val with
    | 0 => 4498
    | 1 => 4499
    | 2 => 4502
    | 3 => 4507
    | 4 => 4510
    | 5 => 4519
    | 6 => 4532
    | 7 => 4547
    | 8 => 4564
    | 9 => 4583
    | 10 => 4604
    | 11 => 4627
    | 12 => 4651
    | 13 => 4678
    | 14 => 4706
    | 15 => 4737
    | _ => 4770
  | 13 => match j.val with
    | 0 => 4225
    | 1 => 4224
    | 2 => 4773
    | 3 => 4778
    | 4 => 4781
    | 5 => 4790
    | 6 => 4803
    | 7 => 4818
    | 8 => 4835
    | 9 => 4853
    | 10 => 4873
    | 11 => 4895
    | 12 => 4919
    | 13 => 4945
    | 14 => 4972
    | 15 => 5001
    | _ => 5032
  | 14 => match j.val with
    | 0 => 5033
    | 1 => 5034
    | 2 => 5037
    | 3 => 5042
    | 4 => 5045
    | 5 => 5054
    | 6 => 5067
    | 7 => 5082
    | 8 => 5099
    | 9 => 5118
    | 10 => 5139
    | 11 => 5162
    | 12 => 5187
    | 13 => 5214
    | 14 => 5242
    | 15 => 5273
    | _ => 5306
  | 15 => match j.val with
    | 0 => 5307
    | 1 => 5307
    | 2 => 5310
    | 3 => 5315
    | 4 => 5318
    | 5 => 5327
    | 6 => 5340
    | 7 => 5355
    | 8 => 5372
    | 9 => 5391
    | 10 => 5412
    | 11 => 5435
    | 12 => 5460
    | 13 => 5487
    | 14 => 5515
    | 15 => 5546
    | _ => 5579
  | _ => match j.val with
    | 0 => 5580
    | 1 => 5581
    | 2 => 5584
    | 3 => 5589
    | 4 => 5592
    | 5 => 5601
    | 6 => 5614
    | 7 => 5629
    | 8 => 5646
    | 9 => 5665
    | 10 => 5686
    | 11 => 5709
    | 12 => 5734
    | 13 => 5761
    | 14 => 5789
    | 15 => 5820
    | _ => 5853


def intermediateProgramMatrix (h : ℝ) (i j : Fin 17) : ℝ :=
  evaluate matrixProgram h (intermediateProgramNode i j)
def coordinateRightProduct (A : Fin 17 → Fin 17 → ℝ) (i j : Fin 17) : ℝ :=
  ∑ b, A i b * coordinateChange b j
def coordinateLeftProduct (A : Fin 17 → Fin 17 → ℝ) (i j : Fin 17) : ℝ :=
  ∑ a, coordinateChange a i * A a j

theorem coordinate_left_right_eq_congruence (A : Fin 17 → Fin 17 → ℝ) (i j : Fin 17) :
    coordinateLeftProduct (coordinateRightProduct A) i j = coordinateCongruence A i j := by
  unfold coordinateLeftProduct coordinateRightProduct coordinateCongruence
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring
theorem coordinate_congruence_symmetric (A : Fin 17 → Fin 17 → ℝ)
    (hsym : ∀ a b, A a b = A b a) (i j : Fin 17) :
    coordinateCongruence A i j = coordinateCongruence A j i := by
  unfold coordinateCongruence
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [hsym b a]
  ring

#print axioms coordinate_left_right_eq_congruence
#print axioms coordinate_congruence_symmetric
end Thomson10IndexedMatrix
