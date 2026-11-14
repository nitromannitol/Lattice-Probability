import Mathlib
import LatticeProb.Prob.BrownianStopFunMarkov
import LatticeProb.Prob.LevelPassageStopShift
import LatticeProb.Prob.BrownianFirstPassageStrict

/-!
# Strong Markov property of two pairs of Brownian paths at level passages

Let `W` be the law on `C(ℝ≥0, ℝ)` of a standard real Brownian motion and let
`ν = (W ⊗ W) ⊗ (W ⊗ W)` be the law of two independent pairs of independent Brownian paths.

* `ae_hitFrom_neg_ne_top_pathLaw`: `W`-almost every path starts at `0` and reaches every level
  `-a ≤ 0` in finite time.
* `lintegral_pairStopAt_pairShiftAt`: at level `b ≥ 0`, each pair stopped at the first passage of its
  first path at `-b` (`pairStopAt b`) is independent of the pair of increments after that passage
  (`pairShiftAt b`), and the two pairs of increments again have law `ν`.
* `lintegral_cauchyLevel_mul_sub`: the level process `cauchyLevel` of the two pairs has, at fixed
  levels `0 ≤ aᵢ ≤ b ≤ c`, an increment `Y c - Y b` independent of the values `Y (aᵢ)` and with the
  law of `Y (c - b)`.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- A continuous path started at `0` that reaches `(-∞, -b]` has a finite first passage at
`-b ≤ 0`. -/
lemma hitFrom_neg_ne_top_of_le {w : C(ℝ≥0, ℝ)} (hw0 : w 0 = 0) {b : ℝ} (hb : 0 ≤ b) {s : ℝ≥0}
    (hs : w s ≤ -b) : hitFrom (-b) 0 (w : ℝ≥0 → ℝ) ≠ ⊤ := by
  have hmem : -b ∈ Icc (w s) (w 0) := ⟨hs, by rw [hw0]; linarith⟩
  obtain ⟨u, -, hwu⟩ := intermediate_value_Icc' zero_le w.continuous.continuousOn hmem
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (hitFrom_le zero_le hwu)

/-- Stopping a pair of paths at the first passage of its first path is measurable. -/
theorem measurable_pairStopAt (b : ℝ) : Measurable (pairStopAt b) :=
  (measurable_stopAt_of (measurable_hitFrom_neg_fst b) measurable_fst).prodMk
    (measurable_stopAt_of (measurable_hitFrom_neg_fst b) measurable_snd)

/-- The increments of a pair of paths after the first passage of its first path are measurable. -/
theorem measurable_pairShiftAt (b : ℝ) : Measurable (pairShiftAt b) :=
  (measurable_shiftPath_of (measurable_hitFrom_neg_fst b).ennreal_toNNReal measurable_fst).prodMk
    (measurable_shiftPath_of (measurable_hitFrom_neg_fst b).ennreal_toNNReal measurable_snd)

section PathLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- Under the Brownian path law, almost every path starts at `0` and has a finite first passage at
every level `-a ≤ 0`. -/
theorem ae_hitFrom_neg_ne_top_pathLaw (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) :
    ∀ᵐ w : C(ℝ≥0, ℝ) ∂(P.map (pathMap B hcont)),
      w 0 = 0 ∧ ∀ a : ℝ, 0 ≤ a → hitFrom (-a) 0 (w : ℝ≥0 → ℝ) ≠ ⊤ := by
  have hS : MeasurableSet {w : C(ℝ≥0, ℝ) |
      w 0 = 0 ∧ ∀ n : ℕ, hitFrom (-(n : ℝ)) 0 (w : ℝ≥0 → ℝ) ≠ ⊤} := by
    rw [Set.ofPred_and, Set.ofPred_forall]
    exact (measurableSet_eq_fun (continuous_eval_const 0).measurable measurable_const).inter
      (MeasurableSet.iInter fun n : ℕ =>
        (measurable_hitFrom (r := fun _ => 0) measurable_const (-(n : ℝ)))
          (measurableSet_singleton ⊤).compl)
  have hae : ∀ᵐ w : C(ℝ≥0, ℝ) ∂(P.map (pathMap B hcont)),
      w 0 = 0 ∧ ∀ n : ℕ, hitFrom (-(n : ℝ)) 0 (w : ℝ≥0 → ℝ) ≠ ⊤ := by
    refine (ae_map_iff (measurable_pathMap B hm hcont).aemeasurable hS).2 ?_
    filter_upwards [ae_all_iff.2 fun n : ℕ => LadderSet.ae_hitDrift_neg_lt_top hB hm hcont (n : ℝ),
      hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω h0
    have h0' : pathMap B hcont ω 0 = 0 := by rw [pathMap_apply]; exact h0
    refine ⟨h0', fun n => ?_⟩
    have hn := hω n
    unfold hitDrift at hn
    split_ifs at hn with hex
    · obtain ⟨s, hs⟩ := hex
      simp only [zero_mul, add_zero] at hs
      refine hitFrom_neg_ne_top_of_le h0' (Nat.cast_nonneg n) (s := s) ?_
      rw [pathMap_apply]
      linarith
    · exact absurd hn (lt_irrefl _)
  filter_upwards [hae] with w hw
  refine ⟨hw.1, fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge a
  exact ne_top_of_le_ne_top (hw.2 n) (hitFrom_neg_le_hitFrom_neg hw.1 ha hn)

/-- **Strong Markov property of two pairs of Brownian paths at level passages.** Under
`ν = (W ⊗ W) ⊗ (W ⊗ W)`, the two pairs stopped at the first passages of their first paths at
`-b ≤ 0` are independent of the two pairs of increments after these passages, and the latter have
law `ν`. -/
theorem lintegral_pairStopAt_pairShiftAt (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 ≤ b)
    {F : ((C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) ×
      ((C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ q, F ((pairStopAt b q.1, pairStopAt b q.2), (pairShiftAt b q.1, pairShiftAt b q.2))
        ∂(((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
          ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont)))) =
      ∫⁻ q, ∫⁻ q', F ((pairStopAt b q.1, pairStopAt b q.2), q')
        ∂(((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
          ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))))
        ∂(((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
          ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont)))) := by
  set W := P.map (pathMap B hcont)
  have : IsProbabilityMeasure W :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pathMap B hm hcont).aemeasurable).2
      inferInstance
  set μ := W.prod W
  set S := pairStopAt b
  set H := pairShiftAt b
  have hS : Measurable S := measurable_pairStopAt b
  have hH : Measurable H := measurable_pairShiftAt b
  have hfin : ∀ᵐ w : C(ℝ≥0, ℝ) ∂W, hitFrom (-b) 0 (w : ℝ≥0 → ℝ) < ⊤ := by
    filter_upwards [ae_hitFrom_neg_ne_top_pathLaw hB hm hcont] with w hw
    exact lt_top_iff_ne_top.2 (hw.2 b hb)
  have hpair : ∀ {G : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) → ℝ≥0∞},
      Measurable G → ∫⁻ p, G (S p, H p) ∂μ = ∫⁻ p, ∫⁻ q, G (S p, q) ∂μ ∂μ := by
    intro G hG
    exact lintegral_pair_stopAt_shiftPath hB hm hcont hB hm hcont
      (measurable_hitFrom (r := fun _ => 0) measurable_const (-b)) (isStopFun_hitFrom_zero (-b))
      hfin hG
  have hSH : Measurable fun q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) =>
      ((S q.1, S q.2), (H q.1, H q.2)) :=
    ((hS.comp measurable_fst).prodMk (hS.comp measurable_snd)).prodMk
      ((hH.comp measurable_fst).prodMk (hH.comp measurable_snd))
  have hm3 : Measurable fun z : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) =>
      ∫⁻ q₂, F ((S z.1, S z.2), (H z.1, q₂)) ∂μ := by
    refine Measurable.lintegral_prod_right'
      (f := fun y : ((C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) ×
        (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) => F ((S y.1.1, S y.1.2), (H y.1.1, y.2))) ?_
    exact hF.comp (((hS.comp (measurable_fst.comp measurable_fst)).prodMk
      (hS.comp (measurable_snd.comp measurable_fst))).prodMk
        ((hH.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))
  have hΦ : Measurable fun q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) =>
      ∫⁻ q', F ((S q.1, S q.2), q') ∂(μ.prod μ) := by
    refine Measurable.lintegral_prod_right'
      (f := fun y : ((C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) ×
        ((C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) => F ((S y.1.1, S y.1.2), y.2)) ?_
    exact hF.comp (((hS.comp (measurable_fst.comp measurable_fst)).prodMk
      (hS.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd)
  calc ∫⁻ q, F ((S q.1, S q.2), (H q.1, H q.2)) ∂(μ.prod μ)
      = ∫⁻ p₁, ∫⁻ p₂, F ((S p₁, S p₂), (H p₁, H p₂)) ∂μ ∂μ :=
        lintegral_prod _ (hF.comp hSH).aemeasurable
    _ = ∫⁻ p₁, ∫⁻ p₂, ∫⁻ q₂, F ((S p₁, S p₂), (H p₁, q₂)) ∂μ ∂μ ∂μ := by
        refine lintegral_congr fun p₁ => ?_
        exact hpair (G := fun z => F ((S p₁, z.1), (H p₁, z.2)))
          (hF.comp ((measurable_const.prodMk measurable_fst).prodMk
            (measurable_const.prodMk measurable_snd)))
    _ = ∫⁻ p₂, ∫⁻ p₁, ∫⁻ q₂, F ((S p₁, S p₂), (H p₁, q₂)) ∂μ ∂μ ∂μ :=
        lintegral_lintegral_swap hm3.aemeasurable
    _ = ∫⁻ p₂, ∫⁻ p₁, ∫⁻ q₁, ∫⁻ q₂, F ((S p₁, S p₂), (q₁, q₂)) ∂μ ∂μ ∂μ ∂μ := by
        refine lintegral_congr fun p₂ => ?_
        refine hpair (G := fun z => ∫⁻ q₂, F ((z.1, S p₂), (z.2, q₂)) ∂μ) ?_
        refine Measurable.lintegral_prod_right'
          (f := fun y : ((C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) ×
            (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) => F ((y.1.1, S p₂), (y.1.2, y.2))) ?_
        exact hF.comp (((measurable_fst.comp measurable_fst).prodMk measurable_const).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    _ = ∫⁻ p₂, ∫⁻ p₁, ∫⁻ q', F ((S p₁, S p₂), q') ∂(μ.prod μ) ∂μ ∂μ := by
        refine lintegral_congr fun p₂ => lintegral_congr fun p₁ => ?_
        exact (lintegral_prod _ (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
    _ = ∫⁻ q, ∫⁻ q', F ((S q.1, S q.2), q') ∂(μ.prod μ) ∂(μ.prod μ) :=
        (lintegral_prod_symm _ hΦ.aemeasurable).symm

/-- **Independent increments of the level-passage process.** Under `ν = (W ⊗ W) ⊗ (W ⊗ W)` and for
levels `0 ≤ aᵢ ≤ b ≤ c`, the values `Y (aᵢ)` of the level process `Y = cauchyLevel` are independent
of the increment `Y c - Y b`, which has the law of `Y (c - b)`. -/
theorem lintegral_cauchyLevel_mul_sub (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {n : ℕ} {a : Fin n → ℝ} {b c : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b) (hb : 0 ≤ b) (hbc : b ≤ c)
    {F : (Fin n → ℝ) → ℝ≥0∞} (hF : Measurable F) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ q, F (fun i => cauchyLevel (a i) q) * G (cauchyLevel c q - cauchyLevel b q)
        ∂(((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
          ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont)))) =
      (∫⁻ q, F (fun i => cauchyLevel (a i) q)
        ∂(((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
          ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))))) *
      ∫⁻ q, G (cauchyLevel (c - b) q)
        ∂(((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
          ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont)))) := by
  set W := P.map (pathMap B hcont)
  have : IsProbabilityMeasure W :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pathMap B hm hcont).aemeasurable).2
      inferInstance
  set ν := (W.prod W).prod (W.prod W)
  have hW := ae_hitFrom_neg_ne_top_pathLaw hB hm hcont
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := W.prod W) (ν := W.prod W)).ae
    ((Measure.quasiMeasurePreserving_fst (μ := W) (ν := W)).ae hW)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := W.prod W) (ν := W.prod W)).ae
    ((Measure.quasiMeasurePreserving_fst (μ := W) (ν := W)).ae hW)
  have hc : 0 ≤ c := hb.trans hbc
  have hstop : ∀ᵐ q ∂ν, F (fun i => cauchyLevel (a i) (pairStopAt b q.1, pairStopAt b q.2)) =
      F (fun i => cauchyLevel (a i) q) := by
    filter_upwards [h1, h2] with q hq1 hq2
    exact congrArg F (funext fun i => cauchyLevel_pairStopAt hq1.1 hq2.1 (ha i) (hab i))
  have hshift : ∀ᵐ q ∂ν, G (cauchyLevel c q - cauchyLevel b q) =
      G (cauchyLevel (c - b) (pairShiftAt b q.1, pairShiftAt b q.2)) := by
    filter_upwards [h1, h2] with q hq1 hq2
    exact congrArg G
      (cauchyLevel_sub_eq_pairShiftAt hq1.1 hq2.1 hb hbc (hq1.2 c hc) (hq2.2 c hc))
  have hYa : Measurable fun s : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) => F (fun i => cauchyLevel (a i) s) :=
    hF.comp (measurable_pi_iff.2 fun i => measurable_cauchyLevel (a i))
  have hYc : Measurable fun s : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) => G (cauchyLevel (c - b) s) :=
    hG.comp (measurable_cauchyLevel (c - b))
  have hΦ : Measurable fun y : ((C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) × ((C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) =>
      F (fun i => cauchyLevel (a i) y.1) * G (cauchyLevel (c - b) y.2) :=
    (hYa.comp measurable_fst).mul (hYc.comp measurable_snd)
  have key := lintegral_pairStopAt_pairShiftAt hB hm hcont hb hΦ
  calc ∫⁻ q, F (fun i => cauchyLevel (a i) q) * G (cauchyLevel c q - cauchyLevel b q) ∂ν
      = ∫⁻ q, F (fun i => cauchyLevel (a i) (pairStopAt b q.1, pairStopAt b q.2)) *
          G (cauchyLevel (c - b) (pairShiftAt b q.1, pairShiftAt b q.2)) ∂ν := by
        refine lintegral_congr_ae ?_
        filter_upwards [hstop, hshift] with q hq hq'
        rw [hq, hq']
    _ = ∫⁻ q, ∫⁻ q', F (fun i => cauchyLevel (a i) (pairStopAt b q.1, pairStopAt b q.2)) *
          G (cauchyLevel (c - b) q') ∂ν ∂ν := key
    _ = ∫⁻ q, F (fun i => cauchyLevel (a i) (pairStopAt b q.1, pairStopAt b q.2)) *
          ∫⁻ q', G (cauchyLevel (c - b) q') ∂ν ∂ν := by
        refine lintegral_congr fun q => ?_
        exact lintegral_const_mul _ hYc
    _ = (∫⁻ q, F (fun i => cauchyLevel (a i) (pairStopAt b q.1, pairStopAt b q.2)) ∂ν) *
          ∫⁻ q', G (cauchyLevel (c - b) q') ∂ν :=
        lintegral_mul_const _ (hYa.comp (((measurable_pairStopAt b).comp measurable_fst).prodMk
          ((measurable_pairStopAt b).comp measurable_snd)))
    _ = _ := by
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [hstop] with q hq
        exact hq

end PathLaw

end LatticeProb
