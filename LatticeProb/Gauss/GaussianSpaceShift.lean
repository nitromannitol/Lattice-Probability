import LatticeProb.Gauss.RegressionDualCauchy

/-!
# Shifts by covariance limits in a centred Gaussian space

Two ingredients for comparing the conditional laws of a Gaussian process given countably many coordinates.

* **Fubini for an independent pair.** If `X` and `W` are independent random variables, then for every measurable set
  `T` of pairs, `P((X, W) ∈ T) = ∫ P((X, W ω') ∈ T) dP(ω')`: the second variable may be frozen and integrated out.
* **Cameron-Martin for covariance limits.** Let `R i`, `i ∈ κ`, and `ζ n`, `n ∈ ℕ`, lie in a centred Gaussian space,
  with `(ζ n)_n` Cauchy in `L²` and `Cov(R i, ζ n) → c i` for every `i`. Then a measurable set of paths has
  probability zero for `R` if and only if it has probability zero for the shifted family `R + c`. The forward
  implication is `LatticeProb.Gauss.measure_shift_eq_zero_of_tendsto_covariance` applied to the process `R ⊕ ζ`; the
  reverse one is the forward one for `R ⊕ (-ζ)`, whose covariance limits are `-c`.

## Main results

* `LatticeProb.Gauss.measure_pair_eq_lintegral_of_indepFun`
* `LatticeProb.Gauss.measure_add_eq_zero_of_tendsto_covariance_of_cauchy`
* `LatticeProb.Gauss.measure_add_eq_zero_iff_of_tendsto_covariance_of_cauchy`
-/

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory Filter Topology
open LatticeProb.GaussianClosure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Fubini for an independent pair.** For independent measurable `X` and `W` and a measurable set `T` of pairs,
`P((X, W) ∈ T) = ∫ P((X, W ω') ∈ T) dP(ω')`. -/
theorem measure_pair_eq_lintegral_of_indepFun [IsProbabilityMeasure P] {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {X : Ω → α} {W : Ω → β} (hX : Measurable X) (hW : Measurable W) (hXW : IndepFun X W P)
    {T : Set (α × β)} (hT : MeasurableSet T) :
    P {ω | (X ω, W ω) ∈ T} = ∫⁻ ω', P {ω | (X ω, W ω') ∈ T} ∂P := by
  have h1 : P {ω | (X ω, W ω) ∈ T} = (P.map fun ω => (X ω, W ω)) T := by
    rw [Measure.map_apply (hX.prodMk hW) hT]
    rfl
  rw [h1, (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hW.aemeasurable).1 hXW,
    Measure.prod_apply_symm hT, lintegral_map (measurable_measure_prodMk_right hT) hW]
  refine lintegral_congr fun ω' => ?_
  rw [Measure.map_apply hX (measurable_prodMk_right hT)]
  rfl

/-- Elements of a centred Gaussian space have mean zero. -/
theorem integral_eq_zero_of_isCentredGaussianSpace {M : Set (Ω → ℝ)} (hM : IsCentredGaussianSpace P M)
    {Y : Ω → ℝ} (hY : Y ∈ M) : P[Y] = 0 := by
  obtain ⟨hm, v, hv⟩ := hM Y hY
  calc P[Y] = ∫ x, x ∂(P.map Y) := (integral_map hm.aemeasurable aestronglyMeasurable_id).symm
    _ = 0 := by rw [hv, integral_id_gaussianReal]

/-- **Cameron-Martin for covariance limits.** Let `R i` and `ζ n` lie in a centred Gaussian space, with `(ζ n)_n`
Cauchy in `L²` and `Cov(R i, ζ n) → c i` for every `i`. Every measurable set of paths of probability zero for `R` has
probability zero for the shifted family `R + c`. -/
theorem measure_add_eq_zero_of_tendsto_covariance_of_cauchy [IsProbabilityMeasure P] {κ : Type*}
    {M : Submodule ℝ (Ω → ℝ)} (hM : IsCentredGaussianSpace P M) {R : κ → Ω → ℝ} {ζ : ℕ → Ω → ℝ}
    (hR : ∀ i, R i ∈ M) (hζ : ∀ n, ζ n ∈ M)
    (hcauchy : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N, ∫ ω, (ζ n ω - ζ k ω) ^ 2 ∂P < ε)
    {c : κ → ℝ} (hc : ∀ i, Tendsto (fun n => cov[R i, ζ n; P]) atTop (𝓝 (c i)))
    {S : Set (κ → ℝ)} (hS : MeasurableSet S) (h0 : P {ω | (fun i => R i ω) ∈ S} = 0) :
    P {ω | (fun i => R i ω + c i) ∈ S} = 0 := by
  have hY : ∀ t, Sum.elim R ζ t ∈ M := fun t => by
    cases t with
    | inl i => exact hR i
    | inr n => exact hζ n
  have hYm : ∀ t, Measurable (Sum.elim R ζ t) := fun t => (hM _ (hY t)).1
  have hcen : ∀ t, P[Sum.elim R ζ t] = 0 := fun t => integral_eq_zero_of_isCentredGaussianSpace hM (hY t)
  have hζ2 : ∀ n, MemLp (ζ n) 2 P := fun n => hM.memLp (hζ n)
  obtain ⟨ξ, -, -, hξ2, hξL2, -, -⟩ := exists_tendsto_L2_of_cauchy_L2 hζ2 hcauchy
  have hcov : ∀ t, Tendsto (fun n => cov[Sum.elim R ζ t, Sum.elim R ζ (Sum.inr n); P]) atTop
      (𝓝 (Sum.elim c (fun j => cov[ξ, ζ j; P]) t)) := by
    rintro (i | j)
    · exact hc i
    · exact (tendsto_covariance_of_tendsto_L2 hζ2 hξ2 (hζ2 j) hξL2).congr fun n => covariance_comm _ _
  have hS' : MeasurableSet ((fun f : κ ⊕ ℕ → ℝ => fun i => f (Sum.inl i)) ⁻¹' S) :=
    (measurable_pi_iff.mpr fun i => measurable_pi_apply (Sum.inl i)) hS
  exact measure_shift_eq_zero_of_tendsto_covariance (isGaussianProcess_of_isCentredGaussianSpace hM hY) hYm hcen
    Sum.inr _ hcauchy hcov hS' h0

/-- **Cameron-Martin for covariance limits, both directions.** Under the hypotheses of
`measure_add_eq_zero_of_tendsto_covariance_of_cauchy`, a measurable set of paths has probability zero for `R + c`
if and only if it has probability zero for `R`. -/
theorem measure_add_eq_zero_iff_of_tendsto_covariance_of_cauchy [IsProbabilityMeasure P] {κ : Type*}
    {M : Submodule ℝ (Ω → ℝ)} (hM : IsCentredGaussianSpace P M) {R : κ → Ω → ℝ} {ζ : ℕ → Ω → ℝ}
    (hR : ∀ i, R i ∈ M) (hζ : ∀ n, ζ n ∈ M)
    (hcauchy : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N, ∫ ω, (ζ n ω - ζ k ω) ^ 2 ∂P < ε)
    {c : κ → ℝ} (hc : ∀ i, Tendsto (fun n => cov[R i, ζ n; P]) atTop (𝓝 (c i)))
    {S : Set (κ → ℝ)} (hS : MeasurableSet S) :
    P {ω | (fun i => R i ω + c i) ∈ S} = 0 ↔ P {ω | (fun i => R i ω) ∈ S} = 0 := by
  refine ⟨fun h => ?_, measure_add_eq_zero_of_tendsto_covariance_of_cauchy hM hR hζ hcauchy hc hS⟩
  have hS2 : MeasurableSet ((fun r : κ → ℝ => fun i => r i + c i) ⁻¹' S) :=
    (measurable_pi_iff.mpr fun i => (measurable_pi_apply i).add_const (c i)) hS
  have hcauchy' : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N, ∫ ω, (-ζ n ω - -ζ k ω) ^ 2 ∂P < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun n hn k hk => ?_⟩
    have hsq : ∀ ω, (-ζ n ω - -ζ k ω) ^ 2 = (ζ n ω - ζ k ω) ^ 2 := fun ω => by ring
    simp_rw [hsq]
    exact hN n hn k hk
  have hc' : ∀ i, Tendsto (fun n => cov[R i, fun ω => -ζ n ω; P]) atTop (𝓝 (-c i)) := fun i =>
    (hc i).neg.congr fun n => covariance_fun_neg_right.symm
  have h2 := measure_add_eq_zero_of_tendsto_covariance_of_cauchy hM hR (ζ := fun n ω => -ζ n ω)
    (fun n => M.neg_mem (hζ n)) hcauchy' hc' hS2 h
  have hset : {ω | (fun i => R i ω + -c i) ∈ (fun r : κ → ℝ => fun i => r i + c i) ⁻¹' S} =
      {ω | (fun i => R i ω) ∈ S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, neg_add_cancel_right]
  rw [← hset]
  exact h2

end LatticeProb.Gauss
