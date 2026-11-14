import Mathlib
import LatticeProb.Prob.CrossingTimesScaling
import LatticeProb.Prob.CrossingTimesIncrements

/-!
# Chebyshev bound for the sum of crossing-time increments

The `n`-th `ε`-crossing time `σₙ = crossTime ε (B · ω) n` of a Brownian motion in `ℝ ^ d` is the
sum of the `n` increments `crossIncr B hcont ε k`, which are pairwise independent with the law of
the first crossing time `σ₁`.  With `E σ₁ = ε ^ 2 m` and `E σ₁ ^ 2 ≤ C ε ^ 4`, Chebyshev's
inequality gives

`P (σₙ = ∞ or |σₙ - n ε ^ 2 m| ≥ δ) ≤ n C ε ^ 4 / δ ^ 2`.

* `measure_sum_deviation_le`: Chebyshev for a sum of `n` pairwise independent square integrable
  variables with common mean `a` and second moments at most `V`;
* `IsBrownianSpace.lintegral_comp_crossIncr`: every increment has the law of `σ₁`;
* `IsBrownianSpace.measure_crossTime_deviation_le`: the bound above for given moment bounds;
* `exists_measure_crossTime_deviation_le`: the bound with `m` and `C` depending only on `d`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

section Chebyshev

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Chebyshev for a sum of pairwise independent variables.**  If `X k` are square integrable,
pairwise independent, with `E X k = a` and `E (X k) ^ 2 ≤ V`, then
`P (|∑_{k < n} X k - n a| ≥ δ) ≤ n V / δ ^ 2`. -/
theorem measure_sum_deviation_le [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ k, MemLp (X k) 2 P) (hind : Pairwise fun j k => IndepFun (X j) (X k) P)
    {a V : ℝ} (hmean : ∀ k, ∫ ω, X k ω ∂P = a) (hsq : ∀ k, ∫ ω, X k ω ^ 2 ∂P ≤ V)
    (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    P {ω | δ ≤ |∑ k ∈ Finset.range n, X k ω - n * a|} ≤ ENNReal.ofReal (n * V / δ ^ 2) := by
  have hS : MemLp (∑ k ∈ Finset.range n, X k) 2 P := memLp_finsetSum' _ (fun k _ => hX k)
  have hint : ∫ ω, (∑ k ∈ Finset.range n, X k) ω ∂P = n * a := by
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ (fun k _ => (hX k).integrable one_le_two)]
    simp [hmean]
  have hvar : variance (∑ k ∈ Finset.range n, X k) P ≤ n * V := by
    rw [IndepFun.variance_sum (fun k _ => hX k) (fun j _ k _ hjk => hind hjk)]
    calc ∑ k ∈ Finset.range n, variance (X k) P ≤ ∑ _k ∈ Finset.range n, V :=
          Finset.sum_le_sum fun k _ =>
            (variance_le_expectation_sq (hX k).aestronglyMeasurable).trans (hsq k)
      _ = n * V := by simp
  have hcheb := meas_ge_le_variance_div_sq hS hδ
  rw [hint] at hcheb
  simp only [Finset.sum_apply] at hcheb
  refine hcheb.trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr

end Chebyshev

section Increments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- **Every increment has the law of the first crossing time.**  Integrals of measurable
functions of `crossIncr k` equal those of `σ₁`. -/
theorem IsBrownianSpace.lintegral_comp_crossIncr (hd : 1 ≤ d) [IsProbabilityMeasure P]
    {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {ε : ℝ} (hε : 0 < ε) (k : ℕ)
    {g : ℝ≥0∞ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (crossIncr B hcont ε k ω) ∂P = ∫⁻ ω, g (crossTime ε (fun t => B t ω) 1) ∂P := by
  have h1 := hB.map_crossIncr_eq hd hm hcont hε k
  have e : (fun ω => crossTime ε (fun s => restartPath B hcont (fun _ => 0) ω s) 1) =
      fun ω => crossTime ε (fun t => B t ω) 1 :=
    funext fun ω => crossTime_restartPath_zero B hcont ε 1 ω
  rw [e] at h1
  rw [← lintegral_map hg (measurable_crossIncr B hm hcont hε k), h1,
    lintegral_map hg (measurable_crossTime_process B hm hcont hε 1)]

omit [MeasurableSpace Ω] in
/-- The `n`-th crossing time is the sum of the first `n` increments. -/
theorem crossTime_eq_sum_crossIncr (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hcont : ∀ ω, Continuous fun t => B t ω) (ε : ℝ) (n : ℕ) (ω : Ω) :
    crossTime ε (fun t => B t ω) n = ∑ k ∈ Finset.range n, crossIncr B hcont ε k ω := by
  induction n with
  | zero => simp [crossTime_zero]
  | succ n ih => rw [crossTime_succ_eq_add_crossIncr, ih, Finset.sum_range_succ]

/-- **Chebyshev for the crossing times of a Brownian motion.**  Given the first and second
moments of the first `ε`-crossing time, `σₙ` is within `δ` of `n ε ^ 2 m` except on an event of
probability at most `n C ε ^ 4 / δ ^ 2` (the event includes `σₙ = ∞`). -/
theorem IsBrownianSpace.measure_crossTime_deviation_le (hd : 1 ≤ d) [IsProbabilityMeasure P]
    {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {ε : ℝ} (hε : 0 < ε) {m : ℝ≥0∞} (hmtop : m ≠ ⊤)
    {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∫⁻ ω, crossTime ε (fun t => B t ω) 1 ∂P = ENNReal.ofReal (ε ^ 2) * m)
    (hsq : ∫⁻ ω, (crossTime ε (fun t => B t ω) 1) ^ 2 ∂P ≤ ENNReal.ofReal (C * ε ^ 4))
    (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    P {ω | crossTime ε (fun t => B t ω) n = ⊤ ∨
        δ ≤ |(crossTime ε (fun t => B t ω) n).toReal - n * (ε ^ 2 * m.toReal)|} ≤
      ENNReal.ofReal (n * (C * ε ^ 4) / δ ^ 2) := by
  have hne : ∫⁻ ω, crossTime ε (fun t => B t ω) 1 ∂P ≠ ⊤ := by
    rw [hmean]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmtop
  have hmI : ∀ k, Measurable (crossIncr B hcont ε k) := fun k => measurable_crossIncr B hm hcont hε k
  have hI1 : ∀ k, ∫⁻ ω, crossIncr B hcont ε k ω ∂P = ENNReal.ofReal (ε ^ 2) * m := fun k => by
    have := hB.lintegral_comp_crossIncr hd hm hcont hε k (g := id) measurable_id
    simp only [id] at this
    rw [this, hmean]
  have hI1ne : ∀ k, ∫⁻ ω, crossIncr B hcont ε k ω ∂P ≠ ⊤ := fun k => by
    rw [hI1 k]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmtop
  have hI2 : ∀ k, ∫⁻ ω, (crossIncr B hcont ε k ω) ^ 2 ∂P ≤ ENNReal.ofReal (C * ε ^ 4) := fun k => by
    have := hB.lintegral_comp_crossIncr hd hm hcont hε k (g := fun y => y ^ 2)
      (measurable_id.pow_const 2)
    rw [this]
    exact hsq
  have hI2ne : ∀ k, ∫⁻ ω, (crossIncr B hcont ε k ω) ^ 2 ∂P ≠ ⊤ := fun k =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hI2 k)
  have hfin : ∀ k, ∀ᵐ ω ∂P, crossIncr B hcont ε k ω ≠ ⊤ := fun k =>
    (ae_lt_top (hmI k) (hI1ne k)).mono fun ω h => h.ne
  have hfin2 : ∀ k, ∀ᵐ ω ∂P, (crossIncr B hcont ε k ω) ^ 2 < ⊤ := fun k =>
    ae_lt_top ((hmI k).pow_const 2) (hI2ne k)
  -- real-valued increments
  set X : ℕ → Ω → ℝ := fun k ω => (crossIncr B hcont ε k ω).toReal with hXdef
  have hXint : ∀ k, Integrable (X k) P := fun k =>
    integrable_toReal_of_lintegral_ne_top (hmI k).aemeasurable (hI1ne k)
  have hX2int : ∀ k, Integrable (fun ω => X k ω ^ 2) P := fun k => by
    have h := integrable_toReal_of_lintegral_ne_top ((hmI k).pow_const 2).aemeasurable (hI2ne k)
    refine h.congr (Eventually.of_forall fun ω => ?_)
    simp [hXdef, ENNReal.toReal_pow]
  have hXmem : ∀ k, MemLp (X k) 2 P := fun k =>
    (memLp_two_iff_integrable_sq (hXint k).aestronglyMeasurable).2 (hX2int k)
  have hXmean : ∀ k, ∫ ω, X k ω ∂P = ε ^ 2 * m.toReal := fun k => by
    have h := integral_toReal (hmI k).aemeasurable ((hfin k).mono fun ω h => h.lt_top)
    simp only [hXdef]
    rw [h, hI1 k, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg ε)]
  have hXsq : ∀ k, ∫ ω, X k ω ^ 2 ∂P ≤ C * ε ^ 4 := fun k => by
    have h := integral_toReal ((hmI k).pow_const 2).aemeasurable (hfin2 k)
    have e : ∫ ω, X k ω ^ 2 ∂P = ∫ ω, ((crossIncr B hcont ε k ω) ^ 2).toReal ∂P := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp [hXdef, ENNReal.toReal_pow]
    rw [e, h]
    calc (∫⁻ ω, (crossIncr B hcont ε k ω) ^ 2 ∂P).toReal
        ≤ (ENNReal.ofReal (C * ε ^ 4)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hI2 k)
      _ = C * ε ^ 4 := ENNReal.toReal_ofReal (by positivity)
  have hind : Pairwise fun j k => IndepFun (X j) (X k) P := by
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact (hB.indepFun_crossIncr hd hm hcont hε h).comp ENNReal.measurable_toReal
        ENNReal.measurable_toReal
    · exact ((hB.indepFun_crossIncr hd hm hcont hε h).comp ENNReal.measurable_toReal
        ENNReal.measurable_toReal).symm
  have hmain := measure_sum_deviation_le hXmem hind hXmean hXsq n hδ
  refine le_trans (measure_mono_ae ?_) hmain
  filter_upwards [ae_all_iff.2 hfin] with ω hω hmem
  have hsum : crossTime ε (fun t => B t ω) n = ∑ k ∈ Finset.range n, crossIncr B hcont ε k ω :=
    crossTime_eq_sum_crossIncr B hcont ε n ω
  have hfinsum : ∀ k ∈ Finset.range n, crossIncr B hcont ε k ω ≠ ⊤ := fun k _ => hω k
  rcases hmem with h | h
  · exfalso
    rw [hsum, ENNReal.sum_eq_top] at h
    obtain ⟨k, hk, hk'⟩ := h
    exact hfinsum k hk hk'
  · have : (crossTime ε (fun t => B t ω) n).toReal = ∑ k ∈ Finset.range n, X k ω := by
      rw [hsum, ENNReal.toReal_sum hfinsum]
    rw [this] at h
    exact h

end Increments

/-- **Chebyshev for the crossing times, with constants depending only on the dimension.**  For
`d ≥ 1` there are `m ∈ (0, ∞)` and `C ≥ 0` such that for every Brownian motion in `ℝ ^ d` with
continuous paths, `ε > 0`, `n` and `δ > 0`,
`P (σₙ = ∞ or |σₙ - n ε ^ 2 m| ≥ δ) ≤ n C ε ^ 4 / δ ^ 2`. -/
theorem exists_measure_crossTime_deviation_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ (m : ℝ≥0∞) (C : ℝ), 0 < m ∧ m < ∞ ∧ 0 ≤ C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
        IsBrownianSpace d x B P → (∀ t, StronglyMeasurable (B t)) →
        (∀ ω, Continuous fun t => B t ω) → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (δ : ℝ), 0 < δ →
          P {ω | crossTime ε (fun t => B t ω) n = ⊤ ∨
              δ ≤ |(crossTime ε (fun t => B t ω) n).toReal - n * (ε ^ 2 * m.toReal)|} ≤
            ENNReal.ofReal (n * (C * ε ^ 4) / δ ^ 2) := by
  obtain ⟨m, hm0, hmtop, hmean⟩ := exists_lintegral_crossTime_eq d hd
  obtain ⟨C, hC0, hCsq⟩ := exists_crossTime_one_sq_lintegral_le d hd
  refine ⟨m, C, hm0, hmtop, hC0, ?_⟩
  intro Ω _ P _ x B hB hm hcont ε hε n δ hδ
  exact hB.measure_crossTime_deviation_le hd hm hcont hε hmtop.ne hC0
    (hmean Ω P x B hB hm hcont ε hε) (hCsq Ω P x B hB hm hcont ε hε) n hδ

end LatticeProb
