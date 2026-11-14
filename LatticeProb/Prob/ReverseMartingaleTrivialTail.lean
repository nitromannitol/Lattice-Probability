import LatticeProb.Prob.TrivialSigma
import LatticeProb.Bonanno.ReflectedGMS.Limit.ReverseRationalAE

/-!
# Lévy's downward theorem along the integers, with a trivial tail

Let `P` be a finite measure and `ℱ : ℕ → MeasurableSpace Ω` an antitone sequence of
sub-σ-algebras. For a real integrable `f`, the conditional expectations `P[f | ℱ n]` converge
almost everywhere to `P[f | ⨅ n, ℱ n]` (the backward martingale convergence theorem, Durrett,
*Probability: Theory and Examples*, Theorem 5.6.1). When the tail σ-algebra `⨅ n, ℱ n` is trivial
(every event has probability `0` or `1`), the limit is the mean `∫ f ∂P`. For a nonnegative `f`
of infinite mean, the means of the truncations `min f C` tend to infinity, so any random sequence
dominating the conditional expectations of all the truncations tends to infinity almost surely.

This is the probabilistic part of the ergodic averaging lemma for uniform dyadic systems in
Gwynne, Miller and Sheffield, *An invariance principle for ergodic scale-free random environments*
(arXiv 1807.07515), Lemma 2.7: there the averages over the squares containing the origin are
conditional expectations given a decreasing sequence of σ-algebras with trivial intersection.

## Main statements

* `LatticeProb.ReverseMartingale.tendsto_condExp_iInf_ae`: Lévy's downward theorem, almost sure,
  along `ℕ` (from the rational-parameter version
  `ReflectedGMS.ReverseRationalAE.tendsto_condExp_iInf_rat_ae`).
* `condExp_ae_eq_integral_of_isTrivialSigma`: conditional expectation given a trivial σ-algebra.
* `tendsto_condExp_integral_ae_of_isTrivialSigma`: the trivial-tail case, limit `∫ f ∂P`.
* `tendsto_integral_min_natCast_atTop`: truncated means of a nonnegative non-integrable function.
* `tendsto_atTop_of_condExp_min_le`: the infinite-mean case.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LatticeProb.ReverseMartingale

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- **Lévy's downward theorem** (backward martingale convergence), almost sure form along the
integers: for a finite measure, an antitone sequence of sub-σ-algebras `ℱ n` and a real integrable
`f`, `P[f | ℱ n] → P[f | ⨅ n, ℱ n]` almost everywhere. -/
theorem tendsto_condExp_iInf_ae [IsFiniteMeasure P] {ℱ : ℕ → MeasurableSpace Ω}
    (hle : ∀ n, ℱ n ≤ m0) (hanti : Antitone ℱ) {f : Ω → ℝ} (hf : Integrable f P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => P[f|ℱ n] ω) atTop (𝓝 (P[f|⨅ n, ℱ n] ω)) := by
  have hanti' : Antitone fun q : ℚ => ℱ ⌈q⌉₊ := fun q r hqr => hanti (Nat.ceil_mono hqr)
  have hinf : (⨅ q : ℚ, ℱ ⌈q⌉₊) = ⨅ n, ℱ n := by
    refine le_antisymm (le_iInf fun n => iInf_le_of_le (n : ℚ) ?_) (le_iInf fun q => iInf_le _ _)
    rw [Nat.ceil_natCast]
  have h := ReflectedGMS.ReverseRationalAE.tendsto_condExp_iInf_rat_ae (P := P)
    (ms := fun q : ℚ => ℱ ⌈q⌉₊) (fun q => hle _) hanti' hf
  rw [hinf] at h
  filter_upwards [h] with ω hω
  simpa [Function.comp_def] using hω.comp tendsto_natCast_atTop_atTop

/-- Conditional expectation given a trivial σ-algebra: for a probability measure and a
σ-algebra `m ≤ m0` all of whose events have probability `0` or `1`, `P[f | m]` is almost
everywhere the mean of `f`. -/
theorem condExp_ae_eq_integral_of_isTrivialSigma [IsProbabilityMeasure P] (hm : m ≤ m0)
    (htriv : IsTrivialSigma m P) {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) :
    P[f|m] =ᵐ[P] fun _ => ∫ x, f x ∂P := by
  have hind : Indep m0 m P := (htriv.indep hm).symm
  calc P[f|m] =ᵐ[P] P[hf.mk f|m] := condExp_congr_ae hf.ae_eq_mk
    _ =ᵐ[P] fun _ => ∫ x, hf.mk f x ∂P :=
      condExp_indep_eq le_rfl hm hf.stronglyMeasurable_mk hind
    _ = fun _ => ∫ x, f x ∂P := by rw [integral_congr_ae hf.ae_eq_mk.symm]

/-- **Backward martingale convergence with a trivial tail**: for a probability measure, an
antitone sequence of sub-σ-algebras `ℱ n` whose intersection is trivial, and a real integrable
`f`, `P[f | ℱ n] → ∫ f ∂P` almost everywhere. -/
theorem tendsto_condExp_integral_ae_of_isTrivialSigma [IsProbabilityMeasure P]
    {ℱ : ℕ → MeasurableSpace Ω} (hle : ∀ n, ℱ n ≤ m0) (hanti : Antitone ℱ)
    (htriv : IsTrivialSigma (⨅ n, ℱ n) P) {f : Ω → ℝ} (hf : Integrable f P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => P[f|ℱ n] ω) atTop (𝓝 (∫ x, f x ∂P)) := by
  filter_upwards [tendsto_condExp_iInf_ae hle hanti hf,
    condExp_ae_eq_integral_of_isTrivialSigma ((iInf_le _ 0).trans (hle 0)) htriv hf.1]
    with ω h1 h2
  rwa [h2] at h1

/-- The truncations `min f C` of a nonnegative function are integrable for a finite measure. -/
theorem integrable_min_natCast [IsFiniteMeasure P] {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[P] f)
    (hfm : AEStronglyMeasurable f P) (C : ℕ) : Integrable (fun x => min (f x) (C : ℝ)) P :=
  (integrable_const (C : ℝ)).mono' (hfm.aemeasurable.min aemeasurable_const).aestronglyMeasurable
    (hf0.mono fun x hx => by
      have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
      have h0 : 0 ≤ min (f x) (C : ℝ) := le_min hx hC
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact min_le_right _ _)

/-- For a nonnegative function of infinite mean (not integrable) under a finite measure, the means
of the truncations `min f C` tend to infinity as `C → ∞`. -/
theorem tendsto_integral_min_natCast_atTop [IsFiniteMeasure P] {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[P] f)
    (hfm : AEStronglyMeasurable f P) (hfi : ¬ Integrable f P) :
    Tendsto (fun C : ℕ => ∫ x, min (f x) (C : ℝ) ∂P) atTop atTop := by
  have htop : ∫⁻ x, ENNReal.ofReal (f x) ∂P = ∞ := by
    by_contra h
    exact hfi ⟨hfm, (hasFiniteIntegral_iff_ofReal hf0).2 (lt_top_iff_ne_top.2 h)⟩
  have hlim : Tendsto (fun C : ℕ => ∫⁻ x, ENNReal.ofReal (min (f x) (C : ℝ)) ∂P) atTop
      (𝓝 ∞) := by
    rw [← htop]
    refine lintegral_tendsto_of_tendsto_of_monotone (fun C => ?_) ?_ ?_
    · exact (hfm.aemeasurable.min aemeasurable_const).ennreal_ofReal
    · exact ae_of_all _ fun x C D hCD =>
        ENNReal.ofReal_le_ofReal (min_le_min_left (f x) (by exact_mod_cast hCD))
    · refine ae_of_all _ fun x => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈f x⌉₊] with C hC
      rw [min_eq_left ((Nat.le_ceil _).trans (by exact_mod_cast hC))]
  rw [tendsto_atTop]
  intro M
  filter_upwards [(tendsto_order.1 hlim).1 (ENNReal.ofReal M) ENNReal.ofReal_lt_top] with C hC
  have hmin0 : 0 ≤ᵐ[P] fun x => min (f x) (C : ℝ) :=
    hf0.mono fun x hx => le_min hx (Nat.cast_nonneg C)
  rw [integral_eq_lintegral_of_nonneg_ae hmin0 (integrable_min_natCast hf0 hfm C).1]
  have hfin : ∫⁻ x, ENNReal.ofReal (min (f x) (C : ℝ)) ∂P ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_
      (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (min_le_right (f x) (C : ℝ)))
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P _)
  rcases le_or_gt M 0 with hM0 | hM0
  · exact hM0.trans ENNReal.toReal_nonneg
  · exact ((ENNReal.ofReal_lt_iff_lt_toReal hM0.le hfin).1 hC).le

/-- **Infinite mean.** For a probability measure, an antitone sequence of sub-σ-algebras with
trivial intersection and a nonnegative non-integrable `f`: if, for every truncation level
`C ∈ ℕ`, the random sequence `A n` almost surely dominates `P[min f C | ℱ n]` for all `n`, then
`A n → ∞` almost surely. -/
theorem tendsto_atTop_of_condExp_min_le [IsProbabilityMeasure P] {ℱ : ℕ → MeasurableSpace Ω}
    (hle : ∀ n, ℱ n ≤ m0) (hanti : Antitone ℱ) (htriv : IsTrivialSigma (⨅ n, ℱ n) P)
    {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[P] f) (hfm : AEStronglyMeasurable f P) (hfi : ¬ Integrable f P)
    {A : ℕ → Ω → ℝ}
    (hA : ∀ C : ℕ, ∀ᵐ ω ∂P, ∀ n, P[fun x => min (f x) (C : ℝ)|ℱ n] ω ≤ A n ω) :
    ∀ᵐ ω ∂P, Tendsto (fun n => A n ω) atTop atTop := by
  have hconv : ∀ᵐ ω ∂P, ∀ C : ℕ, Tendsto (fun n => P[fun x => min (f x) (C : ℝ)|ℱ n] ω) atTop
      (𝓝 (∫ x, min (f x) (C : ℝ) ∂P)) := ae_all_iff.2 fun C =>
    tendsto_condExp_integral_ae_of_isTrivialSigma hle hanti htriv (integrable_min_natCast hf0 hfm C)
  have hmean := tendsto_integral_min_natCast_atTop hf0 hfm hfi
  filter_upwards [hconv, ae_all_iff.2 hA] with ω hω hAω
  rw [tendsto_atTop]
  intro M
  obtain ⟨C, hC⟩ := (tendsto_atTop.1 hmean (M + 1)).exists
  filter_upwards [(tendsto_order.1 (hω C)).1 M (by linarith)] with n hn
  exact (hn.trans_le (hAω C n)).le

end LatticeProb.ReverseMartingale
