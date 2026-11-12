/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.LowerAssemblyAux1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Deterministic lemmas for the lower assembly (`LA`)

* `riemannCost` is nonnegative, depends only on the field at the Riemann points, and is
  multiplied by at most `e^{ξ T}` when the field increases by at most `T` there.
* Continuity of `v ↦ riemannCost ξ N z (extS S v)` for a finite vector `v` indexed by `S`
  (used for the measurability of the events in finite dimensions).
* `lfppDistance ξ φ > 0` for every continuous field `φ` (chord ≤ arclength for admissible
  paths).  This is needed because `Real.log 0 = 0`: without it the ratio `log D / log ε`
  could be `0` on `{D = 0}`.  (The analytic lemmas are adapted from the `J42` development.)
* Point masses as degenerate segments: `avg` and `circCov` of `[(1, s, s)]`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Classical

namespace LQGDimension.LowerAsm

open Blueprint.Draft

/-! ## Riemann costs -/

theorem riemannCost_nonneg (ξ : ℝ) (N : ℕ) (z : List ℂ) (φ : ℂ → ℝ) :
    0 ≤ riemannCost ξ N z φ := by
  unfold riemannCost
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  refine mul_nonneg (mul_nonneg (norm_nonneg _) (by positivity)) ?_
  exact Finset.sum_nonneg fun q _ => (Real.exp_pos _).le

theorem riemannCost_congr (ξ : ℝ) (N : ℕ) (z : List ℂ) {φ ψ : ℂ → ℝ}
    (h : ∀ p ∈ riemannPts N z, φ p = ψ p) : riemannCost ξ N z φ = riemannCost ξ N z ψ := by
  unfold riemannCost
  congr 1
  refine List.map_congr_left fun e he => ?_
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [h _ ⟨e, he, q, Finset.mem_range.1 hq, rfl⟩]

theorem riemannCost_le_exp_mul (ξ : ℝ) (hξ : 0 ≤ ξ) (N : ℕ) (z : List ℂ) {φ ψ : ℂ → ℝ}
    (T : ℝ) (h : ∀ p ∈ riemannPts N z, φ p ≤ ψ p + T) :
    riemannCost ξ N z φ ≤ Real.exp (ξ * T) * riemannCost ξ N z ψ := by
  unfold riemannCost
  rw [← List.sum_map_mul_left]
  refine List.sum_le_sum fun e he => ?_
  have hterm : ∀ q ∈ Finset.range N,
      Real.exp (ξ * φ (e.1 + (((q : ℝ) / N : ℝ) : ℂ) * (e.2 - e.1))) ≤
        Real.exp (ξ * T) * Real.exp (ξ * ψ (e.1 + (((q : ℝ) / N : ℝ) : ℂ) * (e.2 - e.1))) := by
    intro q hq
    rw [← Real.exp_add, Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_left (h _ ⟨e, he, q, Finset.mem_range.1 hq, rfl⟩) hξ
    linarith
  calc ‖e.2 - e.1‖ * ((1 : ℝ) / N) *
        ∑ q ∈ Finset.range N, Real.exp (ξ * φ (e.1 + (((q : ℝ) / N : ℝ) : ℂ) * (e.2 - e.1)))
      ≤ ‖e.2 - e.1‖ * ((1 : ℝ) / N) * ∑ q ∈ Finset.range N,
          Real.exp (ξ * T) * Real.exp (ξ * ψ (e.1 + (((q : ℝ) / N : ℝ) : ℂ) * (e.2 - e.1))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
          (mul_nonneg (norm_nonneg _) (by positivity))
    _ = Real.exp (ξ * T) * (‖e.2 - e.1‖ * ((1 : ℝ) / N) * ∑ q ∈ Finset.range N,
          Real.exp (ξ * ψ (e.1 + (((q : ℝ) / N : ℝ) : ℂ) * (e.2 - e.1)))) := by
        rw [← Finset.mul_sum]
        ring

/-- Extension by zero of a vector indexed by a finite set of points. -/
def extS (S : Finset ℂ) (v : S → ℝ) (z : ℂ) : ℝ :=
  if hz : z ∈ S then v ⟨z, hz⟩ else 0

theorem extS_of_mem {S : Finset ℂ} (v : S → ℝ) {z : ℂ} (hz : z ∈ S) :
    extS S v z = v ⟨z, hz⟩ := by
  simp [extS, hz]

theorem continuous_extS_apply (S : Finset ℂ) (z : ℂ) :
    Continuous fun v : S → ℝ => extS S v z := by
  by_cases hz : z ∈ S
  · simp only [extS, hz, dite_true]
    exact continuous_apply _
  · simp only [extS, hz, dite_false]
    exact continuous_const

theorem continuous_riemannCost_extS (ξ : ℝ) (N : ℕ) (z : List ℂ) (S : Finset ℂ) :
    Continuous fun v : S → ℝ => riemannCost ξ N z (extS S v) := by
  unfold riemannCost
  refine continuous_list_sum _ fun e _ => ?_
  refine continuous_const.mul (continuous_finsetSum _ fun q _ => ?_)
  exact (continuous_const.mul (continuous_extS_apply S _)).rexp

/-! ## Positivity of the LFPP distance -/

section Path

variable {γ : ℝ → ℂ}

theorem norm_le_three_of_mem_U' {z : ℂ} (hz : z ∈ LQGDimension.U) : ‖z‖ ≤ 3 := by
  obtain ⟨h1, h2⟩ := hz
  have hre : z.re ^ 2 < 4 := by
    have := sq_abs z.re
    nlinarith [abs_nonneg z.re]
  have him : z.im ^ 2 < 4 := by
    have := sq_abs z.im
    nlinarith [abs_nonneg z.im]
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    have := Complex.sq_norm_sub_sq_re z
    linarith
  nlinarith [norm_nonneg z]

theorem exists_piece' {k : ℕ} {t : Fin (k + 1) → ℝ} (ht0 : t 0 = 0)
    (htk : t (Fin.last k) = 1) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxt : x ∉ range t) :
    ∃ i : Fin k, t i.castSucc < x ∧ x < t i.succ := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (k + 1)), S = Finset.univ.filter fun j => t j < x :=
    ⟨_, rfl⟩
  have hmem : ∀ j, j ∈ S ↔ t j < x := fun j => by simp [hS]
  have hne : S.Nonempty := ⟨0, (hmem 0).2 (by rw [ht0]; exact hx.1)⟩
  have hm : t (S.max' hne) < x := (hmem _).1 (S.max'_mem hne)
  have hml : S.max' hne ≠ Fin.last k := by
    intro h
    rw [h, htk] at hm
    linarith [hx.2]
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hml
  refine ⟨i, by rw [hi]; exact hm, ?_⟩
  rcases lt_or_ge x (t i.succ) with h | h
  · exact h
  · exfalso
    rcases h.lt_or_eq with h | h
    · have : i.succ ≤ S.max' hne := S.le_max' _ ((hmem _).2 h)
      rw [← hi] at this
      exact absurd this (not_le.2 Fin.castSucc_lt_succ)
    · exact hxt ⟨_, h⟩

theorem hasDerivAt_of_piece' {k : ℕ} {t : Fin (k + 1) → ℝ} (ht0 : t 0 = 0)
    (htk : t (Fin.last k) = 1)
    (hC : ∀ i : Fin k, ContDiffOn ℝ 1 γ (Icc (t i.castSucc) (t i.succ)))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxt : x ∉ range t) : HasDerivAt γ (deriv γ x) x := by
  obtain ⟨i, h1, h2⟩ := exists_piece' ht0 htk hx hxt
  exact ((hC i).contDiffAt (Icc_mem_nhds h1 h2)).differentiableAt_one.hasDerivAt

theorem deriv_bound_piece' {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 1 γ (Icc a b)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ Ioo a b, ‖deriv γ x‖ ≤ C := by
  obtain ⟨C, hC'⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hC.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl)
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  exact (hC' x (Ioo_subset_Icc_self hx)).trans (le_max_left _ _)

theorem deriv_intervalIntegrable' (hγ : IsAdmissiblePath γ) :
    IntervalIntegrable (deriv γ) volume 0 1 := by
  obtain ⟨k, t, ht, ht0, htk, hC⟩ := hγ.piecewise_contDiff
  have hB : ∀ i : Fin k, ∃ C, 0 ≤ C ∧
      ∀ x ∈ Ioo (t i.castSucc) (t i.succ), ‖deriv γ x‖ ≤ C :=
    fun i => deriv_bound_piece' (ht Fin.castSucc_lt_succ) (hC i)
  choose C hC0 hCb using hB
  have hbound : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ range t → ‖deriv γ x‖ ≤ ∑ i, C i := by
    intro x hx hxt
    obtain ⟨i, h1, h2⟩ := exists_piece' ht0 htk hx hxt
    exact (hCb i x ⟨h1, h2⟩).trans
      (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := ∑ i, C i) measure_Ioc_lt_top.ne
    (measurable_deriv γ).aestronglyMeasurable ?_
  have hfin : (insert (1 : ℝ) (range t)).Countable := ((finite_range t).insert 1).countable
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hfin.ae_notMem volume] with x hx hxI
  rw [mem_insert_iff, not_or] at hx
  exact hbound x ⟨hxI.1, lt_of_le_of_ne hxI.2 hx.1⟩ hx.2

/-- Chord ≤ arclength on `[0,1]`. -/
theorem one_le_arclength (hγ : IsAdmissiblePath γ) : 1 ≤ ∫ t in (0 : ℝ)..1, ‖deriv γ t‖ := by
  obtain ⟨k, t, _, ht0, htk, hC⟩ := hγ.piecewise_contDiff
  have hI := deriv_intervalIntegrable' hγ
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le γ (deriv γ) zero_le_one
    (countable_range t) hγ.continuousOn
    (fun x hx => hasDerivAt_of_piece' ht0 htk hC hx.1 hx.2) hI
  have h := intervalIntegral.norm_integral_le_integral_norm (f := deriv γ) (μ := volume)
    zero_le_one
  rw [hFTC, hγ.source, hγ.target, sub_zero, norm_one] at h
  exact h

/-- Every admissible path has LFPP length at least `e^{-|ξ| K}` when `|φ| ≤ K` on the disc of
radius `3`. -/
theorem exp_le_lfppLength (hγ : IsAdmissiblePath γ) {ξ K : ℝ} {φ : ℂ → ℝ}
    (hφ : Continuous φ) (hK : ∀ z ∈ Metric.closedBall (0 : ℂ) 3, ‖φ z‖ ≤ K) :
    Real.exp (-(|ξ| * K)) ≤ lfppLength ξ φ γ := by
  have hD := deriv_intervalIntegrable' hγ
  have hc : ContinuousOn (fun t => Real.exp (ξ * φ (γ t))) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact Real.continuous_exp.comp_continuousOn
      ((continuous_const.mul hφ).comp_continuousOn hγ.continuousOn)
  have hint : IntervalIntegrable (fun t => Real.exp (ξ * φ (γ t)) * ‖deriv γ t‖) volume 0 1 :=
    hD.norm.continuousOn_mul hc
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1,
      Real.exp (-(|ξ| * K)) * ‖deriv γ t‖ ≤ Real.exp (ξ * φ (γ t)) * ‖deriv γ t‖ := by
    intro t ht
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have h3 := norm_le_three_of_mem_U' (hγ.mapsTo ht)
    have hk := hK (γ t) (mem_closedBall_zero_iff.2 h3)
    rw [Real.norm_eq_abs] at hk
    have h1 : |ξ * φ (γ t)| ≤ |ξ| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    linarith [neg_abs_le (ξ * φ (γ t))]
  have hmono := intervalIntegral.integral_mono_on zero_le_one (hD.norm.const_mul _) hint hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  have h1 := one_le_arclength hγ
  unfold lfppLength
  have hE := Real.exp_pos (-(|ξ| * K))
  nlinarith

theorem admissible_ofReal : IsAdmissiblePath fun t : ℝ => (t : ℂ) where
  source := by simp
  target := by simp
  mapsTo := by
    intro t ht
    refine ⟨?_, ?_⟩
    · simp only [Complex.ofReal_re]
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    · simp
  continuousOn := Complex.continuous_ofReal.continuousOn
  piecewise_contDiff := by
    refine ⟨1, fun i => ((i : ℕ) : ℝ), ?_, by simp, by simp, fun i => ?_⟩
    · intro a b hab
      simp only
      exact_mod_cast hab
    · exact Complex.ofRealCLM.contDiff.contDiffOn

/-- The LFPP distance of a continuous field is positive. -/
theorem lfppDistance_pos (ξ : ℝ) {φ : ℂ → ℝ} (hφ : Continuous φ) : 0 < lfppDistance ξ φ := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) 3).exists_bound_of_continuousOn
    hφ.continuousOn
  have : Nonempty {γ : ℝ → ℂ // IsAdmissiblePath γ} := ⟨⟨_, admissible_ofReal⟩⟩
  exact lt_of_lt_of_le (Real.exp_pos _)
    (le_ciInf fun γ => exp_le_lfppLength (ξ := ξ) γ.2 hφ hK)

end Path

/-! ## Points as degenerate segments -/

/-- The point mass at `s`, as a degenerate segment. -/
def ptComb (s : ℂ) : SegComb := [((1 : ℝ), s, s)]

theorem avg_ptComb (φ : ℂ → ℝ) (s : ℂ) : (ptComb s).avg φ = φ s := by
  simp [ptComb, SegComb.avg, segAvg]

theorem circCov_ptComb (ε : ℝ) (s s' : ℂ) :
    (ptComb s).circCov ε (ptComb s') = gffCircleCov ε s ε s' := by
  simp [ptComb, SegComb.circCov, segCircCov]

end LQGDimension.LowerAsm
