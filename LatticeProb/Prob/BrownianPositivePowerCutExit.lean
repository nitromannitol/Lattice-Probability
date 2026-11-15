import LatticeProb.Prob.BrownianCutHarmonicLimit
import LatticeProb.Analysis.WedgeHarmonicBoundary

/-! # Brownian exit identity for positive power profiles -/

set_option autoImplicit false

open MeasureTheory Set Filter InnerProductSpace
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- A positive complex power satisfies the Brownian exit identity on the part of
any bounded open set in the right half-plane, including boundary starts. -/
theorem integral_openExit_positive_re_cpow {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {x : Euc 2} {B : ℝ≥0 → Ω → Euc 2}
    (hB : IsBrownianSpace 2 x B P) {U : Set (Euc 2)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {p : ℝ} (hp : 0 < p) :
    ∫ ω, ((Complex.orthonormalBasisOneI.repr.symm
      (B (openExitTime B (U ∩ {y | 0 <
        (Complex.orthonormalBasisOneI.repr.symm y).re}) ω).toNNReal ω)) ^
          (p : ℂ)).re ∂P =
      ((Complex.orthonormalBasisOneI.repr.symm x) ^ (p : ℂ)).re := by
  have := hB.isProbabilityMeasure
  let J : Euc 2 → ℂ := Complex.orthonormalBasisOneI.repr.symm
  let C : Euc 2 → ℂ := fun y => ((max 0 (J y).re : ℝ) : ℂ) + ((J y).im : ℂ) * Complex.I
  let f : Euc 2 → ℝ := fun y => (C y ^ (p : ℂ)).re
  have hJ : Continuous J := Complex.orthonormalBasisOneI.repr.symm.continuous
  have hC : Continuous C := by
    dsimp [C]
    fun_prop
  have hCe : ∀ y, 0 ≤ (J y).re → C y = J y := by
    intro y hy
    apply Complex.ext <;> simp [C, max_eq_right hy]
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (continuousAt_re_cpow_of_nonneg_re hp (show 0 ≤ (C y).re by
      simp [C])).comp hC.continuousAt
  have hh : ∀ y : Euc 2, 0 < (J y).re → HarmonicAt f y := by
    intro y hy
    have he : f =ᶠ[𝓝 y] (fun z : Euc 2 => (J z ^ (p : ℂ)).re) := by
      filter_upwards [isOpen_lt continuous_const (Complex.continuous_re.comp hJ) |>.mem_nhds hy]
        with z hz
      simp only [f, hCe z hz.le]
    exact (harmonicAt_congr_nhds he).2 (harmonicAt_euclidean_re_cpow hy)
  have hidentity := integral_openExit_positive_re_of_harmonic hB hU hUb hf hh
  let V : Set (Euc 2) := U ∩ {y | 0 < (J y).re}
  have hVo : IsOpen V := hU.inter (isOpen_lt continuous_const (Complex.continuous_re.comp hJ))
  have hVb : Bornology.IsBounded V := hUb.subset inter_subset_left
  have hclosed : ∀ y ∈ closure V, 0 ≤ (J y).re :=
    closure_minimal (fun y hy => (show 0 < (J y).re from hy.2).le)
      (isClosed_le continuous_const (Complex.continuous_re.comp hJ))
  by_cases hx : 0 ≤ (J x).re
  · have he : ∀ᵐ ω ∂P, f (B (openExitTime B V ω).toNNReal ω) =
        (J (B (openExitTime B V ω).toNNReal ω) ^ (p : ℂ)).re := by
      filter_upwards [hB.start, hB.cont, ae_openExitTime_ne_top (by norm_num) hB hVb]
        with ω hstart hcont hfin
      have hout : 0 ≤ (J (B (openExitTime B V ω).toNNReal ω)).re := by
        by_cases hxin : x ∈ V
        · exact hclosed _ (frontier_subset_closure
            (openExitTime_mem_frontier hVo hcont (by rwa [hstart]) hfin))
        · have hz : openExitTime B V ω = 0 :=
            openExitTime_eq_zero_of_not_mem (by rwa [hstart])
          simpa [hz, hstart] using hx
      simp only [f, hCe _ hout]
    have heq := integral_congr_ae he
    change (∫ ω, f (B (openExitTime B V ω).toNNReal ω) ∂P) = f x at hidentity
    rw [heq] at hidentity
    simpa only [f, hCe x hx] using hidentity
  · have he : ∀ᵐ ω ∂P, B (openExitTime B V ω).toNNReal ω = x := by
      filter_upwards [hB.start] with ω hstart
      have hn : x ∉ V := fun h => hx h.2.le
      have hz : openExitTime B V ω = 0 :=
        openExitTime_eq_zero_of_not_mem (by rwa [hstart])
      simp [hz, hstart]
    change (∫ ω, (J (B (openExitTime B V ω).toNNReal ω) ^ (p : ℂ)).re ∂P) = _
    calc
      _ = ∫ _ : Ω, (J x ^ (p : ℂ)).re ∂P :=
        integral_congr_ae (he.mono (fun ω hω => congrArg (fun y : Euc 2 =>
          (J y ^ (p : ℂ)).re) hω))
      _ = _ := by
        rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

end LatticeProb
