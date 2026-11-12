/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20BXMom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldExpTail
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiProp5

/-!
# DDDF Theorem 20, Step 4: exponential moments of `X_{a,b}` (task P2-DDDFT20b)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1158–1172: Step 4 uses moments of `e^{8ξX}` with
`X = X_{a,b} = sup_n ‖φ_{0,n} − ψ_{0,n}‖_{R_{a,b}}` ((2.20) = `DefX`), which follow from the
Gaussian tail of Proposition 5 (`dddf_prop5_XAB`, (2.25)).

* `T20B.measurable_XAB`: `ω ↦ X_{a,b}(ω)` is measurable (continuous fields: the supremum over the
  rectangle equals the supremum over a countable dense subset).
* `dddf_expMoment_XAB`: `E e^{l X_{a,b}} < ∞` for every `l > 0` (`lintegral_exp_le_of_tail`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace T20B

lemma biSup_eq_iSup_dense {S : Set ℂ} {D : Set S} (hD : Dense D) {g : ℂ → ℝ≥0∞}
    (hg : Continuous g) : ⨆ x ∈ S, g x = ⨆ d : D, g (d : S) := by
  refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup_le fun d => le_iSup₂_of_le (d : S).1 (d : S).2
    le_rfl)
  have hcl : IsClosed {y : S | g y ≤ ⨆ d : D, g (d : S)} :=
    isClosed_le (hg.comp continuous_subtype_val) continuous_const
  have hsub : D ⊆ {y : S | g y ≤ ⨆ d : D, g (d : S)} := fun y hy =>
    le_iSup (fun d : D => g (d : S)) ⟨y, hy⟩
  have := hcl.closure_subset_iff.2 hsub
  rw [hD.closure_eq] at this
  exact this (mem_univ (⟨x, hx⟩ : S))

theorem measurable_biSup_of_continuous {S : Set ℂ} {Y : ℂ → Ω → ℝ}
    (hc : ∀ ω, Continuous fun x => Y x ω) (hm : ∀ x, Measurable (Y x)) :
    Measurable fun ω => ⨆ x ∈ S, ENNReal.ofReal |Y x ω| := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense S
  have := hDc.to_subtype
  have e : (fun ω => ⨆ x ∈ S, ENNReal.ofReal |Y x ω|) =
      fun ω => ⨆ d : D, ENNReal.ofReal |Y (d : S) ω| :=
    funext fun ω => biSup_eq_iSup_dense hDd
      (ENNReal.continuous_ofReal.comp (continuous_abs.comp (hc ω)))
  rw [e]
  exact Measurable.iSup fun d => ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hm _))

theorem measurable_XAB (hW : IsWhiteNoise P W) (Q : PsiParams) (a b : ℝ) :
    Measurable fun ω => XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b := by
  unfold XAB
  refine Measurable.iSup fun n => ?_
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  exact measurable_biSup_of_continuous (Y := fun x ω => phiMN W P 0 n x ω - psiMN Q W P 0 n x ω)
    (fun ω => (hφ.cont ω).sub (hψ.cont ω)) fun x => (hφ.meas x).sub (hψ.meas x)

end T20B

open T20B in
/-- **Exponential moments of `X_{a,b}`** (from DDDF Prop 5, (2.25)): `E e^{l X_{a,b}} < ∞`. -/
theorem dddf_expMoment_XAB (hW : IsWhiteNoise P W) (Q : PsiParams) (a b : ℝ) {l : ℝ}
    (hl : 0 < l) : ∃ M : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (l *
      (XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b).toReal)) ∂P ≤
        ENNReal.ofReal M := by
  have := hW.isProbabilityMeasure
  obtain ⟨C, c, hC, hc, htail⟩ := dddf_prop5_XAB hW Q a b
  set X : Ω → ℝ := fun ω =>
    (XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b).toReal
  set L : ℝ := Real.log (l * C + 1)
  have hL : 0 ≤ L := Real.log_nonneg (by nlinarith [mul_pos hl hC])
  set x₀ : ℝ := max 1 ((l + 1) / c + L / c)
  have hx₀ : 1 ≤ x₀ := le_max_left _ _
  have h := lintegral_exp_le_of_tail (P := P) (X := X) (fun ω => ENNReal.toReal_nonneg)
    (measurable_XAB hW Q a b).ennreal_toReal.aemeasurable (x₀ := x₀) (B := 1) (κ := 1) hl
    (by linarith) one_pos zero_le_one fun t ht => ?_
  · exact ⟨_, h⟩
  · have ht0 : 0 < t := by linarith
    have hsub : {ω | t ≤ X ω} ⊆ {ω | ENNReal.ofReal t ≤
        XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b} := by
      intro ω hω
      simp only [mem_ofPred_eq, X] at hω ⊢
      exact (ENNReal.ofReal_le_ofReal hω).trans ENNReal.ofReal_toReal_le
    have hP : P.real {ω | t ≤ X ω} ≤ C * Real.exp (-(c * t ^ 2)) := by
      have h1 := (measure_mono hsub).trans (htail t ht0)
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have hkey : L + (l + 1) * t ≤ c * t ^ 2 := by
      have h1 : (l + 1) / c + L / c ≤ t := (le_max_right _ _).trans ht.le
      have h2 : (l + 1) + L ≤ c * t := by
        rw [← add_div, div_le_iff₀ hc] at h1; linarith
      have ht1 : 1 ≤ t := hx₀.trans ht.le
      nlinarith
    have hlC : l * C ≤ Real.exp L := by rw [Real.exp_log (by positivity)]; linarith
    calc l * Real.exp (l * t) * P.real {ω | t ≤ X ω}
        ≤ l * Real.exp (l * t) * (C * Real.exp (-(c * t ^ 2))) :=
          mul_le_mul_of_nonneg_left hP (by positivity)
      _ = (l * C) * Real.exp (l * t + -(c * t ^ 2)) := by rw [Real.exp_add]; ring
      _ ≤ Real.exp L * Real.exp (l * t + -(c * t ^ 2)) :=
          mul_le_mul_of_nonneg_right hlC (Real.exp_pos _).le
      _ = Real.exp (L + (l * t + -(c * t ^ 2))) := (Real.exp_add _ _).symm
      _ ≤ 1 * Real.exp (-1 * t) := by
          rw [one_mul]; exact Real.exp_le_exp.2 (by linarith)

end DDDF
end LQGMetric
