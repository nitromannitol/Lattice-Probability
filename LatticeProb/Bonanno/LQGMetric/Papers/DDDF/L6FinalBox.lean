/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6FinalBox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiSupTail
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2ContBox
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueKolm

/-!
# DDDF Lemma 6, Step 2: continuous version and sup tail on one box

DDDF (Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `tightness.tex` l. 578–583, proof of
Lemma 6, Step 2): "An application of Kolmogorov's continuity criterion and Fernique's theorem
give uniform Gaussian tails for `φ₁^{(δ)}` and `φ₂^{(δ)}`."

`exists_box_version`: a centered Gaussian field `G` on `ℂ` whose increments satisfy
`E(G v − G u)² ≤ A |u − v|` and whose variance is `≤ σ²` on a set `S` containing the box
`B = ferniqueBox x₀ b` has a version `Y` on `B`, continuous on `ℂ`, with
`P(sup_B |Y| ≥ C_F √(A b) + s) ≤ 2 e^{−s²/(2σ²)}`.
Kolmogorov + Fernique: DZZ Lemma 2.3 (`SupTail.dzz_lemma23`); Borell–TIS:
`SupTail.tail_iSup_abs_box`. The field is first composed with the 1-Lipschitz projection onto
`B` (`DZZ.boxClamp`), so that the global hypotheses of `tail_iSup_abs_box` hold.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Continuous version and Gaussian sup tail on one box** (DDDF Lemma 6, Step 2). -/
theorem exists_box_version {G : ℂ → Ω → ℝ} (hG : IsGaussianProcess G P)
    (h0 : ∀ v, ∫ ω, G v ω ∂P = 0) {S : Set ℂ} {A σ : ℝ} (hA : 0 < A) (hσ : 0 < σ)
    (hinc : ∀ u ∈ S, ∀ v ∈ S, ∫ ω, (G v ω - G u ω) ^ 2 ∂P ≤ A * ‖u - v‖)
    (hvar : ∀ v ∈ S, Var[G v; P] ≤ σ ^ 2) {x₀ : ℂ} {b : ℝ} (hb : 0 < b)
    (hBS : ferniqueBox x₀ b ⊆ S) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun v => Y v ω) ∧
      (∀ v ∈ ferniqueBox x₀ b, Y v =ᵐ[P] G v) ∧
      ∀ s : ℝ, 0 ≤ s → P {ω | ENNReal.ofReal (ferniqueCF * √(A * b) + s) ≤
        ⨆ v ∈ ferniqueBox x₀ b, ENNReal.ofReal |Y v ω|} ≤
          ENNReal.ofReal (2 * exp (-s ^ 2 / (2 * σ ^ 2))) := by
  have hP := hG.isProbabilityMeasure
  set B := ferniqueBox x₀ b
  set C : ℂ → ℂ := DZZ.boxClamp x₀ b
  have hCB : ∀ v, C v ∈ B := fun v => DZZ.boxClamp_mem hb.le v
  have hCC : ∀ v, C (C v) = C v := fun v => DZZ.boxClamp_of_mem (hCB v)
  set κ : ℝ := √(A * b)
  have hκ : 0 < κ := Real.sqrt_pos.mpr (mul_pos hA hb)
  have hκ2 : κ ^ 2 = A * b := Real.sq_sqrt (mul_pos hA hb).le
  set H : ℂ → Ω → ℝ := fun v ω => κ⁻¹ * G (C v) ω
  have hH : IsGaussianProcess H P := by
    have := (hG.comp_right C).smul (fun _ => κ⁻¹)
    simpa [H, smul_eq_mul, Function.comp_def] using this
  have hHinc : ∀ u ∈ B, ∀ v ∈ B, ∫ ω, (H v ω - H u ω) ^ 2 ∂P ≤ ‖u - v‖ / b := by
    intro u _ v _
    have e : (fun ω => (H v ω - H u ω) ^ 2) =
        fun ω => (κ ^ 2)⁻¹ * (G (C v) ω - G (C u) ω) ^ 2 := by
      funext ω; simp only [H]; field_simp
    rw [e, integral_const_mul, hκ2]
    calc (A * b)⁻¹ * ∫ ω, (G (C v) ω - G (C u) ω) ^ 2 ∂P ≤ (A * b)⁻¹ * (A * ‖u - v‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (hinc _ (hBS (hCB u)) _ (hBS (hCB v))).trans ?_
          exact mul_le_mul_of_nonneg_left (DZZ.norm_boxClamp_sub_le x₀ b u v) hA.le
      _ = ‖u - v‖ / b := by field_simp
  obtain ⟨H', hH'ae, hH'c, -, -⟩ := dzz_lemma23 hb (G := H) (hH.comp_right (fun v : B => (v : ℂ)))
    (fun v _ => by simp [H, integral_const_mul, h0]) hHinc
  set Y : ℂ → Ω → ℝ := fun v ω => κ * H' (C v) ω
  have hYc : ∀ ω, Continuous fun v => Y v ω := fun ω =>
    continuous_const.mul ((hH'c ω).comp (DZZ.continuous_boxClamp x₀ b))
  have hYae : ∀ v, Y v =ᵐ[P] G (C v) := by
    intro v
    filter_upwards [hH'ae (C v) (hCB v)] with ω hω
    simp only [Y, hω, H, hCC]
    field_simp
  have hYG : IsGaussianProcess Y P :=
    (hG.comp_right C).congr fun v => (hYae v).symm
  have hY0 : ∀ v, ∫ ω, Y v ω ∂P = 0 := fun v => by rw [integral_congr_ae (hYae v)]; exact h0 _
  have hYinc : ∀ u v, ∫ ω, (Y v ω - Y u ω) ^ 2 ∂P ≤ A * ‖u - v‖ := by
    intro u v
    have e : (fun ω => (Y v ω - Y u ω) ^ 2) =ᵐ[P] fun ω => (G (C v) ω - G (C u) ω) ^ 2 := by
      filter_upwards [hYae u, hYae v] with ω h1 h2
      rw [h1, h2]
    rw [integral_congr_ae e]
    refine (hinc _ (hBS (hCB u)) _ (hBS (hCB v))).trans ?_
    exact mul_le_mul_of_nonneg_left (DZZ.norm_boxClamp_sub_le x₀ b u v) hA.le
  have hYvar : ∀ v, Var[Y v; P] ≤ σ ^ 2 := fun v => by
    rw [variance_congr (hYae v)]; exact hvar _ (hBS (hCB v))
  refine ⟨Y, hYc, fun v hv => ?_, fun s hs => ?_⟩
  · have := hYae v
    rwa [show C v = v from DZZ.boxClamp_of_mem hv] at this
  · have hT := tail_iSup_abs_box (x₀ := x₀) hb hYG hY0 hYc hA hYinc hσ hYvar hs
    have hpos : 0 < ferniqueCF * √(A * b) + s := by
      have := ferniqueCF_pos; positivity
    have hsub : {ω | ENNReal.ofReal (ferniqueCF * √(A * b) + s) ≤
        ⨆ v ∈ B, ENNReal.ofReal |Y v ω|} ⊆
        {ω | ferniqueCF * √(A * b) + s ≤ ⨆ v : B, |Y v ω|} := by
      intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      have h2 := hω.trans (iSup_ofReal_le (isCompact_ferniqueBox x₀ b) (hYc ω))
      rcases (ENNReal.ofReal_le_ofReal_iff').1 h2 with h | h
      · exact h
      · exact absurd h (not_le.2 hpos)
    refine (measure_mono hsub).trans ?_
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hT

end DDDF
end LQGMetric
