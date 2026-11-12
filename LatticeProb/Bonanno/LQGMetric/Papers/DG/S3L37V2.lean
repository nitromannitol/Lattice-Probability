/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L37V2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L37V1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2HatTail
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiSupTail
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputsDG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Lemma 3.7 at `𝕍`-scale, part 2: from `𝕊(1)`-scale to `𝕍`-scale

Ding–Gwynne arXiv:1807.01072 (`metric-comparison-final.tex`), Lemma 3.7
(`lem-circle-avg-approx`, DG:1096–1102), carried to `𝕍` by `T(z) = (z + 1 + i)/3` (D105 item 1).
With `W' = W ∘ U_{3,−(1+i)}` (`l37W`, S3L37V1), a.s. `ĥ_δ[W'](y) = ĥ_{3δ}[W](T⁻¹y) + φ_{1,3}[W](T⁻¹y)`
(`ae_phiVer_l37W`). The smooth window `φ_{1,3}` has a Gaussian sup tail on the compact
`𝕊(1/2) = [−1/2,3/2]²` (DZZ proof of Lemma 2.9, `DZZ.dzz_hat_sup_tail`), hence is
`≤ (ζ/2) log δ⁻¹` w.p. `≥ 1 − Cδ`; together with L3.7 at `δ' = 3δ`, `z = w = T⁻¹ y` this gives
`DGLem37V P W' (p18Vfield hc) S` for every `S` with `T⁻¹ S ⊆ 𝕊(1/2)` (`dgLem37V_l37W`).

* `dgLem37V_exists_sq`: from `Blueprint.DGLem3_7` (stated for `z, w ∈ 𝕊(1/2) = [−1/2,3/2]²`, D118)
  the coupling at `𝕍`-scale on `T(𝕊) = [1/3,2/3]² = p39Sq p18c0 (1/3)`.
* `dgLem37V_exists_box`: on `T(𝕊(1/2)) = [1/6,5/6]² = p39Box p18c0 (1/3) (1/6)` (the form used by
  `dg_prop322_sqOne_muHat`), from `Blueprint.DGLem3_7` on `𝕊(1/2)` — the form DG use at
  DG:1729–1731 (the LFPP paths of P3.22 live in `𝕊(1/2)`; D118).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise

/-- the lower-left corner `−(1+i)/2` of `𝕊(1/2)` -/
def l37x0 : ℂ := ⟨-1 / 2, -1 / 2⟩

lemma p18Half_eq_ferniqueBox : p18Half = SupTail.ferniqueBox l37x0 2 := by
  simp only [p18Half, SupTail.ferniqueBox, l37x0]
  norm_num

/-- `|f(x)| ≤ sup_B |f|` for continuous `f` on the compact box -/
lemma l37_abs_le_iSup {f : ℂ → ℝ} (hf : Continuous f) {x : ℂ} (hx : x ∈ p18Half) :
    |f x| ≤ ⨆ v : SupTail.ferniqueBox l37x0 2, |f v| := by
  rw [p18Half_eq_ferniqueBox] at hx
  exact le_ciSup (f := fun v : SupTail.ferniqueBox l37x0 2 => |f v|)
    (SupTail.bddAbove_abs_of_compact (SupTail.isCompact_ferniqueBox _ _) hf) ⟨x, hx⟩

/-- **DG L3.7 transported to `𝕍`**: if `hc` satisfies L3.7 (`z = w`, polynomial rate) on
`T⁻¹ S ⊆ 𝕊(1/2)` against `ĥ[W]`, then `p18Vfield hc` satisfies it on `S` against `ĥ[W']`. -/
theorem dgLem37V_l37W {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {hc : ℝ → ℂ → Ω → ℝ} {S : Set ℂ}
    (hS : ∀ y ∈ S, p18Tinv y ∈ p18Half)
    (h37 : ∀ ζ : ℝ, 0 < ζ → ∃ p K δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ ∀ y ∈ S, |hc δ (p18Tinv y) ω - DDDF.phiVer W P δ 1 (p18Tinv y) ω| ≤
        ζ * Real.log δ⁻¹} ≤ ENNReal.ofReal (K * δ ^ p)) :
    DGLem37V P (l37W W) (p18Vfield hc) S := by
  have hP := hW.isProbabilityMeasure
  intro ζ hζ
  obtain ⟨p₁, K₁, δ₁, hp₁, hδ₁, e1⟩ := h37 (ζ / 2) (by positivity)
  have hB := DDDF.isPhiVersion_phiVer (P := P) hW one_pos (by norm_num : (1 : ℝ) ≤ 3)
  obtain ⟨C, hC, eT⟩ := DZZ.dzz_hat_sup_tail hW one_pos (by norm_num : (1 : ℝ) ≤ 3)
    (x₀ := l37x0) (s := 2) two_pos hB.cont hB.ae_eq
  refine ⟨min p₁ 1, |K₁| * 3 ^ p₁ + C, min (min (δ₁ / 3) (1 / 4)) (Real.exp (-(4 * C / ζ ^ 2))),
    lt_min hp₁ one_pos, lt_min (lt_min (by positivity) (by norm_num)) (Real.exp_pos _),
    fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδδ⟩ := hδ
  have hδ13 : δ < δ₁ / 3 := hδδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ4 : δ < 1 / 4 := hδδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδe : δ < Real.exp (-(4 * C / ζ ^ 2)) := hδδ.trans_le (min_le_right _ _)
  have h3δ : (0 : ℝ) < 3 * δ := by positivity
  have hL0 : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg (one_le_inv₀ hδ0 |>.2 (by linarith))
  have hL3 : Real.log (3 * δ)⁻¹ ≤ Real.log δ⁻¹ :=
    Real.log_le_log (inv_pos.2 h3δ) ((inv_le_inv₀ h3δ hδ0).2 (by linarith))
  -- the three bad events
  set N := {ω | ¬ ∀ y, DDDF.phiVer (l37W W) P δ 1 y ω =
      DDDF.phiVer W P (3 * δ) 1 (p18Tinv y) ω + DDDF.phiVer W P 1 3 (p18Tinv y) ω}
  set A := {ω | ¬ ∀ y ∈ S, |hc (3 * δ) (p18Tinv y) ω - DDDF.phiVer W P (3 * δ) 1 (p18Tinv y) ω| ≤
      ζ / 2 * Real.log (3 * δ)⁻¹}
  set B := {ω | ζ / 2 * Real.log δ⁻¹ ≤
      ⨆ v : SupTail.ferniqueBox l37x0 2, |DDDF.phiVer W P 1 3 v ω|}
  have hN : P N = 0 := by
    have h := ae_phiVer_l37W hW hδ0 (by linarith)
    rwa [ae_iff] at h
  have hsub : {ω | ¬ ∀ x ∈ S, |p18Vfield hc δ x ω - DDDF.phiVer (l37W W) P δ 1 x ω| ≤
      ζ * Real.log δ⁻¹} ⊆ N ∪ A ∪ B := by
    intro ω hω
    by_contra hc'
    simp only [mem_union, not_or] at hc'
    obtain ⟨⟨hN', hA'⟩, hB'⟩ := hc'
    simp only [N, A, B, mem_setOf_eq, not_not, not_le] at hN' hA' hB'
    refine hω fun y hy => ?_
    have h1 := hA' y hy
    have h2 := l37_abs_le_iSup (f := fun v => DDDF.phiVer W P 1 3 v ω) (hB.cont ω) (hS y hy)
    simp only [p18Vfield, hN' y]
    calc |hc (3 * δ) (p18Tinv y) ω - (DDDF.phiVer W P (3 * δ) 1 (p18Tinv y) ω +
          DDDF.phiVer W P 1 3 (p18Tinv y) ω)|
        ≤ |hc (3 * δ) (p18Tinv y) ω - DDDF.phiVer W P (3 * δ) 1 (p18Tinv y) ω| +
          |DDDF.phiVer W P 1 3 (p18Tinv y) ω| := by
          rw [← sub_sub]; exact abs_sub _ _
      _ ≤ ζ / 2 * Real.log δ⁻¹ + ζ / 2 * Real.log δ⁻¹ := by
          gcongr
          · exact h1.trans (by gcongr)
          · exact h2.trans hB'.le
      _ = ζ * Real.log δ⁻¹ := by ring
  -- tail of the smooth window
  have hBt : P B ≤ ENNReal.ofReal (C * δ) := by
    rw [← ofReal_measureReal (measure_ne_top P B)]
    refine ENNReal.ofReal_le_ofReal ((eT _ (by positivity)).trans ?_)
    gcongr
    have hlog : 4 * C / ζ ^ 2 ≤ Real.log δ⁻¹ := by
      rw [Real.log_inv, le_neg]
      exact ((Real.log_lt_log hδ0 hδe).trans_eq (Real.log_exp _)).le
    calc Real.exp (-(ζ / 2 * Real.log δ⁻¹) ^ 2 / C) ≤ Real.exp (-Real.log δ⁻¹) := by
          gcongr
          rw [div_le_iff₀ hC]
          have hζ2 : 0 < ζ ^ 2 := by positivity
          rw [div_le_iff₀ hζ2] at hlog
          nlinarith [mul_le_mul_of_nonneg_left hlog hL0]
      _ = δ := by rw [Real.exp_neg, Real.exp_log (inv_pos.2 hδ0), inv_inv]
  have hδ1 : δ ≤ 1 := by linarith
  have hA : P A ≤ ENNReal.ofReal (|K₁| * 3 ^ p₁ * δ ^ min p₁ 1) := by
    refine (e1 (3 * δ) ⟨h3δ, by linarith⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.mul_rpow (by norm_num) hδ0.le, ← mul_assoc]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K₁)
      (by positivity)) (by positivity)).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (min_le_left _ _))
      (by positivity)
  have hδp : δ ≤ δ ^ min p₁ 1 := by
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ min p₁ 1 := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (min_le_right _ _)
  calc _ ≤ P (N ∪ A ∪ B) := measure_mono hsub
    _ ≤ P N + P A + P B := (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ 0 + ENNReal.ofReal (|K₁| * 3 ^ p₁ * δ ^ min p₁ 1) + ENNReal.ofReal (C * δ ^ min p₁ 1) := by
        rw [hN]
        gcongr
        exact hBt.trans (ENNReal.ofReal_le_ofReal (by gcongr))
    _ = ENNReal.ofReal ((|K₁| * 3 ^ p₁ + C) * δ ^ min p₁ 1) := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

lemma closedUnitSquare_sub_p18Half : Blueprint.closedUnitSquare ⊆ p18Half := by
  intro z ⟨h1, h2, h3, h4⟩
  simp only [p18Half, Complex.mem_reProdIm, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- DG L3.7's estimate (`C = 1`) on a set `Q` gives the hypothesis of `dgLem37V_l37W` on every
`S` with `T⁻¹ S ⊆ Q` -/
lemma l37_hyp_of {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    {hc : ℝ → ℂ → Ω → ℝ} {Q S : Set ℂ} (hS : ∀ y ∈ S, p18Tinv y ∈ Q)
    (h : ∀ C : ℝ, 0 < C → ∀ ζ ∈ Ioo (0 : ℝ) 1, ∀ p : ℝ, 0 < p → ∃ K δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ ∈ Ioo (0 : ℝ) δ₀,
        P {ω | ¬ ∀ z ∈ Q, ∀ w ∈ Q, ‖z - w‖ ≤ C * δ →
          |hc δ z ω - DDDF.phiVer W P δ 1 w ω| ≤ ζ * Real.log δ⁻¹} ≤ ENNReal.ofReal (K * δ ^ p))
    (ζ : ℝ) (hζ : 0 < ζ) : ∃ p K δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ ∀ y ∈ S, |hc δ (p18Tinv y) ω - DDDF.phiVer W P δ 1 (p18Tinv y) ω| ≤
        ζ * Real.log δ⁻¹} ≤ ENNReal.ofReal (K * δ ^ p) := by
  obtain ⟨K, δ₀, hδ₀, e⟩ := h 1 one_pos (min ζ (1 / 2)) ⟨lt_min hζ (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num)⟩ 1 one_pos
  refine ⟨1, K, min δ₀ 1, one_pos, lt_min hδ₀ one_pos, fun δ hδ => ?_⟩
  refine le_trans (measure_mono fun ω hω => ?_) (e δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩)
  simp only [mem_setOf_eq] at hω ⊢
  refine fun hall => hω fun y hy => ?_
  have hL : 0 ≤ Real.log δ⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ hδ.1).2 (hδ.2.trans_le (min_le_right _ _)).le)
  refine (hall _ (hS y hy) _ (hS y hy) (by simp only [sub_self, norm_zero]; linarith [hδ.1])).trans
    ?_
  exact mul_le_mul_of_nonneg_right (min_le_left _ _) hL

lemma p18Half_eq_sqHalf : p18Half = Blueprint.sqHalf := by
  ext z
  simp only [p18Half, Blueprint.sqHalf, Complex.mem_reProdIm, mem_Icc, mem_setOf_eq]
  tauto

/-- **DG L3.7 at `𝕍`-scale on `T(𝕊(1/2)) = [1/6,5/6]²`** (the input `h37` of
`dg_prop322_sqOne_muHat`), from the cited `Blueprint.DGLem3_7` (on `𝕊(1/2)`, D118). -/
theorem dgLem37V_exists_box (h : Blueprint.DGLem3_7) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W W' : WNSpace → Ω → ℝ)
      (hz : Ω → DistC) (hc : ℝ → ℂ → Ω → ℝ), Blueprint.IsDGCoupling P W hz hc ∧
      IsWhiteNoise P W' ∧ DGLem37V P W' (p18Vfield hc) (p39Box p18c0 (1 / 3) (1 / 6)) := by
  obtain ⟨Ω, _, P, W, hz, hc, hcp, h37⟩ := h
  refine ⟨Ω, _, P, W, l37W W, hz, hc, hcp, isWhiteNoise_l37W hcp.2.1, ?_⟩
  exact dgLem37V_l37W hcp.2.1 (fun y hy => p18_Tinv_mem hy)
    (l37_hyp_of (fun y hy => p18Half_eq_sqHalf ▸ p18_Tinv_mem hy) h37)

end DG
end LQGMetric
