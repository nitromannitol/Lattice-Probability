/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11Scale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Det
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc5

/-!
# DG (3.7) for one grid square of `sℛ_n + b` (P2-DG105g)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, (eqn-dist-scaling) (DG:1032–1036)
as used in the proof of Lemma 3.13 (DG:1305): the grid square `x` of side `s/32` (S3L11Sc, D116) is
carried by `y ↦ s y + c_x` (`c_x = l311Corner s b x`) from the fixed unit-frame square
`sqOne (1/32) (31/64 + 29i/64) (0,0) = [29/64, 35/64]²` with the same side midpoints, so by
`ae_dgLGD_scale` (S3D105Sc5) the event `E_S` for `μ_ĥ` at threshold `M` follows from the same
event for the measure `μ_ĥ` of the rescaled white noise `W ∘ wnScaleDy j c_x` at the level
`(s^{2+γ²/2} e^{γ M_φ})^{−1} ε`, where `M_φ ≥ max_{S(1)} ĥ_s`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the offset `c_x` of the scaling carrying `[29/64,35/64]²` onto `S(1)` of the grid square `x` -/
def l311Corner (s : ℝ) (b : ℂ) (x : ℤ × ℤ) : ℂ :=
  ⟨sqX (s / 32) b x + s / 64 - s / 2, sqY (s / 32) b x + s / 64 - s / 2⟩

/-- the base point `31/64 + 29i/64` of the unit-frame grid square (`sqOne = [29/64, 35/64]²`,
side midpoints at distance `1/64` from `1/2 + i/2`, inside DZZ's `𝕍̄` of `dg_lemma312`) -/
def l311UnitB : ℂ := ⟨31 / 64, 29 / 64⟩

lemma affineC_re (a : ℝ) (c y : ℂ) : (affineC a c y).re = a * y.re + c.re := by
  simp [affineC]

lemma affineC_im (a : ℝ) (c y : ℂ) : (affineC a c y).im = a * y.im + c.im := by
  simp [affineC]

lemma preimage_sqOne_l311 {s : ℝ} (hs : 0 < s) (b : ℂ) (x : ℤ × ℤ) :
    affineC s (l311Corner s b x) ⁻¹' sqOne (s / 32) b x = sqOne (1 / 32) l311UnitB (0, 0) := by
  ext y
  simp only [mem_preimage, sqOne, Complex.mem_reProdIm, mem_Icc, affineC_re, affineC_im,
    l311Corner, l311UnitB, sqX, sqY]
  push_cast
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

lemma affineC_unit_mid {s : ℝ} (hs : 0 < s) (b : ℂ) (x : ℤ × ℤ) {u : ℂ}
    (hu : u ∈ sqMids (s / 32) b x) :
    ∃ u' ∈ sqMids (1 / 32) l311UnitB (0, 0), affineC s (l311Corner s b x) u' = u := by
  have hs0 : (s : ℝ) ≠ 0 := hs.ne'
  simp only [sqMids, mem_insert_iff, mem_singleton_iff] at hu ⊢
  rcases hu with rfl | rfl | rfl | rfl
  · refine ⟨_, Or.inl rfl, Complex.ext ?_ ?_⟩ <;>
      simp only [affineC_re, affineC_im, l311Corner, l311UnitB, sqX, sqY] <;> push_cast <;> ring
  · refine ⟨_, Or.inr (Or.inl rfl), Complex.ext ?_ ?_⟩ <;>
      simp only [affineC_re, affineC_im, l311Corner, l311UnitB, sqX, sqY] <;> push_cast <;> ring
  · refine ⟨_, Or.inr (Or.inr (Or.inl rfl)), Complex.ext ?_ ?_⟩ <;>
      simp only [affineC_re, affineC_im, l311Corner, l311UnitB, sqX, sqY] <;> push_cast <;> ring
  · refine ⟨_, Or.inr (Or.inr (Or.inr rfl)), Complex.ext ?_ ?_⟩ <;>
      simp only [affineC_re, affineC_im, l311Corner, l311UnitB, sqX, sqY] <;> push_cast <;> ring

/-- **DG (3.7) for one grid square** (DG:1032–1036, 1305): a.s., if `ĥ_s ≤ M_φ` on `S(1)` and
the unit-frame square is good for the rescaled noise at level `(s^{2+γ²/2} e^{γM_φ})^{−1} ε`,
then the grid square `x` of `sℛ_n + b` is good for `μ_ĥ` at level `ε`. -/
theorem ae_goodSq_scale (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {y₀ : ℂ} {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hK : ∀ z ∈ ferniqueBox y₀ b₀, Metric.ball z (1 / 10) ⊆ openSquare) (j : ℕ) (b : ℂ)
    (x : ℤ × ℤ)
    (hTK : affineC ((2 : ℝ)⁻¹ ^ j) (l311Corner ((2 : ℝ)⁻¹ ^ j) b x) '' ferniqueBox y₀ b₀ ⊆
      interior (ferniqueBox y₀ b₀))
    (hsq : sqOne ((2 : ℝ)⁻¹ ^ j / 32) b x ⊆ affineC ((2 : ℝ)⁻¹ ^ j)
      (l311Corner ((2 : ℝ)⁻¹ ^ j) b x) '' interior (ferniqueBox y₀ b₀)) :
    ∀ᵐ ω ∂P, ∀ ε Mφ M : ℝ,
      (∀ z ∈ sqOne ((2 : ℝ)⁻¹ ^ j / 32) b x, hatDelta W P ((2 : ℝ)⁻¹ ^ j) z ω ≤ Mφ) →
      goodSq (muHat (dgN5_wnScaleDy hW j (l311Corner ((2 : ℝ)⁻¹ ^ j) b x)).1 γ hb₀ hK ω)
        ((((2 : ℝ)⁻¹ ^ j) ^ (2 + γ ^ 2 / 2) * Real.exp (γ * Mφ))⁻¹ * ε) (1 / 32) l311UnitB M
        (0, 0) →
      goodSq (muHat hW γ hb₀ hK ω) ε ((2 : ℝ)⁻¹ ^ j / 32) b M x := by
  have hs : (0 : ℝ) < (2 : ℝ)⁻¹ ^ j := by positivity
  filter_upwards [ae_dgLGD_scale hW hγ hγ2 hb₀ hK j (l311Corner ((2 : ℝ)⁻¹ ^ j) b x) hTK]
    with ω hω ε Mφ M hMφ hgood u hu v hv
  obtain ⟨u', hu', rfl⟩ := affineC_unit_mid hs b x hu
  obtain ⟨v', hv', rfl⟩ := affineC_unit_mid hs b x hv
  have hcl : closure (sqOne ((2 : ℝ)⁻¹ ^ j / 32) b x) = sqOne ((2 : ℝ)⁻¹ ^ j / 32) b x :=
    (isClosed_sqOne _ _ _).closure_eq
  have hcont : Continuous fun z => hatDelta W P ((2 : ℝ)⁻¹ ^ j) z ω :=
    (hatDelta_spec hW hs (pow_le_one₀ (by norm_num) (by norm_num))).cont ω
  have hcpt : IsCompact (sqOne ((2 : ℝ)⁻¹ ^ j / 32) b x) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨m, hm⟩ := hcpt.bddBelow_image hcont.continuousOn
  obtain ⟨h1, -⟩ := hω (sqOne ((2 : ℝ)⁻¹ ^ j / 32) b x) (by rw [hcl]; exact hsq) m Mφ
    (fun z hz => ⟨hm ⟨z, hcl ▸ hz, rfl⟩, hMφ z (hcl ▸ hz)⟩) ε u' v'
  rw [preimage_sqOne_l311 hs b x] at h1
  exact (ENat.toENNReal_le.2 h1).trans (hgood u' hu' v' hv')

end DG
end LQGMetric
