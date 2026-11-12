/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43cAsm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43cL53
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.EventStmts
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.GoodRadiiLaw
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedSwap
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF

/-!
# GM Proposition 4.3 from Propositions 3.5 and 5.2 (task P2-M2N3)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Proposition 4.3 (l. 1582–1593) and its proof in §5.1 (l. 2722–2836): Proposition 5.2 gives the
events `E_r` at the radii `r` with `ρ r ∈ 𝓡_0` (the scales of Proposition 3.5), Lemma 5.3 the
measurability of `𝔈_r^{𝕫,𝕨}(z)`, Lemma 5.4 condition (4), and (5.4) the conclusion.
* `exists_etaChoice`: GM's "`η` small enough" (l. 2742, 3174); own elementary choice.
* `ae_constCore_eventAt`: with a.s. invariance (D87 (4)), the constant-invariant core of
  `E_r(z)` is a.s. `E_r(z)`.
* `gm_P4_3_core`: GM Proposition 4.3, with the additional hypothesis `ν < 1` (GM: `ν ≤ ν_*` with
  `ν_* ∈ (0,1)` from Theorem 4.2, l. 1586; needed to apply Proposition 3.5, which has `ν < 1`).
Radii: `𝓡 = {r ≤ ε₀ρ⁻¹𝕣 : ρ r ∈ 𝓡_0}` (GM l. 2731–2735, every other radius by
`exists_sparse_radii`, DV-B3); `E_r(z) = constCore (E_r(· + z))` (D87 (4)); `𝔈 = constCore 𝔈`
(D79); `Λ = (N+1)e^{3Λ₀}` (D87 (3), DV-M2N2-a).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- GM's choice of `η` (l. 3174: "`η ∈ (0,1)` small enough that …"); own elementary choice -/
lemma exists_etaChoice {cs Cs c₁ c₂ : ℝ} (hcs : 0 < cs) (hc₁ : cs < c₁) (hc₁₂ : c₁ < c₂)
    (hc₂ : c₂ < Cs) : ∃ η, EtaChoice cs Cs c₁ c₂ η := by
  set k := Cs / cs with hk
  have hk1 : 1 < k := by rw [hk, one_lt_div hcs]; linarith
  have hc₁0 : 0 < c₁ := hcs.trans hc₁
  have hden : 0 < c₁ + k * c₂ := by nlinarith
  set η := min (1 / 2) (min ((c₂ - c₁) / (4 * (c₁ + k * c₂))) ((k - 1) / 4)) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (lt_min (div_pos (by linarith) (by positivity))
    (by linarith))
  have hη1 : η ≤ (c₂ - c₁) / (4 * (c₁ + k * c₂)) := (min_le_right _ _).trans (min_le_left _ _)
  have hη2 : η ≤ (k - 1) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hη3 : η ≤ 1 / 2 := min_le_left _ _
  have hA : η * (4 * (c₁ + k * c₂)) ≤ c₂ - c₁ := by
    rwa [le_div_iff₀ (by positivity)] at hη1
  have hkk : cs⁻¹ * Cs = k := by rw [hk]; field_simp
  have hB : 2 * k * η ≤ 1 / 2 := by nlinarith
  have hkk' : 2 * cs⁻¹ * Cs * η = 2 * k * η := by rw [mul_assoc 2 cs⁻¹ Cs, hkk]
  refine ⟨η, hη0, by linarith, ?_, by nlinarith, by rw [hkk']; linarith, by nlinarith⟩
  rw [hkk', div_lt_iff₀ (by linarith)]
  nlinarith

/-- with a.s. invariance of `E` under additive constants at `h(· + z)`, `h ∈ constCore E_r(z)` iff
`h ∈ E_r(z)`, a.s. -/
lemma ae_constCore_eventAt {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {E : Set DistC} {z : ℂ}
    (hinv : ∀ᵐ ω ∂P, ∀ c : ℝ, addConst (affineComp 1 z (h ω)) c ∈ E ↔ affineComp 1 z (h ω) ∈ E) :
    h ⁻¹' constCore (eventAt E z) =ᵐ[P] h ⁻¹' eventAt E z := by
  filter_upwards [hinv] with ω hω
  refine propext (constCore_eq_of_inv fun c => ?_)
  show affineComp 1 z (addConst (h ω) c) ∈ E ↔ affineComp 1 z (h ω) ∈ E
  rw [affineComp_addConst one_pos]
  exact hω c

lemma measurable_addConst_circleAvg (r : ℝ) (z : ℂ) :
    Measurable fun g : DistC => addConst g (-circleAvg g r z) := by
  refine GFFInv.measurable_distC_iff.2 fun φ => ?_
  simp only [GFFInv.addConst_apply]
  exact (GFFInv.measurable_pair φ).add ((measurable_circleAvg_left r z).neg.const_mul _)

end LQGMetric.GM
