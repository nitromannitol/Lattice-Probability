/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_9Trans at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_10
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_9Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
proof of Proposition 3.9 (T:1769–1773): "Proposition 3.10 together with Axiom IV′ shows that …
for each `k`, `E[(𝔠_{𝕣ρ_k}^{-1} e^{-ξh_{𝕣ρ_k}(𝕣u_k)} sup_{z,w∈𝕣S_k} D_h(z,w;𝕣S_k))^p] ≤ C̃_p`"
(eqn-diam-moment0). We transfer the tail form `DiamTailRS` (see `P3_10.lean`) from the square
`r𝕊` at `0` to the square `z + r𝕊`, uniformly in `r` and `z`, on the canonical space
`(DistC, μ, id)`: Axiom IV′ + Axiom III (`ae_transField_ident`) and the invariance of `μ` under the
recentred translation (`measure_preimage_transField_le`), exactly as `prop3_1_centre`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

/-- the open unit square `𝕊` -/
def unitSq : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < 1}

/-- `internalDiam` of `D' = a·D(· + z, · + z)` on translated sets -/
lemma internalDiam_transl_smul {D D' : ContMetric} {a : ℝ} (ha : 0 < a) (z : ℂ)
    (h : ∀ u v, D'.1 (u, v) = a * D.1 (u + z, v + z)) (A W : Set ℂ) :
    internalDiam D' ((fun w => w - z) '' A) ((fun w => w - z) '' W) =
      ENNReal.ofReal a * internalDiam D A W := by
  unfold internalDiam
  simp only [iSup_image, internal_transl_smul ha z h]
  simp_rw [ENNReal.mul_iSup]

/-- **The tail of Prop 3.10 at every square `z + r𝕊`**, uniformly in `r` and `z` (canonical
space). -/
theorem diam_square_tail (hT : DiamTailRS) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ) {a : ℝ}
    (ha : a < 4 * dGamma γ / γ ^ 2) :
    ∃ C t₀ : ℝ, ∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ t : ℝ, t₀ ≤ t →
      μ {g | ENNReal.ofReal t < ENNReal.ofReal (scaleFac (xiGamma γ) c g r z)⁻¹ *
          internalDiam (D g) (scaleSet r z unitSq) (scaleSet r z unitSq)} ≤
        ENNReal.ofReal (C * t ^ (-a)) := by
  obtain ⟨C, t₀, hC⟩ := hT γ hγ0 hγ2 D c hD a ha
  refine ⟨C, t₀, fun r hr z t ht => ?_⟩
  refine le_trans ?_ ((measure_preimage_transField_le hμ z _).trans (hC μ id hμ r hr t ht))
  apply measure_mono_ae
  filter_upwards [ae_transField_ident hD hμ z hr] with g ⟨hd1, hd2⟩
  intro hg
  simp only [mem_ofPred_eq, mem_preimage, id] at hg ⊢
  set e := Real.exp (-(xiGamma γ * circleAvg g 1 z)) with he_def
  have he : 0 < e := Real.exp_pos _
  have hS : scaleFac (xiGamma γ) c (transField z g) r 0 = e * scaleFac (xiGamma γ) c g r z := by
    unfold scaleFac
    rw [hd2, mul_sub, sub_eq_add_neg, Real.exp_add, he_def]
    ring
  have hX : internalDiam (D (transField z g)) (rS r) (rS r) =
      ENNReal.ofReal e * internalDiam (D g) (scaleSet r z unitSq) (scaleSet r z unitSq) := by
    rw [rS, scaleSet_zero_eq_image r z]
    exact internalDiam_transl_smul he z hd1 _ _
  have hs : 0 < scaleFac (xiGamma γ) c g r z := mul_pos (hD.tightness.1 r hr) (Real.exp_pos _)
  rw [hS, hX]
  have hk : ENNReal.ofReal (e * scaleFac (xiGamma γ) c g r z)⁻¹ * ENNReal.ofReal e =
      ENNReal.ofReal (scaleFac (xiGamma γ) c g r z)⁻¹ := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [← mul_assoc, hk]
  exact hg

end LQGMetric.DFGPS
