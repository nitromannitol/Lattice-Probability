/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Event3Inv at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.EventStmts
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes57
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bInv
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2Meas
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate

/-!
# GM Proposition 5.2: `E_r` is a.s. unaffected by adding a constant to `h` (task P2-M2M4, D83 P4a)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, l. 2801
("the occurrence of the events `E_r` … is unaffected by adding a constant to `h`") and l. 3296–3297
(proof of Lemma 5.9: by Axiom III, `E_r` depends on `h` only modulo additive constants). Every
condition of `E_r` compares `D_h`, `D̃_h` and `𝔠_r e^{ξ h_r(0)}` at the same field, and all three
are multiplied by `e^{ξc}` when `c` is added to `h`; `(h + c, φ)_∇ = (h, φ)_∇` since `∫ Δφ = 0`.
For the Lean events this is an a.s. statement (D87 (4)): `D_{h+c} = e^{ξc} D_h` is Axioms I + III
(`IsWeakLQGMetric.ae_dist_addConst`), `(h + c)_r(0) = h_r(0) + c` holds a.s.
(`CircleAvg.ae_circleAvg_addConst`).

* `mem_linkEvent_of_scale`: the event of Lemma 5.8 is unaffected by scaling `D_h`, `D̃_h` by the
  same factor (as `mem_tubeEvent_of_scale`, GM l. 3001);
* `eventE_addConst_iff`: deterministic invariance at a field where the three scale exactly;
* `ae_eventE_addConst_iff`: the invariance clause of `P5_2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

lemma ofReal_mul_le_scale_iff {e : ℝ} (he : 0 < e) (k a : ℝ) (s : ℝ≥0∞) :
    ENNReal.ofReal (k * (e * a)) ≤ ENNReal.ofReal e * s ↔ ENNReal.ofReal (k * a) ≤ s := by
  rw [show k * (e * a) = e * (k * a) by ring, ENNReal.ofReal_mul he.le]
  exact ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 he).ne' ENNReal.ofReal_ne_top

/-- **GM l. 3001–3002, for Lemma 5.8's event**: unaffected by scaling `D_h`, `D̃_h` by `e > 0` -/
theorem mem_linkEvent_of_scale {D D' : DistC → ContMetric} {cs Cs c₁ η δ ρ b ε r : ℝ}
    {U : ℂ → ℂ → Set ℂ} {g₁ g₂ : DistC} {e : ℝ} (he : 0 < e)
    (h : ∀ u v, (D g₂).1 (u, v) = e * (D g₁).1 (u, v))
    (h' : ∀ u v, (D' g₂).1 (u, v) = e * (D' g₁).1 (u, v)) :
    g₂ ∈ linkEvent D D' cs Cs c₁ η δ ρ b ε r U ↔ g₁ ∈ linkEvent D D' cs Cs c₁ η δ ρ b ε r U := by
  have hr : ∀ u v, (D' g₂).1 (u, v) ≤ c₁ * (D g₂).1 (u, v) ↔
      (D' g₁).1 (u, v) ≤ c₁ * (D g₁).1 (u, v) := fun u v => by
    rw [h, h', show c₁ * (e * (D g₁).1 (u, v)) = e * (c₁ * (D g₁).1 (u, v)) by ring]
    exact mul_le_mul_iff_right₀ he
  simp only [linkEvent, mem_ofPred_eq, hr]
  simp only [h', setDist_of_scale he h', ofReal_le_scale_iff he,
    uniqueGeodIn_iff_of_scale he h', internal_of_scale he h', internal_le_scale_iff he]

/-- **GM l. 2801, 3296–3297**: `E_r` is unaffected by adding `c` to a field `g` at which `D`, `D̃`
and the circle average `g_r(0)` transform as for the GFF (Weyl scaling) -/
theorem eventE_addConst_iff {D D' : DistC → ContMetric} {S : EData} {U : ℂ → ℂ → Set ℂ}
    {fb gb : Set ℂ → TestC} {r : ℝ} {g : DistC} {c : ℝ}
    (hD : ∀ u v, (D (addConst g c)).1 (u, v) = Real.exp (S.ξ * c) * (D g).1 (u, v))
    (hD' : ∀ u v, (D' (addConst g c)).1 (u, v) = Real.exp (S.ξ * c) * (D' g).1 (u, v))
    (hav : circleAvg (addConst g c) r 0 = circleAvg g r 0 + c) :
    addConst g c ∈ eventE D D' S U fb gb r ↔ g ∈ eventE D D' S U fb gb r := by
  have he := Real.exp_pos (S.ξ * c)
  have hsf : scaleFac S.ξ S.c (addConst g c) r 0 =
      Real.exp (S.ξ * c) * scaleFac S.ξ S.c g r 0 := by
    simp only [scaleFac, hav, mul_add, Real.exp_add]; ring
  have hL := mem_linkEvent_of_scale (cs := S.cs) (Cs := S.Cs) (c₁ := S.c₁) (η := S.η) (δ := S.δ)
    (ρ := S.ρ) (b := S.b) (ε := S.ε₀) (r := r) (U := U) he hD hD'
  simp only [eventE, mem_inter_iff, mem_ofPred_eq, hL, hsf]
  simp only [internal_of_scale he hD, setDist_of_scale he hD, len_of_scale he hD,
    DFGPS.L32M.internalDiam_of_scale he hD, internal_le_scale_iff he,
    ofReal_mul_le_scale_iff he, dirInner_addConst]

/-- **The invariance clause of GM Proposition 5.2** (GM l. 2801; D87 (4)): almost surely, adding
any constant to `h` does not change the occurrence of `E_r` -/
theorem ae_eventE_addConst_iff {γ : ℝ} {D D' : DistC → ContMetric} {c₀ : ℝ → ℝ}
    (hPS : PairSetting γ D D' c₀) {S : EData} (hξ : S.ξ = xiGamma γ) (U : ℂ → ℂ → Set ℂ)
    (fb gb : Set ℂ → TestC) {r : ℝ} (hr : 0 < r)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, addConst (h ω) c ∈ eventE D D' S U fb gb r ↔
      h ω ∈ eventE D D' S U fb gb r := by
  obtain ⟨-, -, hD, hD'⟩ := hPS
  have hP := Tight.isGFFPlusCont_of_wp hh
  filter_upwards [hD.ae_dist_addConst hP, hD'.ae_dist_addConst hP,
    CircleAvg.ae_circleAvg_addConst hh 0 hr] with ω h1 h2 h3 c
  exact eventE_addConst_iff (by rw [hξ]; exact h1 c) (by rw [hξ]; exact h2 c) (h3 c)

end LQGMetric.GM
