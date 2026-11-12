/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatBasic at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Killed heat kernel, part 4: definition of `p_A(t; z, w)` and its elementary properties
(task P2-KILLED, decision D-KHK1, `decisions/DEC-KHK.md`)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 467–469):
`p_A(t; u, v) = (2πt)⁻¹ e^{−|u−v|²/(2t)} q(t; u, v)`,
`q(t; u, v) = P(B_s − (s/t)B_t + u + (s/t)(v − u) ∈ A for all s ≤ t)`.
We take this as the definition (`killedHeat`, `bridgeStay`), with `B` the canonical planar
Brownian motion `planarBM`; `bridgeStay_eq_of_isPlanarBM` shows that every planar Brownian
motion on every probability space gives the same value (DZZ's formula verbatim).

Main results: `killedHeat_nonneg`, `killedHeat_le_heatKernel` (`0 ≤ p_A ≤ p_t`),
`killedHeat_mono` (monotone in `A`), `killedHeat_univ` (`p_ℂ = p_t`), `killedHeat_symm`
(symmetry, by time reversal of the bridge: `IsPlanarBridge.reverse`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LQGMetric
namespace KilledHeat

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Time reversal of a bridge -/

/-- The time reversal `s ↦ X_{t − s}`. -/
def reverse (t : ℝ≥0) (X : ℝ≥0 → Ω → ℂ) : ℝ≥0 → Ω → ℂ := fun s ω ↦ X (t - s) ω

lemma bridgeCov_reverse {t s r : ℝ≥0} (hs : s ≤ t) (hr : r ≤ t) (b b' : Bool) :
    bridgeCov t (b, t - s) (b', t - r) = bridgeCov t (b, s) (b', r) := by
  unfold bridgeCov
  simp only
  split_ifs with hb
  · rcases eq_or_ne t 0 with ht | ht
    · subst ht
      have hs0 : s = 0 := le_antisymm hs zero_le
      have hr0 : r = 0 := le_antisymm hr zero_le
      subst hs0 hr0
      simp
    have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    rcases le_total s r with h | h
    · rw [min_eq_right (tsub_le_tsub_left h t), min_eq_left h, NNReal.coe_sub hr,
        NNReal.coe_sub hs]
      field_simp
      ring
    · rw [min_eq_left (tsub_le_tsub_left h t), min_eq_right h, NNReal.coe_sub hr,
        NNReal.coe_sub hs]
      field_simp
      ring
  · rfl

/-- The time reversal of a planar bridge of length `t` is a planar bridge of length `t`. -/
theorem IsPlanarBridge.reverse {t : ℝ≥0} {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsPlanarBridge t X P) : IsPlanarBridge t (KilledHeat.reverse t X) P := by
  refine ⟨?_, hX.gauss.comp_right (fun p : Bool × ℝ≥0 ↦ (p.1, t - p.2)), fun p ↦ hX.mean (p.1, t - p.2),
    fun p q hp hq ↦ ?_⟩
  · filter_upwards [hX.cont] with ω hω
    exact hω.comp (continuous_const.sub continuous_id)
  · show cov[coordProc X (p.1, t - p.2), coordProc X (q.1, t - q.2); P] = _
    rw [hX.cov _ _ tsub_le_self tsub_le_self]
    exact bridgeCov_reverse hp hq p.1 q.1

lemma bridgePath_reverse {t : ℝ≥0} (ht : t ≠ 0) (z w : ℂ) (X : ℝ≥0 → Ω → ℂ) {s : ℝ≥0}
    (hs : s ≤ t) (ω : Ω) :
    bridgePath t z w (KilledHeat.reverse t X) s ω = bridgePath t w z X (t - s) ω := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  unfold bridgePath KilledHeat.reverse
  rw [NNReal.coe_sub hs]
  congr 1
  have hc : ((((t : ℝ) - s) / t : ℝ) : ℂ) = 1 - (((s : ℝ) / t : ℝ) : ℂ) := by
    have ht'' : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht'
    push_cast
    field_simp
  rw [hc]
  ring

lemma bridgeEvent_reverse {t : ℝ≥0} (ht : t ≠ 0) (A : Set ℂ) (z w : ℂ) (X : ℝ≥0 → Ω → ℂ) :
    bridgeEvent A t z w (KilledHeat.reverse t X) = bridgeEvent A t w z X := by
  ext ω
  simp only [bridgeEvent, Set.mem_ofPred_eq]
  constructor
  · intro h u hu
    have := h (t - u) tsub_le_self
    rwa [bridgePath_reverse ht z w X tsub_le_self, tsub_tsub_cancel_of_le hu] at this
  · intro h s hs
    rw [bridgePath_reverse ht z w X hs]
    exact h _ tsub_le_self

/-! ### The definition -/

/-- The centred bridge of the canonical planar Brownian motion, `B_s − (s/t) B_t`. -/
def stdBridge (t : ℝ≥0) : ℝ≥0 → Ω2 → ℂ := bridgeOf t planarBM

lemma isPlanarBridge_stdBridge {t : ℝ≥0} (ht : t ≠ 0) : IsPlanarBridge t (stdBridge t) P2 :=
  isPlanarBM_planarBM.isPlanarBridge t ht

/-- DZZ's `q(t; z, w)`: the probability that the Brownian bridge from `z` to `w` in time `t`
stays in `A`. -/
def bridgeStay (A : Set ℂ) (t : ℝ≥0) (z w : ℂ) : ℝ :=
  (P2 (bridgeEvent A t z w (stdBridge t))).toReal

/-- **The killed heat kernel** `p_A(t; z, w) = p_t(z, w) · q_A(t; z, w)` (DZZ l. 467–469). -/
def killedHeat (A : Set ℂ) (t : ℝ≥0) (z w : ℂ) : ℝ :=
  heatKernel t z w * bridgeStay A t z w

/-- Any planar bridge of length `t` on any probability space gives `bridgeStay`. -/
theorem bridgeStay_eq_of_isPlanarBridge {A : Set ℂ} (hA : IsOpen A) {t : ℝ≥0} (ht : t ≠ 0)
    {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω} (hX : IsPlanarBridge t X P) (z w : ℂ) :
    (P (bridgeEvent A t z w X)).toReal = bridgeStay A t z w := by
  rw [bridgeStay, measure_bridgeEvent_eq hX (isPlanarBridge_stdBridge ht) hA]

lemma bridgeStay_nonneg (A : Set ℂ) (t : ℝ≥0) (z w : ℂ) : 0 ≤ bridgeStay A t z w :=
  ENNReal.toReal_nonneg

lemma bridgeStay_le_one (A : Set ℂ) (t : ℝ≥0) (z w : ℂ) : bridgeStay A t z w ≤ 1 := by
  unfold bridgeStay
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

lemma bridgeStay_mono {A A' : Set ℂ} (h : A ⊆ A') (t : ℝ≥0) (z w : ℂ) :
    bridgeStay A t z w ≤ bridgeStay A' t z w := by
  unfold bridgeStay
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω s hs ↦ h (hω s hs))

lemma bridgeStay_univ (t : ℝ≥0) (z w : ℂ) : bridgeStay Set.univ t z w = 1 := by
  unfold bridgeStay
  have : bridgeEvent Set.univ t z w (stdBridge t) = Set.univ := by
    ext ω; simp [bridgeEvent]
  rw [this, measure_univ, ENNReal.toReal_one]

lemma heatKernel_nonneg' (t : ℝ≥0) (z w : ℂ) : 0 ≤ heatKernel t z w := by
  unfold heatKernel
  positivity

lemma heatKernel_comm (t : ℝ) (z w : ℂ) : heatKernel t z w = heatKernel t w z := by
  unfold heatKernel
  rw [norm_sub_rev]

theorem killedHeat_nonneg (A : Set ℂ) (t : ℝ≥0) (z w : ℂ) : 0 ≤ killedHeat A t z w :=
  mul_nonneg (heatKernel_nonneg' t z w) (bridgeStay_nonneg A t z w)

theorem killedHeat_le_heatKernel (A : Set ℂ) (t : ℝ≥0) (z w : ℂ) :
    killedHeat A t z w ≤ heatKernel t z w :=
  mul_le_of_le_one_right (heatKernel_nonneg' t z w) (bridgeStay_le_one A t z w)

theorem killedHeat_mono {A A' : Set ℂ} (h : A ⊆ A') (t : ℝ≥0) (z w : ℂ) :
    killedHeat A t z w ≤ killedHeat A' t z w :=
  mul_le_mul_of_nonneg_left (bridgeStay_mono h t z w) (heatKernel_nonneg' t z w)

theorem killedHeat_univ (t : ℝ≥0) (z w : ℂ) : killedHeat Set.univ t z w = heatKernel t z w := by
  rw [killedHeat, bridgeStay_univ, mul_one]

/-- Symmetry of the bridge probability (time reversal of the bridge). -/
theorem bridgeStay_symm {A : Set ℂ} (hA : IsOpen A) {t : ℝ≥0} (ht : t ≠ 0) (z w : ℂ) :
    bridgeStay A t z w = bridgeStay A t w z := by
  rw [← bridgeStay_eq_of_isPlanarBridge hA ht (isPlanarBridge_stdBridge ht).reverse z w,
    bridgeEvent_reverse ht]
  rfl

/-- **Symmetry** `p_A(t; z, w) = p_A(t; w, z)` for open `A`. -/
theorem killedHeat_symm {A : Set ℂ} (hA : IsOpen A) (t : ℝ≥0) (z w : ℂ) :
    killedHeat A t z w = killedHeat A t w z := by
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    simp [killedHeat, heatKernel]
  · rw [killedHeat, killedHeat, heatKernel_comm, bridgeStay_symm hA ht]

end KilledHeat
end LQGMetric
