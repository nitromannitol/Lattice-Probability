/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W5Rev at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Dens

/-!
# W5 (part 5): the reversal step on `[0, U]` with weights `χ_c` and `ψ_r`

Last step of W5(i), reversed side, of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1): the Lebesgue
duality W2 (`lintegral_reversal`) on `[0, U]`, applied with the weight `χ_c` at the start and
`ψ_r` at the end, turns the reversed-side expression

`∫ dz χ_c(z) E[g(z + X(U - uᵢ)) ψ_r(z + X_U); z + X > 0 on [0,U]]`

into the `Ŷ`-side expression of `lintegral_postLast_killed` (without the factor `C`):

`∫_{y>0} dy E[g(y + Y(uᵢ)) χ_c(y + Y_U); y + Y > 0 on [0,U]] ψ_r(y)`,

with `ψ_r(y) = P(y + X > 0 on [0, r])` (`psiR`). Sources: Williams (1974); Revuz–Yor VII §4
(time reversal of drift Brownian motion); bookkeeping own.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- `ψ_r(y) = P(y + X > 0 on [0, r])`, `X = dpath σ (-μ) b`. -/
def psiR (b : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (σ μ : ℝ) (r : ℝ≥0) (y : ℝ) : ℝ≥0∞ :=
  P {ω | ∀ t ≤ r, 0 < y + dpath σ (-μ) b ω t}

theorem psiR_eq (hb : GoodBM b P) (σ μ : ℝ) (r : ℝ≥0) (y : ℝ) :
    psiR b P σ μ r y = ∫⁻ ω, (posSet r).indicator 1 (fun t => y + dpath σ (-μ) b ω t) ∂P := by
  have hm : Measurable fun ω => fun t => y + dpath σ (-μ) b ω t :=
    measurable_pi_iff.2 fun t => measurable_const.add (measurable_dpath hb σ (-μ) t)
  have hS : {ω | ∀ t ≤ r, 0 < y + dpath σ (-μ) b ω t}
      = (fun ω => fun t => y + dpath σ (-μ) b ω t) ⁻¹' posSet r := by
    ext ω
    rw [mem_preimage, mem_posSet_iff (show Continuous fun t => y + dpath σ (-μ) b ω t from
      continuous_const.add (continuous_dpath hb σ (-μ) ω))]
    rfl
  rw [psiR, hS, ← lintegral_indicator_one (hm (measurableSet_posSet r))]
  rfl

theorem measurable_psiR (hb : GoodBM b P) (σ μ : ℝ) (r : ℝ≥0) :
    Measurable (psiR b P σ μ r) := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have h : psiR b P σ μ r = fun y =>
      ∫⁻ ω, (posSet r).indicator 1 (fun t => y + dpath σ (-μ) b ω t) ∂P :=
    funext (psiR_eq hb σ μ r)
  rw [h]
  exact Measurable.lintegral_prod_right'
    (f := fun p : ℝ × Ω => (posSet r).indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞)
      (fun t => p.1 + dpath σ (-μ) b p.2 t))
    ((measurable_const.indicator (measurableSet_posSet r)).comp
      (measurable_pi_iff.2 fun t =>
        measurable_fst.add ((measurable_dpath hb σ (-μ) t).comp measurable_snd)))

theorem measurable_chiKill (hb : GoodBM b P) (σ μ c : ℝ) :
    Measurable (chiKill b P σ μ c) := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have h : chiKill b P σ μ c = fun z => ∫⁻ ω', posInd (fun t => z + dpath σ μ b ω' t)
      * hitPosInd c (fun t => z + dpath σ μ b ω' t) ∂P := funext (chiKill_eq hb σ μ c)
  rw [h]
  have hpm : Measurable fun p : ℝ × Ω => fun t => p.1 + dpath σ μ b p.2 t :=
    measurable_pi_iff.2 fun t =>
      measurable_fst.add ((measurable_dpath hb σ μ t).comp measurable_snd)
  exact Measurable.lintegral_prod_right'
    (f := fun p : ℝ × Ω => posInd (fun t => p.1 + dpath σ μ b p.2 t)
      * hitPosInd c (fun t => p.1 + dpath σ μ b p.2 t))
    ((measurable_posInd.comp hpm).mul ((measurable_hitPosInd c).comp hpm))

theorem chiKill_ne_top (hb : GoodBM b P) (σ μ c z : ℝ) : chiKill b P σ μ c z ≠ ∞ := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  exact measure_ne_top _ _

/-- **Reversal step** (blueprint W5(i), reversed side, last step: W2 on `[0, U]`). -/
theorem lintegral_chi_reversal (hb : GoodBM b P) (σ μ c : ℝ) {n : ℕ} (u : Fin n → ℝ≥0)
    (U : ℝ≥0) (hu : ∀ i, u i ≤ U) {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) (r : ℝ≥0) :
    ∫⁻ z, chiKill b P σ μ c z * ∫⁻ ω, {ω | ∀ t ≤ U, 0 < z + dpath σ (-μ) b ω t}.indicator
        (fun ω => g (fun i => z + dpath σ (-μ) b ω (U - u i))
          * psiR b P σ μ r (z + dpath σ (-μ) b ω U)) ω ∂P
      = ∫⁻ y in Ioi 0, (∫⁻ ω, {ω | ∀ t ≤ U, 0 < y + dpath σ μ b ω t}.indicator
          (fun ω => g (fun i => y + dpath σ μ b ω (u i))
            * chiKill b P σ μ c (y + dpath σ μ b ω U)) ω ∂P) * psiR b P σ μ r y := by
  set F : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun q => chiKill b P σ μ c (q 0)
    * ((posSet U).indicator 1 q * (g (fun i => q (U - u i)) * psiR b P σ μ r (q U))) with hFdef
  have hF : Measurable F :=
    ((measurable_chiKill hb σ μ c).comp (measurable_pi_apply 0)).mul
      ((measurable_const.indicator (measurableSet_posSet U)).mul
        ((hg.comp (measurable_pi_iff.2 fun i => measurable_pi_apply _)).mul
          ((measurable_psiR hb σ μ r).comp (measurable_pi_apply U))))
  have hW2 := lintegral_reversal hb σ (-μ) U hF
  simp only [neg_neg] at hW2
  -- the left side of W2
  have hL : ∀ x, ∫⁻ ω, F (fun t => x + dpath σ (-μ) b ω (min t U)) ∂P
      = chiKill b P σ μ c x * ∫⁻ ω, {ω | ∀ t ≤ U, 0 < x + dpath σ (-μ) b ω t}.indicator
        (fun ω => g (fun i => x + dpath σ (-μ) b ω (U - u i))
          * psiR b P σ μ r (x + dpath σ (-μ) b ω U)) ω ∂P := by
    intro x
    rw [← lintegral_const_mul' _ _ (chiKill_ne_top hb σ μ c x)]
    refine lintegral_congr fun ω => ?_
    have hq : Continuous fun t => x + dpath σ (-μ) b ω (min t U) :=
      continuous_const.add ((continuous_dpath hb σ (-μ) ω).comp (continuous_id.min continuous_const))
    have hiff : (fun t => x + dpath σ (-μ) b ω (min t U)) ∈ posSet U
        ↔ ∀ t ≤ U, 0 < x + dpath σ (-μ) b ω t := by
      rw [mem_posSet_iff hq]
      refine forall₂_congr fun t ht => ?_
      rw [min_eq_left ht]
    simp only [hFdef, min_eq_left (zero_le : (0 : ℝ≥0) ≤ U), min_self, dpath_zero hb σ (-μ) ω, add_zero,
      min_eq_left (tsub_le_self : U - u _ ≤ U)]
    by_cases h : ∀ t ≤ U, 0 < x + dpath σ (-μ) b ω t
    · rw [indicator_of_mem (hiff.2 h),
        indicator_of_mem (show ω ∈ {ω | ∀ t ≤ U, 0 < x + dpath σ (-μ) b ω t} from h)]
      simp
    · rw [indicator_of_notMem (fun hm => h (hiff.1 hm)),
        indicator_of_notMem (show ω ∉ {ω | ∀ t ≤ U, 0 < x + dpath σ (-μ) b ω t} from h)]
      simp
  -- the right side of W2
  have hR : ∀ y, ∫⁻ ω, F (fun t => y + dpath σ μ b ω (U - t)) ∂P
      = (Ioi (0 : ℝ)).indicator (fun y => (∫⁻ ω, {ω | ∀ t ≤ U, 0 < y + dpath σ μ b ω t}.indicator
          (fun ω => g (fun i => y + dpath σ μ b ω (u i))
            * chiKill b P σ μ c (y + dpath σ μ b ω U)) ω ∂P) * psiR b P σ μ r y) y := by
    intro y
    have hpull : ∫⁻ ω, F (fun t => y + dpath σ μ b ω (U - t)) ∂P
        = (∫⁻ ω, {ω | ∀ t ≤ U, 0 < y + dpath σ μ b ω t}.indicator
          (fun ω => g (fun i => y + dpath σ μ b ω (u i))
            * chiKill b P σ μ c (y + dpath σ μ b ω U)) ω ∂P) * psiR b P σ μ r y := by
      rw [← lintegral_mul_const' _ _ (by
        haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
        exact measure_ne_top _ _)]
      refine lintegral_congr fun ω => ?_
      have hq : Continuous fun t => y + dpath σ μ b ω (U - t) :=
        continuous_const.add ((continuous_dpath hb σ μ ω).comp (continuous_const.sub continuous_id))
      have hiff : (fun t => y + dpath σ μ b ω (U - t)) ∈ posSet U
          ↔ ∀ t ≤ U, 0 < y + dpath σ μ b ω t := by
        rw [mem_posSet_iff hq]
        constructor
        · intro h t ht
          have := h (U - t) tsub_le_self
          rwa [tsub_tsub_cancel_of_le ht] at this
        · intro h t _
          exact h _ tsub_le_self
      simp only [hFdef, tsub_zero, tsub_self, dpath_zero hb σ μ ω, add_zero,
        tsub_tsub_cancel_of_le (hu _)]
      by_cases h : ∀ t ≤ U, 0 < y + dpath σ μ b ω t
      · rw [indicator_of_mem (hiff.2 h),
          indicator_of_mem (show ω ∈ {ω | ∀ t ≤ U, 0 < y + dpath σ μ b ω t} from h)]
        simp only [Pi.one_apply, one_mul]
        ring
      · rw [indicator_of_notMem (fun hm => h (hiff.1 hm)),
          indicator_of_notMem (show ω ∉ {ω | ∀ t ≤ U, 0 < y + dpath σ μ b ω t} from h)]
        simp
    rw [hpull]
    by_cases hy : (0 : ℝ) < y
    · rw [indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy)]
    · rw [indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy)]
      have hz : ∀ ω, {ω | ∀ t ≤ U, 0 < y + dpath σ μ b ω t}.indicator
          (fun ω => g (fun i => y + dpath σ μ b ω (u i))
            * chiKill b P σ μ c (y + dpath σ μ b ω U)) ω = 0 := by
        intro ω
        refine indicator_of_notMem (fun hm => hy ?_) _
        have := hm 0 (zero_le : (0 : ℝ≥0) ≤ U)
        rwa [dpath_zero hb σ μ ω, add_zero] at this
      simp [hz]
  calc _ = ∫⁻ x, ∫⁻ ω, F (fun t => x + dpath σ (-μ) b ω (min t U)) ∂P :=
        (lintegral_congr hL).symm
    _ = ∫⁻ y, ∫⁻ ω, F (fun t => y + dpath σ μ b ω (U - t)) ∂P := hW2
    _ = _ := by
        rw [lintegral_congr hR, lintegral_indicator measurableSet_Ioi]

end QuantumZipper.Williams
