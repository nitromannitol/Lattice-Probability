/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W4Cond at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W4Main

/-!
# W4 (part 3): the time-integrated law of `Ŷ`, conditional on the last zero

`lintegral_shift_postLast_of_ae`: node W4 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1) under the
hypothesis `hgood` that almost surely `Y = dpath σ μ b` has a last zero after which it is positive.
See `W4Main.lean` for the route and the sources; `hgood` is discharged in `W4Trans.lean`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

theorem lintegral_shift_postLast_of_ae (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ)
    {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) (r : ℝ≥0)
    (hgood : ∀ᵐ ω ∂P, BddAbove {t | dpath σ μ b ω t = 0} ∧
      ∀ t, lastPass (dpath σ μ b ω) 0 < t → 0 < dpath σ μ b ω t) :
    ∫⁻ ω, (∫⁻ s in Set.Ioi (r : ℝ), F (fun u => postLast (dpath σ μ b ω) 0 (s.toNNReal + u))) ∂P =
      ENNReal.ofReal (occDens σ μ 0) * ∫⁻ y in Set.Ioi 0,
        (∫⁻ ω, {ω | ∀ t, 0 < y + dpath σ μ b ω t}.indicator
            (fun ω => F (fun u => y + dpath σ μ b ω u)) ω ∂P)
          * P {ω | ∀ t ≤ r, 0 < y + dpath σ (-μ) b ω t} := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have hcY : ∀ ω, Continuous fun t => dpath σ μ b ω t := continuous_dpath hb σ μ
  have hY0 := dpath_zero hb σ μ
  have hcYa : ∀ (c : ℝ) ω, Continuous fun t => c + dpath σ μ b ω t :=
    fun c ω => continuous_const.add (hcY ω)
  -- the auxiliary functionals `Ĥ` and `Φ_r`
  set Hm : ℝ → ℝ≥0∞ := fun y => ∫⁻ ω, posInd (fun t => y + dpath σ μ b ω t)
      * F (fun u => y + dpath σ μ b ω u) ∂P with hHm
  set Φ : ℝ → ℝ≥0∞ := fun x => ∫⁻ ω, posInd (fun t => x + dpath σ μ b ω t)
      * F (fun u => x + dpath σ μ b ω (r + u)) ∂P with hΦ
  have hHm_meas : Measurable Hm :=
    Measurable.lintegral_prod_right' (f := fun p : ℝ × Ω =>
      posInd (fun t => p.1 + dpath σ μ b p.2 t) * F (fun u => p.1 + dpath σ μ b p.2 u))
      ((measurable_posInd.comp (measurable_addPath hb σ μ fun u => u)).mul
        (hF.comp (measurable_addPath hb σ μ fun u => u)))
  have hΦ_meas : Measurable Φ :=
    Measurable.lintegral_prod_right' (f := fun p : ℝ × Ω =>
      posInd (fun t => p.1 + dpath σ μ b p.2 t) * F (fun u => p.1 + dpath σ μ b p.2 (r + u)))
      ((measurable_posInd.comp (measurable_addPath hb σ μ fun u => u)).mul
        (hF.comp (measurable_addPath hb σ μ fun u => r + u)))
  have hHm0 : ∀ y ≤ 0, Hm y = 0 := by
    intro y hy
    refine (lintegral_congr fun ω => ?_).trans lintegral_zero
    rw [posInd_of_nonpos (hcYa y ω) (by simp [hY0 ω]; exact hy), zero_mul]
  have hΦ0 : ∀ x ≤ 0, Φ x = 0 := by
    intro x hx
    refine (lintegral_congr fun ω => ?_).trans lintegral_zero
    rw [posInd_of_nonpos (hcYa x ω) (by simp [hY0 ω]; exact hx), zero_mul]
  -- S1: pathwise change of variables
  have S1 : ∫⁻ ω, (∫⁻ s in Set.Ioi (r : ℝ),
        F (fun u => postLast (dpath σ μ b ω) 0 (s.toNNReal + u))) ∂P
      = ∫⁻ ω, (∫⁻ m in Set.Ioi (0 : ℝ), posInd (fun t => dpath σ μ b ω (m.toNNReal + t))
          * F (fun u => dpath σ μ b ω (m.toNNReal + (r + u)))) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with ω hω
    exact lintegral_postLast_eq_pathwise (hcY ω) (hY0 ω) hω.1 hω.2 F r
  -- S2: Tonelli
  have hU : Measurable fun q : ℝ≥0 × Ω => dpath σ μ b q.2 q.1 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun t ω => dpath σ μ b ω t)
      (fun ω => hcY ω) (measurable_dpath hb σ μ)
  have hpath : ∀ c : ℝ≥0 → ℝ≥0,
      Measurable fun p : Ω × ℝ => fun t => dpath σ μ b p.1 (p.2.toNNReal + c t) := fun c =>
    measurable_pi_iff.2 fun t =>
      hU.comp ((measurable_snd.real_toNNReal.add_const (c t)).prodMk measurable_fst)
  have S2 : ∫⁻ ω, (∫⁻ m in Set.Ioi (0 : ℝ), posInd (fun t => dpath σ μ b ω (m.toNNReal + t))
          * F (fun u => dpath σ μ b ω (m.toNNReal + (r + u)))) ∂P
      = ∫⁻ m in Set.Ioi (0 : ℝ), (∫⁻ ω, posInd (fun t => dpath σ μ b ω (m.toNNReal + t))
          * F (fun u => dpath σ μ b ω (m.toNNReal + (r + u))) ∂P) :=
    lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      (((measurable_posInd.comp (hpath fun t => t)).mul
        (hF.comp (hpath fun u => r + u)))).aemeasurable
  -- S3: Markov at `m`
  have hG : Measurable (Function.uncurry fun (y : ℝ) (w : ℝ≥0 → ℝ) =>
      posInd (fun t => y + w t) * F (fun u => y + w (r + u))) :=
    (measurable_posInd.comp (measurable_pi_iff.2 fun t =>
      measurable_fst.add ((measurable_pi_apply t).comp measurable_snd))).mul
      (hF.comp (measurable_pi_iff.2 fun u =>
        measurable_fst.add ((measurable_pi_apply (r + u)).comp measurable_snd)))
  have S3 : ∀ m : ℝ, ∫⁻ ω, posInd (fun t => dpath σ μ b ω (m.toNNReal + t))
        * F (fun u => dpath σ μ b ω (m.toNNReal + (r + u))) ∂P
      = ∫⁻ ω, Φ (dpath σ μ b ω m.toNNReal) ∂P := by
    intro m
    have h := markov_fixed hb σ μ m.toNNReal (A := fun _ => 1)
      (G := fun y w => posInd (fun t => y + w t) * F (fun u => y + w (r + u))) measurable_const hG
    simp only [one_mul, add_sub_cancel] at h
    exact h
  -- S4, S5: occupation measure
  have S45 : ∫⁻ m in Set.Ioi (0 : ℝ), (∫⁻ ω, Φ (dpath σ μ b ω m.toNNReal) ∂P)
      = ENNReal.ofReal (occDens σ μ 0) * ∫⁻ x, Φ x := by
    rw [← lintegral_occ_eq hb σ μ hΦ_meas, occ_eq hσ hμ,
      lintegral_withDensity_eq_lintegral_mul _
        (continuous_occDens hσ hμ).measurable.ennreal_ofReal hΦ_meas,
      ← lintegral_const_mul _ hΦ_meas]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rcases le_or_gt 0 x with hx | hx
    · rw [occDens_nonneg_const hσ hμ x hx]
    · rw [hΦ0 x hx.le, mul_zero, mul_zero]
  -- S6: Markov at `r`
  have S6 : ∀ x, Φ x = ∫⁻ ω, posInd (fun t => x + dpath σ μ b ω (min t r))
      * Hm (x + dpath σ μ b ω r) ∂P := by
    intro x
    have hA : Measurable fun w : ℝ≥0 → ℝ => posInd (fun t => x + w t) :=
      measurable_posInd.comp (measurable_pi_iff.2 fun t => measurable_const.add (measurable_pi_apply t))
    have hp : Measurable fun p : ℝ × (ℝ≥0 → ℝ) => fun u => x + p.1 + p.2 u :=
      measurable_pi_iff.2 fun u =>
        (measurable_const.add measurable_fst).add ((measurable_pi_apply u).comp measurable_snd)
    have h := markov_fixed hb σ μ r (A := fun w => posInd (fun t => x + w t))
      (G := fun y w => posInd (fun u => x + y + w u) * F (fun u => x + y + w u)) hA
      ((measurable_posInd.comp hp).mul (hF.comp hp))
    refine Eq.trans ?_ h
    refine lintegral_congr fun ω => ?_
    have e : (fun u => x + dpath σ μ b ω r + (dpath σ μ b ω (r + u) - dpath σ μ b ω r))
        = fun u => x + dpath σ μ b ω (r + u) := by funext u; ring
    have hs := posInd_split (w := fun t => x + dpath σ μ b ω t) (hcYa x ω) r
    try simp only at hs
    rw [e, ← mul_assoc, ← hs]
  -- S7: Lebesgue duality
  have hrev := lintegral_reversal hb σ μ r (F := fun w => posInd w * Hm (w r))
    (measurable_posInd.mul (hHm_meas.comp (measurable_pi_apply r)))
  simp only [min_self, tsub_self, dpath_zero hb σ (-μ), add_zero] at hrev
  -- S8: the right-hand side
  have S8 : ∫⁻ y, ∫⁻ ω, posInd (fun t => y + dpath σ (-μ) b ω (r - t)) * Hm y ∂P
      = ∫⁻ y in Set.Ioi 0,
        (∫⁻ ω, {ω | ∀ t, 0 < y + dpath σ μ b ω t}.indicator
            (fun ω => F (fun u => y + dpath σ μ b ω u)) ω ∂P)
          * P {ω | ∀ t ≤ r, 0 < y + dpath σ (-μ) b ω t} := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun y => ?_
    have hmeasX : Measurable fun ω => fun t : ℝ≥0 => y + dpath σ (-μ) b ω (r - t) :=
      measurable_pi_iff.2 fun t => measurable_const.add (measurable_dpath hb σ (-μ) (r - t))
    rw [lintegral_mul_const (f := fun ω => posInd (fun t => y + dpath σ (-μ) b ω (r - t))) _
      (measurable_posInd.comp hmeasX)]
    by_cases hy : 0 < y
    · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hy), mul_comm]
      congr 1
      · refine lintegral_congr fun ω => ?_
        by_cases h : ∀ t, 0 < y + dpath σ μ b ω t
        · rw [posInd_of_pos (hcYa y ω) h, one_mul,
            Set.indicator_of_mem (show ω ∈ {ω | ∀ t, 0 < y + dpath σ μ b ω t} from h)]
        · rw [posInd_of_not (hcYa y ω) h, zero_mul,
            Set.indicator_of_notMem (show ω ∉ {ω | ∀ t, 0 < y + dpath σ μ b ω t} from h)]
      · have hcX : ∀ ω, Continuous fun t : ℝ≥0 => y + dpath σ (-μ) b ω (r - t) := fun ω =>
          continuous_const.add ((continuous_dpath hb σ (-μ) ω).comp
            (continuous_const.sub continuous_id))
        have hS : {ω | ∀ t ≤ r, 0 < y + dpath σ (-μ) b ω t}
            = (fun ω => fun t : ℝ≥0 => y + dpath σ (-μ) b ω (r - t)) ⁻¹' posAllSet := by
          ext ω
          simp only [mem_setOf_eq, mem_preimage]
          rw [mem_posAllSet_iff (hcX ω)]
          constructor
          · intro h t; exact h _ tsub_le_self
          · intro h t ht; have := h (r - t); rwa [tsub_tsub_cancel_of_le ht] at this
        rw [hS, ← lintegral_indicator_one (measurableSet_posAllSet.preimage hmeasX)]
        rfl
    · rw [Set.indicator_of_notMem (by simpa using hy), hHm0 y (not_lt.1 hy), mul_zero]
  rw [S1, S2, lintegral_congr S3, S45, lintegral_congr S6, hrev, S8]

end QuantumZipper.Williams
