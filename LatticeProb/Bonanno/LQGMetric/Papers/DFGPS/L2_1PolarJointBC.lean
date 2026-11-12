/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1PolarJointBC at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1PolarJointKolm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Kolmogorov + Borel–Cantelli for the three-parameter truncation differences

`ae_eventually_gaussDiff3_le`: for a whole-plane GFF, a.s., for every `R`, eventually in `n`,
`|G_n(q)| ≤ 25 e^{−n/2}` for all `q ∈ [−R, R]³`, where `G_n(q)` is the mean-zero part of
`⟨g, D_n(e^{q₀}, q₁ + i q₂)⟩` (`gaussDiff3`). The three-parameter version of
`IsWholePlaneGFF.ae_eventually_gaussDiffProc_le` (Field/HeatMollifyKolm), same proof:
fourth moments `≤ g₄ mz² B⁴ (n+3)^{18}` from the joint Lipschitz bound, the dyadic Kolmogorov bound
`kolm_sup_tail_N` (`d = 3`, `p = a = 4`, `θ = 7/8`), and Borel–Cantelli.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric.DFGPS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

lemma summable_kolm3 (c cR : ℝ) (hc : 0 ≤ c) (hcR : 0 ≤ cR) :
    Summable fun n : ℕ => c * ((n : ℝ) + 3) ^ 18 * Real.exp (-(n : ℝ)) ^ 4 /
      Real.exp (-(n : ℝ) / 2) ^ 4 * cR := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (((summable_shift_pow_mul_exp 18).mul_left (c * cR)))
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_div_assoc, ← Real.exp_sub]
  have : Real.exp ((4 : ℕ) * -(n : ℝ) - (4 : ℕ) * (-(n : ℝ) / 2)) ≤ Real.exp (-(n : ℝ)) := by
    apply Real.exp_le_exp.2; push_cast; linarith [n.cast_nonneg (α := ℝ)]
  have h18 : 0 ≤ ((n : ℝ) + 3) ^ 18 := by positivity
  calc c * ((n : ℝ) + 3) ^ 18 * Real.exp ((4 : ℕ) * -(n : ℝ) - (4 : ℕ) * (-(n : ℝ) / 2)) * cR
      ≤ c * ((n : ℝ) + 3) ^ 18 * Real.exp (-(n : ℝ)) * cR := by gcongr
    _ = _ := by ring

/-- **Uniform bound** on the three-parameter mean-zero truncation differences. -/
theorem ae_eventually_gaussDiff3_le (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ R : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ q ∈ QuantumZipper.KolmD.boxD (d := 3) R,
        |gaussDiff3 h n q ω| ≤ 25 * Real.exp (-(n : ℝ) / 2) := by
  rw [ae_all_iff]
  intro R
  set a : ℝ := Real.exp (-((R : ℝ) + 1))
  set b : ℝ := Real.exp ((R : ℝ) + 1)
  have ha : 0 < a := Real.exp_pos _
  set r : ℝ := 2 * ((R : ℝ) + 1) with hr
  have hr0 : 0 ≤ r := by positivity
  set L := (heatLipZ a b r + heatLipS a b r) * (Real.exp ((R : ℝ) + 1) + 2)
  have hLZ : 0 ≤ heatLipZ a b r := by unfold heatLipZ; positivity
  have hL : 0 ≤ L := by have := heatLipS_nonneg ha b r; positivity
  set K0 : ℝ := (2 * Real.pi * a)⁻¹ * Real.exp (b / 2 + r)
  have hK0 : 0 ≤ K0 := by positivity
  set g4 := QuantumZipper.gaussianAbsMoment 4
  have hg4 : 0 ≤ g4 := QuantumZipper.gaussianAbsMoment_nonneg 4
  have hmz := mzConst_nonneg
  set c : ℝ := g4 * mzConst ^ 2 * (L + K0) ^ 4
  have hc : 0 ≤ c := by positivity
  set Kn : ℕ → ℝ := fun n => c * ((n : ℝ) + 3) ^ 18 * Real.exp (-(n : ℝ)) ^ 4
  set l : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) / 2)
  set cR : ℝ := ((2 * R + 1) ^ 3 + (3 : ℕ) * (2 * R + 1) ^ 3 /
    (1 - (2 : ℝ) ^ 3 * ((1 / 2 : ℝ) ^ (4 : ℝ) / (7 / 8 : ℝ) ^ 4)))
  have hρ : (2 : ℝ) ^ 3 * ((1 / 2 : ℝ) ^ (4 : ℝ) / (7 / 8 : ℝ) ^ 4) < 1 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hcR : 0 ≤ cR := by
    have : 0 < 1 - (2 : ℝ) ^ 3 * ((1 / 2 : ℝ) ^ (4 : ℝ) / (7 / 8 : ℝ) ^ 4) := by linarith
    positivity
  -- box geometry for `R + 1`
  have hgeo : ∀ q ∈ QuantumZipper.KolmD.boxD (d := 3) (R + 1),
      Real.exp (sz3 q).1 ∈ Icc a b ∧ ‖(sz3 q).2‖ ≤ r := by
    intro q hq
    have h1 := exp_sz3_mem hq
    have h2 := norm_sz3_le hq
    push_cast at h1 h2
    exact ⟨h1, by simp only [hr]; linarith⟩
  have hbound : ∀ n : ℕ, P {ω | ∃ q ∈ QuantumZipper.KolmD.boxD (d := 3) R,
      (((3 : ℕ) : ℝ) / (1 - 7 / 8) + 1) * l n < |gaussDiff3 h n q ω|} ≤
      ENNReal.ofReal (Kn n / l n ^ 4 * cR) := by
    intro n
    have ht : (1 : ℝ) ≤ (n : ℝ) + 3 := by linarith [n.cast_nonneg (α := ℝ)]
    have hsupp : ∀ (s : ℝ) (z : ℂ) (w : ℂ), (n : ℝ) + 3 < ‖w‖ → heatDiff s z n w = 0 :=
      fun s z w hw => heatTrunc_succ_sub_eq_zero' s z n w hw.le
    have hmom : QuantumZipper.KolmG.MomentBoundG (fun q ω => gaussDiff3 h n q ω) P 4 4
        (Kn n) (R + 1) := by
      intro q hq q' hq'
      simp only
      simp_rw [gaussDiff3_sub]
      obtain ⟨hs, hz⟩ := hgeo q hq
      obtain ⟨hs', hz'⟩ := hgeo q' hq'
      have hd := dist_sz3_le hq hq'
      push_cast at hd
      have hB : ∀ w, |(heatDiff (Real.exp (sz3 q).1) (sz3 q).2 n -
          heatDiff (Real.exp (sz3 q').1) (sz3 q').2 n) w| ≤
          L * Real.exp (-(n : ℝ)) * ‖q - q'‖ := by
        intro w
        refine (abs_heatDiff_sub_sz_le ha hr0 hs hs' _ _ hz hz' n w).trans ?_
        have hLS := heatLipS_nonneg ha b r
        calc (heatLipZ a b r + heatLipS a b r) * Real.exp (-(n : ℝ)) *
              (|Real.exp (sz3 q).1 - Real.exp (sz3 q').1| + ‖(sz3 q).2 - (sz3 q').2‖)
            ≤ (heatLipZ a b r + heatLipS a b r) * Real.exp (-(n : ℝ)) *
              ((Real.exp ((R : ℝ) + 1) + 2) * ‖q - q'‖) := by gcongr
          _ = L * Real.exp (-(n : ℝ)) * ‖q - q'‖ := by simp only [L]; ring
      refine (hh.lintegral_pow_four_le _ (by positivity) ht hB (fun w hw => by
        show heatDiff _ _ n w - heatDiff _ _ n w = 0
        rw [hsupp _ _ w hw, hsupp _ _ w hw, sub_zero])).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      simp only [Kn, c]
      have hq0 := norm_nonneg (q - q')
      have hLK : L ^ 4 ≤ (L + K0) ^ 4 := pow_le_pow_left₀ hL (by linarith) 4
      calc g4 * mzConst ^ 2 * (L * Real.exp (-(n : ℝ)) * ‖q - q'‖) ^ 4 * ((n : ℝ) + 3) ^ 18
          = g4 * mzConst ^ 2 * L ^ 4 * ((n : ℝ) + 3) ^ 18 * Real.exp (-(n : ℝ)) ^ 4 *
              ‖q - q'‖ ^ 4 := by ring
        _ ≤ g4 * mzConst ^ 2 * (L + K0) ^ 4 * ((n : ℝ) + 3) ^ 18 *
              Real.exp (-(n : ℝ)) ^ 4 * ‖q - q'‖ ^ 4 := by gcongr
    have hpt : ∀ q ∈ QuantumZipper.KolmD.boxD (d := 3) R,
        ∫⁻ ω, ENNReal.ofReal (|gaussDiff3 h n q ω| ^ 4) ∂P ≤ ENNReal.ofReal (Kn n) := by
      intro q hq
      have hq1 : q ∈ QuantumZipper.KolmD.boxD (d := 3) (R + 1) := by
        intro i
        have : |q i| ≤ (R : ℝ) := hq i
        show |q i| ≤ ((R + 1 : ℕ) : ℝ)
        push_cast; linarith
      obtain ⟨hs, hz⟩ := hgeo q hq1
      have hs0 : 0 < Real.exp (sz3 q).1 := Real.exp_pos _
      have hpw : ∀ w, |heatDiff (Real.exp (sz3 q).1) (sz3 q).2 n w| ≤ K0 * Real.exp (-(n : ℝ)) := by
        intro w
        refine (abs_heatTrunc_succ_sub_le _ hs0 _ r hz n w).trans ?_
        have h1 : (2 * Real.pi * Real.exp (sz3 q).1)⁻¹ ≤ (2 * Real.pi * a)⁻¹ :=
          inv_anti₀ (by positivity) (by nlinarith [Real.pi_pos, hs.1])
        have h2 : Real.exp (Real.exp (sz3 q).1 / 2 + r) ≤ Real.exp (b / 2 + r) :=
          Real.exp_le_exp.2 (by linarith [hs.2])
        exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by positivity))
          (by positivity)
      refine (hh.lintegral_pow_four_le _ (by positivity) ht hpw (hsupp _ _)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      simp only [Kn, c]
      have hLK : K0 ^ 4 ≤ (L + K0) ^ 4 := pow_le_pow_left₀ hK0 (by linarith) 4
      calc g4 * mzConst ^ 2 * (K0 * Real.exp (-(n : ℝ))) ^ 4 * ((n : ℝ) + 3) ^ 18
          = g4 * mzConst ^ 2 * K0 ^ 4 * ((n : ℝ) + 3) ^ 18 * Real.exp (-(n : ℝ)) ^ 4 := by ring
        _ ≤ _ := by gcongr
    exact QuantumZipper.Thm18Asm.G1FM.kolm_sup_tail_N (θ := 7 / 8) (by norm_num) (by norm_num)
      (fun ω => continuous_gaussDiff3 n ω)
      (fun q => (measurable_gaussDiff3 hh n q).aemeasurable) (by norm_num)
      (by positivity) hρ hmom hpt (Real.exp_pos _)
  -- summability of the bounds
  have hKl : ∀ n : ℕ, 0 ≤ Kn n / l n ^ 4 * cR := fun n =>
    mul_nonneg (div_nonneg (by simp only [Kn]; positivity) (by simp only [l]; positivity)) hcR
  have hsum : Summable fun n : ℕ => Kn n / l n ^ 4 * cR := summable_kolm3 c cR hc hcR
  have hBC : ∑' n, P {ω | ∃ q ∈ QuantumZipper.KolmD.boxD (d := 3) R,
      (((3 : ℕ) : ℝ) / (1 - 7 / 8) + 1) * l n < |gaussDiff3 h n q ω|} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg hKl hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hBC] with ω hω
  filter_upwards [hω] with n hn q hq
  simp only [mem_setOf_eq, not_exists, not_and, not_lt] at hn
  have := hn q hq
  norm_num at this
  simpa [l] using this

end LQGMetric.DFGPS
