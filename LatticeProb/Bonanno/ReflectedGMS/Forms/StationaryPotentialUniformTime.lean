/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StationaryPotentialUniformTime at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryPotentialMaximal
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicSupportDensity

/-!
# Uniform-time envelopes from nested stationary grids

This file isolates the measure-theoretic passage from uniformly bounded finite
dyadic maxima to an integrable all-time envelope.  Right continuity is an
explicit input: the result does not supply regularity of a full-energy
potential.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace ReflectedGMS

/-- The largest centered absolute value on the level-`n` dyadic grid of
`[0,T]`, including both endpoints. -/
noncomputable def dyadicCenteredAbsMax
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => |Y (dyadicTime T n k) ω - Y 0 ω|)

theorem measurable_dyadicCenteredAbsMax
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {Y : ℝ≥0 → Ω → ℝ}
    (hY : ∀ t, Measurable (Y t)) (T : ℝ≥0) (n : ℕ) :
    Measurable (dyadicCenteredAbsMax Y T n) := by
  change Measurable (fun ω =>
    (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => |Y (dyadicTime T n k) ω - Y 0 ω|))
  apply measurable_range_sup''
  intro k hk
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    ((hY (dyadicTime T n k)).sub (hY 0)).norm

theorem dyadicCenteredAbsMax_nonneg
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    0 ≤ dyadicCenteredAbsMax Y T n ω := by
  have h := Finset.le_sup'
    (fun k => |Y (dyadicTime T n k) ω - Y 0 ω|)
    (Finset.mem_range.mpr (Nat.zero_lt_succ (2 ^ n)))
  simpa only [dyadicCenteredAbsMax, dyadicTime, Nat.cast_zero, zero_mul,
    zero_div, sub_self, abs_zero] using h

theorem monotone_dyadicCenteredAbsMax
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    Monotone (fun n => dyadicCenteredAbsMax Y T n ω) := by
  intro n N hnN
  apply (Finset.sup'_le_iff Finset.nonempty_range_add_one _).2
  intro k hk
  have hkpow : k ≤ 2 ^ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  let j := k * 2 ^ (N - n)
  have hjpow : j ≤ 2 ^ N := by
    dsimp only [j]
    calc
      k * 2 ^ (N - n) ≤ 2 ^ n * 2 ^ (N - n) :=
        Nat.mul_le_mul_right _ hkpow
      _ = 2 ^ N := by rw [← pow_add, Nat.add_sub_of_le hnN]
  have hjmem : j ∈ Finset.range (2 ^ N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hjpow)
  have hrefine : dyadicTime T N j = dyadicTime T n k := by
    exact dyadicTime_refine_to T hnN
  rw [← hrefine]
  exact Finset.le_sup' (fun i => |Y (dyadicTime T N i) ω - Y 0 ω|) hjmem

/-- Uniform square-integral bounds on nested dyadic grids produce a measurable
integrable envelope for every time in `[0,T]`.  The endpoint `T` is retained
explicitly; values before `T` are recovered from the right by density.

The right-continuity premise is deliberately separate from the finite-grid
estimate, so applying this theorem to the actual full-energy potential does not
assert unproved harmonic regularity. -/
theorem exists_integrable_sq_envelope_of_dyadic_grids
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hY : ∀ t, Measurable (Y t))
    (hgridInt : ∀ n, Integrable
      (fun ω => (dyadicCenteredAbsMax Y T n ω) ^ 2) P)
    (C : ℝ) (hgrid : ∀ n,
      (∫ ω, (dyadicCenteredAbsMax Y T n ω) ^ 2 ∂P) ≤ C)
    (hRC : ∀ᵐ ω ∂P, IsRightContinuous (fun t => Y t ω)) :
    ∃ D : Ω → ℝ, Measurable D ∧ Integrable D P ∧
      (∀ᵐ ω ∂P, ∀ t ≤ T, (Y t ω - Y 0 ω) ^ 2 ≤ D ω) ∧
      (∫ ω, D ω ∂P) ≤ C := by
  let A : ℕ → Ω → ℝ := fun n => dyadicCenteredAbsMax Y T n
  let U : Ω → ℝ≥0∞ := fun ω => ⨆ n, ENNReal.ofReal ((A n ω) ^ 2)
  have hAm (n : ℕ) : Measurable (A n) :=
    measurable_dyadicCenteredAbsMax hY T n
  have hA0 (n : ℕ) (ω : Ω) : 0 ≤ A n ω :=
    dyadicCenteredAbsMax_nonneg Y T n ω
  have hAmono : Monotone A := fun _ _ h ω =>
    monotone_dyadicCenteredAbsMax Y T ω h
  have hUm : Measurable U :=
    Measurable.iSup fun n => (hAm n).pow_const 2 |>.ennreal_ofReal
  have hUbound : (∫⁻ ω, U ω ∂P) ≤ ENNReal.ofReal C := by
    have hmono : Monotone (fun n ω => ENNReal.ofReal ((A n ω) ^ 2)) := by
      intro i j hij ω
      apply ENNReal.ofReal_le_ofReal
      exact (sq_le_sq₀ (hA0 i ω) (hA0 j ω)).2 (hAmono hij ω)
    rw [show (∫⁻ ω, U ω ∂P) =
        ⨆ n, ∫⁻ ω, ENNReal.ofReal ((A n ω) ^ 2) ∂P by
      exact lintegral_iSup
        (fun n => (hAm n).pow_const 2 |>.ennreal_ofReal) hmono]
    apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hgridInt n)
      (Eventually.of_forall fun ω => sq_nonneg (A n ω))]
    exact ENNReal.ofReal_le_ofReal (hgrid n)
  have hUaefin : ∀ᵐ ω ∂P, U ω < ∞ :=
    ae_lt_top hUm (ne_of_lt (hUbound.trans_lt ENNReal.ofReal_lt_top))
  let D : Ω → ℝ := fun ω => (U ω).toReal
  have hDm : Measurable D := hUm.ennreal_toReal
  have hDU : ∀ᵐ ω ∂P, ENNReal.ofReal (D ω) = U ω := by
    filter_upwards [hUaefin] with ω hω
    exact ENNReal.ofReal_toReal hω.ne
  have hDint : Integrable D P := by
    refine ⟨hDm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have henorm : (fun ω => ‖D ω‖ₑ) =ᵐ[P] U := by
      filter_upwards [hDU] with ω hω
      rw [← hω, ← ofReal_norm_eq_enorm,
        Real.norm_of_nonneg ENNReal.toReal_nonneg]
    rw [lintegral_congr_ae henorm]
    exact hUbound.trans_lt ENNReal.ofReal_lt_top
  have hgridDom : ∀ᵐ ω ∂P, ∀ n k, k ≤ 2 ^ n →
      (Y (dyadicTime T n k) ω - Y 0 ω) ^ 2 ≤ D ω := by
    filter_upwards [hUaefin] with ω hω
    intro n k hk
    have hkA : |Y (dyadicTime T n k) ω - Y 0 ω| ≤ A n ω := by
      exact Finset.le_sup' (fun i => |Y (dyadicTime T n i) ω - Y 0 ω|)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    have hsquare : (Y (dyadicTime T n k) ω - Y 0 ω) ^ 2 ≤ (A n ω) ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (hA0 n ω)).2 hkA
    have hU : ENNReal.ofReal ((Y (dyadicTime T n k) ω - Y 0 ω) ^ 2) ≤ U ω :=
      (ENNReal.ofReal_le_ofReal hsquare).trans (le_iSup (fun i =>
        ENNReal.ofReal ((A i ω) ^ 2)) n)
    have hr := ENNReal.toReal_mono hω.ne hU
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _), D] using hr
  refine ⟨D, hDm, hDint, ?_, ?_⟩
  · filter_upwards [hRC, hgridDom] with ω hω hdom
    intro t htT
    rcases eq_or_lt_of_le htT with heq | htT
    · rw [heq]
      have hend : dyadicTime T 0 1 = T := by simp [dyadicTime]
      simpa only [hend] using hdom 0 1 (by simp)
    · letI : (𝓝[dyadicSupport T ∩ Ioi t] t).NeBot :=
        dyadicSupport_nhdsWithin_Ioi_neBot T (t := t)
          (lt_of_le_of_lt zero_le htT) htT
      have hlim : Tendsto (fun r => (Y r ω - Y 0 ω) ^ 2)
          (𝓝[dyadicSupport T ∩ Ioi t] t) (𝓝 ((Y t ω - Y 0 ω) ^ 2)) :=
        (((hω t).mono inter_subset_right).sub continuousWithinAt_const).pow 2
      apply le_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin] with r hr
      obtain ⟨n, k, hk, rfl⟩ := hr.1
      exact hdom n k hk.le
  · have hC0 : 0 ≤ C :=
      (integral_nonneg_of_ae (Eventually.of_forall fun ω =>
        sq_nonneg (dyadicCenteredAbsMax Y T 0 ω))).trans (hgrid 0)
    rw [← ENNReal.ofReal_le_ofReal_iff hC0]
    rw [ofReal_integral_eq_lintegral_ofReal hDint
      (Eventually.of_forall fun ω => ENNReal.toReal_nonneg)]
    rw [lintegral_congr_ae hDU]
    exact hUbound

end ReflectedGMS
