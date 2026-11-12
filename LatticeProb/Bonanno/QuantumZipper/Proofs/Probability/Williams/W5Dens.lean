/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W5Dens at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Kill

/-!
W5(i), reversed side, of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1): the occupation measure of
`X + c` killed at `T_c` (`X = dpath σ (-μ) b`, `T_c` its hitting time of `-c`) has density
`C · χ_c` (`C = occDens σ μ 0`, `χ_c = chiKill`):

`E ∫_{0 < m ≤ T_c} Φ(X_m + c) dm = C ∫ Φ(z) χ_c(z) dz`

for measurable `Φ ≥ 0` vanishing on `(-∞, 0]` with `∫ Φ < ∞` (`lintegral_killed_occ`).

Route (blueprint sketch): the strong Markov split `lintegral_occ_split` at `T_c` gives
`ν^X(· - c) = ν_kill + ν^X` (no subtraction), the occupation measure of `X` is the reflection of
that of `Y` (`lintegral_occ_neg_drift`, symmetry of the Gaussian law) with density
`occDens σ μ (-·)`, and `chiKill_toReal_mul` identifies the difference of densities. The
finiteness hypothesis makes the cancellation legitimate; `occDens σ μ (-z) ≤ C` for `z > 0`.

Sources: Revuz–Yor, *Continuous Martingales and Brownian Motion*, VII §3; D. Williams (1974).
Bookkeeping own.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- The negated Brownian motion is again good. -/
theorem GoodBM.neg (hb : GoodBM b P) : GoodBM (fun t ω => -b t ω) P where
  pre := hb.pre.neg
  meas t := (hb.meas t).neg
  cont ω := (hb.cont ω).neg
  zero ω := by simp [hb.zero ω]

/-- The down-drift process hits every negative level almost surely. -/
theorem ae_exists_eq_neg_level (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) {c : ℝ}
    (hc : 0 < c) : ∀ᵐ ω ∂P, ∃ t : ℝ≥0, dpath σ (-μ) b ω t = -c := by
  filter_upwards [ae_exists_eq_level hb.neg hσ hμ hc] with ω ⟨t, ht⟩
  refine ⟨t, ?_⟩
  simp only [dpath] at ht ⊢
  linarith

/-- The occupation measure of the down-drift process is the reflection of the up-drift one. -/
theorem lintegral_occ_neg_drift (σ μ : ℝ) {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ x, Φ x ∂(occ σ (-μ)) = ∫⁻ x, Φ (-x) ∂(occ σ μ) := by
  rw [occ, occ, Measure.lintegral_bind (measurable_occKernel σ (-μ)).aemeasurable
      hΦ.aemeasurable,
    Measure.lintegral_bind (f := fun x => Φ (-x)) (measurable_occKernel σ μ).aemeasurable
      (hΦ.comp measurable_neg).aemeasurable]
  refine lintegral_congr fun m => ?_
  rw [neg_mul, ← gaussianReal_map_neg, lintegral_map hΦ measurable_neg]

/-- `∫ Φ d occ^X = ∫ Φ(z) occDens σ μ (-z) dz`. -/
theorem lintegral_occ_neg_drift_dens (hσ : 0 < σ) (hμ : 0 < μ) {Φ : ℝ → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    ∫⁻ x, Φ x ∂(occ σ (-μ)) = ∫⁻ z, Φ z * ENNReal.ofReal (occDens σ μ (-z)) := by
  have hd : Measurable fun y => ENNReal.ofReal (occDens σ μ y) :=
    ENNReal.measurable_ofReal.comp (continuous_occDens hσ hμ).measurable
  rw [lintegral_occ_neg_drift σ μ hΦ, occ_eq hσ hμ,
    lintegral_withDensity_eq_lintegral_mul _ hd (g := fun x => Φ (-x)) (hΦ.comp measurable_neg)]
  rw [← lintegral_neg_eq_self]
  refine lintegral_congr fun z => ?_
  simp only [Pi.mul_apply, neg_neg]
  rw [mul_comm]

theorem occDens_neg_le (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) (y : ℝ) :
    occDens σ μ y ≤ occDens σ μ 0 := by
  rcases lt_or_ge y 0 with hy | hy
  · haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
    obtain ⟨hC, hP⟩ := prob_hit_neg hb hσ hμ hy
    have h1 : P.real {ω | ∃ t, dpath σ μ b ω t = y} ≤ 1 := measureReal_le_one
    rw [hP, div_le_one hC] at h1
    exact h1
  · rw [occDens_nonneg_const hσ hμ y hy]

/-- **The killed occupation density** (blueprint W5(i), reversed side). -/
theorem lintegral_killed_occ (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) {c : ℝ} (hc : 0 < c)
    {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) (hΦ0 : ∀ z ≤ 0, Φ z = 0) (hfin : ∫⁻ z, Φ z ≠ ∞) :
    ∫⁻ ω, (∫⁻ m in Ioi (0 : ℝ),
        {m : ℝ | m.toNNReal ≤ hitLevel (dpath σ (-μ) b ω) (-c)}.indicator
          (fun m => Φ (dpath σ (-μ) b ω m.toNNReal + c)) m) ∂P
      = ENNReal.ofReal (occDens σ μ 0) * ∫⁻ z, Φ z * chiKill b P σ μ c z := by
  set C := occDens σ μ 0 with hCdef
  have hd : Measurable fun y => ENNReal.ofReal (occDens σ μ y) :=
    ENNReal.measurable_ofReal.comp (continuous_occDens hσ hμ).measurable
  have hsplit := lintegral_occ_split hb σ (-μ) (-c) (ae_exists_eq_neg_level hb hσ hμ hc)
    (Φ := fun x => Φ (x + c)) (hΦ.comp (measurable_id.add_const c))
  simp only [neg_add_cancel_right] at hsplit
  -- the three occupation integrals in density form
  set I2 := ∫⁻ z, Φ z * ENNReal.ofReal (occDens σ μ (-z)) with hI2
  have hI1 : ∫⁻ x, Φ (x + c) ∂(occ σ (-μ))
      = ∫⁻ z, Φ z * ENNReal.ofReal (occDens σ μ (c - z)) := by
    rw [lintegral_occ_neg_drift_dens hσ hμ (Φ := fun x => Φ (x + c)) (hΦ.comp (measurable_add_const c)),
      ← lintegral_add_right_eq_self _ (-c)]
    refine lintegral_congr fun z => ?_
    simp only [neg_add_cancel_right]
    congr 3
    ring
  rw [hI1, lintegral_occ_neg_drift_dens hσ hμ hΦ, ← hI2] at hsplit
  have hI2fin : I2 ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top
      (b := ENNReal.ofReal C)) ?_
    rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun z => by gcongr; exact occDens_neg_le hb hσ hμ _
  -- the density identity, almost everywhere
  have hne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ c := by
    rw [ae_iff]
    simp
  have hdens : ∫⁻ z, Φ z * ENNReal.ofReal (occDens σ μ (c - z))
      = (∫⁻ z, ENNReal.ofReal C * (Φ z * chiKill b P σ μ c z)) + I2 := by
    rw [hI2, ← lintegral_add_right _ (show Measurable fun z => Φ z * ENNReal.ofReal (occDens σ μ (-z)) from hΦ.mul (hd.comp measurable_neg))]
    refine lintegral_congr_ae ?_
    filter_upwards [hne] with z hz
    rcases le_or_gt z 0 with hz0 | hz0
    · simp [hΦ0 z hz0]
    · have hχ := chiKill_toReal_mul hb hσ hμ hc hz0 hz
      have hχfin : chiKill b P σ μ c z ≠ ∞ := by
        haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
        exact measure_ne_top _ _
      have hdz : occDens σ μ (c - z) = (chiKill b P σ μ c z).toReal * C + occDens σ μ (-z) := by
        rw [hχ]; ring
      rw [hdz, ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg (occDens_nonneg σ μ 0))
        (occDens_nonneg σ μ _),
        ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hχfin]
      ring
  rw [hdens] at hsplit
  have h := (ENNReal.add_left_inj hI2fin).1 hsplit
  rw [← h, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end QuantumZipper.Williams
