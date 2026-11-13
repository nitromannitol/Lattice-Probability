/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Field.LogCov at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Field.Measures
import LatticeProb.Bonanno.HigherDimLFPP.Field.Exists
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral

/-!
# The log covariance (3.2), its positivity, and cutoff domination (3.3) (packet P-F2, target T2)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §3.1, (3.2) and (3.3); planning audit HA2
(`planning/audits/HA2-section-3.md`), finding HA2-03, Details D3 (Steps 0–5) and D4, and the Lean
block (c) (`LogPairable`, `logCov`, `Eq32`, `Eq33`).

For finite measures `μ, ν, μ', ν'` on `ℝ^d` with `μ(ℝ^d) = ν(ℝ^d)`, `μ'(ℝ^d) = ν'(ℝ^d)`, no atoms
and finite logarithmic energy (`LogPairable`), the all-scale pairings are well defined and
`Cov(⟨h, μ - ν⟩, ⟨h, μ' - ν'⟩) = ∫∫ log|z - w|⁻¹ (μ - ν)(dz) (μ' - ν')(dw)`
(`scaleCov_eq_logCov`).  The proof is HA2 D3:

* Step 0: the radial profile `c(s) = C(s e)` of `C = autoCorr κ` (`corrProfile`) is continuous,
  `c(0) = 1`, `|c| ≤ 1`, `c = 0` on `[R, ∞)`, and Lipschitz (`IsProfile`, `exists_isProfile`);
* Step 2: with equal masses, `scalePair κ t = ∫∫ φ(|z - w|, t)` with the Frullani integrand
  `φ(ρ, t) = (c(ρ/t) - c(1/t))/t` (`frInt`, `scalePair_eq_mixInt_frInt`);
* Step 3: `∫₀^∞ |φ(ρ, t)| dt ≤ 2|log ρ| + 2 log R + L` (`IsProfile.integral_abs_frInt_le`);
* Step 4: Mathlib's `Frullani.integral_Ioi_eq` gives `∫₀^∞ φ(ρ, t) dt = -log ρ`
  (`IsProfile.integral_frInt`);
* Step 5: Tonelli/Fubini on `(0, ∞) × (ℝ^d)²` (`IsProfile.frInt_fubini`), using that the diagonal
  is null for atomless measures (`FieldAux.ae_ne_of_nullSingletonClass`).

Consequences: `sum_mul_logCov_nonneg`, `psdOn_logCov` (positive semidefiniteness on finite
families of mass-zero log-pairable pairs, independent of `κ`) and the cutoff domination
`scaleCov_le_logCov` ((3.3): `Var⟨H_S, η⟩ ≤ ∫∫ log|z - w|⁻¹ η(dz) η(dw)` for every scale set
`S ⊆ (0, ∞)`), together with its general form `cutoff_domination` (HA2's `Eq33`).

2D template: `LQGDimension/LFPP/HeatKernel.lean` (`frIntegrand`, `heatRep_of_integrable_log`,
`logCovHeatRep`), with the Gaussian heat kernel replaced by a general compactly supported Lipschitz
profile, and finite segment combinations replaced by finite measures on `ℝ^d`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

variable {d : ℕ}

/-! ### Definitions -/

/-- Domain of the log-kernel formula (3.2): no atoms (Lean's `log 0 = 0` would otherwise hide the
diagonal) and finite absolute logarithmic energy of the total mass (HA2's `LogPairable`). -/
def LogPairable (μ ν μ' ν' : Measure (Rd d)) : Prop :=
  NullSingletonClass μ ∧ NullSingletonClass ν ∧ NullSingletonClass μ' ∧ NullSingletonClass ν' ∧
    Integrable (fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖)
      ((μ + ν + μ' + ν').prod (μ + ν + μ' + ν'))

/-- `∫∫ log|z - w|⁻¹ (μ - ν)(dz) (μ' - ν')(dw)`, expanded (HA2's `logCov`). -/
def logCov (μ ν μ' ν' : Measure (Rd d)) : ℝ :=
  (∫ p, -Real.log ‖p.1 - p.2‖ ∂(μ.prod μ')) - (∫ p, -Real.log ‖p.1 - p.2‖ ∂(μ.prod ν'))
    - (∫ p, -Real.log ‖p.1 - p.2‖ ∂(ν.prod μ')) + (∫ p, -Real.log ‖p.1 - p.2‖ ∂(ν.prod ν'))

/-! ### Frullani's integral for a general profile (HA2 D3, Steps 3–5) -/

/-- The Frullani integrand `φ(ρ, t) = (c(ρ/t) - c(1/t))/t` of HA2 D3, Step 2. -/
def frInt (c : ℝ → ℝ) (ρ t : ℝ) : ℝ := (c (ρ / t) - c (1 / t)) / t

/-- Standing assumptions on a profile `c`: continuous, `c(0) = 1`, `|c| ≤ 1`, `c = 0` on
`[R, ∞)` with `R ≥ 1`, and `L`-Lipschitz. -/
structure IsProfile (c : ℝ → ℝ) (R L : ℝ) : Prop where
  continuous : Continuous c
  zero : c 0 = 1
  abs_le : ∀ s, |c s| ≤ 1
  one_le : 1 ≤ R
  eq_zero : ∀ s, R ≤ s → c s = 0
  nonneg : 0 ≤ L
  lip : ∀ s s', |c s - c s'| ≤ L * |s - s'|

namespace IsProfile

variable {c : ℝ → ℝ} {R L : ℝ}
/-- The majorant of `|φ(ρ, ·)|` on `(0, ∞)`: `2/t` on `[min(ρ,1)/R, max(ρ,1)]`, and
`L max(ρ,1)/t²` above. -/
def maj (R L ρ : ℝ) (t : ℝ) : ℝ :=
  (Icc (min ρ 1 / R) (max ρ 1)).indicator (fun t => 2 * t⁻¹) t +
    (Ioi (max ρ 1)).indicator (fun t => L * max ρ 1 * t ^ (-2 : ℝ)) t

theorem abs_frInt_le_maj (hc : IsProfile c R L) {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    |frInt c ρ t| ≤ maj R L ρ t := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hc.one_le
  have hm0 : 0 < min ρ 1 := lt_min hρ one_pos
  have hM1 : 1 ≤ max ρ 1 := le_max_right ρ 1
  have hn1 : 0 ≤ (Icc (min ρ 1 / R) (max ρ 1)).indicator (fun t => 2 * t⁻¹) t :=
    indicator_nonneg (fun s hs => by
      have : 0 < s := lt_of_lt_of_le (div_pos hm0 hR0) hs.1
      positivity) t
  have hn2 : 0 ≤ (Ioi (max ρ 1)).indicator (fun t => L * max ρ 1 * t ^ (-2 : ℝ)) t :=
    indicator_nonneg (fun s hs => by
      have : 0 < s := lt_of_lt_of_le one_pos (hM1.trans (le_of_lt hs))
      have := hc.nonneg
      positivity) t
  rcases lt_or_ge t (min ρ 1 / R) with h1 | h1
  · -- both profile values vanish
    have htR : t * R < min ρ 1 := by rwa [lt_div_iff₀ hR0] at h1
    have hA : R ≤ ρ / t := by
      rw [le_div_iff₀ ht]
      linarith [min_le_left ρ 1, mul_comm t R]
    have hB : R ≤ 1 / t := by
      rw [le_div_iff₀ ht]
      linarith [min_le_right ρ 1, mul_comm t R]
    rw [frInt, hc.eq_zero _ hA, hc.eq_zero _ hB, sub_self, zero_div, abs_zero]
    exact add_nonneg hn1 hn2
  · rcases le_or_gt t (max ρ 1) with h2 | h2
    · have hmem : t ∈ Icc (min ρ 1 / R) (max ρ 1) := ⟨h1, h2⟩
      have hb : |frInt c ρ t| ≤ 2 * t⁻¹ := by
        rw [frInt, abs_div, abs_of_pos ht, div_eq_mul_inv]
        have : |c (ρ / t) - c (1 / t)| ≤ 2 := by
          have h3 := hc.abs_le (ρ / t)
          have h4 := hc.abs_le (1 / t)
          calc |c (ρ / t) - c (1 / t)| ≤ |c (ρ / t)| + |c (1 / t)| := abs_sub _ _
            _ ≤ 2 := by linarith
        exact mul_le_mul_of_nonneg_right this (inv_nonneg.2 ht.le)
      calc |frInt c ρ t| ≤ 2 * t⁻¹ := hb
        _ = (Icc (min ρ 1 / R) (max ρ 1)).indicator (fun t => 2 * t⁻¹) t := by
          rw [indicator_of_mem hmem]
        _ ≤ maj R L ρ t := le_add_of_nonneg_right hn2
    · have hb : |frInt c ρ t| ≤ L * max ρ 1 * t ^ (-2 : ℝ) := by
        have h2' : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.le, Real.rpow_natCast]
        rw [frInt, abs_div, abs_of_pos ht, h2']
        have hl := hc.lip (ρ / t) (1 / t)
        have hd : |ρ / t - 1 / t| ≤ max ρ 1 / t := by
          rw [← sub_div, abs_div, abs_of_pos ht]
          refine div_le_div_of_nonneg_right ?_ ht.le
          rw [_root_.abs_le]
          constructor
          · linarith [le_max_right ρ 1]
          · linarith [le_max_left ρ 1]
        calc |c (ρ / t) - c (1 / t)| / t ≤ L * (max ρ 1 / t) / t :=
              div_le_div_of_nonneg_right (hl.trans (mul_le_mul_of_nonneg_left hd hc.nonneg)) ht.le
          _ = L * max ρ 1 * (t ^ 2)⁻¹ := by field_simp
      calc |frInt c ρ t| ≤ L * max ρ 1 * t ^ (-2 : ℝ) := hb
        _ = (Ioi (max ρ 1)).indicator (fun t => L * max ρ 1 * t ^ (-2 : ℝ)) t := by
          rw [indicator_of_mem (show t ∈ Ioi (max ρ 1) from h2)]
        _ ≤ maj R L ρ t := le_add_of_nonneg_left hn1

theorem integrableOn_maj (hc : IsProfile c R L) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (maj R L ρ) (Ioi 0) := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hc.one_le
  have ha : 0 < min ρ 1 / R := div_pos (lt_min hρ one_pos) hR0
  have hM : 0 < max ρ 1 := lt_of_lt_of_le one_pos (le_max_right ρ 1)
  refine Integrable.add ?_ ?_
  · refine (integrable_indicator_iff measurableSet_Icc).2 ?_ |>.integrableOn
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_const.mul (continuousOn_inv₀.mono fun s hs => (lt_of_lt_of_le ha hs.1).ne')
  · refine (integrable_indicator_iff measurableSet_Ioi).2 ?_ |>.integrableOn
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hM).const_mul _

theorem integral_maj (hc : IsProfile c R L) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ t in Ioi 0, maj R L ρ t = 2 * |Real.log ρ| + (2 * Real.log R + L) := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hc.one_le
  have hm0 : 0 < min ρ 1 := lt_min hρ one_pos
  have ha : 0 < min ρ 1 / R := div_pos hm0 hR0
  have hM : 0 < max ρ 1 := lt_of_lt_of_le one_pos (le_max_right ρ 1)
  have hab : min ρ 1 / R ≤ max ρ 1 := by
    calc min ρ 1 / R ≤ min ρ 1 := div_le_self hm0.le hc.one_le
      _ ≤ max ρ 1 := min_le_max
  have i1 : IntegrableOn (fun t => 2 * t⁻¹) (Icc (min ρ 1 / R) (max ρ 1)) :=
    ContinuousOn.integrableOn_Icc
      (continuousOn_const.mul (continuousOn_inv₀.mono fun s hs => (lt_of_lt_of_le ha hs.1).ne'))
  have i2 : IntegrableOn (fun t => L * max ρ 1 * t ^ (-2 : ℝ)) (Ioi (max ρ 1)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hM).const_mul _
  have hI1 : Ioi (0 : ℝ) ∩ Icc (min ρ 1 / R) (max ρ 1) = Icc (min ρ 1 / R) (max ρ 1) :=
    inter_eq_right.2 fun s hs => lt_of_lt_of_le ha hs.1
  have hI2 : Ioi (0 : ℝ) ∩ Ioi (max ρ 1) = Ioi (max ρ 1) :=
    inter_eq_right.2 fun s (hs : max ρ 1 < s) => lt_trans hM hs
  unfold maj
  rw [integral_add ((integrable_indicator_iff measurableSet_Icc).2 i1).integrableOn
      ((integrable_indicator_iff measurableSet_Ioi).2 i2).integrableOn,
    setIntegral_indicator measurableSet_Icc, setIntegral_indicator measurableSet_Ioi, hI1, hI2,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_const_mul, integral_inv_of_pos ha hM, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hM]
  have hlogM : Real.log (max ρ 1 / (min ρ 1 / R)) = |Real.log ρ| + Real.log R := by
    rw [div_div_eq_mul_div, Real.log_div (mul_pos hM hR0).ne' hm0.ne',
      Real.log_mul hM.ne' hR0.ne']
    rcases le_total ρ 1 with h | h
    · rw [max_eq_right h, min_eq_left h, Real.log_one, abs_of_nonpos (Real.log_nonpos hρ.le h)]
      ring
    · rw [max_eq_left h, min_eq_right h, Real.log_one, abs_of_nonneg (Real.log_nonneg h)]
      ring
  have hpow : -max ρ 1 ^ ((-2 : ℝ) + 1) / ((-2 : ℝ) + 1) = (max ρ 1)⁻¹ := by
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    ring
  rw [hlogM, hpow]
  field_simp
  ring

/-- **HA2 D3, Step 3**: `φ(ρ, ·)` is integrable on `(0, ∞)` for `ρ > 0`. -/
theorem integrableOn_frInt (hc : IsProfile c R L) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (frInt c ρ) (Ioi 0) := by
  refine (hc.integrableOn_maj hρ).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hne : ∀ t ∈ Ioi (0 : ℝ), t ≠ 0 := fun t ht => (ne_of_lt ht).symm
    refine ContinuousOn.div ?_ continuousOn_id hne
    exact (hc.continuous.comp_continuousOn (continuousOn_const.div continuousOn_id hne)).sub
      (hc.continuous.comp_continuousOn (continuousOn_const.div continuousOn_id hne))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs]
    exact hc.abs_frInt_le_maj hρ ht

/-- **HA2 D3, Step 3**: `∫₀^∞ |φ(ρ, t)| dt ≤ 2|log ρ| + 2 log R + L`. -/
theorem integral_abs_frInt_le (hc : IsProfile c R L) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ t in Ioi 0, |frInt c ρ t| ≤ 2 * |Real.log ρ| + (2 * Real.log R + L) := by
  rw [← hc.integral_maj hρ]
  refine setIntegral_mono_on (hc.integrableOn_frInt hρ).abs (hc.integrableOn_maj hρ)
    measurableSet_Ioi fun t ht => hc.abs_frInt_le_maj hρ ht

/-- **HA2 D3, Step 4 (Frullani)**: `∫₀^∞ (c(ρ/t) - c(1/t)) dt/t = -log ρ` for `ρ > 0`. -/
theorem integral_frInt (hc : IsProfile c R L) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ t in Ioi 0, frInt c ρ t = -Real.log ρ := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hc.one_le
  set f : ℝ → ℝ := fun x => c x⁻¹ with hf
  have hfun : (fun x : ℝ => x⁻¹ • (f (ρ⁻¹ * x) - f (1 * x))) = frInt c ρ := by
    funext x
    simp only [hf, smul_eq_mul, one_mul, frInt, mul_inv, inv_inv]
    rw [div_eq_inv_mul, div_eq_mul_inv ρ x, one_div]
  have hloc : LocallyIntegrableOn f (Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    exact hc.continuous.comp_continuousOn (continuousOn_inv₀.mono fun x hx => (ne_of_lt hx).symm)
  have hL : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (inv_pos.2 hR0)] with x hx
    have hx0 : 0 < x := hx.1
    have : R ≤ x⁻¹ := by
      rw [le_inv_comm₀ hR0 hx0]
      exact hx.2.le
    exact (hc.eq_zero _ this).symm
  have hR : Tendsto f atTop (𝓝 1) := by
    have h := (hc.continuous.tendsto 0).comp tendsto_inv_atTop_zero
    rwa [hc.zero] at h
  have h := Frullani.integral_Ioi_eq hloc (inv_pos.2 hρ) one_pos hL hR
    (by rw [hfun]; exact hc.integrableOn_frInt hρ)
  rw [hfun] at h
  rw [h, one_div, inv_inv, smul_eq_mul, zero_sub, mul_neg_one]

/-- **HA2 D3, Step 5 (abstract Fubini)**: on a finite measure space, if `D > 0` a.e. and
`log D` is integrable, then `t ↦ ∫ φ(D x, t) dπ(x)` is integrable on `(0, ∞)` with integral
`-∫ log D dπ`.  (Generalizes `LQGDimension.HeatKernel.heatRep_of_integrable_log` from the heat
kernel to a general profile.) -/
theorem frInt_fubini (hc : IsProfile c R L) {X : Type*} [MeasurableSpace X] (π : Measure X)
    [IsFiniteMeasure π] {D : X → ℝ} (hD : Measurable D) (hpos : ∀ᵐ x ∂π, 0 < D x)
    (hlog : Integrable (fun x => Real.log (D x)) π) :
    IntegrableOn (fun t => ∫ x, frInt c (D x) t ∂π) (Ioi 0) ∧
      ∫ t in Ioi 0, ∫ x, frInt c (D x) t ∂π = -∫ x, Real.log (D x) ∂π := by
  have hcm := hc.continuous.measurable
  have hFm : Measurable fun q : ℝ × X => frInt c (D q.2) q.1 := by
    unfold frInt
    exact ((hcm.comp ((hD.comp measurable_snd).div measurable_fst)).sub
      (hcm.comp (measurable_const.div measurable_fst))).div measurable_fst
  have hFi : Integrable (fun q : ℝ × X => frInt c (D q.2) q.1)
      ((volume.restrict (Ioi 0)).prod π) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    constructor
    · filter_upwards [hpos] with x hx
      exact hc.integrableOn_frInt hx
    · refine Integrable.mono' ((hlog.abs.const_mul 2).add
        (integrable_const (2 * Real.log R + L))) ?_ ?_
      · exact (StronglyMeasurable.integral_prod_left (μ := volume.restrict (Ioi 0))
          (f := fun t x => ‖frInt c (D x) t‖) hFm.norm.stronglyMeasurable).aestronglyMeasurable
      · filter_upwards [hpos] with x hx
        rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
        simp only [Real.norm_eq_abs]
        exact hc.integral_abs_frInt_le hx
  refine ⟨hFi.integral_prod_left, ?_⟩
  calc ∫ t in Ioi 0, ∫ x, frInt c (D x) t ∂π
      = ∫ x, (∫ t in Ioi 0, frInt c (D x) t) ∂π :=
        integral_integral_swap (f := fun t x => frInt c (D x) t) hFi
    _ = ∫ x, -Real.log (D x) ∂π := by
        refine integral_congr_ae ?_
        filter_upwards [hpos] with x hx
        exact hc.integral_frInt hx
    _ = -∫ x, Real.log (D x) ∂π := integral_neg _

end IsProfile

/-! ### The profile of `C = autoCorr κ` (HA2 D3, Step 0) -/

/-- The radial profile `c(s) = C(s e)` of `C = autoCorr κ` along a unit vector `e`. -/
def corrProfile (κ : Rd d → ℝ) (e : Rd d) (s : ℝ) : ℝ := autoCorr κ (s • e)

section Profile

variable {κ : Rd d → ℝ}

/-- `C(v) = c(|v|)` (`C` is radial). -/
theorem autoCorr_eq_corrProfile (hκ : IsLFPPKernel κ) {e : Rd d} (he : ‖e‖ = 1) (v : Rd d) :
    autoCorr κ v = corrProfile κ e ‖v‖ := by
  refine autoCorr_eq_of_norm_eq hκ ?_
  rw [norm_smul, he, mul_one, Real.norm_of_nonneg (norm_nonneg v)]

/-- **HA2 D3, Step 0**: the profile of `C` is admissible for Frullani's integral. -/
theorem exists_isProfile (hκ : IsLFPPKernel κ) {e : Rd d} (he : ‖e‖ = 1) :
    ∃ R L : ℝ, IsProfile (corrProfile κ e) R L := by
  obtain ⟨ρ, -, hρ⟩ := hκ.exists_radius
  obtain ⟨K, hK⟩ := exists_lipschitzWith_autoCorr hκ
  refine ⟨max (2 * ρ) 1, K, ⟨?_, ?_, ?_, le_max_right _ _, ?_, K.2, ?_⟩⟩
  · exact (continuous_autoCorr hκ).comp (continuous_id.smul continuous_const)
  · simp only [corrProfile, zero_smul, autoCorr_zero hκ]
  · intro s
    exact abs_autoCorr_le_one hκ _
  · intro s hs
    have hs0 : 0 ≤ s := le_trans zero_le_one ((le_max_right _ _).trans hs)
    refine autoCorr_eq_zero_of_two_mul_le hρ ?_
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg hs0]
    exact (le_max_left _ _).trans hs
  · intro s s'
    have h := hK.dist_le_mul (s • e) (s' • e)
    rwa [Real.dist_eq, dist_eq_norm, ← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs] at h

/-- **HA2 D3, Step 2**: with equal masses of the first pair, for `t > 0`,
`scalePair κ t μ ν μ' ν' = ∫∫ φ(|z - w|, t) (μ - ν)(dz) (μ' - ν')(dw)`. -/
theorem scalePair_eq_mixInt_frInt (hκ : IsLFPPKernel κ) {e : Rd d} (he : ‖e‖ = 1) {t : ℝ}
    (ht : 0 < t) (μ ν μ' ν' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] (hmass : μ.real univ = ν.real univ) :
    scalePair κ t μ ν μ' ν' =
      mixInt (fun z w => frInt (corrProfile κ e) ‖z - w‖ t) μ ν μ' ν' := by
  rw [scalePair_eq_mixInt_sub_const hκ t (corrProfile κ e (1 / t) / t) μ ν μ' ν' hmass]
  congr 1
  funext z w
  rw [frInt, sub_div, autoCorr_eq_corrProfile hκ he, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_eq_div]

end Profile

/-! ### Atomless measures: the diagonal is null -/

/-- If the first factor has no atoms, the diagonal is null for the product measure. -/
theorem FieldAux.ae_ne_of_nullSingletonClass (α β : Measure (Rd d)) [NullSingletonClass α] [SFinite α]
    [SFinite β] : ∀ᵐ p ∂(α.prod β), p.1 ≠ p.2 := by
  have hms : MeasurableSet {p : Rd d × Rd d | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [Measure.prod_apply_symm hms]
  have e : ∀ y : Rd d, (fun x => (x, y)) ⁻¹' {p : Rd d × Rd d | p.1 = p.2} = {y} := by
    intro y
    ext x
    simp only [mem_preimage, mem_ofPred_eq, mem_singleton_iff]
  simp only [e, measure_singleton, lintegral_zero]

theorem FieldAux.ae_norm_sub_pos (α β : Measure (Rd d)) [NullSingletonClass α] [SFinite α] [SFinite β] :
    ∀ᵐ p ∂(α.prod β), 0 < ‖p.1 - p.2‖ := by
  filter_upwards [FieldAux.ae_ne_of_nullSingletonClass α β] with p hp
  exact norm_pos_iff.2 (sub_ne_zero.2 hp)

/-- In dimension `0` an atomless measure is zero. -/
theorem eq_zero_of_nullSingletonClass_rd_zero (μ : Measure (Rd 0)) [NullSingletonClass μ] :
    μ = 0 := by
  have hu : (univ : Set (Rd 0)) = {0} := by
    ext x
    simp only [mem_univ, mem_singleton_iff, true_iff]
    exact Subsingleton.elim x 0
  rw [← Measure.measure_univ_eq_zero, hu, measure_singleton]

/-! ### (3.2): the all-scale covariance is the log covariance -/

theorem FieldAux.setIntegral_sub_sub_add {f₁ f₂ f₃ f₄ : ℝ → ℝ} {s : Set ℝ} (h₁ : IntegrableOn f₁ s)
    (h₂ : IntegrableOn f₂ s) (h₃ : IntegrableOn f₃ s) (h₄ : IntegrableOn f₄ s) :
    ∫ t in s, (f₁ t - f₂ t - f₃ t + f₄ t) =
      (∫ t in s, f₁ t) - (∫ t in s, f₂ t) - (∫ t in s, f₃ t) + ∫ t in s, f₄ t := by
  rw [integral_add (f := fun t => f₁ t - f₂ t - f₃ t) ((h₁.sub h₂).sub h₃) h₄,
    integral_sub (f := fun t => f₁ t - f₂ t) (h₁.sub h₂) h₃, integral_sub h₁ h₂]

section LogCov

variable {κ : Rd d → ℝ}

/-- **HA2 D3, Steps 2–5**: for finite measures, atomless first pair of equal masses, and `log|z - w|`
integrable for the four product measures, `t ↦ scalePair κ t μ ν μ' ν'` is integrable on
`(0, ∞)` with integral `logCov μ ν μ' ν'`. -/
theorem integral_scalePair_eq_logCov [NeZero d] (hκ : IsLFPPKernel κ)
    {μ ν μ' ν' : Measure (Rd d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] [NullSingletonClass μ] [NullSingletonClass ν]
    (hmass : μ.real univ = ν.real univ)
    (hint : ∀ α β : Measure (Rd d), (α = μ ∨ α = ν) → (β = μ' ∨ β = ν') →
      Integrable (fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖) (α.prod β)) :
    IntegrableOn (fun t => scalePair κ t μ ν μ' ν') (Ioi 0) ∧
      ∫ t in Ioi 0, scalePair κ t μ ν μ' ν' = logCov μ ν μ' ν' := by
  obtain ⟨e, he⟩ := exists_norm_eq (Rd d) (zero_le_one : (0 : ℝ) ≤ 1)
  obtain ⟨R, L, hc⟩ := exists_isProfile hκ he
  have key : ∀ (α β : Measure (Rd d)) [IsFiniteMeasure α] [IsFiniteMeasure β]
      [NullSingletonClass α],
      Integrable (fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖) (α.prod β) →
      IntegrableOn (fun t => ∫ p, frInt (corrProfile κ e) ‖p.1 - p.2‖ t ∂(α.prod β)) (Ioi 0) ∧
        ∫ t in Ioi 0, ∫ p, frInt (corrProfile κ e) ‖p.1 - p.2‖ t ∂(α.prod β) =
          -∫ p, Real.log ‖p.1 - p.2‖ ∂(α.prod β) := by
    intro α β _ _ _ hl
    exact hc.frInt_fubini (α.prod β) (continuous_fst.sub continuous_snd).norm.measurable
      (FieldAux.ae_norm_sub_pos α β) hl
  obtain ⟨i1, v1⟩ := key μ μ' (hint μ μ' (Or.inl rfl) (Or.inl rfl))
  obtain ⟨i2, v2⟩ := key μ ν' (hint μ ν' (Or.inl rfl) (Or.inr rfl))
  obtain ⟨i3, v3⟩ := key ν μ' (hint ν μ' (Or.inr rfl) (Or.inl rfl))
  obtain ⟨i4, v4⟩ := key ν ν' (hint ν ν' (Or.inr rfl) (Or.inr rfl))
  have heq : EqOn (fun t =>
      ∫ p, frInt (corrProfile κ e) ‖p.1 - p.2‖ t ∂(μ.prod μ') -
        ∫ p, frInt (corrProfile κ e) ‖p.1 - p.2‖ t ∂(μ.prod ν') -
        ∫ p, frInt (corrProfile κ e) ‖p.1 - p.2‖ t ∂(ν.prod μ') +
        ∫ p, frInt (corrProfile κ e) ‖p.1 - p.2‖ t ∂(ν.prod ν'))
      (fun t => scalePair κ t μ ν μ' ν') (Ioi 0) := by
    intro t ht
    dsimp only
    rw [scalePair_eq_mixInt_frInt hκ he ht μ ν μ' ν' hmass]
    rfl
  refine ⟨(((i1.sub i2).sub i3).add i4).congr_fun heq measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, FieldAux.setIntegral_sub_sub_add i1 i2 i3 i4,
    v1, v2, v3, v4, logCov]
  simp only [integral_neg]

theorem FieldAux.le_add_four₁ (μ ν μ' ν' : Measure (Rd d)) : μ ≤ μ + ν + μ' + ν' :=
  Measure.le_add_right (Measure.le_add_right (Measure.le_add_right le_rfl))

theorem FieldAux.le_add_four₂ (μ ν μ' ν' : Measure (Rd d)) : ν ≤ μ + ν + μ' + ν' :=
  Measure.le_add_right (Measure.le_add_right (Measure.le_add_left le_rfl))

theorem FieldAux.le_add_four₃ (μ ν μ' ν' : Measure (Rd d)) : μ' ≤ μ + ν + μ' + ν' :=
  Measure.le_add_right (Measure.le_add_left le_rfl)

theorem FieldAux.le_add_four₄ (μ ν μ' ν' : Measure (Rd d)) : ν' ≤ μ + ν + μ' + ν' :=
  Measure.le_add_left le_rfl

/-- The log energy of `LogPairable` controls every product of two of the four measures. -/
theorem LogPairable.integrable_prod {μ ν μ' ν' : Measure (Rd d)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] (h : LogPairable μ ν μ' ν')
    {α β : Measure (Rd d)} [SFinite β] (hα : α ≤ μ + ν + μ' + ν') (hβ : β ≤ μ + ν + μ' + ν') :
    Integrable (fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖) (α.prod β) :=
  h.2.2.2.2.mono_measure (Measure.prod_mono hα hβ)

/-- **(3.2) with well-posedness** (target T2; HA2's `Eq32`): for finite measures with
`μ(ℝ^d) = ν(ℝ^d)`, `μ'(ℝ^d) = ν'(ℝ^d)`, no atoms and finite logarithmic energy, the all-scale
pairings are defined (`IsPairable κ (0, ∞)`) and
`Cov(⟨h, μ - ν⟩, ⟨h, μ' - ν'⟩) = ∫∫ log|z - w|⁻¹ (μ - ν)(dz) (μ' - ν')(dw)`. -/
theorem scaleCov_eq_logCov (hκ : IsLFPPKernel κ) {μ ν μ' ν' : Measure (Rd d)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (hmass : μ.real univ = ν.real univ) (hmass' : μ'.real univ = ν'.real univ)
    (hlog : LogPairable μ ν μ' ν') :
    IsPairable κ (Ioi 0) μ ν ∧ IsPairable κ (Ioi 0) μ' ν' ∧
      scaleCov κ (Ioi 0) μ ν μ' ν' = logCov μ ν μ' ν' := by
  have h1 : NullSingletonClass μ := hlog.1
  have h2 : NullSingletonClass ν := hlog.2.1
  have h3 : NullSingletonClass μ' := hlog.2.2.1
  have h4 : NullSingletonClass ν' := hlog.2.2.2.1
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    obtain rfl := eq_zero_of_nullSingletonClass_rd_zero μ
    obtain rfl := eq_zero_of_nullSingletonClass_rd_zero ν
    obtain rfl := eq_zero_of_nullSingletonClass_rd_zero μ'
    obtain rfl := eq_zero_of_nullSingletonClass_rd_zero ν'
    have hp : IsPairable κ (Ioi 0) (0 : Measure (Rd 0)) 0 := by
      rw [IsPairable, sub_self]
      exact MemLp.zero
    refine ⟨hp, hp, ?_⟩
    simp only [scaleCov, bandVecM_self, inner_zero_left, logCov, Measure.prod_zero,
      integral_zero_measure, sub_self, add_zero]
  have : NeZero d := ⟨hd.ne'⟩
  have hP : ∀ α β : Measure (Rd d), [SFinite β] → α ≤ μ + ν + μ' + ν' → β ≤ μ + ν + μ' + ν' →
      Integrable (fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖) (α.prod β) :=
    fun α β _ hα hβ => LogPairable.integrable_prod hlog hα hβ
  have l1 := FieldAux.le_add_four₁ μ ν μ' ν'
  have l2 := FieldAux.le_add_four₂ μ ν μ' ν'
  have l3 := FieldAux.le_add_four₃ μ ν μ' ν'
  have l4 := FieldAux.le_add_four₄ μ ν μ' ν'
  have c1 := integral_scalePair_eq_logCov hκ (μ := μ) (ν := ν) (μ' := μ) (ν' := ν) hmass
    (by rintro α β (rfl | rfl) (rfl | rfl) <;> apply hP <;> assumption)
  have c2 := integral_scalePair_eq_logCov hκ (μ := μ') (ν := ν') (μ' := μ') (ν' := ν') hmass'
    (by rintro α β (rfl | rfl) (rfl | rfl) <;> apply hP <;> assumption)
  have c3 := integral_scalePair_eq_logCov hκ (μ := μ) (ν := ν) (μ' := μ') (ν' := ν') hmass
    (by rintro α β (rfl | rfl) (rfl | rfl) <;> apply hP <;> assumption)
  have hp1 : IsPairable κ (Ioi 0) μ ν :=
    isPairable_of_le hκ measurableSet_Ioi subset_rfl μ ν c1.1 fun t _ => le_rfl
  have hp2 : IsPairable κ (Ioi 0) μ' ν' :=
    isPairable_of_le hκ measurableSet_Ioi subset_rfl μ' ν' c2.1 fun t _ => le_rfl
  exact ⟨hp1, hp2, (scaleCov_eq_integral hκ measurableSet_Ioi subset_rfl hp1 hp2).trans c3.2⟩

end LogCov

end HigherDimLFPP
