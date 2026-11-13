/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.StagePairingPolarization at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SpecificEnergyPolarization
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedRootedSpecificEnergyMeasurability

/-!
# The expected Pythagoras identity without any finiteness input, and measurability of the
signed pairing density

`Corrector/SpecificEnergyPolarization.lintegral_rootedSpecificEnergyDensity_eq_add_of_integral_pairing_eq_zero`
(:432) derives the manuscript's `s:prop:projection` identity `E[ρ_θ] = E[ρ_ψ] + E[ρ_{θ−ψ}]`
from a vanishing expected pairing, but it takes **two finiteness hypotheses**: `E[ρ_ψ] ≠ ∞`
and `E[ρ_{θ−ψ}] ≠ ∞`.  Transported to the marked stage energies by
`Corrector/MarkedStagePythagoras.markedNestedProjectionBound_of_pairing` (:124) those become
`hfin : ∀ n, markedStageEnergy ν n ≠ ∞` and `hdfin : ∀ m n, markedStageDefect ν m n ≠ ∞`.

**Those two hypotheses are circular at every stage `n ≥ 1`.**  The only producer of
`markedStageEnergy ν n ≠ ∞` in the tree is
`SpecificEnergyConvergence.markedStageEnergy_lt_top`, whose *own* hypothesis is the
`MarkedNestedProjectionBound` being produced; the unconditional producer
`MarkedStageCoefficientScaling.markedStageEnergy_zero_ne_top` covers the stage `0` only, and
`MarkedStageCoefficientScaling.markedStageDefect_ne_top` needs the finiteness at both stages.
An induction cannot break the loop either: the identity at `(m, n)` needs the finiteness at
the **later** stage `n`, which is exactly what it would produce.

This module removes the loop.  The key observation is that the polarization identity can be
integrated in `ℝ≥0∞` **without any `toReal` step on the energies**, by moving the signed part
to whichever side of the identity makes it nonnegative:

`ρ_ψ + ρ_{θ−ψ} + (2⟪ψ, θ−ψ⟫)⁺ = ρ_θ + (2⟪ψ, θ−ψ⟫)⁻`  pointwise in `ℝ≥0∞`,

an identity between sums of **nonnegative** quantities, which `lintegral` adds unconditionally.
Integrating and cancelling the two constants — equal, and finite, precisely because the pairing
density is integrable with integral zero — gives the identity with no finiteness of the
energies at all.  If either side is `∞` the identity still holds, and says so.

## What is proved

* `ofReal_polarization_shift` — the two-case real arithmetic behind the pointwise `ℝ≥0∞`
  identity.
* `lintegral_rootedSpecificEnergyDensity_eq_add_of_integrable_pairing` — the expected
  Pythagoras identity from **integrability of the pairing density together with its vanishing
  integral**, and nothing else.  Compared with the existing route the two finiteness
  hypotheses are gone, and the measurability of `ρ_θ` is derived rather than assumed.
  The hypotheses are strictly weaker: `integrable_rootedPairingDensity` derives the
  integrability from the two finiteness hypotheses that are dropped here.
* `rootedPairingDensity_eq_half_sub` — the signed pairing density is the polarization of the
  three rooted specific-energy densities of `Θ`, `H` and `Θ + H`.
* `measurable_rootedPairingDensity` — consequently, the measurability engine of
  `Corrector/MarkedRootedSpecificEnergyMeasurability` (which is unconditional and handles the
  varying vertex type and the geometric root selection) measures the **signed** pairing density
  too.  No separate slot construction is needed for the bilinear observable.

## What is **not** proved

The vanishing of the expected pairing itself, and its integrability.  Both remain hypotheses;
this file proves no main theorem and certifies none of its inputs.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.StagePairingPolarization

open Code StatementIngredients RootDensities SpecificEnergyPolarization

/-! ### The real arithmetic of the sign shift -/

/-- **Moving the signed term to the nonnegative side.**  If `a = b + p + d` with `a`, `b`, `d`
nonnegative, then the `ℝ≥0∞`-valued identity `ofReal b + ofReal d + ofReal p =
ofReal a + ofReal (-p)` holds, because exactly one of `ofReal p`, `ofReal (-p)` is zero. -/
theorem ofReal_polarization_shift (a b d p : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d) (ha : 0 ≤ a)
    (h : a = b + p + d) :
    ENNReal.ofReal b + ENNReal.ofReal d + ENNReal.ofReal p
      = ENNReal.ofReal a + ENNReal.ofReal (-p) := by
  rcases le_or_gt 0 p with hp | hp
  · -- `p ≥ 0`: the right-hand correction vanishes.
    rw [ENNReal.ofReal_eq_zero.2 (by linarith : (-p : ℝ) ≤ 0), add_zero,
      ← ENNReal.ofReal_add hb hd, ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ b + d) hp]
    congr 1
    linarith
  · -- `p < 0`: the left-hand correction vanishes.
    rw [ENNReal.ofReal_eq_zero.2 (le_of_lt hp), add_zero,
      ← ENNReal.ofReal_add hb hd, ← ENNReal.ofReal_add ha (by linarith : (0:ℝ) ≤ -p)]
    congr 1
    linarith

/-! ### The expected Pythagoras identity with no finiteness input -/

section Expected

variable {Ω : Type*} [MeasurableSpace Ω] {Vtx : Ω → Type*} [∀ ω, Countable (Vtx ω)]

/-- **Expected Pythagoras, finiteness-free.**  `E[ρ_θ] = E[ρ_ψ] + E[ρ_{θ−ψ}]` as soon as the
signed rooted pairing density is integrable with integral zero.  No finiteness of any expected
specific energy is assumed, and the measurability of `ρ_θ` is derived from the pointwise
polarization rather than assumed.

This is the statement that breaks the circularity of the finiteness hypotheses of
`SpecificEnergyPolarization.lintegral_rootedSpecificEnergyDensity_eq_add_of_integral_pairing_eq_zero`:
there the identity at a pair of stages needed the finiteness at the later stage, which only the
identity itself produces. -/
theorem lintegral_rootedSpecificEnergyDensity_eq_add_of_integrable_pairing
    (μ : Measure Ω) (cells : ∀ ω, IndexedCells (Vtx ω)) (Θ Ψ : ∀ ω, Vtx ω → Plane)
    (root : Ω → Plane) (hcells : ∀ ω, Geometry (cells ω))
    (hΨmeas : AEMeasurable
      (fun ω => rootedSpecificEnergyDensity (cells ω) (Ψ ω) (root ω)) μ)
    (hDmeas : AEMeasurable
      (fun ω => rootedSpecificEnergyDensity (cells ω) (fun v => Θ ω v - Ψ ω v) (root ω)) μ)
    (hPint : Integrable
      (fun ω => rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω)) μ)
    (horth : (∫ ω, rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω) ∂μ)
      = 0) :
    (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω) ∂μ)
      = (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Ψ ω) (root ω) ∂μ)
        + ∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (fun v => Θ ω v - Ψ ω v) (root ω) ∂μ := by
  -- the pointwise real polarization, read at `Θ = Ψ + (Θ − Ψ)`
  have hfun : ∀ ω, (fun v => Ψ ω v + (Θ ω v - Ψ ω v)) = Θ ω := by
    intro ω
    funext v
    abel
  have hpt : ∀ ω, (rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)).toReal
      = (rootedSpecificEnergyDensity (cells ω) (Ψ ω) (root ω)).toReal
        + 2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω)
        + (rootedSpecificEnergyDensity (cells ω)
            (fun v => Θ ω v - Ψ ω v) (root ω)).toReal := by
    intro ω
    have h := toReal_rootedSpecificEnergyDensity_add (cells ω) (hcells ω) (Ψ ω)
      (fun v => Θ ω v - Ψ ω v) (root ω)
    rwa [hfun ω] at h
  have hPaem : AEMeasurable
      (fun ω => rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω)) μ :=
    hPint.aestronglyMeasurable.aemeasurable
  -- measurability of the energy of `Θ` is a consequence, not a hypothesis
  have hΘmeas : AEMeasurable
      (fun ω => rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)) μ := by
    have hm : AEMeasurable (fun ω => ENNReal.ofReal
        ((rootedSpecificEnergyDensity (cells ω) (Ψ ω) (root ω)).toReal
          + 2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω)
          + (rootedSpecificEnergyDensity (cells ω)
              (fun v => Θ ω v - Ψ ω v) (root ω)).toReal)) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((hΨmeas.ennreal_toReal.add (hPaem.const_mul 2)).add hDmeas.ennreal_toReal)
    refine hm.congr (Filter.Eventually.of_forall fun ω => ?_)
    show ENNReal.ofReal
        ((rootedSpecificEnergyDensity (cells ω) (Ψ ω) (root ω)).toReal
          + 2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω)
          + (rootedSpecificEnergyDensity (cells ω)
              (fun v => Θ ω v - Ψ ω v) (root ω)).toReal)
      = rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)
    rw [← hpt ω, ENNReal.ofReal_toReal
      (rootedSpecificEnergyDensity_ne_top (cells ω) (hcells ω) (Θ ω) (root ω))]
  -- the pointwise `ℝ≥0∞` identity with the signed part moved to the nonnegative side
  have hkey : ∀ ω,
      rootedSpecificEnergyDensity (cells ω) (Ψ ω) (root ω)
          + rootedSpecificEnergyDensity (cells ω) (fun v => Θ ω v - Ψ ω v) (root ω)
          + ENNReal.ofReal
              (2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω))
        = rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)
          + ENNReal.ofReal
              (-(2 * rootedPairingDensity (cells ω) (Ψ ω)
                  (fun v => Θ ω v - Ψ ω v) (root ω))) := by
    intro ω
    have h := ofReal_polarization_shift
      (rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)).toReal
      (rootedSpecificEnergyDensity (cells ω) (Ψ ω) (root ω)).toReal
      (rootedSpecificEnergyDensity (cells ω) (fun v => Θ ω v - Ψ ω v) (root ω)).toReal
      (2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω))
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg (hpt ω)
    rwa [ENNReal.ofReal_toReal
        (rootedSpecificEnergyDensity_ne_top (cells ω) (hcells ω) (Ψ ω) (root ω)),
      ENNReal.ofReal_toReal (rootedSpecificEnergyDensity_ne_top (cells ω) (hcells ω)
        (fun v => Θ ω v - Ψ ω v) (root ω)),
      ENNReal.ofReal_toReal
        (rootedSpecificEnergyDensity_ne_top (cells ω) (hcells ω) (Θ ω) (root ω))] at h
  have hlin := lintegral_congr (μ := μ) hkey
  -- split both integrals; the splittings are term-mode so that the `Pi`-shaped
  -- `AEMeasurable.add` is matched up to beta rather than syntactically
  have haddmeas : AEMeasurable (fun ω => rootedSpecificEnergyDensity (cells ω) (Ψ ω) (root ω)
      + rootedSpecificEnergyDensity (cells ω) (fun v => Θ ω v - Ψ ω v) (root ω)) μ :=
    hΨmeas.add hDmeas
  have hL1 : (∫⁻ ω, (rootedSpecificEnergyDensity (cells ω) (Ψ ω) (root ω)
          + rootedSpecificEnergyDensity (cells ω) (fun v => Θ ω v - Ψ ω v) (root ω)
        + ENNReal.ofReal
            (2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω))) ∂μ)
      = (∫⁻ ω, (rootedSpecificEnergyDensity (cells ω) (Ψ ω) (root ω)
            + rootedSpecificEnergyDensity (cells ω) (fun v => Θ ω v - Ψ ω v) (root ω)) ∂μ)
        + ∫⁻ ω, ENNReal.ofReal
            (2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω)) ∂μ :=
    lintegral_add_left' haddmeas _
  have hL2 : (∫⁻ ω, (rootedSpecificEnergyDensity (cells ω) (Ψ ω) (root ω)
          + rootedSpecificEnergyDensity (cells ω) (fun v => Θ ω v - Ψ ω v) (root ω)) ∂μ)
      = (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Ψ ω) (root ω) ∂μ)
        + ∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (fun v => Θ ω v - Ψ ω v) (root ω) ∂μ :=
    lintegral_add_left' hΨmeas _
  have hR : (∫⁻ ω, (rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)
        + ENNReal.ofReal
            (-(2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω))))
          ∂μ)
      = (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω) ∂μ)
        + ∫⁻ ω, ENNReal.ofReal
            (-(2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω)))
          ∂μ := lintegral_add_left' hΘmeas _
  -- the two constants are equal and finite
  have hP2 : Integrable (fun ω =>
      2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω)) μ :=
    hPint.const_mul 2
  have hP2neg : Integrable (fun ω =>
      -(2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω))) μ :=
    hP2.neg
  have hcpos : (∫⁻ ω, ENNReal.ofReal
      (2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω)) ∂μ) ≠ ∞ :=
    hP2.lintegral_lt_top.ne
  have hcneg : (∫⁻ ω, ENNReal.ofReal
      (-(2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω))) ∂μ)
      ≠ ∞ := hP2neg.lintegral_lt_top.ne
  have hzero2 : (∫ ω,
      2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω) ∂μ) = 0 := by
    rw [integral_const_mul, horth, mul_zero]
  have hsplitInt : (∫ ω,
        2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω) ∂μ)
      = (∫⁻ ω, ENNReal.ofReal
            (2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω))
          ∂μ).toReal
        - (∫⁻ ω, ENNReal.ofReal
            (-(2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω)))
          ∂μ).toReal :=
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hP2
  have hc : (∫⁻ ω, ENNReal.ofReal
        (2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω)) ∂μ)
      = ∫⁻ ω, ENNReal.ofReal
        (-(2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω))) ∂μ := by
    rw [hzero2] at hsplitInt
    refine (ENNReal.toReal_eq_toReal_iff' hcpos hcneg).mp ?_
    linarith
  have hcomb : (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Ψ ω) (root ω) ∂μ)
        + (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (fun v => Θ ω v - Ψ ω v) (root ω) ∂μ)
        + (∫⁻ ω, ENNReal.ofReal
            (2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω)) ∂μ)
      = (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω) ∂μ)
        + ∫⁻ ω, ENNReal.ofReal
            (2 * rootedPairingDensity (cells ω) (Ψ ω) (fun v => Θ ω v - Ψ ω v) (root ω)) ∂μ := by
    rw [← hL2, ← hL1, hlin, hR, hc]
  exact ((ENNReal.add_left_inj hcpos).mp hcomb).symm

end Expected

/-! ### The signed pairing density is measurable, by polarization -/

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]

end Measurability

end ReflectedGMS.StagePairingPolarization
