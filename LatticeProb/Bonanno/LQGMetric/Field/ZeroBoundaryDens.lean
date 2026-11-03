/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ZeroBoundaryDens at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryAffine
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.KernelForm4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bounded densities are admissible on bounded domains (task P2-ZB, WP-14)

For a bounded open `U` and a bounded measurable density `u ≥ 0` vanishing off `U`, the measure
`u dz` is in QZ's admissible class for the zero-boundary GFF on `U`
(`isAdmissibleDual_withDensity_of_isBounded`): finite `H⁻¹(U)`-norm. Hence a QZ zero-boundary
GFF `X` on `U` (`QuantumZipper.IsZeroBoundaryGFFOn U X P`) can be paired with such densities,
e.g. with `p_{t/2}(x − ·) 1_D` in DDDF Prop. 29 (`blueprint/DDDF.md`, row DDDF.P29: "GFF pairing
with `p_{t/2}(x−·)1_D` … needs the GFF's extension to `L²(D)` test functions"), for every bounded
`D` such as `(−1,2)²` — QZ proves this only for `D ⊆ ℍ`.

Proof: translate `U` into `ℍ` (`exists_affOpens_one_subset_H`); there QZ's
`K3.isAdmissibleH_withDensity`, `K3.isAdmissibleDual_H_of_isAdmissibleH` and
`K3.dualNormSq_zeroSpace_mono` apply, and the dual norm is translation invariant
(`dualNormSq_affine`, from QZ's conformal invariance `K3.dualNormSq_conformal`). The translated
density is `u(· − w)`, whose measure is the push-forward of `u dz` (translation invariance of
Lebesgue measure, mathlib `lintegral_add_right_eq_self`).
-/

noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal

namespace LQGMetric

open QuantumZipper QuantumZipper.K3

lemma affFwd_one (w y : ℂ) : affFwd 1 w y = y + w := by simp [affFwd]

/-- translating a density: `u(· − w) dz` is the push-forward of `u dz` under `y ↦ y + w` -/
lemma withDensity_comp_affMap_one (u : ℂ → ℝ≥0∞) (w : ℂ) :
    volume.withDensity (fun y => u (affMap 1 w y)) =
      (volume.withDensity u).map (affFwd 1 w) := by
  have hA : Measurable (affFwd 1 w) := (continuous_affFwd 1 w).measurable
  have hB : Measurable (affMap 1 w) := (continuous_affMap 1 w).measurable
  ext s hs
  rw [withDensity_apply _ hs, Measure.map_apply hA hs, withDensity_apply _ (hA hs),
    ← lintegral_indicator hs, ← lintegral_indicator (hA hs)]
  rw [← lintegral_add_right_eq_self (μ := (volume : Measure ℂ))
    (fun y => s.indicator (fun y => u (affMap 1 w y)) y) w]
  refine lintegral_congr fun x => ?_
  have e1 : affMap 1 w (x + w) = x := by simp [affMap]
  by_cases hx : x + w ∈ s
  · have hx' : x ∈ affFwd 1 w ⁻¹' s := by simpa [mem_preimage, affFwd_one] using hx
    rw [indicator_of_mem hx, indicator_of_mem hx', e1]
  · have hx' : x ∉ affFwd 1 w ⁻¹' s := by simpa [mem_preimage, affFwd_one] using hx
    rw [indicator_of_notMem hx, indicator_of_notMem hx']

/-- **Bounded densities are admissible on bounded domains.** -/
theorem isAdmissibleDual_withDensity_of_isBounded {U : Opens ℂ}
    (hU : Bornology.IsBounded (U : Set ℂ)) {u : ℂ → ℝ≥0∞} {M : ℝ≥0∞} {R : ℝ}
    (hu : BddDens u M R) (hu0 : ∀ z ∉ (U : Set ℂ), u z = 0) :
    IsAdmissibleDual U (zeroSpace U) (volume.withDensity u) := by
  obtain ⟨w, hw⟩ := exists_affOpens_one_subset_H hU
  have h1 : (1 : ℝ) ≠ 0 := one_ne_zero
  have hfin := isFiniteMeasure_withDensity_bdd hu.lt_top hu.le hu.zero
  -- the translated density on `U + w ⊆ ℍ`
  set u' : ℂ → ℝ≥0∞ := fun y => u (affMap 1 w y)
  have hu'm : Measurable u' := hu.meas.comp (continuous_affMap 1 w).measurable
  have hcl : IsCompact (closure (U : Set ℂ)) := hU.isCompact_closure
  have hK' : IsCompact (affFwd 1 w '' closure (U : Set ℂ)) :=
    hcl.image (continuous_affFwd 1 w)
  have hu'0 : ∀ y ∉ affFwd 1 w '' closure (U : Set ℂ), u' y = 0 := fun y hy =>
    hu0 _ fun h => hy ⟨affMap 1 w y, subset_closure h, affFwd_affMap h1 y⟩
  have hKH : affFwd 1 w '' closure (U : Set ℂ) ⊆ Hbar := by
    have : affFwd 1 w '' closure (U : Set ℂ) ⊆ closure (affOpens 1 w U : Set ℂ) := by
      rintro _ ⟨x, hx, rfl⟩
      have := image_closure_subset_closure_image (continuous_affFwd 1 w) ⟨x, hx, rfl⟩
      refine closure_mono ?_ this
      rintro _ ⟨y, hy, rfl⟩
      show affMap 1 w (affFwd 1 w y) ∈ (U : Set ℂ)
      rw [affMap_affFwd h1]; exact hy
    exact this.trans ((closure_mono hw).trans closure_H_K3.subset)
  have hH := isAdmissibleH_withDensity hu'm hu.lt_top (fun z => hu.le _) hK' hKH hu'0
  have hfin' : dualNormSq (affOpens 1 w U) (zeroSpace (affOpens 1 w U))
      (volume.withDensity u') < ⊤ :=
    (dualNormSq_zeroSpace_mono (affOpens 1 w U).isOpen hw).trans_lt
      (isAdmissibleDual_H_of_isAdmissibleH hH).2.2
  have hrel : AffRel 1 w U (volume.withDensity u') (volume.withDensity u) :=
    ⟨hH.1, hfin, withDensity_compl_null U.isOpen.measurableSet hu0, fun f _ _ => by
      rw [withDensity_comp_affMap_one u w, one_pow, one_mul]⟩
  rw [dualNormSq_affine h1 hrel] at hfin'
  refine ⟨hfin, ⟨closure (U : Set ℂ), hcl, subset_rfl, withDensity_compl_null
    isClosed_closure.measurableSet fun z hz => hu0 z fun h => hz (subset_closure h)⟩, ?_⟩
  simpa using hfin'

end LQGMetric
