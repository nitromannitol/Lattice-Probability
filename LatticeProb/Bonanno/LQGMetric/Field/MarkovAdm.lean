/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovAdm at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovNorm
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DisjointUnion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Admissibility on open sets disjoint from the unit circle (task P2-MKA, leaf (A) of P2-MARKOV)

LM Lemma 2.1 (`Blueprint.LMLem2_1`) quantifies over all open `V` with `V ∩ ∂𝔻 = ∅`, possibly
unbounded. The zero-boundary GFF on such a `V` still pairs with bounded, compactly supported
densities vanishing off `V` (`isAdmissibleDual_withDensity_of_disjoint_sphere`): split
`V = (V ∩ 𝔻) ∪ (V ∩ ext 𝔻)`; the dual Dirichlet norm is additive over disjoint open sets
(QZ `K3.dualNormSq_union_of_disjoint`), the bounded piece is `isAdmissibleDual_withDensity_of_isBounded`,
and the exterior piece is mapped by the inversion `z ↦ z⁻¹` onto a bounded open set (conformal
invariance of the dual norm, QZ `K3.dualNormSq_conformal`), the pushforward of a bounded
density being again a bounded density (QZ `map_withDensity_eq`, `bounded_density`).

This rests on the conformal invariance of the Dirichlet inner product (Sheffield math/0312099
§2.2; Berestycki–Powell arXiv:2404.16642 Ch. 1); the splitting along `∂𝔻` and the use of the
inversion are our own elementary route (own elementary proof, no published proof of this exact
admissibility statement).
-/

noncomputable section

open MeasureTheory TopologicalSpace Set Metric
open scoped ENNReal

namespace LQGMetric
namespace MarkovAdm

open QuantumZipper QuantumZipper.K3

lemma inv_conformal {D : Set ℂ} (hD : IsOpen D) (h0 : (0 : ℂ) ∉ D) :
    IsConformalOnto (fun z : ℂ => z⁻¹) D ((fun z : ℂ => z⁻¹) '' D) where
  isOpen := hD
  diffOn := fun z hz => (differentiableAt_inv (fun h => h0 (h ▸ hz))).differentiableWithinAt
  injOn := inv_injective.injOn
  image_eq := rfl
  deriv_ne := fun z hz => by
    rw [deriv_inv]
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 fun h => h0 (h ▸ hz)))

/-- the exterior piece: `V ∩ {1 < |z|}` -/
lemma dualNormSq_ext_lt_top {D : Set ℂ} (hD : IsOpen D) (hD1 : ∀ z ∈ D, 1 < ‖z‖)
    {u : ℂ → ℝ≥0∞} {M : ℝ≥0∞} {R : ℝ} (hu : BddDens u M R) :
    dualNormSq D (zeroSpace D) (volume.withDensity u) < ⊤ := by
  have h0 : (0 : ℂ) ∉ D := fun h => by have := hD1 0 h; norm_num at this
  have hφ := inv_conformal hD h0
  have hfin := isFiniteMeasure_withDensity_bdd hu.lt_top hu.le hu.zero
  rw [dualNormSq_conformal hφ, restrict_withDensity hD.measurableSet,
    ← withDensity_indicator hD.measurableSet]
  set s : Set ℂ := D ∩ closedBall 0 R
  set ρ : ℂ → ℝ≥0∞ := D.indicator u with hρdef
  have hρs : ∀ z, z ∉ s → ρ z = 0 := fun z hz => by
    by_cases hzD : z ∈ D
    · rw [hρdef, indicator_of_mem hzD]; exact hu.zero z fun h => hz ⟨hzD, h⟩
    · rw [hρdef]; exact indicator_of_notMem hzD _
  have hU : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) {0}ᶜ := fun z hz =>
    (differentiableAt_inv hz).differentiableWithinAt
  have hder : ∀ z ∈ ({0}ᶜ : Set ℂ), deriv (fun z : ℂ => z⁻¹) z ≠ 0 := fun z hz => by
    rw [deriv_inv]; exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hz))
  have hs : MeasurableSet s := hD.measurableSet.inter measurableSet_closedBall
  set K : Set ℂ := closedBall 0 R \ ball 0 1
  have hK : IsCompact K := (isCompact_closedBall 0 R).diff isOpen_ball
  have hKU : K ⊆ {0}ᶜ := fun z hz h => hz.2 (by simp_all)
  have hsK : s ⊆ K := fun z hz => ⟨hz.2, fun h => by
    have := hD1 z hz.1; rw [mem_ball, dist_zero_right] at h; linarith⟩
  rw [map_withDensity_eq hU hdiff inv_injective.injOn measurable_inv hder hs
    (fun z hz => hKU (hsK hz)) (hu.meas.indicator hD.measurableSet) hρs]
  obtain ⟨c, hc, hle, -, hvan⟩ := bounded_density hU hdiff inv_injective.injOn hder hK hKU hsK
    hρs (M := M) (fun z _ => (indicator_le_self D u z).trans (hu.le z))
  set H : Opens ℂ := ⟨_, hφ.isOpen_target⟩
  have hHb : Bornology.IsBounded (H : Set ℂ) := (isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset
    (by
      rintro _ ⟨z, hz, rfl⟩
      rw [mem_closedBall, dist_zero_right, norm_inv]
      exact inv_le_one_of_one_le₀ (hD1 z hz).le)
  have hbd : BddDens (pushDensity (fun z : ℂ => z⁻¹) s ρ) (M / ENNReal.ofReal c) 1 :=
    { meas := by
        have himg : (fun z : ℂ => z⁻¹) '' s = (fun z : ℂ => z⁻¹) ⁻¹' s :=
          congrFun (inv_involutive (G := ℂ)).image_eq_preimage_symm s
        have heq : pushDensity (fun z : ℂ => z⁻¹) s ρ = ((fun z : ℂ => z⁻¹) ⁻¹' s).indicator
            fun w => ρ w⁻¹ / ENNReal.ofReal (‖deriv (fun z : ℂ => z⁻¹) w⁻¹‖ ^ 2) := by
          funext w
          unfold pushDensity
          rw [himg]
          by_cases hw : w ∈ (fun z : ℂ => z⁻¹) ⁻¹' s
          · have hex : ∃ a ∈ s, a⁻¹ = w := ⟨w⁻¹, hw, inv_inv w⟩
            have e := Function.invFunOn_eq (f := fun z : ℂ => z⁻¹) hex
            have e' : Function.invFunOn (fun z : ℂ => z⁻¹) s w = w⁻¹ := by
              rw [← inv_inv (Function.invFunOn (fun z : ℂ => z⁻¹) s w)]
              exact congrArg (·⁻¹) e
            rw [indicator_of_mem hw, indicator_of_mem hw, e']
          · rw [indicator_of_notMem hw, indicator_of_notMem hw]
        rw [heq]
        refine Measurable.indicator ?_ (measurable_inv hs)
        exact ((hu.meas.indicator hD.measurableSet).comp measurable_inv).div
          (ENNReal.measurable_ofReal.comp (((measurable_deriv _).comp measurable_inv).norm.pow_const 2))
      lt_top := ENNReal.div_lt_top hu.lt_top.ne (ENNReal.ofReal_pos.mpr hc).ne'
      le := hle
      zero := fun w hw => hvan w fun ⟨z, hz, e⟩ => hw (by
        rw [← e, mem_closedBall, dist_zero_right, norm_inv]
        refine inv_le_one_of_one_le₀ (not_lt.mp fun h => hz.2 ?_)
        rwa [mem_ball, dist_zero_right]) }
  exact (isAdmissibleDual_withDensity_of_isBounded (U := H) hHb hbd fun w hw =>
    pushDensity_eq_zero_of_not_mem fun hw' => hw (image_mono inter_subset_left hw')).2.2

/-- **Bounded compactly supported densities are admissible on `V` with `V ∩ ∂𝔻 = ∅`.** -/
theorem isAdmissibleDual_withDensity_of_disjoint_sphere {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) {u : ℂ → ℝ≥0∞} {M : ℝ≥0∞} {R : ℝ}
    (hu : BddDens u M R) (hu0 : ∀ z ∉ (V : Set ℂ), u z = 0) :
    IsAdmissibleDual V (zeroSpace V) (volume.withDensity u) := by
  have hfin := isFiniteMeasure_withDensity_bdd hu.lt_top hu.le hu.zero
  refine ⟨hfin, ⟨closure (V : Set ℂ) ∩ closedBall 0 R,
    (isCompact_closedBall 0 R).inter_left isClosed_closure, inter_subset_left,
    withDensity_compl_null (isClosed_closure.inter isClosed_closedBall).measurableSet
      fun z hz => ?_⟩, ?_⟩
  · by_cases hzV : z ∈ (V : Set ℂ)
    · exact hu.zero z fun h => hz ⟨subset_closure hzV, h⟩
    · exact hu0 z hzV
  set D₁ : Set ℂ := (V : Set ℂ) ∩ ball 0 1
  set D₂ : Set ℂ := (V : Set ℂ) ∩ {z | 1 < ‖z‖}
  have ho1 : IsOpen D₁ := V.isOpen.inter isOpen_ball
  have ho2 : IsOpen D₂ := V.isOpen.inter (isOpen_lt continuous_const continuous_norm)
  have hd : Disjoint D₁ D₂ := Set.disjoint_left.2 fun z h1 h2 => by
    have := h1.2; rw [mem_ball, dist_zero_right] at this
    exact absurd h2.2 (not_lt.2 this.le)
  have hVeq : (V : Set ℂ) = D₁ ∪ D₂ := by
    ext z
    refine ⟨fun hz => ?_, fun h => h.elim (fun h => h.1) fun h => h.1⟩
    rcases lt_trichotomy ‖z‖ 1 with h | h | h
    · exact Or.inl ⟨hz, by rwa [mem_ball, dist_zero_right]⟩
    · exact absurd (mem_sphere_zero_iff_norm.2 h) (Set.disjoint_left.1 hV hz)
    · exact Or.inr ⟨hz, h⟩
  rw [hVeq, dualNormSq_union_of_disjoint ho1 ho2 hd]
  refine ENNReal.add_lt_top.2 ⟨?_, dualNormSq_ext_lt_top ho2 (fun z hz => hz.2) hu⟩
  rw [dualNormSq_zeroSpace_restrict ho1, restrict_withDensity ho1.measurableSet,
    ← withDensity_indicator ho1.measurableSet]
  have hbd : BddDens (D₁.indicator u) M R :=
    { meas := hu.meas.indicator ho1.measurableSet
      lt_top := hu.lt_top
      le := fun z => (indicator_le_self D₁ u z).trans (hu.le z)
      zero := fun z hz => by
        by_cases h : z ∈ D₁
        · rw [indicator_of_mem h]; exact hu.zero z hz
        · exact indicator_of_notMem h _ }
  exact (isAdmissibleDual_withDensity_of_isBounded (U := ⟨D₁, ho1⟩)
    (isBounded_ball.subset inter_subset_right) hbd fun z hz => indicator_of_notMem hz _).2.2

/-- real version: `ρ⁺ dz`, `ρ⁻ dz` for bounded measurable `ρ` vanishing off `V` and off a ball -/
theorem admissible_of_disjoint_sphere {V : Opens ℂ} (hV : Disjoint (V : Set ℂ) (sphere 0 1))
    {ρ : ℂ → ℝ} (hm : Measurable ρ) {C : ℝ} (hC : ∀ z, |ρ z| ≤ C) {R : ℝ}
    (hR : ∀ z ∉ closedBall (0 : ℂ) R, ρ z = 0) (h0 : ∀ z ∉ (V : Set ℂ), ρ z = 0) :
    IsAdmissibleDual V (zeroSpace V) (testMeasPos ρ) ∧
      IsAdmissibleDual V (zeroSpace V) (testMeasNeg ρ) := by
  refine ⟨isAdmissibleDual_withDensity_of_disjoint_sphere hV (M := ENNReal.ofReal C) (R := R)
    ⟨ENNReal.measurable_ofReal.comp hm, ENNReal.ofReal_lt_top,
      fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC z)),
      fun z hz => by rw [hR z hz, ENNReal.ofReal_zero]⟩
    fun z hz => by rw [h0 z hz, ENNReal.ofReal_zero],
    isAdmissibleDual_withDensity_of_disjoint_sphere hV (M := ENNReal.ofReal C) (R := R)
    ⟨ENNReal.measurable_ofReal.comp hm.neg, ENNReal.ofReal_lt_top,
      fun z => ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (hC z)),
      fun z hz => by rw [hR z hz, neg_zero, ENNReal.ofReal_zero]⟩
    fun z hz => by rw [h0 z hz, neg_zero, ENNReal.ofReal_zero]⟩

lemma exists_closedBall_of_test {U : Opens ℂ} (φ : TestOn U) :
    ∃ R : ℝ, ∀ z ∉ closedBall (0 : ℂ) R, φ z = 0 := by
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  exact ⟨R, fun z hz => image_eq_zero_of_notMem_tsupport fun h => hz (hR h)⟩

/-- **Leaf (A), first half.** -/
theorem zbAdmissible_of_disjoint_sphere {V : Opens ℂ} (hV : Disjoint (V : Set ℂ) (sphere 0 1)) :
    ZBAdmissible V := fun φ => by
  obtain ⟨hm, ⟨C, hC⟩, h0⟩ := (TestOn.toBddOn φ).2
  obtain ⟨R, hR⟩ := exists_closedBall_of_test φ
  exact admissible_of_disjoint_sphere hV hm hC hR h0

/-- **Leaf (A), second half.** -/
theorem admissible_extZero_of_disjoint_sphere {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) (φ : TestC) :
    IsAdmissibleDual V (zeroSpace V) (testMeasPos ((V : Set ℂ).indicator φ)) ∧
      IsAdmissibleDual V (zeroSpace V) (testMeasNeg ((V : Set ℂ).indicator φ)) := by
  obtain ⟨hm, ⟨C, hC⟩, h0⟩ := (extZeroTest V φ).2
  obtain ⟨R, hR⟩ := exists_closedBall_of_test φ
  exact admissible_of_disjoint_sphere hV hm hC
    (fun z hz => by
      by_cases h : z ∈ (V : Set ℂ)
      · exact (indicator_of_mem h _).trans (hR z hz)
      · exact indicator_of_notMem h _) h0

end MarkovAdm
end LQGMetric
