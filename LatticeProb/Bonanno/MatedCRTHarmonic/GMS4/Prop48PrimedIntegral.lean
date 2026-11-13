/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48PrimedIntegral at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalStatement
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.MultiVisitNull
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.PrimedObservables

/-!
The all-visit local observable agrees spatially almost everywhere with the
first-hit observable on the canonical zero-cone curve. This is the integral
identity needed to use Lemma 4.3 without trying to recover first-hit order
from the local configuration.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
  MatedCRTHarmonic.GMS4c

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The real product of the maxima over all visits to a point. -/
def uStarPrime (ε : ℝ) (η₀ : Ω → C(ℝ, ℂ)) (ω : Ω) (z : ℂ) : ℝ :=
  (areaRatioPrime ε (η₀ ω) z).toReal *
    (((degreeInPrime ε (η₀ ω) z).toNat +
      (degreeOutPrime ε (η₀ ω) z).toNat : ℕ) : ℝ)

private theorem unique_visit_of_not_multi {c : ℝ → ℂ} {z : ℂ}
    (h : z ∉ multiVisitPoints c) {s t : ℝ}
    (hs : c s = z) (ht : c t = z) : s = t := by
  rcases lt_trichotomy s t with hst | heq | hts
  · exact False.elim (h ⟨s, t, hst, hs, ht⟩)
  · exact heq
  · exact False.elim (h ⟨t, s, hts, ht, hs⟩)

/-- All three primed factors equal the first-hit factors at a uniquely
visited point. -/
theorem prime_factors_eq_firstHit_of_not_multi
    {ε : ℝ} {c : ℝ → ℂ} {z : ℂ}
    (hhit : c (hitTime c z) = z) (hunique : z ∉ multiVisitPoints c) :
    areaRatioPrime ε c z = areaRatio ε c z ∧
      degreeInPrime ε c z = degreeIn ε c z ∧
      degreeOutPrime ε c z = degreeOut ε c z := by
  have heq (t : ℝ) (ht : c t = z) : t = hitTime c z :=
    unique_visit_of_not_multi hunique ht hhit
  constructor
  · apply le_antisymm
    · refine iSup_le fun t => iSup_le fun ht => ?_
      rw [heq t ht]
      rfl
    · exact areaRatio_le_prime hhit
  constructor
  · apply le_antisymm
    · refine iSup_le fun t => iSup_le fun ht => ?_
      rw [heq t ht]
      rfl
    · exact degreeIn_le_prime hhit
  · apply le_antisymm
    · refine iSup_le fun t => iSup_le fun ht => ?_
      rw [heq t ht]
      rfl
    · exact degreeOut_le_prime hhit

theorem uStarPrime_eq_uStar_of_not_multi
    (ε : ℝ) (η₀ : Ω → C(ℝ, ℂ)) (ω : Ω) (z : ℂ)
    (hhit : (η₀ ω) (hitTime (η₀ ω) z) = z)
    (hunique : z ∉ multiVisitPoints (η₀ ω)) :
    uStarPrime ε η₀ ω z = uStar ε η₀ ω z := by
  obtain ⟨hDA, hIn, hOut⟩ :=
    prime_factors_eq_firstHit_of_not_multi hhit hunique
  simp only [uStarPrime, uStar, MatedCRTHarmonic.Canon.realLocalPoint,
    MatedCRTHarmonic.GMS4F.realUStar,
    MatedCRTHarmonic.GMS4F.realAreaRatio,
    MatedCRTHarmonic.GMS4F.natDegreeIn,
    MatedCRTHarmonic.GMS4F.natDegreeOut]
  rw [hDA, hIn, hOut]

/-- The all-visit form of (4.22). Its geometric tests examine every visit;
The two circle averages are the same physical observations as in (4.22). -/
def localEventPrime
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) : Set Ω :=
  {ω | (∀ t : ℝ, η₀ ω t = z →
      diam (locWindow ε (η₀ ω) t) ≤ ε ^ q) ∧
    (((degreeInPrime ε (η₀ ω) z +
      degreeOutPrime ε (η₀ ω) z : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (ε ^ (-ζ))) ∧
    max |fieldCircleAverage D hγ
      (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z ω|
        |igCircleAverage hIG₀ U
          (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z ω| ≤
      2 * q * Real.log ε⁻¹}

def maskedUStarPrime
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  (localEventPrime D hγ ε q ζ z).indicator
    (fun ω' => uStarPrime ε η₀ ω' z) ω

theorem localEventPrime_iff_localEvent_of_not_multi
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (ω : Ω) (z : ℂ)
    (hhit : (η₀ ω) (hitTime (η₀ ω) z) = z)
    (hunique : z ∉ multiVisitPoints (η₀ ω)) :
    ω ∈ localEventPrime D hγ ε q ζ z ↔
      ω ∈ localEvent D hγ ε q ζ z := by
  obtain ⟨_, hIn, hOut⟩ :=
    prime_factors_eq_firstHit_of_not_multi hhit hunique
  have hwindow :
      (∀ t : ℝ, η₀ ω t = z →
        diam (locWindow ε (η₀ ω) t) ≤ ε ^ q) ↔
      windowDiam ε (η₀ ω) z ≤ ε ^ q := by
    constructor
    · intro h
      exact h (hitTime (η₀ ω) z) hhit
    · intro h t ht
      rw [unique_visit_of_not_multi hunique ht hhit]
      exact h
  dsimp [localEventPrime, localEvent,
    MatedCRTHarmonic.Canon.referenceLocalEvent,
    GMS4c.lemma49Event, MatedCRTHarmonic.Canon.referenceConditioningInput,
    fieldCircleAverage, igCircleAverage,
    MatedCRTHarmonic.Canon.actualIGAverage]
  rw [hIn, hOut]
  exact and_congr hwindow (and_congr Iff.rfl Iff.rfl)

private theorem multiVisitPoints_reparam {cL c : ℝ → ℂ}
    (φ : ℝ ≃o ℝ) (hc : ∀ t, c t = cL (φ t)) :
    multiVisitPoints c = multiVisitPoints cL := by
  ext z
  constructor
  · rintro ⟨s, t, hst, hs, ht⟩
    exact ⟨φ s, φ t, φ.strictMono hst, (hc s).symm ▸ hs,
      (hc t).symm ▸ ht⟩
  · rintro ⟨s, t, hst, hs, ht⟩
    refine ⟨φ.symm s, φ.symm t, φ.symm.strictMono hst, ?_, ?_⟩
    · simpa [hc] using hs
    · simpa [hc] using ht

/-- On one probability-one event, the spatial set of multiple visits of the
zero-cone area-time curve has Lebesgue measure zero. -/
theorem ae_zeroCone_volume_multiVisitPoints_eq_zero
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, volume (multiVisitPoints (η₀ ω)) = 0 := by
  filter_upwards [D.areaParam₀, ae_bundle_volume_multiVisitPoints_eq_zero D]
    with ω hparam hnull
  obtain ⟨φ, -, hφ⟩ := hparam.1
  rwa [multiVisitPoints_reparam φ hφ]

/-- The fixed-point uniqueness statement also passes through the zero-cone
time change, so pointwise conditional laws may use the primed event. -/
theorem ae_zeroCone_uniqueVisit_fixed
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (z : ℂ) :
    ∀ᵐ ω ∂P, z ∉ multiVisitPoints (η₀ ω) := by
  filter_upwards [D.areaParam₀, ae_bundle_uniqueVisit_fixed D z]
    with ω hparam hunique
  obtain ⟨φ, -, hφ⟩ := hparam.1
  rwa [multiVisitPoints_reparam φ hφ]

/-- Fixed-point masked variables agree a.s.; this is the bridge from
Lemma 4.9's first-hit conditional moments to the all-visit version. -/
theorem ae_maskedUStarPrime_eq_masked_fixed
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) :
    maskedUStarPrime D hγ ε q ζ z =ᵐ[P]
      maskedUStar D hγ ε q ζ z := by
  filter_upwards [D.spaceFilling, D.areaParam₀,
    ae_zeroCone_uniqueVisit_fixed D z] with ω hspace hparam hunique
  obtain ⟨φ, -, hφ⟩ := hparam.1
  have hsurj : Function.Surjective (η₀ ω) := by
    intro w
    obtain ⟨t, ht⟩ := hspace.1 w
    exact ⟨φ.symm t, by simpa [hφ] using ht⟩
  have htrans : Filter.Tendsto (η₀ ω) (Filter.cocompact ℝ)
      (Filter.cocompact ℂ) := by
    have hφt : Filter.Tendsto φ (Filter.cocompact ℝ) (Filter.cocompact ℝ) :=
      φ.toHomeomorph.isClosedEmbedding.tendsto_cocompact
    have hηfun : (η₀ ω : ℝ → ℂ) = (ηL ω) ∘ φ := funext hφ
    rw [hηfun]
    exact hspace.2.1.comp hφt
  have hhit : (η₀ ω) (hitTime (η₀ ω) z) = z :=
    hitTime_spec (η₀ ω).continuous htrans (hsurj z)
  have hevent := localEventPrime_iff_localEvent_of_not_multi
    D hγ ε q ζ ω z hhit hunique
  by_cases hω : ω ∈ localEventPrime D hγ ε q ζ z
  · have hω' := hevent.mp hω
    simp only [maskedUStarPrime, maskedUStar,
      Set.indicator_of_mem hω, Set.indicator_of_mem hω']
    exact uStarPrime_eq_uStar_of_not_multi ε η₀ ω z hhit hunique
  · have hω' : ω ∉ localEvent D hγ ε q ζ z :=
      fun h => hω (hevent.mpr h)
    simp only [maskedUStarPrime, maskedUStar,
      Set.indicator_of_notMem hω, Set.indicator_of_notMem hω']

/-- The (4.22) masked integral is likewise unchanged when all geometric
tests and the density use all visits. -/
theorem ae_integral_maskedPrime_eq_masked
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 2)
    (ε q ζ : ℝ) (domain : Set ℂ) (f : ℂ → ℝ) :
    ∀ᵐ ω ∂P,
      (∫ z in domain, f z *
        (localEventPrime D hγ ε q ζ z).indicator
          (fun ω' => uStarPrime ε η₀ ω' z) ω) =
      ∫ z in domain, f z * maskedUStar D hγ ε q ζ z ω := by
  filter_upwards [D.spaceFilling, D.areaParam₀,
    ae_zeroCone_volume_multiVisitPoints_eq_zero D] with ω hspace hparam hnull
  obtain ⟨φ, -, hφ⟩ := hparam.1
  have hsurj : Function.Surjective (η₀ ω) := by
    intro z
    obtain ⟨t, ht⟩ := hspace.1 z
    exact ⟨φ.symm t, by simpa [hφ] using ht⟩
  have htrans : Filter.Tendsto (η₀ ω) (Filter.cocompact ℝ)
      (Filter.cocompact ℂ) := by
    have hφt : Filter.Tendsto φ (Filter.cocompact ℝ) (Filter.cocompact ℝ) :=
      φ.toHomeomorph.isClosedEmbedding.tendsto_cocompact
    have hηfun : (η₀ ω : ℝ → ℂ) = (ηL ω) ∘ φ := funext hφ
    rw [hηfun]
    exact hspace.2.1.comp hφt
  change (∫ z, f z * (localEventPrime D hγ ε q ζ z).indicator
      (fun ω' => uStarPrime ε η₀ ω' z) ω ∂volume.restrict domain) =
    ∫ z, f z * maskedUStar D hγ ε q ζ z ω ∂volume.restrict domain
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr hnull)] with z hz
  have hhit : (η₀ ω) (hitTime (η₀ ω) z) = z :=
    hitTime_spec (η₀ ω).continuous htrans (hsurj z)
  have hevent := localEventPrime_iff_localEvent_of_not_multi
    D hγ ε q ζ ω z hhit hz
  by_cases hω : ω ∈ localEventPrime D hγ ε q ζ z
  · have hω' := hevent.mp hω
    simp only [maskedUStar, Set.indicator_of_mem hω,
      Set.indicator_of_mem hω']
    rw [uStarPrime_eq_uStar_of_not_multi ε η₀ ω z hhit hz]
  · have hω' : ω ∉ localEvent D hγ ε q ζ z :=
      fun h => hω (hevent.mpr h)
    simp only [maskedUStar, Set.indicator_of_notMem hω,
      Set.indicator_of_notMem hω']

end MatedCRTHarmonic.GMS4.Canonical

