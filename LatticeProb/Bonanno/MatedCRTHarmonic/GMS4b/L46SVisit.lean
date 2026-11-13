/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46SVisit at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Lemma46

/-!
# The DMS point-visit bound for the mating-of-trees curve

DMS [14, Lemma 8.13 and (8.9)] give a deterministic upper bound, depending on `γ`, for visits to
each point by the Lebesgue-parametrized space-filling SLE curve. The frozen
bundle v2 already includes this source input in `visitBound`; the adapter below
changes only the time parameter.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace MatedCRTHarmonic.GMS4b

/-- DMS Lemma 8.13 plus (8.9), on the bundle's Lebesgue-time curve `ηL`.
The coupling's `visitBound` field supplies this predicate. -/
def VisitBound {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (γ : ℝ) (k : ℕ) {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (_D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) : Prop :=
  ∀ᵐ ω ∂P, ∀ z : ℂ, ((ηL ω) ⁻¹' {z}).encard ≤ k

/-- The v2 frozen bundle supplies the source visit bound. -/
theorem VisitBound.of_bundle {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ k : ℕ, VisitBound γ k D := D.visitBound

/-- The bundle's increasing area-time change preserves every fiber cardinality;
therefore a DMS visit bound for `ηL` also holds for the quantum-area curve `η`. -/
theorem VisitBound.areaParam {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} {k : ℕ} {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hvisit : VisitBound γ k D) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, ((η ω) ⁻¹' {z}).encard ≤ k := by
  filter_upwards [hvisit, D.areaParam] with ω hbound harea
  obtain ⟨φ, _, hη⟩ := harea.1
  intro z
  have hfiber : (η ω) ⁻¹' {z} = φ ⁻¹' ((ηL ω) ⁻¹' {z}) := by
    ext t
    simp only [mem_preimage, mem_singleton_iff]
    rw [hη]
  rw [hfiber, Set.encard_preimage_of_bijective φ.bijective]
  exact hbound z

/-- A time belongs to at most two closed mesh intervals (only grid times
belong to two). -/
theorem mesh_cells_at_time_encard_le_two {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    {x : ℤ | t ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x)}.encard ≤ 2 := by
  have hsub : {x : ℤ | t ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x)} ⊆
      Icc ⌈t / ε⌉ (⌈t / ε⌉ + 1) := by
    intro x hx
    have hleft : (x : ℝ) - 1 ≤ t / ε := by
      apply (le_div_iff₀ hε).2
      nlinarith [hx.1]
    have hright : t / ε ≤ (x : ℝ) := by
      apply (div_le_iff₀ hε).2
      nlinarith [hx.2]
    have hlow : ⌈t / ε⌉ ≤ x := Int.ceil_le.mpr hright
    have hhigh : x ≤ ⌈t / ε⌉ + 1 := by
      have hc := Int.le_ceil (t / ε)
      have hr : (x : ℝ) ≤ (⌈t / ε⌉ : ℝ) + 1 := by linarith
      exact_mod_cast hr
    exact ⟨hlow, hhigh⟩
  calc
    _ ≤ (Icc ⌈t / ε⌉ (⌈t / ε⌉ + 1) : Set ℤ).encard := Set.encard_le_encard hsub
    _ = 2 := by
      rw [Set.encard_Icc, Int.card_Icc]
      have hi : ⌈t / ε⌉ + 1 + 1 - ⌈t / ε⌉ = (2 : ℤ) := by omega
      rw [hi]
      norm_num

/-- A point with at most `k` time visits belongs to at most `2k` closed
mesh cells. The factor two accounts exactly for visits at grid times. -/
theorem cells_through_point_encard_le_two_mul {η : ℝ → ℂ} {ε : ℝ}
    (hε : 0 < ε) {z : ℂ} {k : ℕ}
    (hvisit : (η ⁻¹' {z}).encard ≤ k) :
    {x : ℤ | z ∈ cellOf ε η x}.encard ≤ 2 * k := by
  let T : Set ℝ := η ⁻¹' {z}
  let S : ℝ → Set ℤ := fun t =>
    {x | t ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x)}
  have hfin : T.Finite := Set.finite_of_encard_le_coe hvisit
  have hsub : {x : ℤ | z ∈ cellOf ε η x} ⊆ ⋃ t ∈ T, S t := by
    intro x hx
    obtain ⟨t, ht, hηt⟩ := hx
    simp only [Set.mem_iUnion]
    exact ⟨t, hηt, ht⟩
  calc
    {x : ℤ | z ∈ cellOf ε η x}.encard ≤ (⋃ t ∈ T, S t).encard :=
      Set.encard_le_encard hsub
    _ ≤ ∑ t ∈ hfin.toFinset, (S t).encard := by
      simpa only [Set.Finite.mem_toFinset] using
        hfin.toFinset.set_encard_biUnion_le S
    _ ≤ ∑ _t ∈ hfin.toFinset, (2 : ℕ∞) := by
      apply Finset.sum_le_sum
      intro t _
      exact mesh_cells_at_time_encard_le_two hε t
    _ = 2 * T.encard := by
      rw [hfin.encard_eq_coe_toFinset_card]
      simp [mul_comm]
    _ ≤ 2 * k := by gcongr

end MatedCRTHarmonic.GMS4b
