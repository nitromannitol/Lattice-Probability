import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.SymmDiff

/-!
# Finite flips of Bernoulli product configurations

Interior Bernoulli laws preserve null sets under finite coordinate flips. On a countable
index set, every measurable conull event therefore has a conull subset stable under all
finite flips. The proof separates a finite full-support patch from its independent tail.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.BernoulliFiniteFlip

open MeasureTheory ProbabilityTheory
open scoped BigOperators symmDiff

/-- Flip precisely the coordinates belonging to the finite set. -/
noncomputable def flip {ι : Type*} (F : Finset ι) (ω : ι → Bool) : ι → Bool := by
  classical
  exact fun e => if e ∈ F then !(ω e) else ω e

/-- A finite coordinate flip is measurable for the product sigma algebra. -/
lemma measurable_flip {ι : Type*} (F : Finset ι) : Measurable (flip F) := by
  classical
  apply measurable_pi_iff.mpr
  intro e
  by_cases he : e ∈ F
  · simpa only [flip, if_pos he, Function.comp_def] using
      (measurable_of_finite (fun b : Bool => !b)).comp
        (measurable_pi_apply (X := fun _ : ι => Bool) e)
  · simpa only [flip, if_neg he] using measurable_pi_apply (X := fun _ : ι => Bool) e

/-- Applying the same finite flip twice recovers the configuration. -/
lemma flip_involutive {ι : Type*} (F : Finset ι) : Function.Involutive (flip F) := by
  classical
  intro ω
  funext e
  by_cases he : e ∈ F <;> simp [flip, he]

-- Core section argument. α may be any countable full-support patch.
/-- A measurable map on a countable full-support patch preserves product null sets. -/
lemma patch_null_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] (μ : Measure α) (ν : Measure β) [SFinite ν]
    (hμ : ∀ a, μ {a} ≠ 0) (τ : α → α) (hτ : Measurable τ)
    {N : Set (α × β)} (hN : MeasurableSet N) (hzero : μ.prod ν N = 0) :
    μ.prod ν ((fun z : α × β => (τ z.1, z.2)) ⁻¹' N) = 0 := by
  apply (Measure.measure_prod_null
    (hN.preimage ((hτ.comp measurable_fst).prodMk measurable_snd))).mpr
  have hall := ae_iff_of_countable.mp ((Measure.measure_prod_null hN).mp hzero)
  exact ae_of_all μ (fun a => hall (τ a) (hμ (τ a)))

/-- The independent Boolean product law with constant success probability. -/
noncomputable def patchLaw (ι : Type*) (p : unitInterval) : Measure (ι → Bool) :=
  Measure.infinitePi (fun _ : ι => bernoulliMeasure true false p)

/-- Every finite patch has positive mass at every configuration when the parameter is interior. -/
lemma patch_singleton_ne_zero {ι : Type*} [Fintype ι] (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (ω : ι → Bool) :
    patchLaw ι p {ω} ≠ 0 := by
  rw [patchLaw, Measure.infinitePi_singleton_of_fintype]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have htrue : unitInterval.toNNReal p ≠ 0 := by
    intro h
    have hreal := congrArg (fun q : NNReal => (q : ℝ)) h
    simp only [unitInterval.coe_toNNReal, NNReal.coe_zero] at hreal
    exact hp0.ne' hreal
  have hfalse : unitInterval.toNNReal (unitInterval.symm p) ≠ 0 := by
    intro h
    have hreal := congrArg (fun q : NNReal => (q : ℝ)) h
    simp only [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq, NNReal.coe_zero] at hreal
    exact (sub_pos.mpr hp1).ne' hreal
  cases ω i <;>
    simp [bernoulliMeasure_apply p (measurableSet_singleton _), htrue, hfalse]

/-- Finite patch flips preserve and reflect null sets with an arbitrary s-finite tail. -/
lemma finite_patch_flip_null_iff {ι β : Type*} [Fintype ι] [MeasurableSpace β]
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (ν : Measure β) [SFinite ν] (F : Finset ι)
    {N : Set ((ι → Bool) × β)} (hN : MeasurableSet N) :
    (patchLaw ι p).prod ν ((fun z : (ι → Bool) × β => (flip F z.1, z.2)) ⁻¹' N) = 0 ↔
      (patchLaw ι p).prod ν N = 0 := by
  let T : (ι → Bool) × β → (ι → Bool) × β := fun z => (flip F z.1, z.2)
  have hT : Measurable T := (measurable_flip F |>.comp measurable_fst).prodMk measurable_snd
  have hinv : ∀ z, T (T z) = z := by
    intro z
    exact Prod.ext (flip_involutive F z.1) rfl
  have hpre : T ⁻¹' (T ⁻¹' N) = N := by
    ext z
    simp only [Set.mem_preimage, hinv]
  constructor
  · intro hz
    have h := patch_null_preimage (patchLaw ι p) ν
      (patch_singleton_ne_zero p hp0 hp1) (flip F) (measurable_flip F) (hN.preimage hT) hz
    change (patchLaw ι p).prod ν (T ⁻¹' (T ⁻¹' N)) = 0 at h
    rwa [hpre] at h
  · exact patch_null_preimage (patchLaw ι p) ν
      (patch_singleton_ne_zero p hp0 hp1) (flip F) (measurable_flip F) hN

/-- The simultaneous finite-flip event is a countable intersection of measurable preimages. -/
lemma measurableSet_all_flips {ι : Type*} [Countable ι]
    {A : Set (ι → Bool)} (hA : MeasurableSet A) :
    MeasurableSet {ω | ∀ F : Finset ι, flip F ω ∈ A} := by
  have hset : {ω | ∀ F : Finset ι, flip F ω ∈ A} =
      ⋂ F : Finset ι, flip F ⁻¹' A := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  exact MeasurableSet.iInter (fun F => hA.preimage (measurable_flip F))

/-- The Boolean product law is a probability measure. -/
instance patchLaw_isProbabilityMeasure (ι : Type*) (p : unitInterval) :
    IsProbabilityMeasure (patchLaw ι p) := by
  unfold patchLaw
  infer_instance

/-- Splitting any product probability law by an arbitrary coordinate predicate. -/
lemma infinitePi_split {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (q : ι → Prop) [DecidablePred q] :
    (Measure.infinitePi μ).map (MeasurableEquiv.piEquivPiSubtypeProd X q) =
      (Measure.infinitePi (fun i : Subtype q => μ i)).prod
        (Measure.infinitePi (fun i : {i // ¬q i} => μ i)) := by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]
  symm
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd X q
  have hpre : e.symm ⁻¹' Set.pi (s : Set ι) t =
      (Set.pi (s.subtype q : Set (Subtype q)) (fun i => t i)) ×ˢ
      (Set.pi (s.subtype (fun i => ¬q i) : Set {i // ¬q i}) (fun i => t i)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod,
      Finset.mem_coe, Finset.mem_subtype]
    constructor
    · intro h
      constructor
      · intro i hi
        have := h i hi
        simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
          i.property] using this
      · intro i hi
        have := h i hi
        simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
          i.property] using this
    · rintro ⟨h₁, h₂⟩ i hi
      by_cases hq : q i
      · simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hq]
          using h₁ ⟨i, hq⟩ hi
      · simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hq]
          using h₂ ⟨i, hq⟩ hi
  rw [Measure.map_apply e.symm.measurable (.pi s.countable_toSet (fun i _ => ht i)),
    hpre, Measure.prod_prod,
    Measure.infinitePi_pi (fun i : Subtype q => μ i)
      (s := s.subtype q) (t := fun i => t i) (fun i _ => ht i),
    Measure.infinitePi_pi (fun i : {i // ¬q i} => μ i)
      (s := s.subtype (fun i => ¬q i)) (t := fun i => t i) (fun i _ => ht i),
    Finset.prod_subtype_eq_prod_filter (s := s) (p := q) (fun i => μ i (t i)),
    Finset.prod_subtype_eq_prod_filter (s := s) (p := fun i => ¬q i) (fun i => μ i (t i)),
    Finset.prod_filter_mul_prod_filter_not]

/-- Split the configuration into the finite patch and its complementary coordinates. -/
noncomputable def split {ι : Type*} (F : Finset ι) :
    (ι → Bool) ≃ᵐ ((F → Bool) × ({i // i ∉ F} → Bool)) := by
  classical
  exact MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Bool) (fun i => i ∈ F)

/-- The coordinate split transports a finite flip to the full flip of its finite patch. -/
lemma split_flip {ι : Type*} (F : Finset ι) (ω : ι → Bool) :
    split F (flip F ω) = (flip Finset.univ (split F ω).1, (split F ω).2) := by
  classical
  apply Prod.ext
  · funext i
    simp [split, flip, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd]
  · funext i
    simp [split, flip, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd, i.property]

/-- The two complementary coordinate blocks have the corresponding product law. -/
lemma split_law {ι : Type*} (F : Finset ι) (p : unitInterval) :
    (patchLaw ι p).map (split F) =
      (patchLaw F p).prod (patchLaw {i // i ∉ F} p) := by
  classical
  exact infinitePi_split (fun _ : ι => bernoulliMeasure true false p) (fun i => i ∈ F)

/-- Full product null sets are preserved in both directions by any finite flip. -/
lemma full_product_flip_null_iff {ι : Type*}
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (F : Finset ι) {N : Set (ι → Bool)} (hN : MeasurableSet N) :
    patchLaw ι p (flip F ⁻¹' N) = 0 ↔ patchLaw ι p N = 0 := by
  classical
  let e := split F
  let M := e.symm ⁻¹' N
  let T : (F → Bool) × ({i // i ∉ F} → Bool) →
      (F → Bool) × ({i // i ∉ F} → Bool) :=
    fun z => (flip Finset.univ z.1, z.2)
  have hM : MeasurableSet M := hN.preimage e.symm.measurable
  have hT : Measurable T :=
    ((measurable_flip Finset.univ).comp measurable_fst).prodMk measurable_snd
  have hpre : e ⁻¹' M = N := by
    ext ω
    simp only [M, Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
  have hflippre : e ⁻¹' (T ⁻¹' M) = flip F ⁻¹' N := by
    ext ω
    change e.symm (T (e ω)) ∈ N ↔ flip F ω ∈ N
    have hcomm : T (e ω) = e (flip F ω) := (split_flip F ω).symm
    rw [hcomm, MeasurableEquiv.symm_apply_apply]
  have htransport (B : Set ((F → Bool) × ({i // i ∉ F} → Bool)))
      (hB : MeasurableSet B) :
      patchLaw ι p (e ⁻¹' B) =
        (patchLaw F p).prod (patchLaw {i // i ∉ F} p) B := by
    rw [← Measure.map_apply e.measurable hB, split_law]
  rw [← hflippre, htransport _ (hM.preimage hT), ← hpre, htransport _ hM]
  exact finite_patch_flip_null_iff p hp0 hp1
    (patchLaw {i // i ∉ F} p) Finset.univ hM

/-- Every conull measurable event holds simultaneously after all finite coordinate flips. -/
lemma full_product_all_flips {ι : Type*} [Countable ι]
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {A : Set (ι → Bool)} (hA : MeasurableSet A) (hfull : patchLaw ι p A = 1) :
    patchLaw ι p {ω | ∀ F : Finset ι, flip F ω ∈ A} = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_all_flips hA)).mp
  apply ae_all_iff.mpr
  intro F
  rw [ae_iff]
  change patchLaw ι p (flip F ⁻¹' Aᶜ) = 0
  exact (full_product_flip_null_iff p hp0 hp1 F hA.compl).mpr
    ((prob_compl_eq_zero_iff hA).mpr hfull)

/-- The finite flip has the literal pointwise conditional formula. -/
theorem flip_apply {ι : Type*} [DecidableEq ι] (F : Finset ι) (ω : ι → Bool) (e : ι) :
    flip F ω e = if e ∈ F then !(ω e) else ω e := by
  classical
  by_cases he : e ∈ F <;> simp [flip, he]

/-- Flipping no coordinates is the identity. -/
theorem flip_empty {ι : Type*} (ω : ι → Bool) : flip ∅ ω = ω := by
  classical
  funext e
  simp only [flip, Finset.notMem_empty, if_false]

/-- Composition of finite flips is the flip on their symmetric difference. -/
theorem flip_flip {ι : Type*} [DecidableEq ι] (F G : Finset ι) (ω : ι → Bool) :
    flip F (flip G ω) = flip (F ∆ G) ω := by
  classical
  funext e
  by_cases hF : e ∈ F <;> by_cases hG : e ∈ G <;>
    simp [flip, Finset.mem_symmDiff, hF, hG]

/-- The simultaneous event is stable under every finite flip, pointwise. -/
theorem all_flips_stable {ι : Type*} {A : Set (ι → Bool)} {ω : ι → Bool}
    (hω : ∀ F : Finset ι, flip F ω ∈ A) (G : Finset ι) :
    ∀ F : Finset ι, flip F (flip G ω) ∈ A := by
  classical
  intro F
  rw [flip_flip]
  exact hω (F ∆ G)

/-- The simultaneous event is contained in the original event by the empty flip. -/
theorem all_flips_subset {ι : Type*} (A : Set (ι → Bool)) :
    {ω | ∀ F : Finset ι, flip F ω ∈ A} ⊆ A := by
  intro ω hω
  simpa only [flip_empty] using hω ∅

end LatticeProb.BernoulliFiniteFlip
