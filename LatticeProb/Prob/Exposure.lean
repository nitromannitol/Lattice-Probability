/-
Several fresh coordinates of an infinite product at once.

`LatticeProb/Prob/Coordinate.lean` peels ONE coordinate off a function that does
not read it.  What an exposure argument needs is the same statement for a whole
finite family of unread coordinates at once: the values read at fresh indices are
independent of everything already exposed, and each has its own law.  That is
the product rule below, in three forms: for the measure of an event, for the
integral of a function, and for the integral of a function that also reads a
second, independent, source of randomness.

"Already exposed" is again stated as invariance under overwriting, one unread
coordinate at a time: `F (Function.update ω j (c j)) = F ω` for every `j` in the
family.  That is how it arises in the lattice models, where the event that the
odometer has reached the `j`-th instruction at a site does not depend on that
instruction, and it is what makes the statement usable without naming the
sigma-algebra the exposure generates: the identity holds against EVERY bounded
function invariant in that sense, which is the conditional-expectation statement.
-/
import Mathlib
import LatticeProb.Prob.Coordinate
import LatticeProb.Prob.Exploration

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- The event that a finite family of coordinates lands in prescribed sets is
measurable. -/
theorem measurableSet_evalBox (s : Finset ι) (t : ∀ i, Set (X i))
    (ht : ∀ i, MeasurableSet (t i)) :
    MeasurableSet {ω : Π i, X i | ∀ j ∈ s, ω j ∈ t j} := by
  classical
  have hrw : {ω : Π i, X i | ∀ j ∈ s, ω j ∈ t j} = ⋂ j ∈ s, {ω : Π i, X i | ω j ∈ t j} := by
    ext ω
    simp
  rw [hrw]
  exact MeasurableSet.biInter (Finset.countable_toSet s)
    fun j _ => (measurable_pi_apply j) (ht j)

omit [∀ i, MeasurableSpace (X i)] in
/-- Overwriting a coordinate outside the family does not move the event. -/
theorem evalBox_update_of_notMem [DecidableEq ι] {s : Finset ι} {t : ∀ i, Set (X i)}
    {a : ι} (ha : a ∉ s) (v : X a) (ω : Π i, X i) :
    Function.update ω a v ∈ {ω : Π i, X i | ∀ j ∈ s, ω j ∈ t j}
      ↔ ω ∈ {ω : Π i, X i | ∀ j ∈ s, ω j ∈ t j} := by
  constructor
  · intro h j hj
    have hne : j ≠ a := fun hEq => ha (hEq ▸ hj)
    have := h j hj
    rwa [Function.update_of_ne hne] at this
  · intro h j hj
    have hne : j ≠ a := fun hEq => ha (hEq ▸ hj)
    rw [Function.update_of_ne hne]
    exact h j hj

/-- **The product rule for an event.**  An event that reads none of a finite
family of coordinates is independent of them, and they are independent of each
other, so the measure of the intersection is the product. -/
theorem measure_inter_evalBox_of_update_invariant [DecidableEq ι]
    (c : ∀ i, X i) {A : Set (Π i, X i)} (hA : MeasurableSet A)
    (t : ∀ i, Set (X i)) (ht : ∀ i, MeasurableSet (t i)) :
    ∀ s : Finset ι, (∀ j ∈ s, ∀ ω : Π i, X i, Function.update ω j (c j) ∈ A ↔ ω ∈ A) →
      Measure.infinitePi μ (A ∩ {ω : Π i, X i | ∀ j ∈ s, ω j ∈ t j})
        = Measure.infinitePi μ A * ∏ j ∈ s, μ j (t j) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      have hbox : {ω : Π i, X i | ∀ j ∈ (∅ : Finset ι), ω j ∈ t j} = Set.univ := by
        ext ω
        simp
      rw [hbox, Set.inter_univ, Finset.prod_empty, mul_one]
  | insert a s ha ih =>
      intro hinv
      have hinv' : ∀ j ∈ s, ∀ ω : Π i, X i, Function.update ω j (c j) ∈ A ↔ ω ∈ A :=
        fun j hj => hinv j (Finset.mem_insert_of_mem hj)
      have hsplit : A ∩ {ω : Π i, X i | ∀ j ∈ insert a s, ω j ∈ t j}
          = (A ∩ {ω : Π i, X i | ∀ j ∈ s, ω j ∈ t j}) ∩ {ω : Π i, X i | ω a ∈ t a} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert]
        constructor
        · rintro ⟨hA', hbox⟩
          exact ⟨⟨hA', fun j hj => hbox j (Or.inr hj)⟩, hbox a (Or.inl rfl)⟩
        · rintro ⟨⟨hA', hbox⟩, hain⟩
          refine ⟨hA', fun j hj => ?_⟩
          rcases hj with rfl | hj
          · exact hain
          · exact hbox j hj
      rw [hsplit]
      have hmeas : MeasurableSet (A ∩ {ω : Π i, X i | ∀ j ∈ s, ω j ∈ t j}) :=
        hA.inter (measurableSet_evalBox s t ht)
      have hinvA : ∀ ω : Π i, X i,
          Function.update ω a (c a) ∈ A ∩ {ω : Π i, X i | ∀ j ∈ s, ω j ∈ t j}
            ↔ ω ∈ A ∩ {ω : Π i, X i | ∀ j ∈ s, ω j ∈ t j} := by
        intro ω
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨(hinv a (Finset.mem_insert_self a s) ω).mp h1,
            (evalBox_update_of_notMem (X := X) (t := t) ha (c a) ω).mp h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨(hinv a (Finset.mem_insert_self a s) ω).mpr h1,
            (evalBox_update_of_notMem (X := X) (t := t) ha (c a) ω).mpr h2⟩
      rw [measure_inter_eval_of_update_invariant μ (c a) hmeas hinvA (ht a), ih hinv',
        Finset.prod_insert ha]
      ring

/-! ### The integral forms -/

omit [∀ i, MeasurableSpace (X i)] in
/-- The product of the indicators of a finite family of coordinates is the
indicator of the event that all of them land in their sets. -/
theorem prod_indicator_eval_eq {Ω : Type*} (s : Finset ι) (t : ∀ i, Set (X i))
    (pr : Ω → Π i, X i) (F : Ω → ℝ) :
    (fun p => F p * ∏ j ∈ s, Set.indicator (t j) (fun _ => (1 : ℝ)) (pr p j))
      = Set.indicator {p : Ω | ∀ j ∈ s, pr p j ∈ t j} F := by
  classical
  funext p
  by_cases h : p ∈ {p : Ω | ∀ j ∈ s, pr p j ∈ t j}
  · have h' : ∀ j ∈ s, pr p j ∈ t j := h
    have hone : ∀ j ∈ s, Set.indicator (t j) (fun _ => (1 : ℝ)) (pr p j) = 1 :=
      fun j hj => Set.indicator_of_mem (h' j hj) _
    rw [Finset.prod_congr rfl hone, Finset.prod_const_one, mul_one,
      Set.indicator_of_mem h]
  · have h' : ¬ ∀ j ∈ s, pr p j ∈ t j := h
    obtain ⟨j0, hj0, hnot⟩ : ∃ j0 ∈ s, pr p j0 ∉ t j0 := by
      by_contra hc
      exact h' fun j hj => by
        by_contra hcc
        exact hc ⟨j, hj, hcc⟩
    have hzero : Set.indicator (t j0) (fun _ => (1 : ℝ)) (pr p j0) = 0 :=
      Set.indicator_of_notMem hnot _
    rw [Finset.prod_eq_zero hj0 hzero, mul_zero, Set.indicator_of_notMem h]

/-- **The product rule for an integral.**  A function that reads none of a finite
family of coordinates integrates against the indicators of those coordinates as a
product: the values read at fresh indices are independent of everything the
function sees, and of each other. -/
theorem integral_mul_prod_indicator_eval [DecidableEq ι]
    (c : ∀ i, X i) (F : (Π i, X i) → ℝ) (hF : Measurable F)
    (t : ∀ i, Set (X i)) (ht : ∀ i, MeasurableSet (t i)) :
    ∀ s : Finset ι, (∀ j ∈ s, ∀ ω : Π i, X i, F (Function.update ω j (c j)) = F ω) →
      ∫ ω, F ω * ∏ j ∈ s, Set.indicator (t j) (fun _ => (1 : ℝ)) (ω j)
          ∂(Measure.infinitePi μ)
        = (∏ j ∈ s, (μ j (t j)).toReal) * ∫ ω, F ω ∂(Measure.infinitePi μ) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | insert a s ha ih =>
      intro hinv
      have hinv' : ∀ j ∈ s, ∀ ω : Π i, X i, F (Function.update ω j (c j)) = F ω :=
        fun j hj => hinv j (Finset.mem_insert_of_mem hj)
      set G : (Π i, X i) → ℝ :=
        fun ω => F ω * ∏ j ∈ s, Set.indicator (t j) (fun _ => (1 : ℝ)) (ω j) with hG
      have hGeq : G = Set.indicator {ω : Π i, X i | ∀ j ∈ s, ω j ∈ t j} F := by
        rw [hG]
        exact prod_indicator_eval_eq (X := X) s t (fun ω => ω) F
      have hGmeas : Measurable G := by
        rw [hGeq]
        exact hF.indicator (measurableSet_evalBox (X := X) s t ht)
      have hGinv : ∀ ω : Π i, X i, G (Function.update ω a (c a)) = G ω := by
        intro ω
        rw [hGeq]
        by_cases h : ω ∈ {ω : Π i, X i | ∀ j ∈ s, ω j ∈ t j}
        · have h' : Function.update ω a (c a) ∈ {ω : Π i, X i | ∀ j ∈ s, ω j ∈ t j} :=
            (evalBox_update_of_notMem (X := X) (t := t) ha (c a) ω).mpr h
          rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
          exact hinv a (Finset.mem_insert_self a s) ω
        · have h' : Function.update ω a (c a) ∉ {ω : Π i, X i | ∀ j ∈ s, ω j ∈ t j} := fun hc =>
            h ((evalBox_update_of_notMem (X := X) (t := t) ha (c a) ω).mp hc)
          rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
      have hrw : ∀ ω : Π i, X i,
          F ω * ∏ j ∈ insert a s, Set.indicator (t j) (fun _ => (1 : ℝ)) (ω j)
            = G ω * Set.indicator (t a) (fun _ => (1 : ℝ)) (ω a) := by
        intro ω
        rw [Finset.prod_insert ha, hG]
        ring
      simp only [hrw]
      rw [integral_mul_indicator_eval μ a (c a) G hGmeas hGinv (ht a), ih hinv',
        Finset.prod_insert ha]
      ring

/-- **The product rule on a product space.**  The same factorization when the
function also reads a second, independent, source of randomness, which is the
shape a driving law built as a product of an initial configuration, an
instruction stack and an auxiliary family sits in. -/
theorem integral_mul_prod_indicator_eval_prod [DecidableEq ι] {Ω : Type*}
    [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (c : ∀ i, X i) (F : (Π i, X i) × Ω → ℝ) (hF : Measurable F)
    (hFint : Integrable F ((Measure.infinitePi μ).prod ν))
    (t : ∀ i, Set (X i)) (ht : ∀ i, MeasurableSet (t i)) :
    ∀ s : Finset ι, (∀ j ∈ s, ∀ (ω : Π i, X i) (y : Ω),
        F (Function.update ω j (c j), y) = F (ω, y)) →
      ∫ p, F p * ∏ j ∈ s, Set.indicator (t j) (fun _ => (1 : ℝ)) (p.1 j)
          ∂((Measure.infinitePi μ).prod ν)
        = (∏ j ∈ s, (μ j (t j)).toReal) * ∫ p, F p ∂((Measure.infinitePi μ).prod ν) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | insert a s ha ih =>
      intro hinv
      have hinv' : ∀ j ∈ s, ∀ (ω : Π i, X i) (y : Ω),
          F (Function.update ω j (c j), y) = F (ω, y) :=
        fun j hj => hinv j (Finset.mem_insert_of_mem hj)
      set S : Set ((Π i, X i) × Ω) := {p | ∀ j ∈ s, p.1 j ∈ t j} with hS
      have hSmeas : MeasurableSet S := by
        rw [hS]
        exact measurable_fst (measurableSet_evalBox (X := X) s t ht)
      set G : (Π i, X i) × Ω → ℝ :=
        fun p => F p * ∏ j ∈ s, Set.indicator (t j) (fun _ => (1 : ℝ)) (p.1 j) with hG
      have hGeq : G = Set.indicator S F := by
        rw [hG, hS]
        exact prod_indicator_eval_eq (X := X) s t (fun p => p.1) F
      have hGmeas : Measurable G := by
        rw [hGeq]
        exact hF.indicator hSmeas
      have hGint : Integrable G ((Measure.infinitePi μ).prod ν) := by
        rw [hGeq]
        exact hFint.indicator hSmeas
      have hGinv : ∀ (ω : Π i, X i) (y : Ω), G (Function.update ω a (c a), y) = G (ω, y) := by
        intro ω y
        rw [hGeq]
        by_cases h : ((ω, y) : (Π i, X i) × Ω) ∈ S
        · have hmem : ∀ j ∈ s, ω j ∈ t j := h
          have h' : ((Function.update ω a (c a), y) : (Π i, X i) × Ω) ∈ S := by
            intro j hj
            have hne : j ≠ a := fun hEq => ha (hEq ▸ hj)
            show Function.update ω a (c a) j ∈ t j
            rw [Function.update_of_ne hne]
            exact hmem j hj
          rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
          exact hinv a (Finset.mem_insert_self a s) ω y
        · have h' : ((Function.update ω a (c a), y) : (Π i, X i) × Ω) ∉ S := by
            intro hc
            refine h fun j hj => ?_
            have hne : j ≠ a := fun hEq => ha (hEq ▸ hj)
            have hcj : Function.update ω a (c a) j ∈ t j := hc j hj
            rwa [Function.update_of_ne hne] at hcj
          rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
      have hrw : ∀ p : (Π i, X i) × Ω,
          F p * ∏ j ∈ insert a s, Set.indicator (t j) (fun _ => (1 : ℝ)) (p.1 j)
            = G p * Set.indicator (t a) (fun _ => (1 : ℝ)) (p.1 a) := by
        intro p
        rw [Finset.prod_insert ha, hG]
        ring
      simp only [hrw]
      rw [integral_mul_indicator_eval_prod μ ν a (c a) G hGmeas hGint
        (fun ω y => hGinv ω y) (ht a), ih hinv', Finset.prod_insert ha]
      ring

end LatticeProb
