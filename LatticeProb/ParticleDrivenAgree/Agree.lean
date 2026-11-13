/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.Agree at commit 66d817d. The module paths and the namespace `Parking`
   are renamed (to `LatticeProb.ParticleDrivenAgree`), and proofs are adapted to the Lean and Mathlib
   versions of this repository where needed. -/
import LatticeProb.ParticleDriven
import LatticeProb.ParticleDrivenAgree.Reads
import LatticeProb.ParticleDrivenAgree.DeferredIntegral
import LatticeProb.ParticleDrivenAgree.ParticleMeasurability

/-!
# The two constructions have the same law

The stack construction and the particle-driven construction have the same law.

`parking.tex:645-646` states it.  What makes it true is that the
departures of the stack construction read pairwise distinct stack entries
(`LatticeProb.readIndex_injective`) and that each read looks only at the reads
that precede it in a well-founded dependency once the configuration is fixed,
so the displacements the particles take are independent draws from one law.
That is `LatticeProb.map_revealed_dag`.

Three things have to be arranged before the exploration lemma applies.

- The reads must be defined for EVERY realization, not almost every one, since
  freshness and predictability are pathwise.  The instructions are therefore
  read through `LatticeProb.ParticleDrivenAgree.nbrProj`, which forces every instruction to be a
  neighbour of its site and is the identity almost surely.
- A pair `(p, t)` at which the particle `p` is not active reads no stack entry,
  so the family is enlarged by an auxiliary independent displacement for each
  such pair; the two branches live in the two summands of `LatticeProb.ParticleDrivenAgree.RIdx` and
  never collide.
- The dependency set of `(p, t)` must be FINITE.  It is the pairs `(q, s)` with
  `s < t` and `q` started within `2t² + 3t` of `p`: a read outside that box is
  either unread by the light cone (`LatticeProb.state_agree_box`) or too far to
  have influenced `p`.
-/

open LatticeProb (measurable_from_countable' measurable_of_countable_partition)

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.ParticleDrivenAgree

open LatticeProb Finset

variable {d : ℕ}

/-- A sum type inherits `MeasurableSingletonClass` from its two summands, by checking each
singleton's preimage under `Sum.inl` and `Sum.inr` directly. -/
instance instMeasurableSingletonSum {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) := by
  constructor
  intro x
  rw [measurableSet_sum_iff]
  cases x with
  | inl a =>
      constructor
      · have h : Sum.inl ⁻¹' ({Sum.inl a} : Set (α ⊕ β)) = {a} := by ext b; simp
        rw [h]; exact measurableSet_singleton a
      · have h : Sum.inr ⁻¹' ({Sum.inl a} : Set (α ⊕ β)) = ∅ := by ext b; simp
        rw [h]; exact MeasurableSet.empty
  | inr b =>
      constructor
      · have h : Sum.inl ⁻¹' ({Sum.inr b} : Set (α ⊕ β)) = ∅ := by ext c; simp
        rw [h]; exact MeasurableSet.empty
      · have h : Sum.inr ⁻¹' ({Sum.inr b} : Set (α ⊕ β)) = {b} := by ext c; simp
        rw [h]; exact measurableSet_singleton b

/-- Overwriting one instruction commutes with the neighbour projection. -/
theorem nbrProj_update' (i₀ : Fin d) (σ : Site d × ℕ → Site d) (q₀ : Site d × ℕ)
    (c : Site d) :
    nbrProj i₀ (Function.update σ q₀ c)
      = Function.update (nbrProj i₀ σ) q₀ (if c ∈ nbrFinset q₀.1 then c else q₀.1 + unit i₀) := by
  funext q
  by_cases hq : q = q₀
  · subst hq; simp [nbrProj]
  · simp [nbrProj, Function.update_of_ne hq]

/-! ### The enlarged independent family -/

/-- The coordinates the exploration reads: a stack entry, or the auxiliary
displacement of a pair at which no particle departs. -/
abbrev RIdx (d : ℕ) : Type := (Site d × ℕ) ⊕ (Label d × ℕ)

/-- The stacks of a realization of the enlarged family, every instruction
forced to be a neighbour of its site. -/
def expStack (i₀ : Fin d) (ω : RIdx d → Site d) : Site d × ℕ → Site d :=
  nbrProj i₀ fun q => ω (Sum.inl q)

/-- The driver of the stack construction read off the enlarged family. -/
def expDriver (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (ω : RIdx d → Site d) : Driver d := ⟨η, expStack i₀ ω, ρ⟩

/-- The driver built from the enlarged family always steps to a neighbour, since its
stack comes from `nbrProj`. -/
theorem expDriver_steps (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (ω : RIdx d → Site d) : StepsToNeighbour (expDriver i₀ η ρ ω) :=
  stepsToNeighbour_of_mem fun q => nbrProj_mem i₀ (fun r => ω (Sum.inl r)) q

/-- The coordinate the pair `(p, t)` reads: the stack entry `p` takes in round
`t + 1` when it is active, and its auxiliary displacement otherwise. -/
def expIdxOf (D : Driver d) (a : Label d × ℕ) : RIdx d :=
  if (state D a.2).active a.1 then Sum.inl (readIndex D a.2 a.1) else Sum.inr a

/-- The coordinate the pair `(p, t)` reads, as a function of the family. -/
def expIdx (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (a : Label d × ℕ) (ω : RIdx d → Site d) : RIdx d :=
  expIdxOf (expDriver i₀ η ρ ω) a

/-- The reads that `(p, t)` depends on: the earlier rounds of the particles
started within `2t² + 3t` of `p`. -/
def expDep (η : Site d → ℤ) (a : Label d × ℕ) : Finset (Label d × ℕ) :=
  (candidates η a.1.1 (2 * a.2 * a.2 + 3 * a.2)) ×ˢ Finset.range a.2

/-- The displacement a coordinate reveals. -/
def expG (i₀ : Fin d) : RIdx d → Site d → Site d :=
  Sum.elim (fun q z => (if z ∈ nbrFinset q.1 then z else q.1 + unit i₀) - q.1)
    (fun _ z => z)

/-- The law of the enlarged family: the instruction law at the site of a stack
entry, the displacement law at an auxiliary coordinate. -/
def expLaw (d : ℕ) : RIdx d → Measure (Site d) :=
  Sum.elim (fun q => instructionLaw q.1) (fun _ => LatticeProb.displacementLaw d)

/-! ### The exploration hypotheses -/

/-- `expIdxOf` is measurable in the driver's data, branching on the measurable activity
predicate and composing with the measurable read index. -/
theorem measurable_expIdxOf (a : Label d × ℕ) :
    Measurable fun v : Data d => expIdxOf (toDriver v) a := by
  classical
  obtain ⟨hact, -, -, -⟩ := measurable_state (d := d) a.2
  refine Measurable.ite ?_ ?_ measurable_const
  · exact hact a.1 (measurableSet_singleton true)
  · exact measurable_inl.comp (measurable_readIndex a.2 a.1)

/-- `expIdx` is measurable in the enlarged family `ω`, composing `measurable_expIdxOf` with
the measurable embedding into `expDriver`. -/
theorem expIdx_measurable (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (a : Label d × ℕ) : Measurable (expIdx i₀ η ρ a) := by
  classical
  have hemb : Measurable fun ω : RIdx d → Site d => ((η, expStack i₀ ω, ρ) : Data d) :=
    measurable_const.prodMk
      (((measurable_nbrProj i₀).comp
        (Measurable.of_eval fun q => measurable_pi_apply (Sum.inl q))).prodMk
        measurable_const)
  exact (measurable_expIdxOf a).comp hemb

/-- Distinct pairs `a ≠ b` read distinct coordinates of the enlarged family, using
`readIndex_injective` on the `Sum.inl` branch and injectivity of the two `Sum` summands
elsewhere. -/
theorem expIdx_fresh (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (a b : Label d × ℕ) (ω : RIdx d → Site d) (hab : a ≠ b) :
    expIdx i₀ η ρ a ω ≠ expIdx i₀ η ρ b ω := by
  have hs := expDriver_steps i₀ η ρ ω
  show expIdxOf (expDriver i₀ η ρ ω) a ≠ expIdxOf (expDriver i₀ η ρ ω) b
  unfold expIdxOf
  split_ifs with ha hb hb
  · intro hcon
    obtain ⟨h1, h2⟩ := readIndex_injective hs ha hb (Sum.inl_injective hcon)
    exact hab (Prod.ext h2 h1)
  · exact fun hcon => absurd hcon (by simp)
  · exact fun hcon => absurd hcon (by simp)
  · exact fun hcon => hab (Sum.inr_injective hcon)

/-- The dependency relation `expDep` is well-founded, since it strictly decreases the round
coordinate. -/
theorem expDep_wf (η : Site d → ℤ) :
    WellFounded fun b a : Label d × ℕ => b ∈ expDep η a := by
  have hlt : ∀ a b : Label d × ℕ, b ∈ expDep η a → b.2 < a.2 := by
    intro a b hb
    rw [expDep, Finset.mem_product] at hb
    exact Finset.mem_range.mp hb.2
  exact Subrelation.wf (fun {b a} hb => hlt a b hb)
    (InvImage.wf (fun a : Label d × ℕ => a.2) wellFounded_lt)

/-- **The read of a pair looks only at the reads it depends on.**  Two cases:
either the overwritten site is outside the light cone of `p`, and the states
agree near `p` by `LatticeProb.state_agree_box`, or it is inside it, and then
every departure that could have read that entry is a pair of `expDep`. -/
theorem expIdx_pred (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (a : Label d × ℕ) (ω : RIdx d → Site d) (j : RIdx d) (c : Site d)
    (h : ∀ b ∈ expDep η a, expIdx i₀ η ρ b ω ≠ j) :
    expIdx i₀ η ρ a (Function.update ω j c) = expIdx i₀ η ρ a ω := by
  classical
  set ω' := Function.update ω j c with hω'def
  set D := expDriver i₀ η ρ ω with hDdef
  set D' := expDriver i₀ η ρ ω' with hD'def
  have hsD : StepsToNeighbour D := expDriver_steps i₀ η ρ ω
  have hsD' : StepsToNeighbour D' := expDriver_steps i₀ η ρ ω'
  show expIdxOf D' a = expIdxOf D a
  cases j with
  | inr b =>
      have hst : D' = D := by
        have : (fun r : Site d × ℕ => ω' (Sum.inl r)) = fun r => ω (Sum.inl r) := by
          funext r
          exact Function.update_of_ne (by simp) _ _
        show (⟨η, expStack i₀ ω', ρ⟩ : Driver d) = ⟨η, expStack i₀ ω, ρ⟩
        rw [expStack, expStack, this]
      rw [hst]
  | inl q₀ =>
      have hstack : ∀ q : Site d × ℕ, q ≠ q₀ → D.stack q = D'.stack q := by
        intro q hq
        show nbrProj i₀ (fun r => ω (Sum.inl r)) q = nbrProj i₀ (fun r => ω' (Sum.inl r)) q
        have : ω' (Sum.inl q) = ω (Sum.inl q) :=
          Function.update_of_ne (by simpa using hq) _ _
        show (if ω (Sum.inl q) ∈ nbrFinset q.1 then ω (Sum.inl q) else q.1 + unit i₀)
            = (if ω' (Sum.inl q) ∈ nbrFinset q.1 then ω' (Sum.inl q) else q.1 + unit i₀)
        rw [this]
      have hstate_or : (state D a.2 = state D' a.2) ∨
          (StateAgreeOn (state D a.2) (state D' a.2) a.1.1 (2 * a.2)) := by
        by_cases hfar : q₀.1 ∈ boxFinset a.1.1 (2 * a.2 + 2 * a.2 * a.2)
        · left
          refine state_congr_of_unread (D := D) (D' := D') hsD rfl rfl q₀ hstack a.2 ?_
          intro s hs q hq hr
          have hposq : (state D s).pos q = q₀.1 := congrArg Prod.fst hr
          have hbox : q.1 ∈ boxFinset q₀.1 a.2 := by
            refine mem_boxFinset_iff.mpr fun i' => ?_
            have hb := abs_pos_sub_start_le hsD s q i'
            rw [hposq] at hb
            rw [abs_sub_comm]
            exact hb.trans (by exact_mod_cast Nat.le_of_lt hs)
          have harith : 2 * a.2 + 2 * a.2 * a.2 + a.2 = 2 * a.2 * a.2 + 3 * a.2 := by ring
          have hbox2 : q.1 ∈ boxFinset a.1.1 (2 * a.2 * a.2 + 3 * a.2) := by
            have := mem_boxFinset_add hfar hbox
            rwa [harith] at this
          have hmem : q ∈ candidates η a.1.1 (2 * a.2 * a.2 + 3 * a.2) :=
            mem_candidates (mem_boxFinset_iff.mp hbox2) (lt_toNat_of_active hq)
          refine h (q, s) (Finset.mem_product.mpr ⟨hmem, Finset.mem_range.mpr hs⟩) ?_
          show expIdxOf D (q, s) = Sum.inl q₀
          unfold expIdxOf
          rw [if_pos hq, hr]
        · right
          refine state_agree_box hsD a.1.1 a.2 (2 * a.2) ⟨fun _ _ => rfl, ?_, fun _ _ _ => rfl⟩
          intro w hw k
          exact hstack (w, k) (by rintro rfl; exact hfar hw)
      rcases hstate_or with hEq | hSA
      · show (if (state D' a.2).active a.1 then Sum.inl (readIndex D' a.2 a.1) else Sum.inr a)
            = (if (state D a.2).active a.1 then Sum.inl (readIndex D a.2 a.1) else Sum.inr a)
        have hri : readIndex D' a.2 a.1 = readIndex D a.2 a.1 := by
          show ((state D' a.2).pos a.1, instructionIndex D' (state D' a.2) a.2 a.1)
              = ((state D a.2).pos a.1, instructionIndex D (state D a.2) a.2 a.1)
          rw [← hEq, instructionIndex_congr (D := D') (D' := D) rfl]
        rw [hri, hEq]
      · have hp1 : a.1.1 ∈ boxFinset a.1.1 (2 * a.2) :=
          mem_boxFinset_iff.mpr fun i => by simp
        have hpos : (state D a.2).pos a.1 = (state D' a.2).pos a.1 := hSA.pos a.1 hp1
        have hact : (state D a.2).active a.1 = (state D' a.2).active a.1 := hSA.active a.1 hp1
        have hy0 : (state D a.2).pos a.1 ∈ boxFinset a.1.1 a.2 := by
          have := pos_mem_boxFinset hsD (y := a.1.1) (r := 0) (p := a.1) a.2
            (mem_boxFinset_iff.mpr fun i => by simp)
          simpa using this
        have hy : (state D a.2).pos a.1 ∈ boxFinset a.1.1 (2 * a.2) :=
          boxFinset_mono (by omega) hy0
        have hdepeq : (state D a.2).departures ((state D a.2).pos a.1)
            = (state D' a.2).departures ((state D a.2).pos a.1) := hSA.departures _ hy
        have hactset : activeAt D (state D a.2) a.2 ((state D a.2).pos a.1)
            = activeAt D' (state D' a.2) a.2 ((state D a.2).pos a.1) := by
          show (candidates η ((state D a.2).pos a.1) a.2).filter
                (fun p => (state D a.2).active p ∧ (state D a.2).pos p = (state D a.2).pos a.1)
              = (candidates η ((state D a.2).pos a.1) a.2).filter
                (fun p => (state D' a.2).active p ∧ (state D' a.2).pos p = (state D a.2).pos a.1)
          refine Finset.filter_congr fun q hq => ?_
          have hq1 : q.1 ∈ boxFinset a.1.1 (2 * a.2) := by
            have hqb : q.1 ∈ boxFinset ((state D a.2).pos a.1) a.2 :=
              mem_boxFinset_iff.mpr (mem_candidates_iff.mp hq).1
            have := mem_boxFinset_add hy0 hqb
            exact boxFinset_mono (by omega) this
          rw [hSA.active q hq1, hSA.pos q hq1]
        have hii : instructionIndex D (state D a.2) a.2 a.1
            = instructionIndex D' (state D' a.2) a.2 a.1 := by
          show (state D a.2).departures ((state D a.2).pos a.1)
              + ((activeAt D (state D a.2) a.2 ((state D a.2).pos a.1)).filter
                  fun q => labelLT q a.1).card
            = (state D' a.2).departures ((state D' a.2).pos a.1)
              + ((activeAt D' (state D' a.2) a.2 ((state D' a.2).pos a.1)).filter
                  fun q => labelLT q a.1).card
          rw [← hpos, hdepeq, hactset]
        show (if (state D' a.2).active a.1 then Sum.inl (readIndex D' a.2 a.1) else Sum.inr a)
            = (if (state D a.2).active a.1 then Sum.inl (readIndex D a.2 a.1) else Sum.inr a)
        have hri : readIndex D' a.2 a.1 = readIndex D a.2 a.1 := by
          show ((state D' a.2).pos a.1, instructionIndex D' (state D' a.2) a.2 a.1)
              = ((state D a.2).pos a.1, instructionIndex D (state D a.2) a.2 a.1)
          rw [hpos, hii]
        rw [hri, hact]

/-- **The exploration hypotheses hold.** `expIdx` together with the dependency set `expDep`
is a `IsDagExploration`, packaging `expIdx_measurable`, `expDep_wf`, `expIdx_fresh`, and
`expIdx_pred`. -/
theorem expIdx_isDagExploration (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) :
    IsDagExploration (X := fun _ : RIdx d => Site d) (expIdx i₀ η ρ) (expDep η) where
  meas := expIdx_measurable i₀ η ρ
  wf := expDep_wf η
  fresh := fun a b ω hab => expIdx_fresh i₀ η ρ a b ω hab
  pred := expIdx_pred i₀ η ρ

/-! ### The revealed displacements drive the particle-driven construction -/

/-- The displacements the exploration reveals. -/
def expMove (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (ω : RIdx d → Site d) : Label d × ℕ → Site d :=
  revealedDag (expIdx i₀ η ρ) (expG i₀) ω

/-- When the particle `a.1` is active at round `a.2`, the revealed displacement is the
recorded stack entry minus its current position. -/
theorem expMove_active (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (ω : RIdx d → Site d) (a : Label d × ℕ)
    (ha : (state (expDriver i₀ η ρ ω) a.2).active a.1 = true) :
    expMove i₀ η ρ ω a
      = (expDriver i₀ η ρ ω).stack (readIndex (expDriver i₀ η ρ ω) a.2 a.1)
        - ((state (expDriver i₀ η ρ ω) a.2).pos a.1) := by
  have hidx : expIdx i₀ η ρ a ω = Sum.inl (readIndex (expDriver i₀ η ρ ω) a.2 a.1) := by
    show expIdxOf (expDriver i₀ η ρ ω) a = _
    unfold expIdxOf
    rw [if_pos ha]
  show expG i₀ (expIdx i₀ η ρ a ω) (ω (expIdx i₀ η ρ a ω)) = _
  rw [hidx]
  rfl

/-- **The pathwise identification.**  The state of the particle-driven
construction driven by the revealed displacements is the state of the stack
construction, round by round. -/
theorem pState_expMove (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (ω : RIdx d → Site d) :
    ∀ t : ℕ, LatticeProb.pState ⟨η, expMove i₀ η ρ ω, ρ⟩ t
      = state (expDriver i₀ η ρ ω) t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      have hnext : ∀ p : Label d,
          LatticeProb.pNextPos ⟨η, expMove i₀ η ρ ω, ρ⟩ (state (expDriver i₀ η ρ ω) t) t p
            = nextPos (expDriver i₀ η ρ ω) (state (expDriver i₀ η ρ ω) t) t p := by
        intro p
        by_cases hact : (state (expDriver i₀ η ρ ω) t).active p = true
        · show (if (state (expDriver i₀ η ρ ω) t).active p
                then (state (expDriver i₀ η ρ ω) t).pos p + expMove i₀ η ρ ω (p, t)
                else (state (expDriver i₀ η ρ ω) t).pos p)
              = (if (state (expDriver i₀ η ρ ω) t).active p
                then (expDriver i₀ η ρ ω).stack ((state (expDriver i₀ η ρ ω) t).pos p,
                  instructionIndex (expDriver i₀ η ρ ω) (state (expDriver i₀ η ρ ω) t) t p)
                else (state (expDriver i₀ η ρ ω) t).pos p)
          rw [if_pos hact, if_pos hact, expMove_active i₀ η ρ ω (p, t) hact]
          show (state (expDriver i₀ η ρ ω) t).pos p
              + ((expDriver i₀ η ρ ω).stack (readIndex (expDriver i₀ η ρ ω) t p)
                - (state (expDriver i₀ η ρ ω) t).pos p) = _
          have : readIndex (expDriver i₀ η ρ ω) t p
              = ((state (expDriver i₀ η ρ ω) t).pos p,
                 instructionIndex (expDriver i₀ η ρ ω) (state (expDriver i₀ η ρ ω) t) t p) := rfl
          rw [this]
          abel
        · show (if (state (expDriver i₀ η ρ ω) t).active p
                then (state (expDriver i₀ η ρ ω) t).pos p + expMove i₀ η ρ ω (p, t)
                else (state (expDriver i₀ η ρ ω) t).pos p)
              = (if (state (expDriver i₀ η ρ ω) t).active p
                then (expDriver i₀ η ρ ω).stack ((state (expDriver i₀ η ρ ω) t).pos p,
                  instructionIndex (expDriver i₀ η ρ ω) (state (expDriver i₀ η ρ ω) t) t p)
                else (state (expDriver i₀ η ρ ω) t).pos p)
          rw [if_neg hact, if_neg hact]
      have harr : ∀ x : Site d,
          LatticeProb.pArrivalsAt ⟨η, expMove i₀ η ρ ω, ρ⟩ (state (expDriver i₀ η ρ ω) t) t x
            = arrivalsAt (expDriver i₀ η ρ ω) (state (expDriver i₀ η ρ ω) t) t x := by
        intro x
        show (candidates η x (t + 1)).filter
              (fun p => (state (expDriver i₀ η ρ ω) t).active p ∧
                LatticeProb.pNextPos ⟨η, expMove i₀ η ρ ω, ρ⟩
                  (state (expDriver i₀ η ρ ω) t) t p = x)
            = (candidates η x (t + 1)).filter
              (fun p => (state (expDriver i₀ η ρ ω) t).active p ∧
                nextPos (expDriver i₀ η ρ ω) (state (expDriver i₀ η ρ ω) t) t p = x)
        exact Finset.filter_congr fun p _ => by rw [hnext p]
      have hsettle : ∀ p : Label d,
          LatticeProb.pSettles ⟨η, expMove i₀ η ρ ω, ρ⟩ (state (expDriver i₀ η ρ ω) t) t p
            = settles (expDriver i₀ η ρ ω) (state (expDriver i₀ η ρ ω) t) t p := by
        intro p
        unfold LatticeProb.pSettles settles
        rw [hnext p, harr]
        rfl
      show LatticeProb.pStep ⟨η, expMove i₀ η ρ ω, ρ⟩
          (LatticeProb.pState ⟨η, expMove i₀ η ρ ω, ρ⟩ t) t
        = step (expDriver i₀ η ρ ω) (state (expDriver i₀ η ρ ω) t) t
      rw [ih]
      unfold LatticeProb.pStep step
      congr 1
      · funext p; rw [hsettle p]
      · funext p; exact hnext p
      · funext x; rw [harr x]

/-! ### The law of the revealed displacements -/

/-- `expG i₀ i` is measurable, being defined by cases on a countable index. -/
theorem measurable_expG (i₀ : Fin d) (i : RIdx d) : Measurable (expG i₀ i) :=
  measurable_from_countable' _

/-- Each coordinate of the enlarged family's law `expLaw` is a probability measure, since it
is one of the `instructionLaw` measures. -/
theorem expLaw_isProbability (hd : 1 ≤ d) (i : RIdx d) :
    IsProbabilityMeasure (expLaw d i) := by
  cases i with
  | inl q => exact LatticeProb.instructionLaw_isProbability hd q.1
  | inr _ => exact LatticeProb.instructionLaw_isProbability hd 0

/-- Each coordinate's revealing map `expG i₀ i` pushes `expLaw d i` forward to the
displacement law, at a stack coordinate via `instructionLaw_map_sub_self` and at an
auxiliary coordinate by the identity map. -/
theorem expLaw_map_expG (i₀ : Fin d) (i : RIdx d) :
    (expLaw d i).map (expG i₀ i) = LatticeProb.displacementLaw d := by
  cases i with
  | inl q =>
      have hae : (expG i₀ (Sum.inl q)) =ᵐ[instructionLaw q.1] (fun z : Site d => z - q.1) := by
        refine MeasureTheory.ae_iff.mpr ?_
        refine measure_mono_null (fun z hz => ?_) (instructionLaw_compl_nbr q.1)
        simp only [Set.mem_setOf_eq] at hz
        intro hmem
        apply hz
        show (if z ∈ nbrFinset q.1 then z else q.1 + unit i₀) - q.1 = z - q.1
        rw [if_pos (Finset.mem_coe.mp hmem)]
      show (instructionLaw q.1).map (expG i₀ (Sum.inl q)) = _
      rw [Measure.map_congr hae]
      exact LatticeProb.instructionLaw_map_sub_self q.1
  | inr _ =>
      show (LatticeProb.displacementLaw d).map (fun z : Site d => z) = _
      exact Measure.map_id

/-- The revealed displacements are an independent family with the one-step
law, whatever the configuration and the uniform variables are. -/
theorem map_expMove (hd : 1 ≤ d) (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) :
    (Measure.infinitePi (expLaw d)).map (expMove i₀ η ρ) = LatticeProb.moveLaw d := by
  haveI : ∀ i, IsProbabilityMeasure (expLaw d i) := expLaw_isProbability hd
  exact map_revealed_dag (expLaw d) (expIdx_isDagExploration i₀ η ρ)
    (measurable_expG i₀) (expLaw_map_expG i₀)

/-- The stack coordinates of the enlarged family, projected, have the stack
law. -/
theorem map_expStack (hd : 1 ≤ d) (i₀ : Fin d) :
    (Measure.infinitePi (expLaw d)).map (expStack i₀) = LatticeProb.stackLaw d := by
  haveI : ∀ i, IsProbabilityMeasure (expLaw d i) := expLaw_isProbability hd
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
    fun q => LatticeProb.instructionLaw_isProbability hd q.1
  haveI : ∀ q : Label d × ℕ, IsProbabilityMeasure (LatticeProb.displacementLaw d) :=
    fun _ => LatticeProb.instructionLaw_isProbability hd 0
  have hsplit := LatticeProb.infinitePi_sum (X := fun _ : RIdx d => Site d) (expLaw d)
  have hfst : (Measure.infinitePi (expLaw d)).map (fun ω q => ω (Sum.inl q))
      = LatticeProb.stackLaw d := by
    have hm : Measurable fun ω : RIdx d → Site d =>
        (((fun q : Site d × ℕ => ω (Sum.inl q)), fun q : Label d × ℕ => ω (Sum.inr q)) :
          (Site d × ℕ → Site d) × (Label d × ℕ → Site d)) :=
      (Measurable.of_eval fun q => measurable_pi_apply (Sum.inl q)).prodMk
        (Measurable.of_eval fun q => measurable_pi_apply (Sum.inr q))
    haveI : IsProbabilityMeasure
        (Measure.infinitePi fun q : Label d × ℕ => expLaw d (Sum.inr q)) := by
      infer_instance
    calc (Measure.infinitePi (expLaw d)).map (fun ω q => ω (Sum.inl q))
        = ((Measure.infinitePi (expLaw d)).map
            (fun ω => (((fun q : Site d × ℕ => ω (Sum.inl q)),
              fun q : Label d × ℕ => ω (Sum.inr q)) :
                (Site d × ℕ → Site d) × (Label d × ℕ → Site d)))).map Prod.fst := by
          rw [Measure.map_map measurable_fst hm]; rfl
      _ = ((Measure.infinitePi fun q : Site d × ℕ => expLaw d (Sum.inl q)).prod
            (Measure.infinitePi fun q : Label d × ℕ => expLaw d (Sum.inr q))).map Prod.fst := by
          rw [hsplit]
      _ = LatticeProb.stackLaw d := by
          rw [← Measure.fst]
          exact Measure.fst_prod
  have hproj : (LatticeProb.stackLaw d).map (nbrProj i₀) = LatticeProb.stackLaw d := by
    have hae : (nbrProj i₀) =ᵐ[LatticeProb.stackLaw d] id := by
      filter_upwards [stackLaw_ae_nbr hd] with σ hσ
      exact nbrProj_eq_self hσ
    rw [Measure.map_congr hae, Measure.map_id]
  calc (Measure.infinitePi (expLaw d)).map (expStack i₀)
      = ((Measure.infinitePi (expLaw d)).map (fun ω q => ω (Sum.inl q))).map (nbrProj i₀) := by
        rw [Measure.map_map (measurable_nbrProj i₀)
          (Measurable.of_eval fun q => measurable_pi_apply (Sum.inl q))]
        rfl
    _ = LatticeProb.stackLaw d := by rw [hfst, hproj]

/-! ### The two constructions have the same law -/

/-- Reshuffling a triple product: the third factor moves inside, in front of
the second. -/
theorem map_reshuffle {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (P : Measure A) (Q : Measure B) (R : Measure C)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    ((P.prod Q).prod R).map (fun x => (x.1.1, (x.2, x.1.2))) = P.prod (R.prod Q) := by
  have hassoc : Measurable fun x : (A × B) × C => (x.1.1, (x.1.2, x.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hswap : Measurable fun y : A × (B × C) => ((y.1, (y.2.2, y.2.1)) : A × (C × B)) :=
    measurable_fst.prodMk
      ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))
  have h1 : ((P.prod Q).prod R).map (fun x : (A × B) × C => (x.1.1, (x.1.2, x.2)))
      = P.prod (Q.prod R) := Measure.prodAssoc_prod
  calc ((P.prod Q).prod R).map (fun x => (x.1.1, (x.2, x.1.2)))
      = (((P.prod Q).prod R).map (fun x : (A × B) × C => (x.1.1, (x.1.2, x.2)))).map
          (fun y : A × (B × C) => ((y.1, (y.2.2, y.2.1)) : A × (C × B))) := by
        rw [Measure.map_map hswap hassoc]; rfl
    _ = (P.prod (Q.prod R)).map (fun y : A × (B × C) => ((y.1, (y.2.2, y.2.1)) : A × (C × B))) := by
        rw [h1]
    _ = P.prod (R.prod Q) := by
        rw [show (fun y : A × (B × C) => ((y.1, (y.2.2, y.2.1)) : A × (C × B)))
              = Prod.map id Prod.swap from rfl,
          ← Measure.map_prod_map _ _ measurable_id measurable_swap, Measure.map_id,
          Measure.prod_swap]

/-- The observables of the two constructions agree realization by realization,
once the displacements are the ones the exploration reveals. -/
theorem stackObservables_eq_pObservables (i₀ : Fin d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (ω : RIdx d → Site d) :
    LatticeProb.stackObservables ((η, (expStack i₀ ω, ρ)) : LatticeProb.StackData d)
      = LatticeProb.pObservables ((η, (expMove i₀ η ρ ω, ρ)) : LatticeProb.PData d) := by
  have hst := pState_expMove i₀ η ρ ω
  refine Prod.ext (funext fun tx => ?_) (Prod.ext (funext fun tx => ?_)
    (Prod.ext (funext fun tx => ?_) (funext fun ti => ?_)))
  · show (state (expDriver i₀ η ρ ω) tx.1).departures tx.2
        = (LatticeProb.pState ⟨η, expMove i₀ η ρ ω, ρ⟩ tx.1).departures tx.2
    rw [hst tx.1]
  · show (activeAt (expDriver i₀ η ρ ω) (state (expDriver i₀ η ρ ω) tx.1) tx.1 tx.2).card
        = (LatticeProb.pActiveAt ⟨η, expMove i₀ η ρ ω, ρ⟩
            (LatticeProb.pState ⟨η, expMove i₀ η ρ ω, ρ⟩ tx.1) tx.1 tx.2).card
    rw [hst tx.1]
    rfl
  · show (state (expDriver i₀ η ρ ω) tx.1).holes tx.2
        = (LatticeProb.pState ⟨η, expMove i₀ η ρ ω, ρ⟩ tx.1).holes tx.2
    rw [hst tx.1]
  · show (state (expDriver i₀ η ρ ω) ti.1).active ti.2
        = (LatticeProb.pState ⟨η, expMove i₀ η ρ ω, ρ⟩ ti.1).active ti.2
    rw [hst ti.1]

/-- **The two constructions have the same law, at a fixed configuration law `μ`.** Assembled
from the stack and revealed-move pushforwards `map_expStack`, `map_expMove` through the
exploration `expIdx_isDagExploration`, reshuffled into the two data laws with
`map_reshuffle`. -/
theorem constructionsAgree_conf (d : ℕ) (hd : 1 ≤ d) (μ : Measure (Site d → ℤ))
    [IsProbabilityMeasure μ] :
    (μ.prod ((LatticeProb.stackLaw d).prod (LatticeProb.rankLaw d))).map
        (fun ω : LatticeProb.StackData d => (ω.1, LatticeProb.stackObservables ω))
      = (μ.prod ((LatticeProb.moveLaw d).prod (LatticeProb.rankLaw d))).map
        (fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω)) := by
  classical
  let i₀ : Fin d := ⟨0, hd⟩
  haveI hpl : ∀ i, IsProbabilityMeasure (expLaw d i) := expLaw_isProbability hd
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
    fun q => LatticeProb.instructionLaw_isProbability hd q.1
  haveI : IsProbabilityMeasure (LatticeProb.stackLaw d) := by
    unfold LatticeProb.stackLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.displacementLaw d) :=
    LatticeProb.instructionLaw_isProbability hd 0
  haveI : IsProbabilityMeasure (LatticeProb.moveLaw d) := by
    unfold LatticeProb.moveLaw; infer_instance
  set P : Measure ((Site d → ℤ) × (Label d × ℕ → ℝ)) :=
    (μ).prod (LatticeProb.rankLaw d) with hP
  set R : Measure (RIdx d → Site d) := Measure.infinitePi (expLaw d) with hR
  haveI : IsProbabilityMeasure R := by rw [hR]; infer_instance
  -- the stack coordinates
  have hstackU : Measurable (Function.uncurry
      fun (_ : (Site d → ℤ) × (Label d × ℕ → ℝ)) (ω : RIdx d → Site d) => expStack i₀ ω) :=
    (measurable_nbrProj i₀).comp
      ((Measurable.of_eval fun q => measurable_pi_apply (Sum.inl q)).comp measurable_snd)
  have hstep1 : (P.prod R).map (fun x => (x.1, expStack i₀ x.2))
      = P.prod (LatticeProb.stackLaw d) :=
    LatticeProb.map_prod_pair_of_forall_map P R hstackU fun _ => map_expStack hd i₀
  -- the revealed displacements
  have hJ : ∀ a : Label d × ℕ,
      Measurable fun x : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (RIdx d → Site d) =>
        expIdx i₀ x.1.1 x.1.2 a x.2 := by
    intro a
    have hemb : Measurable fun x : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (RIdx d → Site d) =>
        ((x.1.1, expStack i₀ x.2, x.1.2) : Data d) :=
      (measurable_fst.comp measurable_fst).prodMk
        (((measurable_nbrProj i₀).comp
          ((Measurable.of_eval fun q => measurable_pi_apply (Sum.inl q)).comp
            measurable_snd)).prodMk (measurable_snd.comp measurable_fst))
    exact (measurable_expIdxOf a).comp hemb
  have hmoveU : Measurable (Function.uncurry
      fun (y : (Site d → ℤ) × (Label d × ℕ → ℝ)) (ω : RIdx d → Site d) =>
        expMove i₀ y.1 y.2 ω) := by
    refine Measurable.of_eval fun a => ?_
    exact measurable_of_countable_partition
      (fun x : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (RIdx d → Site d) =>
        expIdx i₀ x.1.1 x.1.2 a x.2) (hJ a) _
      (fun j x => expG i₀ j (x.2 j))
      (fun j => (measurable_expG i₀ j).comp ((measurable_pi_apply j).comp measurable_snd))
      fun _ => rfl
  have hstep2 : (P.prod R).map (fun x => (x.1, expMove i₀ x.1.1 x.1.2 x.2))
      = P.prod (LatticeProb.moveLaw d) :=
    LatticeProb.map_prod_pair_of_forall_map P R hmoveU fun y => map_expMove hd i₀ y.1 y.2
  -- the reshuffles
  have hstackfull : (P.prod R).map
        (fun x => ((x.1.1, (expStack i₀ x.2, x.1.2)) : LatticeProb.StackData d))
      = μ.prod ((LatticeProb.stackLaw d).prod (LatticeProb.rankLaw d)) := by
    have hcomp : (fun x : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (RIdx d → Site d) =>
          ((x.1.1, (expStack i₀ x.2, x.1.2)) : LatticeProb.StackData d))
        = (fun y : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (Site d × ℕ → Site d) =>
            (y.1.1, (y.2, y.1.2))) ∘ (fun x => (x.1, expStack i₀ x.2)) := rfl
    have hm1 : Measurable fun x : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (RIdx d → Site d) =>
        (x.1, expStack i₀ x.2) := measurable_fst.prodMk hstackU
    have hm2 : Measurable fun y : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (Site d × ℕ → Site d) =>
        (y.1.1, (y.2, y.1.2)) :=
      (measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    rw [hcomp, ← Measure.map_map hm2 hm1, hstep1, hP,
      map_reshuffle (μ) (LatticeProb.rankLaw d) (LatticeProb.stackLaw d)]
  have hmovefull : (P.prod R).map
        (fun x => ((x.1.1, (expMove i₀ x.1.1 x.1.2 x.2, x.1.2)) : LatticeProb.PData d))
      = μ.prod ((LatticeProb.moveLaw d).prod (LatticeProb.rankLaw d)) := by
    have hcomp : (fun x : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (RIdx d → Site d) =>
          ((x.1.1, (expMove i₀ x.1.1 x.1.2 x.2, x.1.2)) : LatticeProb.PData d))
        = (fun y : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (Label d × ℕ → Site d) =>
            (y.1.1, (y.2, y.1.2))) ∘ (fun x => (x.1, expMove i₀ x.1.1 x.1.2 x.2)) := rfl
    have hm1 : Measurable fun x : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (RIdx d → Site d) =>
        (x.1, expMove i₀ x.1.1 x.1.2 x.2) := measurable_fst.prodMk hmoveU
    have hm2 : Measurable fun y : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (Label d × ℕ → Site d) =>
        (y.1.1, (y.2, y.1.2)) :=
      (measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    rw [hcomp, ← Measure.map_map hm2 hm1, hstep2, hP,
      map_reshuffle (μ) (LatticeProb.rankLaw d) (LatticeProb.moveLaw d)]
  have hmS : Measurable fun x : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (RIdx d → Site d) =>
      ((x.1.1, (expStack i₀ x.2, x.1.2)) : LatticeProb.StackData d) :=
    (measurable_fst.comp measurable_fst).prodMk
      (hstackU.prodMk (measurable_snd.comp measurable_fst))
  have hmP : Measurable fun x : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (RIdx d → Site d) =>
      ((x.1.1, (expMove i₀ x.1.1 x.1.2 x.2, x.1.2)) : LatticeProb.PData d) :=
    (measurable_fst.comp measurable_fst).prodMk
      (hmoveU.prodMk (measurable_snd.comp measurable_fst))
  have hmS' : Measurable fun x : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (RIdx d → Site d) =>
      ((x.1.1, LatticeProb.stackObservables ((x.1.1, (expStack i₀ x.2, x.1.2)) :
        LatticeProb.StackData d)) :
        (Site d → ℤ) × ((ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) ×
          (ℕ × Label d → Bool))) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_stackObservables.comp hmS)
  have hmP' : Measurable fun x : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (RIdx d → Site d) =>
      ((x.1.1, LatticeProb.pObservables ((x.1.1, (expMove i₀ x.1.1 x.1.2 x.2, x.1.2)) :
        LatticeProb.PData d)) :
        (Site d → ℤ) × ((ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) ×
          (ℕ × Label d → Bool))) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_pObservables.comp hmP)
  calc (μ.prod ((LatticeProb.stackLaw d).prod (LatticeProb.rankLaw d))).map
        (fun ω : LatticeProb.StackData d => (ω.1, LatticeProb.stackObservables ω))
      = ((P.prod R).map
          (fun x => ((x.1.1, (expStack i₀ x.2, x.1.2)) : LatticeProb.StackData d))).map
          (fun ω : LatticeProb.StackData d => (ω.1, LatticeProb.stackObservables ω)) := by
        rw [hstackfull]
    _ = (P.prod R).map (fun x =>
          (x.1.1, LatticeProb.stackObservables
            ((x.1.1, (expStack i₀ x.2, x.1.2)) : LatticeProb.StackData d))) := by
        rw [Measure.map_map (measurable_fst.prodMk measurable_stackObservables) hmS]; rfl
    _ = (P.prod R).map (fun x =>
          (x.1.1, LatticeProb.pObservables
            ((x.1.1, (expMove i₀ x.1.1 x.1.2 x.2, x.1.2)) : LatticeProb.PData d))) := by
        refine congrArg (fun f => Measure.map f (P.prod R)) ?_
        exact funext fun x : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × (RIdx d → Site d) =>
          congrArg (fun z => (x.1.1, z)) (stackObservables_eq_pObservables i₀ x.1.1 x.1.2 x.2)
    _ = ((P.prod R).map
          (fun x => ((x.1.1, (expMove i₀ x.1.1 x.1.2 x.2, x.1.2)) : LatticeProb.PData d))).map
          (fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω)) := by
        rw [Measure.map_map (measurable_fst.prodMk measurable_pObservables) hmP]; rfl
    _ = (μ.prod ((LatticeProb.moveLaw d).prod (LatticeProb.rankLaw d))).map
          (fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω)) := by
        rw [hmovefull]

/-- **The stack construction and the particle-driven construction have the same
law**, as `parking.tex:645-646` states. -/
theorem constructionsAgree : LatticeProb.ConstructionsAgree := by
  intro d hd ν hν
  haveI := hν
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  calc (LatticeProb.stackDataLaw d ν).map LatticeProb.stackObservables
      = (((LatticeProb.iidLaw d ν).prod
          ((LatticeProb.stackLaw d).prod (LatticeProb.rankLaw d))).map
          (fun ω : LatticeProb.StackData d => (ω.1, LatticeProb.stackObservables ω))).map
          Prod.snd := by
        rw [Measure.map_map measurable_snd
          (measurable_fst.prodMk measurable_stackObservables)]
        rfl
    _ = (((LatticeProb.iidLaw d ν).prod
          ((LatticeProb.moveLaw d).prod (LatticeProb.rankLaw d))).map
          (fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω))).map Prod.snd := by
        rw [constructionsAgree_conf d hd (LatticeProb.iidLaw d ν)]
    _ = (LatticeProb.pDataLaw d ν).map LatticeProb.pObservables := by
        rw [Measure.map_map measurable_snd (measurable_fst.prodMk measurable_pObservables)]
        rfl

/-! ### The construction of this repository -/

/-- The signed direction pushes forward to one lattice step. -/
theorem map_stepLaw_stepVec :
    (stepLaw d).map (stepVec (d := d)) = LatticeProb.displacementLaw d := by
  have hmeas : Measurable (stepVec (d := d)) := measurable_from_countable' _
  rw [stepLaw, Measure.map_smul _ hmeas.aemeasurable,
    Measure.map_finset_sum' hmeas.aemeasurable]
  show ((2 * (d : ℝ≥0∞))⁻¹) • Finset.univ.sum
      (fun b : Fin d × Bool => (Measure.dirac b).map (stepVec (d := d))) = _
  show _ = ((2 * (d : ℝ≥0∞))⁻¹) • Finset.univ.sum
      (fun i : Fin d => Measure.dirac ((0 : Site d) + LatticeProb.unit i)
        + Measure.dirac ((0 : Site d) - LatticeProb.unit i))
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp [Measure.map_dirac' hmeas, stepVec]

/-- Recoding a signed direction as a displacement turns the particle-driven
construction of this repository into the one of the library. -/
theorem pState_stepVec (η : Site d → ℤ) (m : Label d × ℕ → Fin d × Bool)
    (ρ : Label d × ℕ → ℝ) :
    ∀ t : ℕ, pState ⟨η, m, ρ⟩ t
      = LatticeProb.pState ⟨η, fun q => stepVec (m q), ρ⟩ t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      show pStep ⟨η, m, ρ⟩ (pState ⟨η, m, ρ⟩ t) t
        = LatticeProb.pStep ⟨η, fun q => stepVec (m q), ρ⟩
            (LatticeProb.pState ⟨η, fun q => stepVec (m q), ρ⟩ t) t
      rw [← ih]
      unfold pStep LatticeProb.pStep
      congr 1

/-- **The two constructions of this repository have the same law.**  This is
`parking.tex:645-646`, and with it the pathwise couplings of `lem:one-particle` and
`lem:tagged-monotonicity` carry over to the odometer, the activity and the hole
counts of the stack process. -/
theorem constructionsAgree' : ConstructionsAgree := by
  intro d hd ν hν
  haveI := hν
  haveI := stepLaw_isProbability hd
  have hmeas : Measurable (stepVec (d := d)) := measurable_from_countable' _
  have hrecode : Measurable fun ω : PData d =>
      ((ω.1, (fun q => stepVec (ω.2.1 q), ω.2.2)) : LatticeProb.PData d) :=
    measurable_fst.prodMk
      ((Measurable.of_eval fun q =>
        hmeas.comp ((measurable_pi_apply q).comp (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd))
  have hlaw : (pDataLaw d ν).map (fun ω : PData d =>
      ((ω.1, (fun q => stepVec (ω.2.1 q), ω.2.2)) : LatticeProb.PData d))
      = LatticeProb.pDataLaw d ν :=
    LatticeProb.map_pDataLaw_of_map (stepLaw d) stepVec hmeas map_stepLaw_stepVec ν hd
  have hobs : ∀ ω : PData d,
      ((fun tx : ℕ × Site d => pOdometer (toPDriver ω) tx.1 tx.2,
        fun tx : ℕ × Site d => pActiveCount (toPDriver ω) tx.1 tx.2,
        fun tx : ℕ × Site d => pHoleCount (toPDriver ω) tx.1 tx.2,
        fun ti : ℕ × Label d => (pState (toPDriver ω) ti.1).active ti.2))
      = LatticeProb.pObservables ((ω.1, (fun q => stepVec (ω.2.1 q), ω.2.2)) :
          LatticeProb.PData d) := by
    intro ω
    have hst : ∀ t : ℕ, pState (toPDriver ω) t
        = LatticeProb.pState ⟨ω.1, fun q => stepVec (ω.2.1 q), ω.2.2⟩ t :=
      pState_stepVec ω.1 ω.2.1 ω.2.2
    refine Prod.ext (funext fun tx => ?_) (Prod.ext (funext fun tx => ?_)
      (Prod.ext (funext fun tx => ?_) (funext fun ti => ?_)))
    · show (pState (toPDriver ω) tx.1).departures tx.2
          = (LatticeProb.pState ⟨ω.1, fun q => stepVec (ω.2.1 q), ω.2.2⟩ tx.1).departures tx.2
      rw [hst tx.1]
    · show (pActiveAt (toPDriver ω) (pState (toPDriver ω) tx.1) tx.1 tx.2).card
          = (LatticeProb.pActiveAt ⟨ω.1, fun q => stepVec (ω.2.1 q), ω.2.2⟩
              (LatticeProb.pState ⟨ω.1, fun q => stepVec (ω.2.1 q), ω.2.2⟩ tx.1) tx.1 tx.2).card
      rw [hst tx.1]
      rfl
    · show (pState (toPDriver ω) tx.1).holes tx.2
          = (LatticeProb.pState ⟨ω.1, fun q => stepVec (ω.2.1 q), ω.2.2⟩ tx.1).holes tx.2
      rw [hst tx.1]
    · show (pState (toPDriver ω) ti.1).active ti.2
          = (LatticeProb.pState ⟨ω.1, fun q => stepVec (ω.2.1 q), ω.2.2⟩ ti.1).active ti.2
      rw [hst ti.1]
  calc (law d ν).map (fun ω : Data d =>
          (fun tx : ℕ × Site d => U ω tx.1 tx.2,
           fun tx : ℕ × Site d => A ω tx.1 tx.2,
           fun tx : ℕ × Site d => H ω tx.1 tx.2,
           fun ti : ℕ × Label d => (state (toDriver ω) ti.1).active ti.2))
      = (LatticeProb.stackDataLaw d ν).map LatticeProb.stackObservables := rfl
    _ = (LatticeProb.pDataLaw d ν).map LatticeProb.pObservables := constructionsAgree d hd ν hν
    _ = ((pDataLaw d ν).map (fun ω : PData d =>
          ((ω.1, (fun q => stepVec (ω.2.1 q), ω.2.2)) : LatticeProb.PData d))).map
          LatticeProb.pObservables := by rw [hlaw]
    _ = (pDataLaw d ν).map (fun ω : PData d => LatticeProb.pObservables
          ((ω.1, (fun q => stepVec (ω.2.1 q), ω.2.2)) : LatticeProb.PData d)) := by
        rw [Measure.map_map measurable_pObservables hrecode]; rfl
    _ = (pDataLaw d ν).map (fun ω : PData d =>
          (fun tx : ℕ × Site d => pOdometer (toPDriver ω) tx.1 tx.2,
           fun tx : ℕ × Site d => pActiveCount (toPDriver ω) tx.1 tx.2,
           fun tx : ℕ × Site d => pHoleCount (toPDriver ω) tx.1 tx.2,
           fun ti : ℕ × Label d => (pState (toPDriver ω) ti.1).active ti.2)) := by
        refine congrArg (fun f => Measure.map f (pDataLaw d ν)) ?_
        exact funext fun ω => (hobs ω).symm

end LatticeProb.ParticleDrivenAgree

end
