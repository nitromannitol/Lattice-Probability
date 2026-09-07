/-
Translation equivariance of the particle-hole process.

Translating the data by `v` means reading the configuration, the instruction
stacks and the uniform variables at the translated site, and translating the
instructions themselves back, so that an instruction of the shifted data is
again a neighbour of the site carrying it.  The particle labelled `(x, i)` in
the shifted realization is the particle labelled `(x + v, i)` in the original
one, which is `shiftLabel`.

The whole round commutes with that relabelling, field by field.  The one thing
that has to be checked, and that is easy to doubt, is that the order which
fixes the reading order of co-departing particles is itself translation
invariant.  It is: `labelKey` compares the start sites lexicographically in
their coordinates, and the lexicographic order on `Fin d -> Z` is invariant
under adding a fixed vector to both sides, coordinate by coordinate.  So the
equivariance holds at the level of the labels and not only of the counts, which
is what the survivor counts of a mass transport argument need.
-/
import LatticeProb.ParticleHoleLemmas

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### The translation of labels and of the data -/

/-- The particle `(x, i)` of the data translated by `v` is the particle
`(x + v, i)` of the original data. -/
def shiftLabel (v : Site d) (p : Label d) : Label d := (p.1 + v, p.2)

theorem shiftLabel_injective (v : Site d) : Function.Injective (shiftLabel (d := d) v) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  simp only [shiftLabel, Prod.mk.injEq] at h
  exact Prod.ext (add_right_cancel h.1) h.2

/-- `shiftLabel` as an embedding of finsets of labels. -/
def shiftLabelEmb (v : Site d) : Label d ↪ Label d :=
  ⟨shiftLabel v, shiftLabel_injective v⟩

@[simp] theorem shiftLabelEmb_apply (v : Site d) (p : Label d) :
    shiftLabelEmb v p = shiftLabel v p := rfl

theorem mem_map_shiftLabel {s : Finset (Label d)} {v : Site d} {b : Label d} :
    b ∈ s.map (shiftLabelEmb v) ↔ (b.1 - v, b.2) ∈ s := by
  simp only [Finset.mem_map, shiftLabelEmb_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [shiftLabel] using ha
  · intro h
    exact ⟨(b.1 - v, b.2), h, by simp [shiftLabel]⟩

/-- The translation of a stack family by `v`: the stack of the site `y` of the
shifted data is the stack of `y + v`, with its instructions translated back, so
that they are again neighbours of `y`. -/
def shiftStack (v : Site d) (σ : Site d × ℕ → Site d) : Site d × ℕ → Site d :=
  fun q => σ (q.1 + v, q.2) - v

/-- The translation of the uniform variables by `v`. -/
def shiftRank (v : Site d) (r : Label d × ℕ → ℝ) : Label d × ℕ → ℝ :=
  fun q => r (shiftLabel v q.1, q.2)

/-! ### The label order is translation invariant -/

theorem toLex_add_lt_add_iff {x y v : Site d} :
    (toLex (x + v) : Lex (Fin d → ℤ)) < toLex (y + v)
      ↔ (toLex x : Lex (Fin d → ℤ)) < toLex y := by
  constructor
  · rintro ⟨i, hj, hi⟩
    exact ⟨i, fun j hjj => by have := hj j hjj; simpa using this, by simpa using hi⟩
  · rintro ⟨i, hj, hi⟩
    exact ⟨i, fun j hjj => by have := hj j hjj; simpa using this, by simpa using hi⟩

theorem toLex_add_inj {x y v : Site d} :
    (toLex (x + v) : Lex (Fin d → ℤ)) = toLex (y + v)
      ↔ (toLex x : Lex (Fin d → ℤ)) = toLex y := by
  constructor
  · intro h
    have : x + v = y + v := toLex_inj.mp h
    exact congrArg _ (add_right_cancel this)
  · intro h
    exact congrArg _ (by rw [toLex_inj.mp h])

/-- The order that fixes the reading order of co-departing particles is
invariant under translating both labels. -/
theorem labelLT_shift (v : Site d) (p q : Label d) :
    labelLT (shiftLabel v p) (shiftLabel v q) ↔ labelLT p q := by
  simp only [labelLT, labelKey, shiftLabel, Prod.Lex.toLex_lt_toLex]
  rw [toLex_add_lt_add_iff, toLex_add_inj]

/-! ### The candidate sets -/

theorem mem_candidates_shift {η : Site d → ℤ} {y v : Site d} {r : ℕ} {p : Label d} :
    p ∈ candidates (fun x => η (x + v)) y r ↔ shiftLabel v p ∈ candidates η (y + v) r := by
  simp only [mem_candidates_iff, shiftLabel]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, h2⟩
    have := h1 i
    simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, h2⟩
    have := h1 i
    simpa using this

theorem candidates_shift (η : Site d → ℤ) (y v : Site d) (r : ℕ) :
    (candidates (fun x => η (x + v)) y r).map (shiftLabelEmb v) = candidates η (y + v) r := by
  ext b
  rw [mem_map_shiftLabel, mem_candidates_shift]
  simp [shiftLabel]

/-! ### The relations between a shifted realization and the original one -/

/-- The driver of the shifted data, described without mentioning `shiftData`. -/
structure ShiftDriver (v : Site d) (D' D : Driver d) : Prop where
  eta : ∀ x, D'.eta x = D.eta (x + v)
  stack : ∀ q : Site d × ℕ, D'.stack q = D.stack (q.1 + v, q.2) - v
  rank : ∀ (p : Label d) (t : ℕ), D'.rank (p, t) = D.rank (shiftLabel v p, t)

/-- The driver translated by `v`. -/
def shiftDriver (v : Site d) (D : Driver d) : Driver d where
  eta := fun x => D.eta (x + v)
  stack := fun q => D.stack (q.1 + v, q.2) - v
  rank := fun q => D.rank (shiftLabel v q.1, q.2)

theorem shiftDriver_spec (v : Site d) (D : Driver d) :
    ShiftDriver v (shiftDriver v D) D where
  eta _ := rfl
  stack _ := rfl
  rank _ _ := rfl

/-- The state of the shifted realization, described against the original one. -/
structure ShiftState (v : Site d) (S' S : State d) : Prop where
  active : ∀ p, S'.active p = S.active (shiftLabel v p)
  pos : ∀ p, S'.pos p = S.pos (shiftLabel v p) - v
  holes : ∀ x, S'.holes x = S.holes (x + v)
  departures : ∀ x, S'.departures x = S.departures (x + v)

variable {v : Site d} {D' D : Driver d} {S' S : State d}

theorem mem_activeAt_shift (hD : ShiftDriver v D' D) (hS : ShiftState v S' S)
    (t : ℕ) (y : Site d) (p : Label d) :
    p ∈ activeAt D' S' t y ↔ shiftLabel v p ∈ activeAt D S t (y + v) := by
  have hη : D'.eta = fun x => D.eta (x + v) := funext hD.eta
  simp only [activeAt, Finset.mem_filter, hη]
  rw [mem_candidates_shift, hS.active p, hS.pos p, sub_eq_iff_eq_add]

theorem activeAt_shift (hD : ShiftDriver v D' D) (hS : ShiftState v S' S) (t : ℕ) (y : Site d) :
    (activeAt D' S' t y).map (shiftLabelEmb v) = activeAt D S t (y + v) := by
  ext b
  rw [mem_map_shiftLabel, mem_activeAt_shift hD hS]
  have hb : shiftLabel v ((b.1 - v, b.2) : Label d) = b := by simp [shiftLabel]
  rw [hb]

theorem card_activeAt_shift (hD : ShiftDriver v D' D) (hS : ShiftState v S' S)
    (t : ℕ) (y : Site d) :
    (activeAt D' S' t y).card = (activeAt D S t (y + v)).card := by
  rw [← activeAt_shift hD hS t y, Finset.card_map]

theorem filter_labelLT_shift (hD : ShiftDriver v D' D) (hS : ShiftState v S' S)
    (t : ℕ) (y : Site d) (p : Label d) :
    ((activeAt D' S' t y).filter fun q => labelLT q p).map (shiftLabelEmb v)
      = (activeAt D S t (y + v)).filter fun q => labelLT q (shiftLabel v p) := by
  ext b
  simp only [mem_map_shiftLabel, Finset.mem_filter]
  have hb : shiftLabel v ((b.1 - v, b.2) : Label d) = b := by simp [shiftLabel]
  have hmem := mem_activeAt_shift hD hS t y ((b.1 - v, b.2) : Label d)
  rw [hb] at hmem
  have hlab : labelLT ((b.1 - v, b.2) : Label d) p ↔ labelLT b (shiftLabel v p) := by
    rw [← labelLT_shift v ((b.1 - v, b.2) : Label d) p, hb]
  rw [hmem, hlab]

theorem instructionIndex_shift (hD : ShiftDriver v D' D) (hS : ShiftState v S' S)
    (t : ℕ) (p : Label d) :
    instructionIndex D' S' t p = instructionIndex D S t (shiftLabel v p) := by
  have hp : S'.pos p = S.pos (shiftLabel v p) - v := hS.pos p
  have h1 : S.pos (shiftLabel v p) - v + v = S.pos (shiftLabel v p) := by abel
  have hdep : S'.departures (S'.pos p) = S.departures (S.pos (shiftLabel v p)) := by
    rw [hS.departures, hp, h1]
  have hfil : ((activeAt D' S' t (S'.pos p)).filter fun q => labelLT q p).card
      = ((activeAt D S t (S.pos (shiftLabel v p))).filter fun q =>
          labelLT q (shiftLabel v p)).card := by
    have hmap := filter_labelLT_shift hD hS t (S'.pos p) p
    rw [hp, h1] at hmap
    rw [hp, ← hmap, Finset.card_map]
  rw [instructionIndex, instructionIndex, hdep, hfil]

theorem nextPos_shift (hD : ShiftDriver v D' D) (hS : ShiftState v S' S)
    (t : ℕ) (p : Label d) :
    nextPos D' S' t p = nextPos D S t (shiftLabel v p) - v := by
  have hp : S'.pos p = S.pos (shiftLabel v p) - v := hS.pos p
  by_cases h : S.active (shiftLabel v p) = true
  · simp only [nextPos, hS.active p, h, if_true, hD.stack, instructionIndex_shift hD hS, hp,
      sub_add_cancel]
  · simp only [Bool.not_eq_true] at h
    simp only [nextPos, hS.active p, h, Bool.false_eq_true, if_false, hp]

theorem mem_arrivalsAt_shift (hD : ShiftDriver v D' D) (hS : ShiftState v S' S)
    (t : ℕ) (x : Site d) (p : Label d) :
    p ∈ arrivalsAt D' S' t x ↔ shiftLabel v p ∈ arrivalsAt D S t (x + v) := by
  have hη : D'.eta = fun y => D.eta (y + v) := funext hD.eta
  simp only [arrivalsAt, Finset.mem_filter, hη]
  rw [mem_candidates_shift, hS.active p, nextPos_shift hD hS t p, sub_eq_iff_eq_add]

theorem arrivalsAt_shift (hD : ShiftDriver v D' D) (hS : ShiftState v S' S)
    (t : ℕ) (x : Site d) :
    (arrivalsAt D' S' t x).map (shiftLabelEmb v) = arrivalsAt D S t (x + v) := by
  ext b
  rw [mem_map_shiftLabel, mem_arrivalsAt_shift hD hS]
  have hb : shiftLabel v ((b.1 - v, b.2) : Label d) = b := by simp [shiftLabel]
  rw [hb]

theorem card_arrivalsAt_shift (hD : ShiftDriver v D' D) (hS : ShiftState v S' S)
    (t : ℕ) (x : Site d) :
    (arrivalsAt D' S' t x).card = (arrivalsAt D S t (x + v)).card := by
  rw [← arrivalsAt_shift hD hS t x, Finset.card_map]

theorem filter_prec_shift (hD : ShiftDriver v D' D) (hS : ShiftState v S' S)
    (t : ℕ) (x : Site d) (p : Label d) :
    ((arrivalsAt D' S' t x).filter fun q =>
        D'.rank (q, t) < D'.rank (p, t) ∨
          (D'.rank (q, t) = D'.rank (p, t) ∧ labelLT q p)).map (shiftLabelEmb v)
      = (arrivalsAt D S t (x + v)).filter fun q =>
        D.rank (q, t) < D.rank (shiftLabel v p, t) ∨
          (D.rank (q, t) = D.rank (shiftLabel v p, t) ∧ labelLT q (shiftLabel v p)) := by
  classical
  ext b
  simp only [mem_map_shiftLabel, Finset.mem_filter]
  have hb : shiftLabel v ((b.1 - v, b.2) : Label d) = b := by simp [shiftLabel]
  have hmem := mem_arrivalsAt_shift hD hS t x ((b.1 - v, b.2) : Label d)
  rw [hb] at hmem
  have hlab : labelLT ((b.1 - v, b.2) : Label d) p ↔ labelLT b (shiftLabel v p) := by
    rw [← labelLT_shift v ((b.1 - v, b.2) : Label d) p, hb]
  have hr : D'.rank (((b.1 - v, b.2) : Label d), t) = D.rank (b, t) := by
    rw [hD.rank, hb]
  rw [hmem, hlab, hr, hD.rank p t]

theorem settles_shift (hD : ShiftDriver v D' D) (hS : ShiftState v S' S)
    (t : ℕ) (p : Label d) :
    settles D' S' t p = settles D S t (shiftLabel v p) := by
  classical
  have hz : nextPos D' S' t p = nextPos D S t (shiftLabel v p) - v := nextPos_shift hD hS t p
  have hhole : S'.holes (nextPos D' S' t p) = S.holes (nextPos D S t (shiftLabel v p)) := by
    rw [hS.holes, hz, sub_add_cancel]
  have hcard : ((arrivalsAt D' S' t (nextPos D' S' t p)).filter fun q =>
        D'.rank (q, t) < D'.rank (p, t) ∨
          (D'.rank (q, t) = D'.rank (p, t) ∧ labelLT q p)).card
      = ((arrivalsAt D S t (nextPos D S t (shiftLabel v p))).filter fun q =>
        D.rank (q, t) < D.rank (shiftLabel v p, t) ∨
          (D.rank (q, t) = D.rank (shiftLabel v p, t) ∧ labelLT q (shiftLabel v p))).card := by
    have hmap := filter_prec_shift hD hS t (nextPos D' S' t p) p
    rw [hz] at hmap
    rw [show nextPos D S t (shiftLabel v p) - v + v = nextPos D S t (shiftLabel v p) by abel]
      at hmap
    rw [hz, ← hmap, Finset.card_map]
  simp only [settles, hS.active p, hcard, hhole]

theorem step_shift (hD : ShiftDriver v D' D) (hS : ShiftState v S' S) (t : ℕ) :
    ShiftState v (step D' S' t) (step D S t) where
  active p := by simp only [step, hS.active p, settles_shift hD hS t p]
  pos p := nextPos_shift hD hS t p
  holes x := by simp only [step, hS.holes x, card_arrivalsAt_shift hD hS t x]
  departures y := by simp only [step, hS.departures y, card_activeAt_shift hD hS t y]

/-- The state of the shifted realization is the state of the original one, read
at the translated labels and sites. -/
theorem state_shift (hD : ShiftDriver v D' D) :
    ∀ t : ℕ, ShiftState v (state D' t) (state D t)
  | 0 => by
      refine ⟨fun p => ?_, fun p => ?_, fun x => ?_, fun _ => rfl⟩
      · simp only [state, initial, shiftLabel, hD.eta]
      · simp only [state, initial, shiftLabel]; abel
      · simp only [state, initial, hD.eta]
  | t + 1 => step_shift hD (state_shift hD t) t


/-! ### The observables -/

theorem particleOdometer_shift (hD : ShiftDriver v D' D) (t : ℕ) (x : Site d) :
    particleOdometer D' t x = particleOdometer D t (x + v) :=
  (state_shift hD t).departures x

theorem holeCount_shift (hD : ShiftDriver v D' D) (t : ℕ) (x : Site d) :
    holeCount D' t x = holeCount D t (x + v) :=
  (state_shift hD t).holes x

theorem activeCount_shift (hD : ShiftDriver v D' D) (t : ℕ) (x : Site d) :
    activeCount D' t x = activeCount D t (x + v) :=
  card_activeAt_shift hD (state_shift hD t) t x

theorem survivorsFrom_shift (hD : ShiftDriver v D' D) (t : ℕ) (y : Site d) :
    survivorsFrom D' t y = survivorsFrom D t (y + v) := by
  have hact : ∀ i : ℕ, (state D' t).active (y, i) = (state D t).active (y + v, i) := fun i =>
    (state_shift hD t).active (y, i)
  have heta : D'.eta y = D.eta (y + v) := hD.eta y
  simp only [survivorsFrom, hact, heta]

/-- The translated driver moves particles to neighbours as soon as the original
one does. -/
theorem stepsToNeighbour_shiftDriver {D : Driver d} (h : StepsToNeighbour D) (v : Site d) :
    StepsToNeighbour (shiftDriver v D) := by
  intro q i
  have := h (q.1 + v, q.2) i
  show |D.stack (q.1 + v, q.2) i - v i - q.1 i| ≤ 1
  have hshow : |D.stack (q.1 + v, q.2) i - (q.1 + v) i| ≤ 1 := this
  have harg : D.stack (q.1 + v, q.2) i - v i - q.1 i
      = D.stack (q.1 + v, q.2) i - (q.1 + v) i := by
    show _ = D.stack (q.1 + v, q.2) i - (q.1 i + v i)
    ring
  rw [harg]
  exact hshow

end LatticeProb

end
