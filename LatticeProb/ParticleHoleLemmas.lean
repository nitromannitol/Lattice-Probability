/-
The leaf facts about the particle–hole process of `LatticeProb.ParticleHole`.

Every count in that file ranges over the finite set `candidates`, so the first
question about any of them is whether the restriction to that set loses
anything.  It does not: an active particle after `t` rounds has moved at most
`t` steps from where it started, so the particles that can be at `y` after
round `t` are all candidates for `y` at radius `t`, and the particles that can
arrive at `x` in round `t + 1` are all candidates for `x` at radius `t + 1`.
That is what `mem_activeAt_iff` and `mem_arrivalsAt_iff` say, and it is what
lets the recursions below be read as statements about the process rather than
about the bookkeeping.

The recursions themselves are the three conservation laws of one round: the
odometer grows by the number of active particles, the holes shrink by the
number of particles that settle, and a particle that has settled never moves
again.  The count of particles that settle at a site in one round is
`min (arrivals) (holes)`: the arrivals are filled in by increasing rank, so the
ones that find a hole are exactly those of rank below the number of holes, and
`LatticeProb.card_filter_rank_lt` counts them.
-/
import LatticeProb.ParticleHole
import LatticeProb.Rank

noncomputable section

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### The candidate set -/

theorem mem_boxFinset_iff {y x : Site d} {r : ℕ} :
    x ∈ boxFinset y r ↔ ∀ i, |x i - y i| ≤ (r : ℤ) := by
  simp only [boxFinset, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  constructor
  · intro h i; exact ⟨by linarith [(h i).1], by linarith [(h i).2]⟩
  · intro h i; exact ⟨by linarith [(h i).1], by linarith [(h i).2]⟩

/-- The candidates for `y` at radius `r` are exactly the labels whose start site
is within sup-distance `r` of `y` and whose index is below `η⁺` there. -/
theorem mem_candidates_iff {η : Site d → ℤ} {y : Site d} {r : ℕ} {p : Label d} :
    p ∈ candidates η y r ↔ (∀ i, |p.1 i - y i| ≤ (r : ℤ)) ∧ p.2 < (η p.1).toNat := by
  simp only [candidates, Finset.mem_biUnion, Finset.mem_map, Finset.mem_range,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨x, hx, i, hi, hp⟩
    obtain ⟨rfl, rfl⟩ : x = p.1 ∧ i = p.2 := by
      constructor <;> [exact congrArg Prod.fst hp; exact congrArg Prod.snd hp]
    exact ⟨mem_boxFinset_iff.mp hx, hi⟩
  · rintro ⟨hx, hi⟩
    exact ⟨p.1, mem_boxFinset_iff.mpr hx, p.2, hi, rfl⟩

/-- Every label whose start site is within sup-distance `r` of `y` and whose
index is below `η⁺` there is a candidate. -/
theorem mem_candidates {η : Site d → ℤ} {y : Site d} {r : ℕ} {p : Label d}
    (hx : ∀ i, |p.1 i - y i| ≤ (r : ℤ)) (hi : p.2 < (η p.1).toNat) :
    p ∈ candidates η y r :=
  mem_candidates_iff.mpr ⟨hx, hi⟩

/-- The candidates form a finite set. -/
theorem candidates_finite (η : Site d → ℤ) (y : Site d) (r : ℕ) :
    (↑(candidates η y r) : Set (Label d)).Finite :=
  (candidates η y r).finite_toSet

theorem activeAt_subset_candidates (D : Driver d) (S : State d) (t : ℕ) (y : Site d) :
    activeAt D S t y ⊆ candidates D.eta y t :=
  Finset.filter_subset _ _

theorem arrivalsAt_subset_candidates (D : Driver d) (S : State d) (t : ℕ) (x : Site d) :
    arrivalsAt D S t x ⊆ candidates D.eta x (t + 1) :=
  Finset.filter_subset _ _

/-! ### Activity -/

theorem active_step {D : Driver d} {S : State d} {t : ℕ} {p : Label d}
    (h : (step D S t).active p = true) : S.active p = true := by
  simp only [step, decide_eq_true_eq] at h
  exact h.1

/-- Activity is antitone in time: a particle active after `t` rounds was active
after every earlier round. -/
theorem active_of_le {D : Driver d} {p : Label d} :
    ∀ {s t : ℕ}, s ≤ t → (state D t).active p = true → (state D s).active p = true := by
  intro s t hst
  induction t with
  | zero => intro h; simpa [Nat.le_zero.mp hst] using h
  | succ t ih =>
      intro h
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · exact ih (Nat.lt_succ_iff.mp hlt) (active_step h)
      · have : s = t + 1 := le_antisymm hst hge
        subst this; exact h

/-- A particle that has settled is never active again. -/
theorem not_active_of_settles {D : Driver d} {t s : ℕ} {p : Label d}
    (h : settles D (state D t) t p = true) (hts : t < s) : (state D s).active p = false := by
  have hstep : (state D (t + 1)).active p = false := by
    simp [state, step, h]
  rcases Bool.eq_false_or_eq_true ((state D s).active p) with hc | hc
  · have := active_of_le (D := D) (p := p) hts hc
    rw [this] at hstep
    exact absurd hstep (by simp)
  · exact hc

/-- An active particle carries an index below `η⁺` at its start site. -/
theorem lt_toNat_of_active {D : Driver d} {t : ℕ} {p : Label d}
    (h : (state D t).active p = true) : p.2 < (D.eta p.1).toNat := by
  have h0 := active_of_le (D := D) (p := p) (Nat.zero_le t) h
  simpa [state, initial] using h0

/-! ### Displacement -/

/-- The instruction stacks move a particle by at most one in each coordinate.
Both the symmetric and the oriented stack laws of `LatticeProb.ParticleHole`
are supported on such stacks. -/
def StepsToNeighbour (D : Driver d) : Prop :=
  ∀ (q : Site d × ℕ) (i : Fin d), |D.stack q i - q.1 i| ≤ 1

theorem abs_nextPos_sub_le {D : Driver d} (h : StepsToNeighbour D) (S : State d) (t : ℕ)
    (p : Label d) (i : Fin d) : |nextPos D S t p i - S.pos p i| ≤ 1 := by
  unfold nextPos
  split
  · exact h (S.pos p, instructionIndex D S t p) i
  · simp

/-- After `t` rounds a particle is within sup-distance `t` of its start site. -/
theorem abs_pos_sub_start_le {D : Driver d} (h : StepsToNeighbour D) (t : ℕ) (p : Label d)
    (i : Fin d) : |(state D t).pos p i - p.1 i| ≤ (t : ℤ) := by
  induction t with
  | zero => simp [state, initial]
  | succ t ih =>
      have hstep : |(state D (t + 1)).pos p i - (state D t).pos p i| ≤ 1 := by
        have := abs_nextPos_sub_le h (state D t) t p i
        simpa [state, step] using this
      have := abs_sub_abs_le_abs_sub ((state D (t+1)).pos p i - p.1 i)
        ((state D t).pos p i - p.1 i)
      have habs : |(state D (t+1)).pos p i - p.1 i|
          ≤ |(state D t).pos p i - p.1 i| + 1 := by
        have hrw : (state D (t+1)).pos p i - p.1 i
            = ((state D (t+1)).pos p i - (state D t).pos p i)
              + ((state D t).pos p i - p.1 i) := by ring
        calc |(state D (t+1)).pos p i - p.1 i|
            ≤ |(state D (t+1)).pos p i - (state D t).pos p i|
              + |(state D t).pos p i - p.1 i| := by rw [hrw]; exact abs_add_le _ _
          _ ≤ 1 + |(state D t).pos p i - p.1 i| := by linarith
          _ = |(state D t).pos p i - p.1 i| + 1 := by ring
      push_cast
      linarith

/-! ### The counts are counts of the process -/

/-- The candidate restriction is not lossy: `activeAt D (state D t) t y` is
exactly the set of active particles standing at `y` after round `t`. -/
theorem mem_activeAt_iff {D : Driver d} (h : StepsToNeighbour D) (t : ℕ) (y : Site d)
    (p : Label d) :
    p ∈ activeAt D (state D t) t y ↔ ((state D t).active p = true ∧ (state D t).pos p = y) := by
  unfold activeAt
  rw [Finset.mem_filter]
  refine ⟨fun hp => hp.2, fun hp => ⟨?_, hp⟩⟩
  refine mem_candidates (fun i => ?_) (lt_toNat_of_active hp.1)
  have := abs_pos_sub_start_le h t p i
  rw [hp.2] at this
  rwa [abs_sub_comm]

/-- `arrivalsAt D (state D t) t x` is exactly the set of active particles whose
position after the step of round `t + 1` is `x`. -/
theorem mem_arrivalsAt_iff {D : Driver d} (h : StepsToNeighbour D) (t : ℕ) (x : Site d)
    (p : Label d) :
    p ∈ arrivalsAt D (state D t) t x
      ↔ ((state D t).active p = true ∧ nextPos D (state D t) t p = x) := by
  unfold arrivalsAt
  rw [Finset.mem_filter]
  refine ⟨fun hp => hp.2, fun hp => ⟨?_, hp⟩⟩
  refine mem_candidates (fun i => ?_) (lt_toNat_of_active hp.1)
  have h1 := abs_pos_sub_start_le h t p i
  have h2 := abs_nextPos_sub_le h (state D t) t p i
  rw [hp.2] at h2
  have hrw : p.1 i - x i = (p.1 i - (state D t).pos p i) + ((state D t).pos p i - x i) := by ring
  have h1' : |p.1 i - (state D t).pos p i| ≤ (t : ℤ) := by rwa [abs_sub_comm]
  have h2' : |(state D t).pos p i - x i| ≤ 1 := by rwa [abs_sub_comm]
  calc |p.1 i - x i| ≤ |p.1 i - (state D t).pos p i| + |(state D t).pos p i - x i| := by
        rw [hrw]; exact abs_add_le _ _
    _ ≤ (t : ℤ) + 1 := by linarith
    _ = ((t + 1 : ℕ) : ℤ) := by push_cast; ring

/-! ### The odometer -/

/-- The odometer of one round: the departures from `x` grow by the number of
particles active at `x`. -/
theorem particleOdometer_succ (D : Driver d) (t : ℕ) (x : Site d) :
    particleOdometer D (t + 1) x = particleOdometer D t x + activeCount D t x := rfl

theorem particleOdometer_le_succ (D : Driver d) (t : ℕ) (x : Site d) :
    particleOdometer D t x ≤ particleOdometer D (t + 1) x := by
  rw [particleOdometer_succ]; exact Nat.le_add_right _ _

/-- The odometer is monotone in time. -/
theorem particleOdometer_mono (D : Driver d) (x : Site d) :
    Monotone fun t => particleOdometer D t x :=
  monotone_nat_of_le_succ fun t => particleOdometer_le_succ D t x

/-! ### The holes -/

theorem holeCount_succ (D : Driver d) (t : ℕ) (x : Site d) :
    holeCount D (t + 1) x = holeCount D t x - (arrivalsAt D (state D t) t x).card := rfl

theorem holeCount_succ_le (D : Driver d) (t : ℕ) (x : Site d) :
    holeCount D (t + 1) x ≤ holeCount D t x := by
  rw [holeCount_succ]; exact Nat.sub_le _ _

/-- The holes at a site never increase. -/
theorem holeCount_antitone (D : Driver d) (x : Site d) :
    Antitone fun t => holeCount D t x :=
  antitone_nat_of_succ_le fun t => holeCount_succ_le D t x

/-! ### How many settle -/

/-- The particles that settle at `x` in round `t + 1`. -/
def settledAt (D : Driver d) (t : ℕ) (x : Site d) : Finset (Label d) :=
  (arrivalsAt D (state D t) t x).filter fun p => settles D (state D t) t p

/-- The number of particles that settle at `x` in round `t + 1` is the smaller
of the number of arrivals and the number of holes.  The arrivals are filled in
by increasing rank, ties broken by the order on labels, and that order is
linear, so the arrivals whose rank is below the number of holes are exactly
`min (arrivals) (holes)` of them. -/
theorem card_settledAt {D : Driver d} (t : ℕ) (x : Site d) :
    (settledAt D t x).card
      = min ((arrivalsAt D (state D t) t x).card) (holeCount D t x) := by
  classical
  set S := state D t with hS
  set A := arrivalsAt D S t x with hA
  set f : Label d → Lex (ℝ × Lex (Lex (Fin d → ℤ) × ℕ)) :=
    fun p => toLex (D.rank (p, t), labelKey p) with hf
  have hfinj : Function.Injective f := by
    intro p q h
    have h' : ((D.rank (p, t), labelKey p) : ℝ × Lex (Lex (Fin d → ℤ) × ℕ))
        = (D.rank (q, t), labelKey q) := toLex_inj.mp h
    exact labelKey_injective (congrArg Prod.snd h')
  have hcongr : ∀ p ∈ A,
      (settles D S t p = true) ↔ ((A.filter fun q => f q < f p).card < holeCount D t x) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hact : S.active p = true := hp'.2.1
    have hpos : nextPos D S t p = x := hp'.2.2
    have hfil : (A.filter fun q => D.rank (q, t) < D.rank (p, t)
          ∨ (D.rank (q, t) = D.rank (p, t) ∧ labelLT q p))
        = A.filter fun q => f q < f p := by
      refine Finset.filter_congr fun q _ => ?_
      rw [hf]
      simp only [Prod.Lex.toLex_lt_toLex]
      rfl
    unfold settles
    rw [hpos]
    simp only [decide_eq_true_eq, hact, true_and]
    rw [← hA, hfil]
    rfl
  have hfilter : settledAt D t x = A.filter fun p => (A.filter fun q => f q < f p).card
      < holeCount D t x := by
    unfold settledAt
    rw [← hS, ← hA]
    exact Finset.filter_congr hcongr
  rw [hfilter]
  exact card_filter_rank_lt A f hfinj.injOn _

/-- The holes at `x` shrink by exactly the number of particles that settle
there. -/
theorem holeCount_succ_eq_sub_settled {D : Driver d} (t : ℕ) (x : Site d) :
    holeCount D (t + 1) x = holeCount D t x - (settledAt D t x).card := by
  rw [holeCount_succ, card_settledAt t x]
  omega

end LatticeProb

end
