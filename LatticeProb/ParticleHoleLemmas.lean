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


/-! ### The process is local in space

The state after `t` rounds reads the driving data only inside a finite box.
Information travels at speed one, so the state at a label or a site of the box
of radius `r` about `y` is decided by the configuration, the instruction stacks
and the uniform variables on the box of radius `r + 2t²` about `y`.  The
quadratic radius is not the physical light cone; it is what the syntactic
recursion gives, because `activeAt` and `arrivalsAt` are written over the
candidate sets, which look a further `t` steps outward at every round.  Any
finite radius is what the martingale decompositions need.
-/

theorem boxFinset_mono {y : Site d} {r r' : ℕ} (h : r ≤ r') :
    boxFinset y r ⊆ boxFinset y r' := by
  intro x hx
  rw [mem_boxFinset_iff] at hx ⊢
  exact fun i => (hx i).trans (by exact_mod_cast h)

theorem mem_boxFinset_add {y z x : Site d} {a b : ℕ} (hz : z ∈ boxFinset y a)
    (hx : x ∈ boxFinset z b) : x ∈ boxFinset y (a + b) := by
  rw [mem_boxFinset_iff] at hz hx ⊢
  intro i
  have hrw : x i - y i = (x i - z i) + (z i - y i) := by ring
  have : |x i - y i| ≤ (b : ℤ) + (a : ℤ) := by
    calc |x i - y i| ≤ |x i - z i| + |z i - y i| := by rw [hrw]; exact abs_add_le _ _
      _ ≤ (b : ℤ) + (a : ℤ) := add_le_add (hx i) (hz i)
  push_cast
  linarith

theorem mem_boxFinset_of_mem_candidates {η : Site d → ℤ} {y z : Site d} {a b : ℕ}
    {p : Label d} (hz : z ∈ boxFinset y a) (hp : p ∈ candidates η z b) :
    p.1 ∈ boxFinset y (a + b) :=
  mem_boxFinset_add hz (mem_boxFinset_iff.mpr (mem_candidates_iff.mp hp).1)

theorem pos_mem_boxFinset {D : Driver d} (hs : StepsToNeighbour D) {y : Site d} {r : ℕ}
    (t : ℕ) {p : Label d} (hp : p.1 ∈ boxFinset y r) :
    (state D t).pos p ∈ boxFinset y (r + t) :=
  mem_boxFinset_add hp (mem_boxFinset_iff.mpr fun i => abs_pos_sub_start_le hs t p i)

theorem nextPos_mem_boxFinset {D : Driver d} (hs : StepsToNeighbour D) {y : Site d} {r : ℕ}
    (t : ℕ) {p : Label d} (hp : p.1 ∈ boxFinset y r) :
    nextPos D (state D t) t p ∈ boxFinset y (r + (t + 1)) := by
  refine mem_boxFinset_add hp (mem_boxFinset_iff.mpr fun i => ?_)
  have h1 := abs_pos_sub_start_le hs t p i
  have h2 := abs_nextPos_sub_le hs (state D t) t p i
  have hrw : nextPos D (state D t) t p i - p.1 i
      = (nextPos D (state D t) t p i - (state D t).pos p i)
        + ((state D t).pos p i - p.1 i) := by ring
  have : |nextPos D (state D t) t p i - p.1 i| ≤ 1 + (t : ℤ) := by
    calc |nextPos D (state D t) t p i - p.1 i|
        ≤ |nextPos D (state D t) t p i - (state D t).pos p i|
          + |(state D t).pos p i - p.1 i| := by rw [hrw]; exact abs_add_le _ _
      _ ≤ 1 + (t : ℤ) := add_le_add h2 h1
  push_cast
  linarith

/-- Two drivers agree on the box of radius `r` about `y`. -/
structure AgreeOn (D D' : Driver d) (y : Site d) (r : ℕ) : Prop where
  /-- The configurations agree on the box. -/
  eta : ∀ z ∈ boxFinset y r, D.eta z = D'.eta z
  /-- The instruction stacks agree at every site of the box. -/
  stack : ∀ z ∈ boxFinset y r, ∀ i : ℕ, D.stack (z, i) = D'.stack (z, i)
  /-- The uniform variables agree for every particle starting in the box. -/
  rank : ∀ p : Label d, p.1 ∈ boxFinset y r → ∀ s : ℕ, D.rank (p, s) = D'.rank (p, s)

theorem AgreeOn.mono {D D' : Driver d} {y : Site d} {r r' : ℕ} (h : AgreeOn D D' y r')
    (hr : r ≤ r') : AgreeOn D D' y r :=
  ⟨fun z hz => h.eta z (boxFinset_mono hr hz),
   fun z hz => h.stack z (boxFinset_mono hr hz),
   fun p hp => h.rank p (boxFinset_mono hr hp)⟩

/-- Two states agree on the box of radius `r` about `y`. -/
structure StateAgreeOn (S S' : State d) (y : Site d) (r : ℕ) : Prop where
  /-- The same particles of the box are active. -/
  active : ∀ p : Label d, p.1 ∈ boxFinset y r → S.active p = S'.active p
  /-- The particles of the box stand in the same places. -/
  pos : ∀ p : Label d, p.1 ∈ boxFinset y r → S.pos p = S'.pos p
  /-- The sites of the box carry the same numbers of holes. -/
  holes : ∀ x ∈ boxFinset y r, S.holes x = S'.holes x
  /-- The sites of the box have seen the same numbers of departures. -/
  departures : ∀ x ∈ boxFinset y r, S.departures x = S'.departures x

theorem StateAgreeOn.mono {S S' : State d} {y : Site d} {r r' : ℕ}
    (h : StateAgreeOn S S' y r') (hr : r ≤ r') : StateAgreeOn S S' y r :=
  ⟨fun p hp => h.active p (boxFinset_mono hr hp),
   fun p hp => h.pos p (boxFinset_mono hr hp),
   fun x hx => h.holes x (boxFinset_mono hr hx),
   fun x hx => h.departures x (boxFinset_mono hr hx)⟩

theorem activeAt_congr_box {D D' : Driver d} {S S' : State d} {y z : Site d} {a t : ℕ}
    (hz : z ∈ boxFinset y a)
    (heta : ∀ w ∈ boxFinset y (a + t), D.eta w = D'.eta w)
    (hS : StateAgreeOn S S' y (a + t)) :
    activeAt D S t z = activeAt D' S' t z := by
  classical
  have hcand : candidates D.eta z t = candidates D'.eta z t := by
    ext p
    rw [mem_candidates_iff, mem_candidates_iff]
    constructor
    · rintro ⟨hp, hi⟩
      exact ⟨hp, by rwa [← heta p.1 (mem_boxFinset_add hz (mem_boxFinset_iff.mpr hp))]⟩
    · rintro ⟨hp, hi⟩
      exact ⟨hp, by rwa [heta p.1 (mem_boxFinset_add hz (mem_boxFinset_iff.mpr hp))]⟩
  unfold activeAt
  rw [hcand]
  refine Finset.filter_congr fun p hp => ?_
  have hp1 : p.1 ∈ boxFinset y (a + t) :=
    mem_boxFinset_of_mem_candidates hz hp
  rw [hS.active p hp1, hS.pos p hp1]

theorem arrivalsAt_congr_box {D D' : Driver d} {S S' : State d} {y x : Site d} {a t : ℕ}
    (hx : x ∈ boxFinset y a)
    (heta : ∀ w ∈ boxFinset y (a + (t + 1)), D.eta w = D'.eta w)
    (hact : ∀ p : Label d, p.1 ∈ boxFinset y (a + (t + 1)) → S.active p = S'.active p)
    (hnext : ∀ p : Label d, p.1 ∈ boxFinset y (a + (t + 1)) →
      nextPos D S t p = nextPos D' S' t p) :
    arrivalsAt D S t x = arrivalsAt D' S' t x := by
  classical
  have hcand : candidates D.eta x (t + 1) = candidates D'.eta x (t + 1) := by
    ext p
    rw [mem_candidates_iff, mem_candidates_iff]
    constructor
    · rintro ⟨hp, hi⟩
      exact ⟨hp, by rwa [← heta p.1 (mem_boxFinset_add hx (mem_boxFinset_iff.mpr hp))]⟩
    · rintro ⟨hp, hi⟩
      exact ⟨hp, by rwa [heta p.1 (mem_boxFinset_add hx (mem_boxFinset_iff.mpr hp))]⟩
  unfold arrivalsAt
  rw [hcand]
  refine Finset.filter_congr fun p hp => ?_
  have hp1 : p.1 ∈ boxFinset y (a + (t + 1)) := mem_boxFinset_of_mem_candidates hx hp
  rw [hact p hp1, hnext p hp1]

/-- **The state is a function of the data in a box.**  Two drivers that agree
on the box of radius `r + 2t²` about `y` have, after `t` rounds, the same
activity and the same positions for every particle started in the box of radius
`r`, and the same holes and the same odometer at every site of that box. -/
theorem state_agree_box {D D' : Driver d} (hs : StepsToNeighbour D) (y : Site d) :
    ∀ (t r : ℕ), AgreeOn D D' y (r + 2 * t * t) →
      StateAgreeOn (state D t) (state D' t) y r := by
  classical
  intro t
  induction t with
  | zero =>
      intro r hA
      have hA' : AgreeOn D D' y r := by simpa using hA
      refine ⟨fun p hp => ?_, fun p _ => rfl, fun x hx => ?_, fun x _ => rfl⟩
      · show decide (p.2 < (D.eta p.1).toNat) = decide (p.2 < (D'.eta p.1).toNat)
        rw [hA'.eta p.1 hp]
      · show (-D.eta x).toNat = (-D'.eta x).toNat
        rw [hA'.eta x hx]
  | succ t ih =>
      intro r hA
      have hrad : r + 2 * (t + 1) * (t + 1) = (r + 4 * t + 2) + 2 * t * t := by ring
      have hAbig : AgreeOn D D' y ((r + 4 * t + 2) + 2 * t * t) := by rwa [hrad] at hA
      have hS : StateAgreeOn (state D t) (state D' t) y (r + 4 * t + 2) :=
        ih (r + 4 * t + 2) hAbig
      have hAdata : AgreeOn D D' y (r + 4 * t + 2) := hA.mono (by nlinarith)
      -- the step of round `t + 1` agrees on the box of radius `r + 2t + 2`
      have hnext : ∀ q : Label d, q.1 ∈ boxFinset y (r + 2 * t + 2) →
          nextPos D (state D t) t q = nextPos D' (state D' t) t q := by
        intro q hq
        have hq4 : q.1 ∈ boxFinset y (r + 4 * t + 2) := boxFinset_mono (by omega) hq
        have hposq : (state D t).pos q = (state D' t).pos q := hS.pos q hq4
        have hactq : (state D t).active q = (state D' t).active q := hS.active q hq4
        have hpb : (state D t).pos q ∈ boxFinset y (r + 3 * t + 2) := by
          have := pos_mem_boxFinset hs (y := y) (r := r + 2 * t + 2) t hq
          exact boxFinset_mono (by omega) this
        have hpb4 : (state D t).pos q ∈ boxFinset y (r + 4 * t + 2) :=
          boxFinset_mono (by omega) hpb
        have hactEq : activeAt D (state D t) t ((state D t).pos q)
            = activeAt D' (state D' t) t ((state D t).pos q) := by
          refine activeAt_congr_box (a := r + 3 * t + 2) hpb
            (fun w hw => hAdata.eta w (boxFinset_mono (by omega) hw))
            (hS.mono (by omega))
        have key : instructionIndex D (state D t) t q
            = instructionIndex D' (state D' t) t q := by
          unfold instructionIndex
          rw [← hposq, hS.departures _ hpb4, hactEq]
        unfold nextPos
        rw [hactq, hposq, key]
        by_cases hb : (state D' t).active q = true
        · rw [if_pos hb, if_pos hb]
          exact hAdata.stack _ (by rwa [hposq] at hpb4) _
        · rw [if_neg hb, if_neg hb]
      have harr : ∀ x ∈ boxFinset y (r + t + 1),
          arrivalsAt D (state D t) t x = arrivalsAt D' (state D' t) t x := by
        intro x hx
        refine arrivalsAt_congr_box (a := r + t + 1) hx
          (fun w hw => hAdata.eta w (boxFinset_mono (by omega) hw))
          (fun p hp => hS.active p (boxFinset_mono (by omega) hp))
          (fun p hp => hnext p (boxFinset_mono (by omega) hp))
      have hsettles : ∀ p : Label d, p.1 ∈ boxFinset y r →
          settles D (state D t) t p = settles D' (state D' t) t p := by
        intro p hp
        have hnp : nextPos D (state D t) t p = nextPos D' (state D' t) t p :=
          hnext p (boxFinset_mono (by omega) hp)
        have hxb : nextPos D (state D t) t p ∈ boxFinset y (r + t + 1) := by
          have := nextPos_mem_boxFinset hs (y := y) (r := r) t hp
          exact boxFinset_mono (by omega) this
        have hxb4 : nextPos D (state D t) t p ∈ boxFinset y (r + 4 * t + 2) :=
          boxFinset_mono (by omega) hxb
        have hfil : ((arrivalsAt D' (state D' t) t (nextPos D (state D t) t p)).filter
              fun q => D.rank (q, t) < D.rank (p, t) ∨
                (D.rank (q, t) = D.rank (p, t) ∧ labelLT q p))
            = ((arrivalsAt D' (state D' t) t (nextPos D (state D t) t p)).filter
              fun q => D'.rank (q, t) < D'.rank (p, t) ∨
                (D'.rank (q, t) = D'.rank (p, t) ∧ labelLT q p)) := by
          refine Finset.filter_congr fun q hq => ?_
          have hq1 : q.1 ∈ boxFinset y (r + 2 * t + 2) := by
            have := mem_boxFinset_of_mem_candidates (a := r + t + 1) hxb
              (arrivalsAt_subset_candidates D' (state D' t) t _ hq)
            exact boxFinset_mono (by omega) this
          rw [hAdata.rank q (boxFinset_mono (by omega) hq1) t,
            hAdata.rank p (boxFinset_mono (by omega) hp) t]
        unfold settles
        rw [hS.active p (boxFinset_mono (by omega) hp), ← hnp, harr _ hxb, hfil,
          hS.holes _ hxb4]
      refine ⟨fun p hp => ?_, fun p hp => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · show (step D (state D t) t).active p = (step D' (state D' t) t).active p
        unfold step
        simp only
        rw [hS.active p (boxFinset_mono (by omega) hp), hsettles p hp]
      · show (step D (state D t) t).pos p = (step D' (state D' t) t).pos p
        exact hnext p (boxFinset_mono (by omega) hp)
      · show (step D (state D t) t).holes x = (step D' (state D' t) t).holes x
        unfold step
        simp only
        rw [hS.holes x (boxFinset_mono (by omega) hx),
          harr x (boxFinset_mono (by omega) hx)]
      · show (step D (state D t) t).departures x = (step D' (state D' t) t).departures x
        unfold step
        simp only
        have hact : activeAt D (state D t) t x = activeAt D' (state D' t) t x := by
          refine activeAt_congr_box (a := r) hx
            (fun w hw => hAdata.eta w (boxFinset_mono (by omega) hw))
            (hS.mono (by omega))
        rw [hS.departures x (boxFinset_mono (by omega) hx), hact]

/-- The odometer at a site of a box is a function of the data on a larger box. -/
theorem particleOdometer_congr_box {D D' : Driver d} (hs : StepsToNeighbour D)
    (y : Site d) (t r : ℕ) (hA : AgreeOn D D' y (r + 2 * t * t)) :
    ∀ x ∈ boxFinset y r, particleOdometer D t x = particleOdometer D' t x :=
  fun x hx => (state_agree_box hs y t r hA).departures x hx

/-! ### No site carries an active particle and an unfilled hole -/

/-- **No site carries an active particle and an unfilled hole.** -/
theorem holeCount_eq_zero_of_activeCount_pos {D : Driver d}
    (t : ℕ) (x : Site d) (h : 0 < activeCount D t x) :
    holeCount D t x = 0 := by
  classical
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  rw [activeAt, Finset.mem_filter] at hp
  obtain ⟨hcand, hact, hpos⟩ := hp
  cases t with
  | zero =>
      have hlt : p.2 < (D.eta p.1).toNat := by
        have : (decide (p.2 < (D.eta p.1).toNat)) = true := hact
        simpa using this
      have hxp : p.1 = x := hpos
      rw [hxp] at hlt
      have hpos' : 0 < (D.eta x).toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
      have : 0 < D.eta x := by omega
      show (state D 0).holes x = 0
      show (-D.eta x).toNat = 0
      omega
  | succ s =>
      set S := state D s with hS
      have hactS : S.active p = true ∧ (settles D S s p) = false := by
        have h2 : (state D (s + 1)).active p = true := hact
        rw [show state D (s + 1) = step D S s from rfl] at h2
        simp only [step, decide_eq_true_eq, Bool.not_eq_true'] at h2
        exact h2
      have hnext : nextPos D S s p = x := hpos
      have hmem : p ∈ arrivalsAt D S s x := by
        rw [arrivalsAt, Finset.mem_filter]
        exact ⟨hcand, hactS.1, hnext⟩
      -- the arrivals of smaller rank than `p` are at least the holes
      have hns : ¬ (((arrivalsAt D S s (nextPos D S s p)).filter
          fun q => D.rank (q, s) < D.rank (p, s) ∨
            (D.rank (q, s) = D.rank (p, s) ∧ labelLT q p)).card
          < S.holes (nextPos D S s p)) := by
        intro hlt
        have : settles D S s p = true := by
          rw [settles]
          simp only [decide_eq_true_eq]
          exact ⟨hactS.1, hlt⟩
        rw [hactS.2] at this
        exact Bool.noConfusion this
      rw [hnext] at hns
      rw [not_lt] at hns
      -- `p` is an arrival but is not of smaller rank than itself
      have hsub : ((arrivalsAt D S s x).filter
          fun q => D.rank (q, s) < D.rank (p, s) ∨
            (D.rank (q, s) = D.rank (p, s) ∧ labelLT q p))
          ⊆ (arrivalsAt D S s x).erase p := by
        intro q hq
        rw [Finset.mem_filter] at hq
        refine Finset.mem_erase.mpr ⟨?_, hq.1⟩
        intro hqp
        subst hqp
        rcases hq.2 with hlt | ⟨-, hlt⟩
        · exact lt_irrefl _ hlt
        · exact labelLT_irrefl q hlt
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hmem] at hcard
      have hpos1 : 1 ≤ (arrivalsAt D S s x).card := Finset.card_pos.mpr ⟨p, hmem⟩
      have hstrict : S.holes x < (arrivalsAt D S s x).card := by omega
      show (state D (s + 1)).holes x = 0
      show S.holes x - (arrivalsAt D S s x).card = 0
      omega

end LatticeProb

end