/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.Parallel at commit 66d817d. The module paths and the namespace `Parking`
   are renamed (to `LatticeProb.ParticleDrivenAgree`), and proofs are adapted to the Lean and Mathlib
   versions of this repository where needed. -/
import LatticeProb.ParticleDrivenAgree.Odometer

/-!
# Lemma 3.1: the parallel toppling recursion

Lemma 3.1 of `parking.tex`: the odometer of the particle system obeys the
parallel recursion `U_{n+1} = (η + ∑_y I_{y,·}(U_n(y)))⁺`.

The proof has three parts.  A strict total order on a finite set numbers its
elements `0, …, |A| - 1`, and exactly `min(|A|, H)` of them get a number below
`H`: that is `image_countLT` and `card_filter_countLT_lt`.  Applied to the
labels of the particles active at a site, the first says that the instructions
they read in one round are exactly those whose index lies between the
departures before and after the round, so the arrivals at `x` through `n`
rounds are counted by the instructions of the neighbours of `x` that point at
`x`.  Applied to the arrivals at a site, ordered by rank with ties broken by
the label, the second says that exactly `min(arrivals, holes)` of them settle;
the holes are therefore what is left of the initial ones after the arrivals,
and the odometer identity follows by induction on the rounds.

Ties in the ranks need no separate treatment: the order that decides which
arrivals fill the holes falls back on the label order, which is linear.
-/

noncomputable section

namespace LatticeProb.ParticleDrivenAgree

open LatticeProb Finset

variable {α : Type*} [DecidableEq α]

/-- The number of elements of `A` that a strict total order puts below `p`. -/
theorem countLT_lt_card {A : Finset α} {r : α → α → Prop} [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) {p : α} (hp : p ∈ A) :
    (A.filter fun q => r q p).card < A.card := by
  have hsub : (A.filter fun q => r q p) ⊆ A.erase p := by
    intro q hq
    rw [Finset.mem_filter] at hq
    refine Finset.mem_erase.mpr ⟨?_, hq.1⟩
    rintro rfl
    exact hirr q hq.2
  exact lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem hp)

omit [DecidableEq α] in
/-- The count of elements below `p` is strictly less than the count below `q` whenever
`r p q`: every element counted for `p` is also counted for `q` (by transitivity), plus `p`
itself is counted for `q` but not for itself (by irreflexivity). -/
theorem countLT_lt_countLT {A : Finset α} {r : α → α → Prop} [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) (htr : ∀ a b c, r a b → r b c → r a c)
    {p q : α} (hp : p ∈ A) (h : r p q) :
    (A.filter fun z => r z p).card < (A.filter fun z => r z q).card := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, htr z p q hz.2 h⟩
  · intro hsub
    have := hsub (Finset.mem_filter.mpr ⟨hp, h⟩)
    rw [Finset.mem_filter] at this
    exact hirr p this.2

/-- Under a strict total order, the map sending each element of `A` to the count of elements
below it is injective on `A`: distinct comparable elements have distinct counts by
`countLT_lt_countLT`, applied to whichever of the two the order puts first. -/
theorem countLT_injOn {A : Finset α} {r : α → α → Prop} [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) (htr : ∀ a b c, r a b → r b c → r a c)
    (htot : ∀ a b, a ≠ b → r a b ∨ r b a) :
    Set.InjOn (fun p => (A.filter fun q => r q p).card) A := by
  intro p hp q hq h
  by_contra hne
  rcases htot p q hne with hlt | hlt
  · exact absurd h (ne_of_lt (countLT_lt_countLT hirr htr hp hlt))
  · exact absurd h.symm (ne_of_lt (countLT_lt_countLT hirr htr hq hlt))

/-- Under a strict total order the counts of smaller elements are exactly
`0, …, |A| - 1`. -/
theorem image_countLT {A : Finset α} {r : α → α → Prop} [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) (htr : ∀ a b c, r a b → r b c → r a c)
    (htot : ∀ a b, a ≠ b → r a b ∨ r b a) :
    A.image (fun p => (A.filter fun q => r q p).card) = Finset.range A.card := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (countLT_lt_card hirr hp)
  · rw [Finset.card_range,
      Finset.card_image_of_injOn (countLT_injOn hirr htr htot)]

/-- Under a strict total order, exactly `min |A| H` elements of `A` have fewer
than `H` elements below them. -/
theorem card_filter_countLT_lt {A : Finset α} {r : α → α → Prop} [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) (htr : ∀ a b c, r a b → r b c → r a c)
    (htot : ∀ a b, a ≠ b → r a b ∨ r b a) (H : ℕ) :
    (A.filter fun p => (A.filter fun q => r q p).card < H).card = min A.card H := by
  classical
  set c : α → ℕ := fun p => (A.filter fun q => r q p).card with hc
  have hinj : Set.InjOn c (A.filter fun p => c p < H) :=
    (countLT_injOn hirr htr htot).mono (by exact_mod_cast Finset.filter_subset _ A)
  have himg : (A.filter fun p => c p < H).image c
      = (Finset.range A.card).filter fun k => k < H := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨p, ⟨hp, hlt⟩, rfl⟩
      exact ⟨countLT_lt_card hirr hp, hlt⟩
    · rintro ⟨hk, hkH⟩
      have : k ∈ (Finset.range A.card) := Finset.mem_range.mpr hk
      rw [← image_countLT hirr htr htot] at this
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp this
      exact ⟨p, ⟨hp, hkH⟩, rfl⟩
  have := Finset.card_image_of_injOn hinj
  rw [himg] at this
  rw [← this,
    show (Finset.range A.card).filter (fun k => k < H) = Finset.range (min A.card H) by
      ext k; simp,
    Finset.card_range]

section Process

variable {d : ℕ}

/-- The strict total order hypothesis on labels that the model needs: it is
what makes the co-departing particles at a site read distinct instructions. -/
structure LabelOrder (d : ℕ) : Prop where
  irr : ∀ p : Label d, ¬ labelLT p p
  trans : ∀ p q z : Label d, labelLT p q → labelLT q z → labelLT p z
  total : ∀ p q : Label d, p ≠ q → labelLT p q ∨ labelLT q p

/-- The order in which the arrivals of a round fill the holes: by rank, with
ties broken by the label. -/
def prec (rank : Label d × ℕ → ℝ) (t : ℕ) (q p : Label d) : Prop :=
  rank (q, t) < rank (p, t) ∨ (rank (q, t) = rank (p, t) ∧ labelLT q p)

/-- `prec rank t` is decidable, via classical choice, since it is a proposition built from
the linear order `<` and `=` on `ℝ` together with `labelLT`. -/
instance (rank : Label d × ℕ → ℝ) (t : ℕ) : DecidableRel (prec rank t) :=
  Classical.decRel _

/-- `prec` is irreflexive: an element neither has strictly smaller rank than itself nor,
by `LabelOrder.irr`, a strictly smaller label at equal rank. -/
theorem prec_irrefl (h : LabelOrder d) (rank : Label d × ℕ → ℝ) (t : ℕ) (p : Label d) :
    ¬ prec rank t p p := by
  rintro (hlt | ⟨-, hlab⟩)
  · exact lt_irrefl _ hlt
  · exact h.irr p hlab

/-- `prec` is transitive, combining the transitivity of `<` on ranks with `LabelOrder.trans`
on labels for the equal-rank case. -/
theorem prec_trans (h : LabelOrder d) (rank : Label d × ℕ → ℝ) (t : ℕ) (p q z : Label d) :
    prec rank t p q → prec rank t q z → prec rank t p z := by
  rintro (h1 | ⟨e1, l1⟩) (h2 | ⟨e2, l2⟩)
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (e2 ▸ h1)
  · exact Or.inl (e1 ▸ h2)
  · exact Or.inr ⟨e1.trans e2, h.trans p q z l1 l2⟩

/-- `prec` is total on distinct labels: trichotomy on the ranks settles the case of unequal
rank, and `LabelOrder.total` breaks ties at equal rank. -/
theorem prec_total (h : LabelOrder d) (rank : Label d × ℕ → ℝ) (t : ℕ) (p q : Label d)
    (hne : p ≠ q) : prec rank t p q ∨ prec rank t q p := by
  rcases lt_trichotomy (rank (p, t)) (rank (q, t)) with hlt | heq | hgt
  · exact Or.inl (Or.inl hlt)
  · rcases h.total p q hne with hl | hl
    · exact Or.inl (Or.inr ⟨heq, hl⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hl⟩)
  · exact Or.inr (Or.inl hgt)

/-- The number of particles that settle at `x` in round `t + 1` is the smaller
of the number of arrivals and the number of holes.  No assumption on the ranks
is needed: ties are broken by the label order. -/
theorem card_settledAt' (h : LabelOrder d) (D : Driver d) (t : ℕ) (x : Site d) :
    (settledAt D t x).card
      = min ((arrivalsAt D (state D t) t x).card) (holeCount D t x) := by
  classical
  set S := state D t with hS
  set A := arrivalsAt D S t x with hA
  have hfilter : settledAt D t x
      = A.filter fun p => (A.filter fun q => prec D.rank t q p).card < holeCount D t x := by
    unfold settledAt
    rw [← hS, ← hA]
    refine Finset.filter_congr fun p hp => ?_
    have hp' := Finset.mem_filter.mp (hA ▸ hp)
    have hact : S.active p = true := hp'.2.1
    have hpos : nextPos D S t p = x := hp'.2.2
    unfold settles
    rw [hpos]
    simp only [decide_eq_true_eq, hact, true_and, ← hA]
    simp only [prec, holeCount, ← hS]
    convert Iff.rfl
    congr 1
  rw [hfilter]
  exact card_filter_countLT_lt (prec_irrefl h D.rank t) (prec_trans h D.rank t)
    (prec_total h D.rank t) _

/-- For a particle `p` active at `y`, its instruction index is the departures already made
from `y` plus the count of particles at `y` whose label precedes `p`'s, unfolding
`instructionIndex` at `S.pos p = y`. -/
theorem instructionIndex_of_mem {D : Driver d} {S : State d} {t : ℕ} {y : Site d}
    {p : Label d} (hp : p ∈ activeAt D S t y) :
    instructionIndex D S t p
      = S.departures y + ((activeAt D S t y).filter fun q => labelLT q p).card := by
  have hpos : S.pos p = y := (Finset.mem_filter.mp hp).2.2
  unfold instructionIndex
  rw [hpos]

/-- For a particle `p` active at `y`, its next position is read off the departure stack at
`y` at its own instruction index, unfolding `nextPos` at `S.active p = true` and
`S.pos p = y`. -/
theorem nextPos_of_mem {D : Driver d} {S : State d} {t : ℕ} {y : Site d}
    {p : Label d} (hp : p ∈ activeAt D S t y) :
    nextPos D S t p = D.stack (y, instructionIndex D S t p) := by
  have hact : S.active p = true := (Finset.mem_filter.mp hp).2.1
  have hpos : S.pos p = y := (Finset.mem_filter.mp hp).2.2
  unfold nextPos
  rw [if_pos hact, hpos]

/-- Within one round the instructions read at `y` are exactly those whose index
lies between the departures before and after the round. -/
theorem card_filter_nextPos (h : LabelOrder d) (D : Driver d) (S : State d) (t : ℕ)
    (y x : Site d) :
    ((activeAt D S t y).filter fun p => nextPos D S t p = x).card
      = ((Finset.Ico (S.departures y) (S.departures y + (activeAt D S t y).card)).filter
          fun j => D.stack (y, j) = x).card := by
  classical
  refine Finset.card_bij (fun p _ => instructionIndex D S t p) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp, hnx⟩ := hp
    rw [Finset.mem_filter, Finset.mem_Ico, instructionIndex_of_mem hp]
    refine ⟨⟨Nat.le_add_right _ _, by
      have := countLT_lt_card (r := labelLT (d := d)) h.irr hp
      omega⟩, ?_⟩
    rw [← instructionIndex_of_mem hp, ← nextPos_of_mem hp]
    exact hnx
  · intro p hp q hq hpq
    rw [Finset.mem_filter] at hp hq
    rw [instructionIndex_of_mem hp.1, instructionIndex_of_mem hq.1] at hpq
    exact countLT_injOn (r := labelLT (d := d)) h.irr h.trans h.total hp.1 hq.1
      (Nat.add_left_cancel hpq)
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_Ico] at hj
    obtain ⟨⟨hlo, hhi⟩, hst⟩ := hj
    have hmem : j - S.departures y ∈ Finset.range (activeAt D S t y).card :=
      Finset.mem_range.mpr (by omega)
    rw [← image_countLT (r := labelLT (d := d)) h.irr h.trans h.total] at hmem
    obtain ⟨p, hp, hcnt⟩ := Finset.mem_image.mp hmem
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, ?_⟩
    · rw [nextPos_of_mem hp, instructionIndex_of_mem hp, hcnt]
      rw [show S.departures y + (j - S.departures y) = j by omega]
      exact hst
    · rw [instructionIndex_of_mem hp, hcnt]
      omega

set_option maxHeartbeats 400000 in
/-- The arrivals at `x` in a round, split according to the neighbour of `x` the
arriving particle came from. -/
theorem arrivalsAt_eq_biUnion {D : Driver d}
    (hn : ∀ q : Site d × ℕ, D.stack q ∈ nbrFinset q.1) (t : ℕ) (x : Site d) :
    arrivalsAt D (state D t) t x
      = (nbrFinset x).biUnion fun y =>
          (activeAt D (state D t) t y).filter fun p =>
            nextPos D (state D t) t p = x := by
  have hstep := stepsToNeighbour_of_mem hn
  ext p
  rw [mem_arrivalsAt_iff hstep, Finset.mem_biUnion]
  constructor
  · rintro ⟨hact, hpos⟩
    have hmem : p ∈ activeAt D (state D t) t ((state D t).pos p) :=
      (mem_activeAt_iff hstep t _ p).mpr ⟨hact, rfl⟩
    refine ⟨(state D t).pos p, ?_, Finset.mem_filter.mpr ⟨hmem, hpos⟩⟩
    refine nbrFinset_symm ?_
    rw [← hpos, nextPos_of_mem hmem]
    exact hn ((state D t).pos p, instructionIndex D (state D t) t p)
  · rintro ⟨y, -, hp⟩
    rw [Finset.mem_filter] at hp
    exact ⟨(Finset.mem_filter.mp hp.1).2.1, hp.2⟩

set_option maxHeartbeats 400000 in
/-- The number of arrivals at `x` in one round is the sum, over neighbours `y` of `x`, of
the number of particles active at `y` whose next position is `x`, since
`arrivalsAt_eq_biUnion` writes the arrivals as a union over disjoint neighbour classes. -/
theorem card_arrivalsAt {D : Driver d}
    (hn : ∀ q : Site d × ℕ, D.stack q ∈ nbrFinset q.1) (t : ℕ) (x : Site d) :
    (arrivalsAt D (state D t) t x).card
      = ∑ y ∈ nbrFinset x, ((activeAt D (state D t) t y).filter fun p =>
          nextPos D (state D t) t p = x).card := by
  rw [arrivalsAt_eq_biUnion hn]
  refine Finset.card_biUnion fun y hy z hz hyz => ?_
  refine Finset.disjoint_left.mpr fun p hp hq => hyz ?_
  rw [Finset.mem_filter] at hp hq
  rw [← (Finset.mem_filter.mp hp.1).2.2, ← (Finset.mem_filter.mp hq.1).2.2]

/-- The arrivals at `x` through the first `n` rounds. -/
def totalArrivals (D : Driver d) (n : ℕ) (x : Site d) : ℕ :=
  ∑ t ∈ Finset.range n, (arrivalsAt D (state D t) t x).card

/-- `totalArrivals` accumulates one more round's arrivals: the sum defining it splits off
its last term by `Finset.sum_range_succ`. -/
theorem totalArrivals_succ (D : Driver d) (n : ℕ) (x : Site d) :
    totalArrivals D (n + 1) x
      = totalArrivals D n x + (arrivalsAt D (state D n) n x).card := by
  simp [totalArrivals, Finset.sum_range_succ]

/-- The holes at `x` are what is left of the initial ones after the arrivals. -/
theorem holeCount_eq (D : Driver d) (n : ℕ) (x : Site d) :
    holeCount D n x = (-(D.eta x)).toNat - totalArrivals D n x := by
  induction n with
  | zero => simp [holeCount, state, initial, totalArrivals]
  | succ n ih => rw [holeCount_succ, ih, totalArrivals_succ, Nat.sub_sub]

/-- The odometer identity of `lem:parallel`, with the arrivals still counted as
arrivals. -/
theorem odometer_eq (h : LabelOrder d) {D : Driver d}
    (hn : ∀ q : Site d × ℕ, D.stack q ∈ nbrFinset q.1) (n : ℕ) (x : Site d) :
    (particleOdometer D (n + 1) x : ℤ) = max 0 (D.eta x + (totalArrivals D n x : ℤ)) := by
  have hstep := stepsToNeighbour_of_mem hn
  induction n with
  | zero =>
      rw [particleOdometer_succ, show particleOdometer D 0 x = 0 from rfl,
        activeCount_zero]
      simp only [totalArrivals, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, add_zero]
      omega
  | succ n ih =>
      have hact := activeCount_succ hstep n x
      have hset := card_settledAt' h D n x
      have hhole := holeCount_eq D n x
      have harr := totalArrivals_succ D n x
      have hsub : (settledAt D n x).card ≤ (arrivalsAt D (state D n) n x).card :=
        Finset.card_le_card (settledAt_subset D n x)
      rw [particleOdometer_succ, hact]
      have hcast : ((particleOdometer D (n + 1) x : ℤ)) =
          max 0 (D.eta x + (totalArrivals D n x : ℤ)) := ih
      have hpos : (0 : ℤ) ≤ ((-(D.eta x)).toNat : ℤ) := Int.natCast_nonneg _
      have h1 : ((-(D.eta x)).toNat : ℤ) = max 0 (-(D.eta x)) := by
        simp [max_comm]
      push_cast [hset, hhole, harr] at *
      omega

/-- Summing, over `t < n`, the count of `P` in the interval `Ico (u t) (u (t + 1))` for a
monotone sequence `u` with `u 0 = 0` gives the count of `P` in `range (u n)`: the intervals
partition `range (u n)` by `Finset.Ico_union_Ico_eq_Ico`, proved by induction on `n`. -/
theorem sum_Ico_filter (P : ℕ → Prop) [DecidablePred P] (u : ℕ → ℕ) (h0 : u 0 = 0)
    (hm : Monotone u) (n : ℕ) :
    ∑ t ∈ Finset.range n, ((Finset.Ico (u t) (u (t + 1))).filter P).card
      = ((Finset.range (u n)).filter P).card := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hle : u n ≤ u (n + 1) := hm (Nat.le_succ n)
      have hsplit : Finset.range (u (n + 1))
          = Finset.range (u n) ∪ Finset.Ico (u n) (u (n + 1)) := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
          Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hle]
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint]
      exact Finset.disjoint_filter_filter
        (by rw [Finset.range_eq_Ico]; exact Finset.Ico_disjoint_Ico_consecutive 0 (u n) (u (n + 1)))

/-- The arrivals at `x` in round `t` are counted, neighbour by neighbour, by the departure
indices in the window `Ico (particleOdometer D t y) (particleOdometer D (t + 1) y)` whose
stack entry points at `x`: combines `card_arrivalsAt` with `card_filter_nextPos`. -/
theorem card_arrivalsAt_Ico (h : LabelOrder d) {D : Driver d}
    (hn : ∀ q : Site d × ℕ, D.stack q ∈ nbrFinset q.1) (t : ℕ) (x : Site d) :
    (arrivalsAt D (state D t) t x).card
      = ∑ y ∈ nbrFinset x,
          ((Finset.Ico (particleOdometer D t y) (particleOdometer D (t + 1) y)).filter
            fun j => D.stack (y, j) = x).card := by
  rw [card_arrivalsAt hn]
  exact Finset.sum_congr rfl fun y _ => card_filter_nextPos h D (state D t) t y x

/-- The arrivals at `x` through the first `n` rounds are counted by the
instructions of the neighbours of `x` that point at `x`. -/
theorem totalArrivals_eq (h : LabelOrder d) {D : Driver d}
    (hn : ∀ q : Site d × ℕ, D.stack q ∈ nbrFinset q.1) (n : ℕ) (x : Site d) :
    totalArrivals D n x
      = ∑ y ∈ nbrFinset x, arrivals D.stack y x (particleOdometer D n y) := by
  unfold totalArrivals arrivals
  rw [Finset.sum_congr rfl fun t _ => card_arrivalsAt_Ico h hn t x, Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ =>
    sum_Ico_filter _ (fun t => particleOdometer D t y) rfl (particleOdometer_mono D y) n

/-- Lemma 3.1 of the paper, for a driver whose instructions are neighbours of
the site carrying them and whose labels are linearly ordered. -/
theorem parallel_of_labelOrder (h : LabelOrder d) {D : Driver d}
    (hn : ∀ q : Site d × ℕ, D.stack q ∈ nbrFinset q.1) :
    (∀ x, particleOdometer D 0 x = 0) ∧
    ∀ (n : ℕ) (x : Site d),
      (particleOdometer D (n + 1) x : ℤ)
        = max 0 (D.eta x + ∑ y ∈ nbrFinset x,
            (arrivals D.stack y x (particleOdometer D n y) : ℤ)) := by
  refine ⟨fun x => rfl, fun n x => ?_⟩
  rw [odometer_eq h hn n x, totalArrivals_eq h hn n x]
  push_cast
  ring_nf

end Process


/-- The labels are linearly ordered, so the model reads one instruction per
departure and fills the holes in a definite order. -/
theorem labelOrder (d : ℕ) : LabelOrder d where
  irr := labelLT_irrefl
  trans := fun _ _ _ h₁ h₂ => labelLT_trans h₁ h₂
  total := fun p q hne => by
    rcases labelLT_trichotomous p q with h | h | h
    · exact Or.inl h
    · exact absurd h hne
    · exact Or.inr h

end LatticeProb.ParticleDrivenAgree

end
