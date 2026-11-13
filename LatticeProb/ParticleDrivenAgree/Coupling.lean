/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.Coupling at commit 66d817d. The module paths and the namespace `Parking`
   are renamed (to `LatticeProb.ParticleDrivenAgree`), and proofs are adapted to the Lean and Mathlib
   versions of this repository where needed. -/
import LatticeProb.ParticleDrivenAgree.Parallel

/-!
# The one-particle coupling

The one-particle coupling of `parking.tex`, Section 3: the process started from
`η` beside the process started from `η` with one more particle at `x₀`, every
other particle keeping its walk and its uniform variables.

`tagged_invariant` is what an induction over the rounds proves and what
`lem:tagged-monotonicity` reads off: a particle active in the first process is
active in the second and stands where it stands there, and the second process
has no more unfilled holes anywhere.  The two halves feed each other.  A
particle active in the first process is among the arrivals of the second, so
the arrivals of the first are arrivals of the second; a particle that does not
settle in the first has at least as many arrivals of smaller rank ahead of it
in the second and finds no more holes there, so it does not settle in the
second either; and the holes, which shrink by the number of arrivals, stay
below.  Nothing in the argument reads the order on the labels beyond the fact
that both processes break ties by the same rule.
-/

noncomputable section

namespace LatticeProb.ParticleDrivenAgree

open LatticeProb Finset

variable {d : ℕ}

/-! ### The candidate restriction is lossless for the particle process -/

/-- Each coordinate of a single step vector changes by at most `1`. -/
theorem abs_stepVec_le_one (b : Fin d × Bool) (i : Fin d) : |stepVec b i| ≤ 1 := by
  unfold stepVec
  by_cases hb : b.2
  · simp only [hb, if_true]
    by_cases hij : i = b.1
    · subst hij; simp [unit, Pi.single_eq_same]
    · simp [unit, Pi.single_eq_of_ne hij]
  · simp only [hb, Bool.false_eq_true, if_false]
    by_cases hij : i = b.1
    · subst hij; simp [unit, Pi.single_eq_same]
    · simp [unit, Pi.single_eq_of_ne hij]

/-- After `t` rounds, a label's position has moved from its starting site by at
most `t` in each coordinate, by induction on `t` using `abs_stepVec_le_one`. -/
theorem abs_pPos_sub_start_le (D : PDriver d) (t : ℕ) (p : Label d) (i : Fin d) :
    |(pState D t).pos p i - p.1 i| ≤ (t : ℤ) := by
  induction t with
  | zero => simp [pState, initial]
  | succ t ih =>
      have hstep : |(pState D (t + 1)).pos p i - (pState D t).pos p i| ≤ 1 := by
        show |pNextPos D (pState D t) t p i - (pState D t).pos p i| ≤ 1
        unfold pNextPos
        split
        · simpa using abs_stepVec_le_one (D.move (p, t)) i
        · simp
      have hrw : (pState D (t + 1)).pos p i - p.1 i
          = ((pState D (t + 1)).pos p i - (pState D t).pos p i)
            + ((pState D t).pos p i - p.1 i) := by ring
      calc |(pState D (t + 1)).pos p i - p.1 i|
          ≤ |(pState D (t + 1)).pos p i - (pState D t).pos p i|
            + |(pState D t).pos p i - p.1 i| := by rw [hrw]; exact abs_add_le _ _
        _ ≤ 1 + (t : ℤ) := by linarith
        _ = ((t + 1 : ℕ) : ℤ) := by push_cast; ring

/-- If a label is active at time `t`, it was already active at time `0`, since
activity can only be lost during the recursion, never gained. -/
theorem pActive_le (D : PDriver d) (p : Label d) :
    ∀ t : ℕ, (pState D t).active p = true → (pState D 0).active p = true := by
  intro t
  induction t with
  | zero => exact id
  | succ t ih =>
      intro hh
      refine ih ?_
      simp only [pState, pStep, decide_eq_true_eq] at hh
      exact hh.1

/-- An active label's index is below the initial particle count at its site,
by `pActive_le` reduced to the initial state. -/
theorem lt_toNat_of_pActive {D : PDriver d} {t : ℕ} {p : Label d}
    (h : (pState D t).active p = true) : p.2 < (D.eta p.1).toNat := by
  have := pActive_le D p t h
  simpa [pState, initial] using this

/-- `p` belongs to the active particles `pActiveAt D (pState D t) t y` iff it is
active at time `t` and stands at `y`, the candidate condition being automatic
from `abs_pPos_sub_start_le`. -/
theorem mem_pActiveAt_iff (D : PDriver d) (t : ℕ) (y : Site d) (p : Label d) :
    p ∈ pActiveAt D (pState D t) t y
      ↔ ((pState D t).active p = true ∧ (pState D t).pos p = y) := by
  unfold pActiveAt
  rw [Finset.mem_filter]
  refine ⟨fun hp => hp.2, fun hp => ⟨?_, hp⟩⟩
  refine mem_candidates (fun i => ?_) (lt_toNat_of_pActive hp.1)
  have := abs_pPos_sub_start_le D t p i
  rw [hp.2] at this
  rwa [abs_sub_comm]

/-- `p` belongs to the arrivals `pArrivalsAt D (pState D t) t x` iff it is active
at time `t` and its next position is `x`, the candidate condition again being
automatic from the one-step displacement bound. -/
theorem mem_pArrivalsAt_iff (D : PDriver d) (t : ℕ) (x : Site d) (p : Label d) :
    p ∈ pArrivalsAt D (pState D t) t x
      ↔ ((pState D t).active p = true ∧ pNextPos D (pState D t) t p = x) := by
  unfold pArrivalsAt
  rw [Finset.mem_filter]
  refine ⟨fun hp => hp.2, fun hp => ⟨?_, hp⟩⟩
  refine mem_candidates (fun i => ?_) (lt_toNat_of_pActive hp.1)
  have h1 := abs_pPos_sub_start_le D t p i
  have h2 : |pNextPos D (pState D t) t p i - (pState D t).pos p i| ≤ 1 := by
    unfold pNextPos
    split
    · simpa using abs_stepVec_le_one (D.move (p, t)) i
    · simp
  rw [hp.2] at h2
  have hrw : p.1 i - x i
      = (p.1 i - (pState D t).pos p i) + ((pState D t).pos p i - x i) := by ring
  have h1' : |p.1 i - (pState D t).pos p i| ≤ (t : ℤ) := by rwa [abs_sub_comm]
  have h2' : |(pState D t).pos p i - x i| ≤ 1 := by rwa [abs_sub_comm]
  calc |p.1 i - x i| ≤ |p.1 i - (pState D t).pos p i| + |(pState D t).pos p i - x i| := by
        rw [hrw]; exact abs_add_le _ _
    _ ≤ (t : ℤ) + 1 := by linarith
    _ = ((t + 1 : ℕ) : ℤ) := by push_cast; ring

/-! ### How many arrivals settle -/

/-- The particles that settle at `x` in round `t + 1`. -/
def pSettledAt (D : PDriver d) (t : ℕ) (x : Site d) : Finset (Label d) :=
  (pArrivalsAt D (pState D t) t x).filter fun p => pSettles D (pState D t) t p

/-- The particles that settle at `x` in round `t + 1` are among the arrivals
there. -/
theorem pSettledAt_subset' (D : PDriver d) (t : ℕ) (x : Site d) :
    pSettledAt D t x ⊆ pArrivalsAt D (pState D t) t x := Finset.filter_subset _ _

/-- The arrivals that settle are those the round's order puts below the number
of holes, so there are `min (arrivals) (holes)` of them. -/
theorem pSettledAt_eq (D : PDriver d) (t : ℕ) (x : Site d) :
    pSettledAt D t x
      = (pArrivalsAt D (pState D t) t x).filter fun p =>
          ((pArrivalsAt D (pState D t) t x).filter fun q => prec D.rank t q p).card
            < pHoleCount D t x := by
  unfold pSettledAt
  refine Finset.filter_congr fun p hp => ?_
  have hp' := (mem_pArrivalsAt_iff D t x p).mp hp
  unfold pSettles
  rw [hp'.2]
  simp only [decide_eq_true_eq, hp'.1, true_and]
  simp only [prec, pHoleCount]
  convert Iff.rfl
  congr 1

/-- The number of arrivals at `x` that settle is `min(arrivals, holes)`, applying
`card_filter_countLT_lt` to the total, irreflexive, transitive priority order
`prec`. -/
theorem card_pSettledAt (h : LabelOrder d) (D : PDriver d) (t : ℕ) (x : Site d) :
    (pSettledAt D t x).card
      = min ((pArrivalsAt D (pState D t) t x).card) (pHoleCount D t x) := by
  rw [pSettledAt_eq]
  exact card_filter_countLT_lt (prec_irrefl h D.rank t) (prec_trans h D.rank t)
    (prec_total h D.rank t) _

/-- If `η ≤ η'` pointwise, the candidate labels for `y` at round `r` under `η`
are a subset of those under `η'`, since a larger configuration only admits more
label indices at each site. -/
theorem candidates_mono {η η' : Site d → ℤ} (h : ∀ x, η x ≤ η' x) (y : Site d) (r : ℕ) :
    candidates η y r ⊆ candidates η' y r := by
  intro p hp
  simp only [candidates, Finset.mem_biUnion, Finset.mem_map, Finset.mem_range,
    Function.Embedding.coeFn_mk] at hp ⊢
  obtain ⟨x, hx, i, hi, rfl⟩ := hp
  exact ⟨x, hx, i, lt_of_lt_of_le hi (Int.toNat_le_toNat (h x)), rfl⟩

/-- Adding one particle at `x₀` can only increase the configuration pointwise. -/
theorem le_addParticle (x₀ : Site d) (η : Site d → ℤ) (x : Site d) :
    η x ≤ addParticle x₀ η x := by
  unfold addParticle; split <;> omega

/-- An active label's next position is its current position plus the step
vector of its move instruction. -/
theorem pNextPos_of_active (D : PDriver d) (S : State d) (t : ℕ) (p : Label d)
    (h : S.active p = true) : pNextPos D S t p = S.pos p + stepVec (D.move (p, t)) := by
  simp [pNextPos, h]

/-- A label is active at `t + 1` iff it was active at `t` and did not settle in
round `t`. -/
theorem pActive_succ_iff (D : PDriver d) (t : ℕ) (p : Label d) :
    (pState D (t + 1)).active p = true
      ↔ ((pState D t).active p = true ∧ pSettles D (pState D t) t p = false) := by
  simp [pState, pStep]

/-- `pState D (t + 1)`'s position at `p` unfolds to `pNextPos D (pState D t) t p`,
by definition of the recursion. -/
theorem pPos_succ (D : PDriver d) (t : ℕ) (p : Label d) :
    (pState D (t + 1)).pos p = pNextPos D (pState D t) t p := rfl

/-- The hole count at `x` after round `t + 1` is the hole count at `t` minus the
number of arrivals there, by definition of the recursion. -/
theorem pHoles_succ (D : PDriver d) (t : ℕ) (x : Site d) :
    (pState D (t + 1)).holes x
      = (pState D t).holes x - (pArrivalsAt D (pState D t) t x).card := rfl

/-- Adding a particle to a driver does not change its move instructions. -/
theorem addParticleDriver_move (x₀ : Site d) (D : PDriver d) :
    (addParticleDriver x₀ D).move = D.move := rfl

/-- Adding a particle to a driver does not change its priority order. -/
theorem addParticleDriver_rank (x₀ : Site d) (D : PDriver d) :
    (addParticleDriver x₀ D).rank = D.rank := rfl

/-- The invariant behind `lem:tagged-monotonicity`. -/
theorem tagged_invariant (D : PDriver d) (x₀ : Site d) (t : ℕ) :
    (∀ p, (pState D t).active p = true →
        (pState (addParticleDriver x₀ D) t).active p = true ∧
          (pState D t).pos p = (pState (addParticleDriver x₀ D) t).pos p) ∧
    (∀ x, (pState (addParticleDriver x₀ D) t).holes x ≤ (pState D t).holes x) := by
  classical
  have hEta : ∀ x, D.eta x ≤ (addParticleDriver x₀ D).eta x :=
    fun x => le_addParticle x₀ D.eta x
  induction t with
  | zero =>
      refine ⟨fun p hp => ⟨?_, rfl⟩, fun x => ?_⟩
      · simp only [pState, initial, decide_eq_true_eq] at hp ⊢
        exact lt_of_lt_of_le hp (Int.toNat_le_toNat (hEta p.1))
      · simp only [pState, initial]
        exact Int.toNat_le_toNat (by have := hEta x; omega)
  | succ t ih =>
      obtain ⟨ihact, ihhole⟩ := ih
      have hnext : ∀ p, (pState D t).active p = true →
          pNextPos D (pState D t) t p
            = pNextPos (addParticleDriver x₀ D) (pState (addParticleDriver x₀ D) t) t p := by
        intro p hact
        obtain ⟨hact', hposeq⟩ := ihact p hact
        rw [pNextPos_of_active _ _ _ _ hact, pNextPos_of_active _ _ _ _ hact',
          addParticleDriver_move, hposeq]
      have harr : ∀ x, pArrivalsAt D (pState D t) t x
          ⊆ pArrivalsAt (addParticleDriver x₀ D) (pState (addParticleDriver x₀ D) t) t x := by
        intro x p hp
        simp only [pArrivalsAt, Finset.mem_filter] at hp ⊢
        obtain ⟨hc, hact, hpos⟩ := hp
        obtain ⟨hact', -⟩ := ihact p hact
        exact ⟨candidates_mono hEta x (t + 1) hc, hact', by rw [← hnext p hact]; exact hpos⟩
      have hsettles : ∀ (D₁ : PDriver d) (S : State d) (p : Label d),
          pSettles D₁ S t p = false ↔ ¬ (S.active p = true ∧
            ((pArrivalsAt D₁ S t (pNextPos D₁ S t p)).filter fun q =>
              D₁.rank (q, t) < D₁.rank (p, t) ∨
                (D₁.rank (q, t) = D₁.rank (p, t) ∧ labelLT q p)).card
              < S.holes (pNextPos D₁ S t p)) := by
        intro D₁ S p; simp [pSettles]
      have hset : ∀ p, (pState D t).active p = true →
          pSettles D (pState D t) t p = false →
          pSettles (addParticleDriver x₀ D) (pState (addParticleDriver x₀ D) t) t p = false := by
        intro p hact hno
        obtain ⟨hact', -⟩ := ihact p hact
        rw [hsettles] at hno ⊢
        rintro ⟨-, hlt⟩
        rw [← hnext p hact] at hlt
        refine hno ⟨hact, lt_of_le_of_lt ?_ (lt_of_lt_of_le hlt (ihhole _))⟩
        exact Finset.card_le_card (Finset.filter_subset_filter _ (harr _))
      refine ⟨fun p hp => ?_, fun x => ?_⟩
      · rw [pActive_succ_iff] at hp
        obtain ⟨hact, hno⟩ := hp
        obtain ⟨hact', -⟩ := ihact p hact
        exact ⟨(pActive_succ_iff _ _ _).mpr ⟨hact', hset p hact hno⟩,
          by rw [pPos_succ, pPos_succ]; exact hnext p hact⟩
      · rw [pHoles_succ, pHoles_succ]
        have h1 := ihhole x
        have h2 := Finset.card_le_card (harr x)
        omega

end LatticeProb.ParticleDrivenAgree

end
