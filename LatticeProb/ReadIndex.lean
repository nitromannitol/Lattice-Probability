/-
Which stack entry a particle reads, and that no entry is read twice.

In the stack construction the randomness sits at the sites: the `j`-th
departure from `y` follows the instruction `stack (y, j)`.  A particle `p`
active after round `t` departs from `(state D t).pos p` and reads the
instruction whose index is `instructionIndex`, the departures from that site so
far plus the number of particles leaving it in the same round with a smaller
label.  `readIndex` is that pair.

The point of the file is `readIndex_injective`: distinct departures read
distinct entries, so the whole process reads the family `stack` along an
injective sequence of coordinates and never returns to one.  That is the
hypothesis `IsExploration.fresh` of `LatticeProb.Prob.Exploration`, which is
why the instructions a single particle reads are independent draws and why
distinct particles read independent instructions.

The proof is an interval argument at each site.  The departures of round
`t + 1` from `y` read exactly the indices in
`[U_t(y), U_{t+1}(y))`: the offset of a departing particle within its round is
its rank among the co-departing particles for the label order, so it runs over
`0, …, A_t(y) - 1` injectively, and the odometer is monotone, so different
rounds use disjoint intervals.
-/
import LatticeProb.ParticleHoleLemmas

noncomputable section

namespace LatticeProb

open Finset

variable {d : ℕ}

/-- The stack entry `p` reads in round `t + 1`: the site it departs from, and
the index of the instruction it takes there. -/
def readIndex (D : Driver d) (t : ℕ) (p : Label d) : Site d × ℕ :=
  ((state D t).pos p, instructionIndex D (state D t) t p)

/-- The offset of `p` within the departures of its round is its rank for the
label order among the particles leaving the same site in the same round. -/
theorem instructionIndex_eq_add_rankIn (D : Driver d) (t : ℕ) (p : Label d) :
    instructionIndex D (state D t) t p
      = particleOdometer D t ((state D t).pos p)
        + rankIn (activeAt D (state D t) t ((state D t).pos p)) labelKey p := by
  show (state D t).departures ((state D t).pos p)
      + ((activeAt D (state D t) t ((state D t).pos p)).filter fun q => labelLT q p).card
    = (state D t).departures ((state D t).pos p)
      + ((activeAt D (state D t) t ((state D t).pos p)).filter
          fun q => labelKey q < labelKey p).card
  congr 2
  exact Finset.filter_congr fun x _ => Iff.rfl

/-- The index a departing particle reads is at least the odometer of its site. -/
theorem le_instructionIndex (D : Driver d) (t : ℕ) (p : Label d) :
    particleOdometer D t ((state D t).pos p) ≤ instructionIndex D (state D t) t p :=
  Nat.le_add_right _ _

/-- The index a departing particle reads is below the odometer of its site
after the round. -/
theorem instructionIndex_lt {D : Driver d} (h : StepsToNeighbour D) (t : ℕ) {p : Label d}
    (hp : (state D t).active p = true) :
    instructionIndex D (state D t) t p
      < particleOdometer D (t + 1) ((state D t).pos p) := by
  have hmem : p ∈ activeAt D (state D t) t ((state D t).pos p) :=
    (mem_activeAt_iff h t _ p).mpr ⟨hp, rfl⟩
  rw [instructionIndex_eq_add_rankIn, particleOdometer_succ]
  exact Nat.add_lt_add_left (rankIn_lt_card hmem) _

/-- Two particles departing from the same site in the same round read different
instructions. -/
theorem instructionIndex_injective {D : Driver d} (h : StepsToNeighbour D) (t : ℕ)
    {p q : Label d} (hp : (state D t).active p = true) (hq : (state D t).active q = true)
    (hpos : (state D t).pos p = (state D t).pos q)
    (hidx : instructionIndex D (state D t) t p = instructionIndex D (state D t) t q) :
    p = q := by
  set y := (state D t).pos p with hy
  have hmp : p ∈ activeAt D (state D t) t y := (mem_activeAt_iff h t y p).mpr ⟨hp, rfl⟩
  have hmq : q ∈ activeAt D (state D t) t y :=
    (mem_activeAt_iff h t y q).mpr ⟨hq, hpos.symm⟩
  have hrank : rankIn (activeAt D (state D t) t y) labelKey p
      = rankIn (activeAt D (state D t) t y) labelKey q := by
    have hp' := instructionIndex_eq_add_rankIn D t p
    have hq' := instructionIndex_eq_add_rankIn D t q
    rw [← hy] at hp'
    rw [← hpos] at hq'
    omega
  have hinj : Set.InjOn labelKey ((activeAt D (state D t) t y : Finset (Label d)) : Set (Label d)) :=
    fun a _ b _ hab => labelKey_injective hab
  exact rankIn_injOn hinj (Finset.mem_coe.mpr hmp) (Finset.mem_coe.mpr hmq) hrank

/-- **No stack entry is read twice.**  Two departures that read the same entry
are the same particle in the same round. -/
theorem readIndex_injective {D : Driver d} (h : StepsToNeighbour D) {t s : ℕ}
    {p q : Label d} (hp : (state D t).active p = true) (hq : (state D s).active q = true)
    (hread : readIndex D t p = readIndex D s q) : t = s ∧ p = q := by
  have hpos : (state D t).pos p = (state D s).pos q := congrArg Prod.fst hread
  have hidx : instructionIndex D (state D t) t p = instructionIndex D (state D s) s q :=
    congrArg Prod.snd hread
  have hts : t = s := by
    by_contra hne
    rcases Nat.lt_or_ge t s with hlt | hge
    · have h1 : instructionIndex D (state D t) t p
          < particleOdometer D (t + 1) ((state D t).pos p) := instructionIndex_lt h t hp
      have h2 : particleOdometer D (t + 1) ((state D t).pos p)
          ≤ particleOdometer D s ((state D s).pos q) := by
        rw [hpos]; exact particleOdometer_mono D _ hlt
      have h3 : particleOdometer D s ((state D s).pos q)
          ≤ instructionIndex D (state D s) s q := le_instructionIndex D s q
      omega
    · have hlt : s < t := lt_of_le_of_ne hge (Ne.symm hne)
      have h1 : instructionIndex D (state D s) s q
          < particleOdometer D (s + 1) ((state D s).pos q) := instructionIndex_lt h s hq
      have h2 : particleOdometer D (s + 1) ((state D s).pos q)
          ≤ particleOdometer D t ((state D t).pos p) := by
        rw [← hpos]; exact particleOdometer_mono D _ hlt
      have h3 : particleOdometer D t ((state D t).pos p)
          ≤ instructionIndex D (state D t) t p := le_instructionIndex D t p
      omega
  subst hts
  exact ⟨rfl, instructionIndex_injective h t hp hq hpos hidx⟩

end LatticeProb

end
