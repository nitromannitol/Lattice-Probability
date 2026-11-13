/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.Reads at commit 66d817d. The module paths and the namespace `Parking`
   are renamed (to `LatticeProb.ParticleDrivenAgree`), and proofs are adapted to the Lean and Mathlib
   versions of this repository where needed. -/
import LatticeProb.ReadIndex
import LatticeProb.ParticleDrivenAgree.Measurability
import LatticeProb.ParticleDrivenAgree.Deferred
import LatticeProb.ParticleDrivenAgree.Parallel

/-!
# Which instructions are read

Which instructions a realization of the stack construction has read.

`LatticeProb.ParticleDrivenAgree.Deferred` cuts the instructions a state depends on by their
INDEX: the state after `t` rounds reads only the instructions of index below
the odometer.  What the passage to the particle-driven construction needs is
the converse, that every index below the odometer IS read, and by exactly one
departure.  With that, "the instruction `(z, i)` is unread through round `t`"
and "`i` is at least the odometer at `z`" are the same condition, and
overwriting an unread instruction changes nothing.

Also here: the instruction index a particle reads, and the pair of site and
index it reads, are measurable functions of the driving data.  Only the state
was proved measurable in `LatticeProb.ParticleDrivenAgree.Measurability`; the index is the sum
of the odometer at the position, read at a variable site, and the number of
co-departing particles with a smaller label.
-/

open LatticeProb (measurable_eval_var measurable_from_countable')

noncomputable section

open MeasureTheory

namespace LatticeProb.ParticleDrivenAgree

open LatticeProb Finset

variable {d : ℕ}

/-! ### Every index below the odometer is read -/

/-- **The reads exhaust the odometer.**  If the odometer at `z` after `t`
rounds has passed `i`, then some particle read the instruction `(z, i)` in one
of those rounds. -/
theorem exists_read_of_lt_odometer {D : Driver d} (hs : StepsToNeighbour D) :
    ∀ (t : ℕ) (z : Site d) (i : ℕ), i < particleOdometer D t z →
      ∃ s, s < t ∧ ∃ q : Label d,
        (state D s).active q = true ∧ readIndex D s q = (z, i) := by
  intro t
  induction t with
  | zero =>
      intro z i hi
      simp [particleOdometer, state, initial] at hi
  | succ t ih =>
      intro z i hi
      by_cases hlt : i < particleOdometer D t z
      · obtain ⟨s, hs', q, hq, hr⟩ := ih z i hlt
        exact ⟨s, Nat.lt_succ_of_lt hs', q, hq, hr⟩
      · rw [Nat.not_lt] at hlt
        have hcard : particleOdometer D (t + 1) z
            = particleOdometer D t z + (activeAt D (state D t) t z).card := rfl
        have hk : i - particleOdometer D t z < (activeAt D (state D t) t z).card := by omega
        have hinj : Set.InjOn (labelKey (d := d))
            ((activeAt D (state D t) t z : Finset (Label d)) : Set (Label d)) :=
          fun a _ b _ h => labelKey_injective h
        have hmem : (i - particleOdometer D t z)
            ∈ (activeAt D (state D t) t z).image
                (rankIn (activeAt D (state D t) t z) labelKey) := by
          rw [image_rankIn hinj]
          exact Finset.mem_range.mpr hk
        obtain ⟨q, hqA, hrank⟩ := Finset.mem_image.mp hmem
        have hq := (mem_activeAt_iff hs t z q).mp hqA
        refine ⟨t, Nat.lt_succ_self t, q, hq.1, ?_⟩
        have hii := instructionIndex_eq_add_rankIn D t q
        rw [hq.2] at hii
        show ((state D t).pos q, instructionIndex D (state D t) t q) = (z, i)
        rw [hq.2, hii, hrank]
        have : particleOdometer D t z + (i - particleOdometer D t z) = i := by omega
        rw [this]

/-- **Overwriting an unread instruction changes nothing.**  If no departure of
the first `t` rounds reads the entry `c`, then the state after `t` rounds is the
same for a driver that differs only there. -/
theorem state_congr_of_unread {D D' : Driver d} (hs : StepsToNeighbour D)
    (heta : D.eta = D'.eta) (hrank : D.rank = D'.rank) (c : Site d × ℕ)
    (hstack : ∀ q : Site d × ℕ, q ≠ c → D.stack q = D'.stack q) (t : ℕ)
    (hun : ∀ s, s < t → ∀ q : Label d, (state D s).active q = true →
      readIndex D s q ≠ c) :
    state D t = state D' t := by
  refine state_congr hs heta hrank t fun z i hi => ?_
  by_cases hc : (z, i) = c
  · exfalso
    obtain ⟨s, hst, q, hq, hr⟩ := exists_read_of_lt_odometer hs t z i hi
    exact hun s hst q hq (by rw [hr, hc])
  · exact hstack _ hc

/-! ### The read index is measurable -/

/-- The number of particles active at a fixed site after `t` rounds that
satisfy a fixed predicate is a measurable function of the data. -/
theorem measurable_activeAt_filter_card (t : ℕ) (y : Site d) (P : Label d → Prop)
    [DecidablePred P] :
    Measurable fun ω : Data d =>
      ((activeAt (toDriver ω) (state (toDriver ω) t) t y).filter P).card := by
  classical
  obtain ⟨hact, hpos, -, -⟩ := measurable_state (d := d) t
  have hbool : ∀ (f g : Data d → Bool), Measurable f → Measurable g →
      Measurable fun ω => (f ω && g ω) := by
    intro f g hf hg
    exact (measurable_from_countable' fun b : Bool × Bool => b.1 && b.2).comp (hf.prodMk hg)
  have hposeq : ∀ q : Label d,
      Measurable fun ω : Data d => decide ((state (toDriver ω) t).pos q = y) :=
    fun q => (measurable_from_countable' fun z : Site d => decide (z = y)).comp (hpos q)
  have hrw : ∀ ω : Data d,
      ((activeAt (toDriver ω) (state (toDriver ω) t) t y).filter P).card
        = ((candidates ω.1 y t).filter fun q =>
            (((state (toDriver ω) t).active q
              && decide ((state (toDriver ω) t).pos q = y)) && decide (P q)) = true).card := by
    intro ω
    unfold activeAt
    rw [Finset.filter_filter]
    congr 1
  simp only [hrw]
  exact measurable_card_filter_candidates y t _ fun q =>
    hbool _ _ (hbool _ _ (hact q) (hposeq q)) measurable_const

/-- The instruction index a particle reads in round `t + 1` is measurable. -/
theorem measurable_instructionIndex (t : ℕ) (p : Label d) :
    Measurable fun ω : Data d =>
      instructionIndex (toDriver ω) (state (toDriver ω) t) t p := by
  classical
  obtain ⟨-, hpos, -, hdep⟩ := measurable_state (d := d) t
  have h1 : Measurable fun ω : Data d =>
      (state (toDriver ω) t).departures ((state (toDriver ω) t).pos p) :=
    measurable_eval_var _ (hpos p) (fun ω y => (state (toDriver ω) t).departures y) hdep
  have h2 : Measurable fun ω : Data d =>
      ((activeAt (toDriver ω) (state (toDriver ω) t) t ((state (toDriver ω) t).pos p)).filter
        fun q => labelLT q p).card :=
    measurable_eval_var _ (hpos p)
      (fun ω y => ((activeAt (toDriver ω) (state (toDriver ω) t) t y).filter
        fun q => labelLT q p).card)
      (fun y => measurable_activeAt_filter_card t y _)
  exact h1.add h2

/-- The stack entry a particle reads in round `t + 1` is measurable. -/
theorem measurable_readIndex (t : ℕ) (p : Label d) :
    Measurable fun ω : Data d => readIndex (toDriver ω) t p := by
  obtain ⟨-, hpos, -, -⟩ := measurable_state (d := d) t
  exact (hpos p).prodMk (measurable_instructionIndex t p)

end LatticeProb.ParticleDrivenAgree

end
