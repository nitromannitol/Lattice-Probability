/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.Transport at commit 66d817d; only the module paths and the namespace `Parking` are renamed
   (to `LatticeProb.ParticleDrivenAgree`). -/
import LatticeProb.ParticleDrivenAgree.Pathwise

/-!
# Pathwise identities behind the averaged transport statements

The two pathwise identities of Section 3 of `parking.tex` that the averaged
statements rest on.

`U_eq_sum_A` is that the odometer is the running total of the active counts,
which is what turns `E U_n(0) = ∑_{s<n} S_s` into `E A_s(0) = S_s` summed.

`signed_count` is `eq:signed-count`: at every site the active particles minus
the unfilled holes are the initial count plus the arrivals minus the
departures.  It follows from the parallel identity and from the holes being
what is left of the initial ones after the arrivals, because a positive and a
negative part are never both positive.
-/

noncomputable section

namespace LatticeProb.ParticleDrivenAgree

open LatticeProb Finset

variable {d : ℕ}

/-- The odometer is the running total of the active counts. -/
theorem particleOdometer_eq_sum (D : Driver d) (n : ℕ) (x : Site d) :
    particleOdometer D n x = ∑ s ∈ Finset.range n, activeCount D s x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [particleOdometer_succ, ih, Finset.sum_range_succ]

/-- Transports `particleOdometer_eq_sum` along `toDriver`: the odometer `U ω n x` is the
running total of the active counts `A ω s x` over `s < n`. -/
theorem U_eq_sum_A (ω : Data d) (n : ℕ) (x : Site d) :
    U ω n x = ∑ s ∈ Finset.range n, A ω s x :=
  particleOdometer_eq_sum (toDriver ω) n x

/-- The signed count of `eq:signed-count`: the active particles minus the
unfilled holes at a site are the mass that has arrived there and not left. -/
theorem signed_count {ω : Data d}
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (t : ℕ) (x : Site d) :
    (A ω t x : ℤ) - (H ω t x : ℤ)
      = ω.1 x + (∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω t y) : ℤ)) - (U ω t x : ℤ) := by
  have hpar := (parallel_of_labelOrder (D := toDriver ω) (labelOrder d) hstep).2 t x
  have hhole : H ω t x = (-(ω.1 x)).toNat - totalArrivals (toDriver ω) t x :=
    holeCount_eq (toDriver ω) t x
  have harr : totalArrivals (toDriver ω) t x
      = ∑ y ∈ nbrFinset x, arrivals ω.2.1 y x (U ω t y) :=
    totalArrivals_eq (labelOrder d) hstep t x
  have hsucc : U ω (t + 1) x = U ω t x + A ω t x := particleOdometer_succ (toDriver ω) t x
  rw [harr] at hhole
  set Arr := ∑ y ∈ nbrFinset x, arrivals ω.2.1 y x (U ω t y) with hArr
  have hcast : ((∑ y ∈ nbrFinset x, arrivals ω.2.1 y x (U ω t y) : ℕ) : ℤ)
      = ∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω t y) : ℤ) := by push_cast; ring
  rw [← hcast, ← hArr]
  have hpar' : (U ω (t + 1) x : ℤ)
      = max 0 (ω.1 x + ∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω t y) : ℤ)) := hpar
  rw [hsucc, ← hcast, ← hArr] at hpar'
  rw [hhole]
  push_cast at hpar' ⊢
  omega

end LatticeProb.ParticleDrivenAgree

end
