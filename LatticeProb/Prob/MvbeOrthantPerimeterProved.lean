import Mathlib
import LatticeProb.Prob.PerimBand
import LatticeProb.Prob.PerimPsi
import LatticeProb.Prob.MvbeOrthantBerryEsseen

/-!
# The Gaussian perimeter of the rounded orthants is `O(m^{1/4})`, proved

`PerimBand.lean` derives the cited proposition `MvbeOrthantPerimeterQuarter` from a bound on
`Ψ(t) = E[|V|; N² < t²]`, and `PerimPsi.lean` proves that bound (Stein-type identity, tilted
Cauchy-Schwarz chain, two regimes).  This file composes them and removes the last cited input of
the multivariate Berry-Esseen comparison for orthants: `Sandpile.External.MultivariateBerryEsseen`
and its Parking copy are then proved exactly as stated.
-/

namespace LatticeProb

/-- **The Gaussian perimeter bound** `MvbeOrthantPerimeterQuarter` (formerly cited from Raič's
Theorem 1.2), proved: `γ*` of the rounded orthants is at most `c m^{1/4}` (in fact `O(1 + √log m)`). -/
theorem mvbe_orthantPerimeterQuarter_proved : MvbeOrthantPerimeterQuarter :=
  perimB_quarter 1000 (fun m hm h t ht => perimP_psi_bound m hm h t ht)

/-- **The multivariate Berry-Esseen comparison for orthants with the frozen factor `m^{1/4}`**,
unconditionally: `MvbeFrozenQuarter` is textually the frozen
`Sandpile.External.MultivariateBerryEsseen` (and, with the vocabulary renamed, its Parking copy). -/
theorem mvbe_frozenQuarter_unconditional : MvbeFrozenQuarter :=
  mvbe_frozenQuarter_of_perimeter mvbe_orthantPerimeterQuarter_proved

end LatticeProb
