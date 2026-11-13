import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR8
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WeldingUniqueness

/-!
# Deterministic conformal-welding uniqueness without assumed inputs

The welding-uniqueness theorems `QuantumZipper.revMap_eq_of_welding_eq`,
`QuantumZipper.revHull_eq_of_welding_eq` and `QuantumZipper.time_eq_of_welding_eq` take the
Carathéodory extension of reverse Loewner maps (`Blueprint.RevMapCaratheodory`) as a hypothesis.
That statement is the theorem `QuantumZipper.CaraR.revMapCaratheodory`. This file states the three
theorems with that hypothesis discharged. The remaining hypotheses are those of the conditional
statements: continuous drivers started at `0`, positive times, simple-curve hulls, equal
weldings, and conformal removability of the closed arc together with its reflection.

References: Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity
zipper* (2016), §1.4; Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Thm 2.1.
-/

open Set Complex
open scoped ComplexConjugate

namespace QuantumZipper

namespace WeldingUniquenessUncond

/-- **Deterministic conformal-welding uniqueness.** Let `W, W'` be continuous drivers with
`W 0 = W' 0 = 0` and `T, T' > 0`, whose reverse hulls are simple arcs with the same welding
(`zeroMinus` and `weldingHom` on `[zeroMinus W T, 0]`), and suppose the closed arc together with
its reflection is conformally removable. Then the two reverse Loewner maps agree on `ℍ`. -/
theorem revMap_eq_of_welding_eq {W W' : ℝ → ℝ} (hW : Continuous W)
    (hW' : Continuous W') (hW0 : W 0 = 0) (hW'0 : W' 0 = 0) {T T' : ℝ} (hT : 0 < T)
    (hT' : 0 < T') (hK : IsSimpleCurveHull (revHull W T))
    (hK' : IsSimpleCurveHull (revHull W' T')) (hzm : zeroMinus W T = zeroMinus W' T')
    (hweld : EqOn (weldingHom W T) (weldingHom W' T') (Icc (zeroMinus W T) 0))
    (hrem : IsConformallyRemovable (closure (revHull W T) ∪ conj '' closure (revHull W T))) :
    EqOn (revMap W' T') (revMap W T) H :=
  QuantumZipper.revMap_eq_of_welding_eq CaraR.revMapCaratheodory hW hW' hW0 hW'0 hT hT' hK hK'
    hzm hweld hrem

/-- **Deterministic conformal-welding uniqueness, hull form.** Under the hypotheses of
`revMap_eq_of_welding_eq`, the two reverse hulls coincide. -/
theorem revHull_eq_of_welding_eq {W W' : ℝ → ℝ} (hW : Continuous W)
    (hW' : Continuous W') (hW0 : W 0 = 0) (hW'0 : W' 0 = 0) {T T' : ℝ} (hT : 0 < T)
    (hT' : 0 < T') (hK : IsSimpleCurveHull (revHull W T))
    (hK' : IsSimpleCurveHull (revHull W' T')) (hzm : zeroMinus W T = zeroMinus W' T')
    (hweld : EqOn (weldingHom W T) (weldingHom W' T') (Icc (zeroMinus W T) 0))
    (hrem : IsConformallyRemovable (closure (revHull W T) ∪ conj '' closure (revHull W T))) :
    revHull W' T' = revHull W T :=
  QuantumZipper.revHull_eq_of_welding_eq CaraR.revMapCaratheodory hW hW' hW0 hW'0 hT hT' hK hK'
    hzm hweld hrem

/-- **Deterministic conformal-welding uniqueness, time form.** Under the hypotheses of
`revMap_eq_of_welding_eq`, the capacities agree, `T' = T`, and so do the terminal driver values,
`W' T' = W T`. -/
theorem time_eq_of_welding_eq {W W' : ℝ → ℝ} (hW : Continuous W)
    (hW' : Continuous W') (hW0 : W 0 = 0) (hW'0 : W' 0 = 0) {T T' : ℝ} (hT : 0 < T)
    (hT' : 0 < T') (hK : IsSimpleCurveHull (revHull W T))
    (hK' : IsSimpleCurveHull (revHull W' T')) (hzm : zeroMinus W T = zeroMinus W' T')
    (hweld : EqOn (weldingHom W T) (weldingHom W' T') (Icc (zeroMinus W T) 0))
    (hrem : IsConformallyRemovable (closure (revHull W T) ∪ conj '' closure (revHull W T))) :
    T' = T ∧ W' T' = W T :=
  QuantumZipper.time_eq_of_welding_eq CaraR.revMapCaratheodory hW hW' hW0 hW'0 hT hT' hK hK'
    hzm hweld hrem

end WeldingUniquenessUncond

end QuantumZipper
