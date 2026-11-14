/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepairedInputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAnnuli

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepairedInputs

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

 
def RectAnnulusCoverAt (Ucross Uaround E F : Set ℂ)
    (ks kl : ℕ) (N : ℝ) : Prop :=
  ∃ (Js Jl : Finset ℕ) (us ul : ℕ → Circle) (cs cl : ℕ → ℂ),
    (Js.card : ℝ) ≤ N ∧ (Jl.card : ℝ) ≤ N ∧
    ∀ (ξ : ℝ) (f : ℂ → ℝ) (hf : Continuous f) (a b : ℝ),
      (crossLenIn ξ f Ucross E F < ENNReal.ofReal a →
        ∃ j ∈ Js, T20B.mrectLen ξ f ks (us j) (cs j) 1 3 < a) ∧
      (ENNReal.ofReal (N * b) <
        (lfppContMetric ξ f hf).aroundDist Uaround E F →
        ∃ j ∈ Jl, b < T20B.mrectLen ξ f kl (ul j) (cl j) 3 1)

 
def LargeAnnulusGeometry : Prop :=
  ∃ R₀ G : ℝ, 24 ≤ R₀ ∧ 1 ≤ G ∧
    ∀ R : ℝ, R₀ ≤ R →
      RectAnnulusCoverAt
        {z : ℂ | dist z 0 ∈ Icc R (2 * R)}
        {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
        (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R)) 0 0 (G * R)

 
def UnitBlockGeometry (Ucross Uaround E F : Bool → Set ℂ) : Prop :=
  ∃ G : ℝ, 1 ≤ G ∧ ∀ i : Bool,
    RectAnnulusCoverAt (Ucross i) (Uaround i) (E i) (F i)
      3 (if i then 0 else 3) G

end SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepairedInputs
