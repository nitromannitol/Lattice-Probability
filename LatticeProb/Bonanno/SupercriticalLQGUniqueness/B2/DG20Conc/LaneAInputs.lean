/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneAInputs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneAFamilies
import LatticeProb.Bonanno.LQGMetric.LFPP.ContMetric
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect

 












set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc.LaneAInputs

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

 

def RectAnnulusCover (Ucross Uaround E F : Set ℂ) (N : ℝ) : Prop :=
  ∃ (Js Jl : Finset ℕ) (us ul : ℕ → Circle) (cs cl : ℕ → ℂ),
    (Js.card : ℝ) ≤ N ∧ (Jl.card : ℝ) ≤ N ∧
    ∀ (ξ : ℝ) (f : ℂ → ℝ) (hf : Continuous f) (a b : ℝ),
      (crossLenIn ξ f Ucross E F < ENNReal.ofReal a →
        ∃ j ∈ Js, T20B.mrectLen ξ f 0 (us j) (cs j) 1 3 < a) ∧
      (ENNReal.ofReal (N * b) <
        (lfppContMetric ξ f hf).aroundDist Uaround E F →
        ∃ j ∈ Jl, b < T20B.mrectLen ξ f 0 (ul j) (cl j) 3 1)

 


def LargeAnnulusGeometry : Prop :=
  ∃ R₀ G : ℝ, 1 ≤ R₀ ∧ 1 ≤ G ∧
    ∀ R : ℝ, R₀ ≤ R →
      RectAnnulusCover
        {z : ℂ | dist z 0 ∈ Icc R (2 * R)}
        {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
        (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R)) (G * R)

 



def UnitBlockGeometry {ι : Type*}
    (Ucross Uaround E F : ι → Set ℂ) : Prop :=
  ∃ G : ℝ, 1 ≤ G ∧ ∀ i : ι,
    RectAnnulusCover (Ucross i) (Uaround i) (E i) (F i) G

end SupercriticalLQGUniqueness.B2.DG20Conc.LaneAInputs
