import LatticeProb.Analysis.ContractionSemigroupResolvent
import LatticeProb.Prob.BrownianDirichlet.KilledStrongContinuity

/-!
# The killed Brownian Laplace resolvent

The generic Laplace resolvent applies to the strongly continuous killed Brownian
contraction semigroup on L² of the domain. Both inverse identities use its actual
generator graph defined by right difference quotients.
-/

namespace LatticeProb

open MeasureTheory Set
open ContractionSemigroup

noncomputable section

variable {d : ℕ} {B : Set (Euc d)} [IsFiniteMeasure (volume.restrict B)]
  (hB : IsOpen B) (σ : ℝ) {μ : Measure (BrownianPath d)}
  (hμ : IsStandardBrownianLaw μ)

/-- The Laplace resolvent of killed Brownian evolution on the domain's L² space. -/
def killedResolvent (a : ℝ) (ha : 0 < a) :
    Lp ℝ 2 (volume.restrict B) →L[ℝ] Lp ℝ 2 (volume.restrict B) :=
  resolvent (killedSemigroup hB σ hμ) a ha

/-- The killed resolvent is the Bochner integral of discounted killed L² evolution. -/
theorem killedResolvent_apply {a : ℝ} (ha : 0 < a) (f : Lp ℝ 2 (volume.restrict B)) :
    killedResolvent hB σ hμ a ha f =
      ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) • killedLp hB σ hμ t.toNNReal f := rfl

/-- Discounted killed L² evolution is Bochner integrable for every positive discount. -/
theorem integrable_discounted_killedLp {a : ℝ} (ha : 0 < a)
    (f : Lp ℝ 2 (volume.restrict B)) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) • killedLp hB σ hμ t.toNNReal f)
      (Ioi 0) :=
  integrable_discounted_orbit (killedSemigroup hB σ hμ) ha f

/-- The killed resolvent has operator norm bounded by the inverse discount. -/
theorem norm_killedResolvent_le {a : ℝ} (ha : 0 < a) :
    ‖killedResolvent hB σ hμ a ha‖ ≤ a⁻¹ :=
  norm_resolvent_le (killedSemigroup hB σ hμ) ha

/-- The killed resolvent produces a vector in the genuine killed generator graph. -/
theorem killedResolvent_mem_generatorGraph {a : ℝ} (ha : 0 < a)
    (f : Lp ℝ 2 (volume.restrict B)) :
    (killedResolvent hB σ hμ a ha f, a • killedResolvent hB σ hμ a ha f - f) ∈
      generatorGraph (killedSemigroup hB σ hμ) :=
  resolvent_mem_generatorGraph (killedSemigroup hB σ hμ) ha f

/-- The killed resolvent inverts the positive shifted generator on its actual domain. -/
theorem killedResolvent_of_mem_generatorGraph {a : ℝ} (ha : 0 < a)
    {v w : Lp ℝ 2 (volume.restrict B)}
    (h : (v, w) ∈ generatorGraph (killedSemigroup hB σ hμ)) :
    killedResolvent hB σ hμ a ha (a • v - w) = v :=
  resolvent_of_mem_generatorGraph (killedSemigroup hB σ hμ) ha h

/-- The killed generator graph is closed in the product L² space. -/
theorem isClosed_killed_generatorGraph :
    IsClosed (generatorGraph (killedSemigroup hB σ hμ)) :=
  isClosed_generatorGraph (killedSemigroup hB σ hμ)

/-- The killed generator domain is a real vector subspace. -/
def killedGeneratorSubmodule : Submodule ℝ (Lp ℝ 2 (volume.restrict B)) :=
  generatorSubmodule (killedSemigroup hB σ hμ)

/-- The full killed generator domain is a core. -/
theorem isCore_killedGeneratorSubmodule :
    IsCore (killedSemigroup hB σ hμ) (killedGeneratorSubmodule hB σ hμ) :=
  isCore_generatorSubmodule (killedSemigroup hB σ hμ)

end

end LatticeProb
