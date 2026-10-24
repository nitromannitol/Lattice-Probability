import LatticeProb.Analysis.ContractionSemigroup

/-!
# Ethier–Kurtz: convergence of semigroups on varying spaces

S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
(1986), Chapter 1, Theorem 6.1, implication (c) ⇒ (a): for strongly continuous contraction
semigroups `T n` on Banach spaces `L n` and `T` on `L`, bounded linear maps `π n : L → L n`
with `sup ‖π n‖ < ∞`, and a core `D` for the generator of `T`, if every graph pair `(f, g)` of
the generator with `f ∈ D` is the limit of graph pairs of the generators of `T n` (in the sense
`‖f n − π n f‖ → 0`), then `T n (t) (π n f)` converges to `T (t) f` uniformly on bounded time
intervals, for every `f`. The proposition is stated so that a formalization citing it can carry
it as an explicit hypothesis; it is not proved here.
-/

namespace LatticeProb.External

open Filter Topology
open scoped NNReal
open LatticeProb.ContractionSemigroup

/-- **Ethier–Kurtz, Chapter 1, Theorem 6.1, (c) ⇒ (a).** -/
def EthierKurtzTrotterKato : Prop :=
  ∀ (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]
    (Ln : ℕ → Type) [∀ n, NormedAddCommGroup (Ln n)] [∀ n, NormedSpace ℝ (Ln n)]
    [∀ n, CompleteSpace (Ln n)] (π : ∀ n, L →L[ℝ] Ln n),
    (∃ C : ℝ, ∀ n, ‖π n‖ ≤ C) →
    ∀ (T : StronglyContinuousContractionSemigroup L)
      (Tn : ∀ n, StronglyContinuousContractionSemigroup (Ln n))
      (D : Submodule ℝ L),
      IsCore T D → GraphApproximation π T Tn D → UniformSemigroupConvergence π T Tn

/-- The input applies to the identity semigroup on `ℝ` with constant spaces. -/
theorem ethierKurtzTrotterKato_identity (hEK : EthierKurtzTrotterKato) :
    UniformSemigroupConvergence (fun _ : ℕ => ContinuousLinearMap.id ℝ ℝ)
      identitySemigroup (fun _ => identitySemigroup) :=
  hEK ℝ (fun _ => ℝ) _ ⟨1, fun _ => ContinuousLinearMap.norm_id_le⟩ _ _ ⊤
    identity_isCore identity_graphApproximation

end LatticeProb.External
