/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: MeshOnly/MeshOnlyHeatGenerator.lean.
-/
import LatticeProb.Network.FiniteCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Mass generators on a finite network

For a conductance `c` of a locally finite graph `G` and a vertex mass `m` with no zero entry, the
mass generator `f ↦ Δ_c f / m` has jump rates `c(v, w) / m(v)`, where `Δ_c` is the network
Laplacian `netLaplacian`. This file defines the mass generator and its killed restriction to a
vertex set `S` (extend by zero, apply the generator, keep the values on `S`).

It proves, for both generators, the weighted Green identity, the symmetry of the weighted pairing
and the energy identity, all with the Dirichlet energy `dirichletEnergy`. It also differentiates
the weighted square norm `∑ m v * (u s v) ^ 2` along a family `u` that solves the killed generator
equation. The identities follow from the Green identity `green_netLaplacian`. The bridge lemma
`netLaplacian_eq_sum_univ` rewrites the neighbour sum defining `netLaplacian` as a sum over all
vertices.
-/

namespace LatticeProb.Network

variable {V : Type*} [Fintype V]

/-- The mass generator `f ↦ Δ_c f / m`, with jump rates `c(v, w) / m(v)`. -/
noncomputable def massGenerator (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (m : V → ℝ) (f : V → ℝ) (v : V) : ℝ :=
  netLaplacian G c f v / m v

/-- The killed mass generator on the vertex set `S`: extend `f` by zero outside `S`, apply the
mass generator, and keep only the values on `S`. -/
noncomputable def killedMassGenerator (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (m : V → ℝ) (S : Set V) (f : V → ℝ) : V → ℝ :=
  S.indicator (massGenerator G c m (S.indicator f))

section Heat

variable (G : SimpleGraph V) [G.LocallyFinite]

/-- Bridge lemma: on a finite vertex type the neighbour sum defining `netLaplacian` may be replaced
by the sum over all vertices, because `c` vanishes on non-edges. -/
theorem netLaplacian_eq_sum_univ {c : V → V → ℝ} (hc : IsCond G c) (f : V → ℝ) (v : V) :
    netLaplacian G c f v = ∑ w, c v w * (f w - f v) := by
  unfold netLaplacian
  exact sum_neighborFinset_eq_sum v Finset.univ (fun w => c v w * (f w - f v))
    (fun y hy => by simp [hc.zero_of_not_adj hy]) (fun y _ _ => Finset.mem_univ y)

/-- The weighted pairing of the mass generator with `g` is the Green form of the network:
`∑ m v * (massGenerator f) v * g v = -1/2 ∑_v ∑_w c v w (f w - f v) (g w - g v)`. -/
theorem massGenerator_green {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ) (hm : ∀ v, m v ≠ 0)
    (f g : V → ℝ) :
    (∑ v, m v * massGenerator G c m f v * g v) =
      -(1 / 2 : ℝ) * ∑ v, ∑ w, c v w * (f w - f v) * (g w - g v) := by
  calc
    _ = ∑ v, netLaplacian G c f v * g v := by
      apply Finset.sum_congr rfl
      intro v _
      unfold massGenerator
      field_simp [hm v]
    _ = _ := green_netLaplacian hc f g

/-- The weighted pairing is symmetric in the two functions for the mass generator. -/
theorem massGenerator_symmetric {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, m v ≠ 0) (f g : V → ℝ) :
    (∑ v, m v * massGenerator G c m f v * g v) =
      ∑ v, m v * f v * massGenerator G c m g v := by
  rw [massGenerator_green G hc m hm]
  have h := massGenerator_green G hc m hm g f
  calc
    _ = -(1 / 2 : ℝ) * ∑ v, ∑ w, c v w * (g w - g v) * (f w - f v) := by
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = ∑ v, m v * massGenerator G c m g v * f v := h.symm
    _ = _ := by apply Finset.sum_congr rfl; intro v _; ring

omit [Fintype V] in
/-- The killed mass generator vanishes outside `S`. -/
theorem killedMassGenerator_eq_zero_of_not_mem (c : V → V → ℝ) (m : V → ℝ) (S : Set V)
    (f : V → ℝ) {v : V} (hv : v ∉ S) : killedMassGenerator G c m S f v = 0 := by
  simp [killedMassGenerator, hv]

/-- The weighted pairing of the killed mass generator obeys the Green identity, with every term
restricted to `S`. -/
theorem killedMassGenerator_green {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, m v ≠ 0) (S : Set V) (f g : V → ℝ) :
    (∑ v, m v * killedMassGenerator G c m S f v * g v) =
      -(1 / 2 : ℝ) * ∑ v, ∑ w, c v w *
        (S.indicator f w - S.indicator f v) * (S.indicator g w - S.indicator g v) := by
  calc
    _ = ∑ v, m v * massGenerator G c m (S.indicator f) v * S.indicator g v := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ S <;> simp [killedMassGenerator, hv]
    _ = _ := massGenerator_green G hc m hm _ _

/-- The weighted pairing of the killed mass generator is symmetric in the two functions. -/
theorem killedMassGenerator_symmetric {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, m v ≠ 0) (S : Set V) (f g : V → ℝ) :
    (∑ v, m v * killedMassGenerator G c m S f v * g v) =
      ∑ v, m v * f v * killedMassGenerator G c m S g v := by
  rw [killedMassGenerator_green G hc m hm]
  have h := killedMassGenerator_green G hc m hm S g f
  calc
    _ = -(1 / 2 : ℝ) * ∑ v, ∑ w, c v w *
        (S.indicator g w - S.indicator g v) * (S.indicator f w - S.indicator f v) := by
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = ∑ v, m v * killedMassGenerator G c m S g v * f v := h.symm
    _ = _ := by apply Finset.sum_congr rfl; intro v _; ring

/-- The weighted pairing of the killed mass generator with `f` is minus the Dirichlet energy of
the zero extension of `f` to `S`. -/
theorem killedMassGenerator_energy {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, m v ≠ 0) (S : Set V) (f : V → ℝ) :
    (∑ v, m v * f v * killedMassGenerator G c m S f v) =
      -dirichletEnergy c (S.indicator f) := by
  rw [← killedMassGenerator_symmetric G hc m hm S f f, killedMassGenerator_green G hc m hm]
  simp only [dirichletEnergy, neg_mul, mul_assoc, pow_two]

/-- Along a family `u` that solves the killed generator equation `hu` at time `t`, the weighted
square norm `∑ m v * (u s v) ^ 2` has derivative `-2 * dirichletEnergy c (S.indicator (u t))` at
`t`. The generator equation is an explicit premise of this calculus lemma. -/
theorem hasDerivAt_weighted_sq_of_killed_heat {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, m v ≠ 0) (S : Set V) (u : ℝ → V → ℝ) (t : ℝ)
    (hu : ∀ v, HasDerivAt (fun s => u s v) (killedMassGenerator G c m S (u t) v) t) :
    HasDerivAt (fun s => ∑ v, m v * (u s v) ^ 2)
      (-2 * dirichletEnergy c (S.indicator (u t))) t := by
  have h : HasDerivAt (fun s => ∑ v, m v * (u s v) ^ 2)
      (∑ v, m v * (2 * u t v * killedMassGenerator G c m S (u t) v)) t := by
    apply HasDerivAt.fun_sum
    intro v _
    simpa using ((hu v).pow 2).const_mul (m v)
  convert h using 1
  rw [show (∑ v, m v * (2 * u t v * killedMassGenerator G c m S (u t) v)) =
      2 * ∑ v, m v * u t v * killedMassGenerator G c m S (u t) v by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring]
  rw [killedMassGenerator_energy G hc m hm]
  ring

end Heat

namespace HeatGeneratorExample

open SimpleGraph

/-- The path on three vertices is locally finite. -/
@[reducible] noncomputable def pathLocallyFinite : (pathGraph 3).LocallyFinite :=
  fun _ => Fintype.ofFinite _

attribute [local instance] pathLocallyFinite

/-- The unit conductance on the path `0 – 1 – 2` satisfies the conductance hypothesis. -/
example : IsCond (pathGraph 3) (unitCond (pathGraph 3)) := isCond_unitCond

/-- The zero family solves the killed generator equation on the path with unit mass and `S = univ`,
so the hypotheses of `hasDerivAt_weighted_sq_of_killed_heat` are jointly satisfiable. -/
example (t : ℝ) :
    HasDerivAt (fun s => ∑ v : Fin 3,
        (fun _ => (1 : ℝ)) v * ((fun (_ : ℝ) (_ : Fin 3) => (0 : ℝ)) s v) ^ 2)
      (-2 * dirichletEnergy (unitCond (pathGraph 3))
        (Set.univ.indicator ((fun (_ : ℝ) (_ : Fin 3) => (0 : ℝ)) t))) t := by
  refine hasDerivAt_weighted_sq_of_killed_heat (pathGraph 3) isCond_unitCond (fun _ => (1 : ℝ))
    (fun _ => one_ne_zero) Set.univ (fun (_ : ℝ) (_ : Fin 3) => (0 : ℝ)) t (fun v => ?_)
  simpa [killedMassGenerator, massGenerator, netLaplacian] using hasDerivAt_const t (0 : ℝ)

end HeatGeneratorExample

end LatticeProb.Network
