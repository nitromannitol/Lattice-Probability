/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MeshOnly.MeshOnlyHeatGenerator at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.DiscretePDEAlgebra
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! The actual tile-mass generator on a finite conductance network, its killed
restriction, and the weighted Green and dissipation identities. The mass is a
positive function, to be instantiated with the actual tile volumes. -/

open scoped BigOperators

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

/-- Generator with jump rates `a(v,w) / m(v)`. -/
noncomputable def massGenerator (m : V → ℝ) (f : V → ℝ) (v : V) : ℝ :=
  N.laplacian f v / m v

/-- Kill outside `S`: extend the function by zero before applying the generator. -/
noncomputable def killedMassGenerator (m : V → ℝ) (S : Set V) (f : V → ℝ) : V → ℝ :=
  S.indicator (N.massGenerator m (S.indicator f))

lemma massGenerator_green (m : V → ℝ) (hm : ∀ v, m v ≠ 0) (f g : V → ℝ) :
    (∑ v, m v * N.massGenerator m f v * g v) =
      -(1 / 2 : ℝ) * ∑ v, ∑ w, N.a v w * (f w - f v) * (g w - g v) := by
  calc
    _ = ∑ v, N.laplacian f v * g v := by
      apply Finset.sum_congr rfl
      intro v _
      unfold massGenerator
      field_simp [hm v]
    _ = _ := N.green_laplacian f g

lemma massGenerator_symmetric (m : V → ℝ) (hm : ∀ v, m v ≠ 0) (f g : V → ℝ) :
    (∑ v, m v * N.massGenerator m f v * g v) =
      ∑ v, m v * f v * N.massGenerator m g v := by
  rw [N.massGenerator_green m hm]
  have h := N.massGenerator_green m hm g f
  calc
    _ = -(1 / 2 : ℝ) * ∑ v, ∑ w, N.a v w * (g w - g v) * (f w - f v) := by
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = ∑ v, m v * N.massGenerator m g v * f v := h.symm
    _ = _ := by apply Finset.sum_congr rfl; intro v _; ring

lemma killedMassGenerator_eq_zero_of_not_mem (m : V → ℝ) (S : Set V)
    (f : V → ℝ) {v : V} (hv : v ∉ S) : N.killedMassGenerator m S f v = 0 := by
  simp [killedMassGenerator, hv]

lemma killedMassGenerator_green (m : V → ℝ) (hm : ∀ v, m v ≠ 0)
    (S : Set V) (f g : V → ℝ) :
    (∑ v, m v * N.killedMassGenerator m S f v * g v) =
      -(1 / 2 : ℝ) * ∑ v, ∑ w, N.a v w *
        (S.indicator f w - S.indicator f v) * (S.indicator g w - S.indicator g v) := by
  calc
    _ = ∑ v, m v * N.massGenerator m (S.indicator f) v * S.indicator g v := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ S <;> simp [killedMassGenerator, hv]
    _ = _ := N.massGenerator_green m hm _ _

lemma killedMassGenerator_symmetric (m : V → ℝ) (hm : ∀ v, m v ≠ 0)
    (S : Set V) (f g : V → ℝ) :
    (∑ v, m v * N.killedMassGenerator m S f v * g v) =
      ∑ v, m v * f v * N.killedMassGenerator m S g v := by
  rw [N.killedMassGenerator_green m hm]
  have h := N.killedMassGenerator_green m hm S g f
  calc
    _ = -(1 / 2 : ℝ) * ∑ v, ∑ w, N.a v w *
        (S.indicator g w - S.indicator g v) * (S.indicator f w - S.indicator f v) := by
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = ∑ v, m v * N.killedMassGenerator m S g v * f v := h.symm
    _ = _ := by apply Finset.sum_congr rfl; intro v _; ring

lemma killedMassGenerator_energy (m : V → ℝ) (hm : ∀ v, m v ≠ 0)
    (S : Set V) (f : V → ℝ) :
    (∑ v, m v * f v * N.killedMassGenerator m S f v) =
      -N.energy (S.indicator f) := by
  rw [← N.killedMassGenerator_symmetric m hm S f f, N.killedMassGenerator_green m hm]
  simp only [energy, neg_mul, mul_assoc, pow_two]

/-- Along the actual killed heat equation, squared weighted L² norm loses twice
the Dirichlet energy. This calculus helper retains the generator equation as
an explicit premise; the exponential semigroup will supply that equation. -/
theorem hasDerivAt_weighted_sq_of_killed_heat (m : V → ℝ) (hm : ∀ v, m v ≠ 0)
    (S : Set V) (u : ℝ → V → ℝ) (t : ℝ)
    (hu : ∀ v, HasDerivAt (fun s => u s v) (N.killedMassGenerator m S (u t) v) t) :
    HasDerivAt (fun s => ∑ v, m v * (u s v) ^ 2)
      (-2 * N.energy (S.indicator (u t))) t := by
  have h : HasDerivAt (fun s => ∑ v, m v * (u s v) ^ 2)
      (∑ v, m v * (2 * u t v * N.killedMassGenerator m S (u t) v)) t := by
    apply HasDerivAt.fun_sum
    intro v _
    simpa using ((hu v).pow 2).const_mul (m v)
  convert h using 1
  rw [show (∑ v, m v * (2 * u t v * N.killedMassGenerator m S (u t) v)) =
      2 * ∑ v, m v * u t v * N.killedMassGenerator m S (u t) v by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring]
  rw [N.killedMassGenerator_energy m hm]
  ring

end BouRabeeGwynne.FiniteConductanceNetwork
