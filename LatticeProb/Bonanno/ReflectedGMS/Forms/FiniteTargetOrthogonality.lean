/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteTargetOrthogonality at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Proposition13

/-!
# Full finite-energy orthogonality for finite-target extensions

Reuse the existing energy minimizer's orthogonal-projection construction. These
identities retain all finite-energy variations and support the finite-target
approximation in the reflected-process/full-form identification.
-/

set_option autoImplicit false
open scoped InnerProductSpace

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-- Constants do not contribute to the full energy pairing. -/
theorem dirichletForm_add_const_left (f g : V → ℝ) (c : ℝ) :
    G.dirichletForm (fun v => f v + c) g = G.dirichletForm f g := by
  unfold ReflectedWalk.ConductanceGraph.dirichletForm
  congr 1
  apply tsum_congr
  intro p
  unfold ReflectedWalk.ConductanceGraph.gradProd
  congr 1 <;> ring

/-- The actual finite-target minimizer is orthogonal to every full finite-energy
variation vanishing on that target. -/
theorem energyMin_dirichletForm_zero
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    (f g : V → ℝ) (hg : G.HasFiniteEnergy g) (hgA : ∀ v ∈ A, g v = 0) :
    G.dirichletForm (G.energyMin hG A f) g = 0 := by
  let a := hA.choose
  have ha : a ∈ A := hA.choose_spec
  let z : G.DirichletSpace hG a :=
    ReflectedWalk.ConductanceGraph.DirichletSpace.mk g hg (hgA a ha)
  let K := G.zeroOn hG a A
  let v := G.shiftedExt hG ha f
  have hz : z ∈ K := hgA
  have ho := K.starProjection_inner_eq_zero v z hz
  rw [G.energyMin_eq_aux hG hA]
  change G.dirichletForm (G.energyMinAux hG ha f) g = 0
  rw [show G.energyMinAux hG ha f =
      (fun x => (v - K.starProjection v) x + f a) from
        funext (G.energyMinAux_eq hG ha f)]
  rw [dirichletForm_add_const_left]
  exact ho

/-- Exact energy decomposition against the actual finite-target extension.
There is no finite-support restriction on the competitor or its residual. -/
theorem energyMin_energy_pythagorean
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    (f : V → ℝ) (hf : G.HasFiniteEnergy f) :
    G.Energy f = G.Energy (G.energyMin hG A f) +
      G.Energy (f - G.energyMin hG A f) := by
  let u := G.energyMin hG A f
  have hu : G.HasFiniteEnergy u := G.energyMin_hasFiniteEnergy hG hA f
  have hr := hf.sub hu
  have ho : G.dirichletForm u (f - u) = 0 :=
    energyMin_dirichletForm_zero G hG hA f (f - u) hr (by
      intro x hx
      simp only [Pi.sub_apply, u, G.energyMin_eqOn hG hA f hx, sub_self])
  have hs : u + (f - u) = f := by ext x; simp
  conv_lhs => rw [← hs]
  rw [← G.dirichletForm_self,
    G.dirichletForm_add_left hu hr (hu.add hr),
    G.dirichletForm_comm u (u + (f - u)), G.dirichletForm_add_left hu hr hu,
    G.dirichletForm_comm (f - u) (u + (f - u)), G.dirichletForm_add_left hu hr hr,
    G.dirichletForm_self, G.dirichletForm_self, G.dirichletForm_comm (f - u) u, ho]
  simp only [add_zero, zero_add]
  rfl

end ReflectedGMS.FullNetworkForm
