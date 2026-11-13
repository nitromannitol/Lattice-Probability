/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteTraceEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceGraph

/-!
# Equality of the finite trace energy and the full harmonic-extension energy

Reuse the checked equality of harmonic-basis and trace-Laplacian matrices.
Only finite bilinear expansion is needed; the extension still minimizes over
the full finite-energy domain of the original network.
-/

set_option autoImplicit false
open Classical

namespace ReflectedGMS.FullNetworkForm

variable {V I : Type*} (G : ReflectedWalk.ConductanceGraph V)

private theorem finiteEnergy_sum (s : Finset I) (f : I → V → ℝ)
    (hf : ∀ i ∈ s, G.HasFiniteEnergy (f i)) :
    G.HasFiniteEnergy (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using G.hasFiniteEnergy_zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem pairing_sum_left (s : Finset I) (f : I → V → ℝ)
    (g : V → ℝ) (hf : ∀ i ∈ s, G.HasFiniteEnergy (f i)) (hg : G.HasFiniteEnergy g) :
    G.dirichletForm (∑ i ∈ s, f i) g = ∑ i ∈ s, G.dirichletForm (f i) g := by
  induction s using Finset.induction_on with
  | empty => simp [ReflectedWalk.ConductanceGraph.dirichletForm,
      ReflectedWalk.ConductanceGraph.gradProd]
  | @insert i s hi ih =>
    have hrest := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      G.dirichletForm_add_left (hf i (Finset.mem_insert_self _ _))
        (finiteEnergy_sum G s f hrest) hg, ih hrest]

private theorem energy_sum_smul (s : Finset I) (f : I → V → ℝ)
    (a : I → ℝ) (hf : ∀ i ∈ s, G.HasFiniteEnergy (f i)) :
    G.Energy (∑ i ∈ s, a i • f i) =
      ∑ i ∈ s, ∑ j ∈ s, a i * a j * G.dirichletForm (f i) (f j) := by
  have ha : ∀ i ∈ s, G.HasFiniteEnergy (a i • f i) := fun i hi => (hf i hi).smul _
  rw [← G.dirichletForm_self, pairing_sum_left G s _ _ ha (finiteEnergy_sum G s _ ha)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [G.dirichletForm_comm, pairing_sum_left G s _ _ ha (ha i hi)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [G.dirichletForm_smul_left, G.dirichletForm_comm, G.dirichletForm_smul_left]
  ring

private theorem indic_pairing (x y : V) :
    G.dirichletForm (G.indic x) (G.indic y) =
      if x = y then G.pi x else -G.c x y := by
  rw [VertexTest.dirichletForm_indic_eq_neg_laplacian G _
    (VertexTest.indic_hasFiniteEnergy G x)]
  by_cases hxy : x = y
  · subst y
    have hp (z : V) : G.lapTerm (G.indic x) x z = -G.c x z := by
      by_cases hzx : z = x
      · subst z; simp [ReflectedWalk.ConductanceGraph.lapTerm, G.c_self]
      · simp [ReflectedWalk.ConductanceGraph.lapTerm,
          ReflectedWalk.ConductanceGraph.indic, hzx]
    simp_rw [hp]
    simp [tsum_neg, ReflectedWalk.ConductanceGraph.pi]
  · simp [ReflectedWalk.ConductanceGraph.lapTerm,
      ReflectedWalk.ConductanceGraph.indic, hxy, Ne.symm hxy, mul_ite, G.c_symm]

/-- The full energy of the actual harmonic extension equals the energy of its
boundary data in the finite trace graph, including singleton targets. -/
theorem finiteTargetGraph_energy
    (hG : G.toSimpleGraph.Connected) (A : Finset V) (hA : A.Nonempty) (f : V → ℝ) :
    (finiteTargetGraph G hG A hA).Energy (fun x => f x.1) =
      G.Energy (G.energyMin hG A f) := by
  let J := {x // x ∈ A}
  let T : ReflectedWalk.ConductanceGraph J := finiteTargetGraph G hG A hA
  let b : J → V → ℝ := fun x => G.energyMin hG A (G.indic x.1)
  have hfull : (∑ x : J, f x.1 • b x) = G.energyMin hG A f := by
    ext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b]
    change (∑ x ∈ A.attach, f x.1 * G.harmonicMeasure hG A z x.1) = _
    exact (Finset.sum_attach A (fun x => f x * G.harmonicMeasure hG A z x)).trans
      (G.energyMin_eq_sum_harmonicMeasure hG hA f z).symm
  have htrace : (∑ x : J, f x.1 • T.indic x) = (fun x : J => f x.1) := by
    ext z
    simp only [ReflectedWalk.ConductanceGraph.indic, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single z]
    · simp
    · intro c hc hcz
      simp [Ne.symm hcz]
    · simp
  calc
    T.Energy (fun x : J => f x.1) =
        ∑ x : J, ∑ y : J, f x.1 * f y.1 * T.dirichletForm (T.indic x) (T.indic y) := by
      rw [← htrace]
      exact energy_sum_smul T Finset.univ _ _
        (fun x _ => VertexTest.indic_hasFiniteEnergy T x)
    _ = ∑ x : J, ∑ y : J, f x.1 * f y.1 * G.dirichletForm (b x) (b y) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      simp only [b]
      rw [indic_pairing T, finiteTargetGraph_basis_pairing G hG A hA x y]
      split_ifs <;> rfl
    _ = G.Energy (G.energyMin hG A f) := by
      rw [← hfull]
      exact (energy_sum_smul G Finset.univ b (fun x : J => f x.1)
        (fun x _ => G.energyMin_hasFiniteEnergy hG hA (G.indic x.1))).symm

end ReflectedGMS.FullNetworkForm
