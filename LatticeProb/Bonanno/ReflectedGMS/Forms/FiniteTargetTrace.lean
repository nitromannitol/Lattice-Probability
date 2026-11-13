/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteTargetTrace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTargetOrthogonality
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexTest

/-!
# Effective finite-target conductances from the full energy form

Pair the existing harmonic extensions against actual vertex tests. This
identifies the off-diagonal trace coefficients and proves their symmetry using
full-energy orthogonality, including the harmonic return through the complement.
-/

set_option autoImplicit false

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-- Harmonic extension of the second argument preserves pairing with an
energy-minimizing extension of the first argument. -/
theorem energyMin_pairing_eq
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    (f g : V → ℝ) (hg : G.HasFiniteEnergy g) :
    G.dirichletForm (G.energyMin hG A f) (G.energyMin hG A g) =
      G.dirichletForm (G.energyMin hG A f) g := by
  let u := G.energyMin hG A f
  let v := G.energyMin hG A g
  have hu := G.energyMin_hasFiniteEnergy hG hA f
  have hv := G.energyMin_hasFiniteEnergy hG hA g
  have hz : G.dirichletForm u (g - v) = 0 :=
    energyMin_dirichletForm_zero G hG hA f (g - v) (hg.sub hv) (by
      intro x hx
      simp only [Pi.sub_apply, v, G.energyMin_eqOn hG hA g hx, sub_self])
  have hs : v + (g - v) = g := by ext x; simp
  have he := G.dirichletForm_add_left hv (hg.sub hv) hu
  rw [hs, G.dirichletForm_comm g u,
    G.dirichletForm_comm v u, G.dirichletForm_comm (g - v) u, hz, add_zero] at he
  exact he.symm

/-- An off-diagonal harmonic-basis pairing is the negative effective
conductance, including all excursions through vertices outside the target. -/
theorem energyMin_indic_pairing_offDiagonal
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    {x y : V} (hy : y ∈ A) (hxy : x ≠ y) :
    G.dirichletForm (G.energyMin hG A (G.indic x))
      (G.energyMin hG A (G.indic y)) =
        -∑' z, G.c y z * G.harmonicMeasure hG A z x := by
  classical
  rw [energyMin_pairing_eq G hG hA _ _ (VertexTest.indic_hasFiniteEnergy G y),
    VertexTest.dirichletForm_indic_eq_neg_laplacian G _
      (G.energyMin_hasFiniteEnergy hG hA _)]
  congr 1
  apply tsum_congr
  intro z
  simp only [ReflectedWalk.ConductanceGraph.lapTerm,
    G.energyMin_eqOn hG hA (G.indic x) hy,
    ReflectedWalk.ConductanceGraph.indic, if_neg (Ne.symm hxy), sub_zero,
    ReflectedWalk.ConductanceGraph.harmonicMeasure]

/-- The actual effective off-diagonal finite-target conductances are symmetric. -/
theorem harmonic_trace_conductance_symm
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    {x y : V} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    (∑' z, G.c x z * G.harmonicMeasure hG A z y) =
      ∑' z, G.c y z * G.harmonicMeasure hG A z x := by
  have h1 := energyMin_indic_pairing_offDiagonal G hG hA hy hxy
  have h2 := energyMin_indic_pairing_offDiagonal G hG hA hx hxy.symm
  rw [G.dirichletForm_comm] at h1
  linarith

/-- Nonnegativity of the effective harmonic-return coefficient. -/
theorem harmonic_trace_conductance_nonneg
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty) (x y : V) :
    0 ≤ ∑' z, G.c x z * G.harmonicMeasure hG A z y :=
  tsum_nonneg (fun z => mul_nonneg (G.c_nonneg x z)
    (G.harmonicMeasure_nonneg hG hA z y))

/-- The harmonic-return coefficient is an actual convergent sum. -/
theorem harmonic_trace_conductance_summable
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty) (x y : V) :
    Summable (fun z => G.c x z * G.harmonicMeasure hG A z y) :=
  Summable.of_nonneg_of_le
    (fun z => mul_nonneg (G.c_nonneg x z) (G.harmonicMeasure_nonneg hG hA z y))
    (fun z => by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (G.harmonicMeasure_le_one hG hA z y) (G.c_nonneg x z))
    (G.summable_c x)

/-- Summing all harmonic-return coefficients, including the return to the
starting vertex, recovers its original total conductance. -/
theorem harmonic_trace_conductance_sum
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty) (x : V) :
    (∑ y ∈ A, ∑' z, G.c x z * G.harmonicMeasure hG A z y) = G.pi x := by
  rw [← Summable.tsum_finsetSum
    (fun y (_ : y ∈ A) => harmonic_trace_conductance_summable G hG hA x y)]
  simp_rw [← Finset.mul_sum, G.sum_harmonicMeasure hG hA, mul_one]
  rfl

end ReflectedGMS.FullNetworkForm
