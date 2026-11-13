/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteTraceGraph at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTargetTrace

/-!
# The finite trace as an existing conductance graph

The full-network harmonic-return coefficients supply the off-diagonal edges.
The diagonal return coefficient is removed from the holding rate. A singleton
target therefore has zero generator, with no nontriviality assumption.
-/

set_option autoImplicit false
open Classical

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-- The finite harmonic trace, using the existing conductance-graph definition. -/
noncomputable def finiteTargetGraph (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) : ReflectedWalk.ConductanceGraph {x // x ∈ A} := by
  classical
  exact
    { c := fun x y => if x = y then 0 else
        ∑' z, G.c x.1 z * G.harmonicMeasure hG A z y.1
      c_symm := by
        intro x y
        by_cases hxy : x = y
        · simp [hxy]
        · simp only [ite_eq_right hxy, ite_eq_right (Ne.symm hxy)]
          exact harmonic_trace_conductance_symm G hG hA x.2 y.2
            (fun h => hxy (Subtype.ext h))
      c_nonneg := by
        intro x y
        split_ifs
        · exact le_rfl
        · exact harmonic_trace_conductance_nonneg G hG hA x.1 y.1
      c_self := by intro x; simp
      summable_c := fun _ => (hasSum_fintype _).summable }

/-- The trace has exactly the full-network harmonic-return coefficient off its diagonal. -/
theorem finiteTargetGraph_c_of_ne (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) {x y : {v // v ∈ A}} (hxy : x ≠ y) :
    (finiteTargetGraph G hG A hA).c x y =
      ∑' z, G.c x.1 z * G.harmonicMeasure hG A z y.1 := by
  classical
  exact if_neg hxy

/-- The total trace conductance removes only the return-to-self coefficient. -/
theorem finiteTargetGraph_pi (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (x : {v // v ∈ A}) :
    (finiteTargetGraph G hG A hA).pi x = G.pi x.1 -
      ∑' z, G.c x.1 z * G.harmonicMeasure hG A z x.1 := by
  classical
  let K : {v // v ∈ A} → ℝ := fun y =>
    ∑' z, G.c x.1 z * G.harmonicMeasure hG A z y.1
  have hs : (∑ y : {v // v ∈ A}, K y) = G.pi x.1 := by
    change (∑ y ∈ A.attach, K y) = _
    exact (Finset.sum_attach A _).trans (harmonic_trace_conductance_sum G hG hA x.1)
  have hsplit : (∑ y : {v // v ∈ A}, if x = y then (0 : ℝ) else K y) + K x =
      ∑ y : {v // v ∈ A}, K y := by
    have he := Finset.sum_add_distrib (s := Finset.univ)
      (f := fun y => if x = y then (0 : ℝ) else K y)
      (g := fun y => if x = y then K y else 0)
    have hp (y : {v // v ∈ A}) :
        (if x = y then (0 : ℝ) else K y) + (if x = y then K y else 0) = K y := by
      split_ifs <;> simp
    simp_rw [hp] at he
    simpa only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] using he.symm
  change (∑' y : {v // v ∈ A}, if x = y then (0 : ℝ) else K y) = G.pi x.1 - K x
  rw [tsum_fintype]
  linarith

/-- Diagonal harmonic-basis energy is the original conductance minus self return. -/
theorem energyMin_indic_pairing_diagonal
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    {x : V} (hx : x ∈ A) :
    G.dirichletForm (G.energyMin hG A (G.indic x))
      (G.energyMin hG A (G.indic x)) = G.pi x -
        ∑' z, G.c x z * G.harmonicMeasure hG A z x := by
  classical
  rw [energyMin_pairing_eq G hG hA _ _ (VertexTest.indic_hasFiniteEnergy G x),
    VertexTest.dirichletForm_indic_eq_neg_laplacian G _
      (G.energyMin_hasFiniteEnergy hG hA _)]
  have hp (z : V) : G.lapTerm (G.energyMin hG A (G.indic x)) x z =
      G.c x z * G.harmonicMeasure hG A z x - G.c x z := by
    simp only [ReflectedWalk.ConductanceGraph.lapTerm,
      G.energyMin_eqOn hG hA (G.indic x) hx,
      ReflectedWalk.ConductanceGraph.indic, ite_true,
      ReflectedWalk.ConductanceGraph.harmonicMeasure]
    ring
  simp_rw [hp]
  rw [(harmonic_trace_conductance_summable G hG hA x x).tsum_sub (G.summable_c x)]
  change -( _ - G.pi x) = _
  ring

/-- The full-energy harmonic-basis matrix is exactly the trace graph Laplacian. -/
theorem finiteTargetGraph_basis_pairing
    (hG : G.toSimpleGraph.Connected) (A : Finset V) (hA : A.Nonempty)
    (x y : {v // v ∈ A}) :
    G.dirichletForm (G.energyMin hG A (G.indic x.1))
      (G.energyMin hG A (G.indic y.1)) =
        if x = y then (finiteTargetGraph G hG A hA).pi x
        else -(finiteTargetGraph G hG A hA).c x y := by
  classical
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl, energyMin_indic_pairing_diagonal G hG hA x.2,
      finiteTargetGraph_pi]
  · rw [if_neg hxy, finiteTargetGraph_c_of_ne G hG A hA hxy,
      G.dirichletForm_comm]
    exact energyMin_indic_pairing_offDiagonal G hG hA x.2
      (fun h => hxy (Subtype.ext h.symm))

end ReflectedGMS.FullNetworkForm
