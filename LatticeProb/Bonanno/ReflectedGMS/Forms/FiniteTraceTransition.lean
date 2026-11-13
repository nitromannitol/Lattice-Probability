/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteTraceTransition at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceGraph
import LatticeProb.Bonanno.ReflectedWalk.ApproximatingChain

/-!
# The existing induced chain has the full trace conductances

This identifies the concrete induced transition probabilities of the reflected
walk construction with the full-energy trace. Self returns remain in the induced
chain and disappear only from the off-diagonal continuous-time jump rates.
No assertion about a time-changed process law is made here.
-/

set_option autoImplicit false

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

theorem inducedTransProb_eq_harmonic_trace_div
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    {x y : V} (hx : x ∈ A) (hy : y ∈ A) :
    G.inducedTransProb hG A x y =
      (∑' z, G.c x z * G.harmonicMeasure hG A z y) / G.pi x := by
  classical
  let d : V → ℝ := fun z => if z = y then G.c x y / G.pi x else 0
  have hd : Summable d := summable_of_ne_finset_zero (s := {y}) (by
    intro z hz
    have hzy : z ≠ y := by simpa using hz
    simp [d, hzy])
  have hpoint (z : V) : G.c x z * G.harmonicMeasure hG A z y / G.pi x =
      d z + G.jumpTerm hG A x y z := by
    by_cases hz : z ∈ A
    · have he : G.harmonicMeasure hG A z y = if z = y then 1 else 0 := by
        exact G.energyMin_eqOn hG hA (G.indic y) hz
      simp only [he, ReflectedWalk.ConductanceGraph.jumpTerm, if_pos hz, add_zero, d]
      split_ifs with hzy
      · subst z; simp
      · simp
    · have hzy : z ≠ y := fun he => hz (he ▸ hy)
      simp only [ReflectedWalk.ConductanceGraph.jumpTerm, if_neg hz, d, if_neg hzy, zero_add]
      ring
  rw [G.inducedTransProb_of_mem_of_mem hG hx hy, ← tsum_div_const]
  simp_rw [hpoint]
  rw [hd.tsum_add (G.summable_jumpTerm hG hA x y)]
  simp [d]

theorem pi_mul_inducedTransProb [Nontrivial V]
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    {x y : V} (hx : x ∈ A) (hy : y ∈ A) :
    G.pi x * G.inducedTransProb hG A x y =
      ∑' z, G.c x z * G.harmonicMeasure hG A z y := by
  rw [inducedTransProb_eq_harmonic_trace_div G hG hA hx hy]
  field_simp [(G.pi_pos_of_connected hG x).ne']

end ReflectedGMS.FullNetworkForm
