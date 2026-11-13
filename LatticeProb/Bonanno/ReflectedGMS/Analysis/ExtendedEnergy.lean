/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Analysis.ExtendedEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.DirichletSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open scoped ENNReal NNReal

set_option autoImplicit false

namespace ReflectedGMS

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

noncomputable def energyENN (f : V → ℝ) : ℝ≥0∞ :=
  (∑' p : V × V, ENNReal.ofReal (G.gradSq f p)) / 2

theorem energyENN_sub_const (f : V → ℝ) (a : ℝ) :
    energyENN G (fun x => f x - a) = energyENN G f := by
  unfold energyENN
  simp_rw [G.gradSq_sub_const f a]

theorem energyENN_smul (a : ℝ) (f : V → ℝ) :
    energyENN G (a • f) = ENNReal.ofReal (a ^ 2) * energyENN G f := by
  unfold energyENN
  simp_rw [G.gradSq_smul a f, ENNReal.ofReal_mul (sq_nonneg a)]
  rw [ENNReal.tsum_mul_left, mul_div_assoc]

lemma tsum_ofReal_gradSq_ne_top_iff (f : V → ℝ) :
    (∑' p : V × V, ENNReal.ofReal (G.gradSq f p)) ≠ ∞ ↔
      G.HasFiniteEnergy f := by
  simpa only [ENNReal.ofReal,
    Real.coe_toNNReal _ (G.gradSq_nonneg f _),
    ReflectedWalk.ConductanceGraph.HasFiniteEnergy] using
    (ENNReal.tsum_coe_ne_top_iff_summable_coe
      (f := fun p : V × V => Real.toNNReal (G.gradSq f p)))

theorem energyENN_ne_top_iff (f : V → ℝ) :
    energyENN G f ≠ ∞ ↔ G.HasFiniteEnergy f := by
  constructor
  · intro h
    apply (tsum_ofReal_gradSq_ne_top_iff G f).1
    intro htop
    apply h
    rw [energyENN, htop]
    exact ENNReal.top_div_of_ne_top (by norm_num)
  · intro hf
    exact ENNReal.div_ne_top
      ((tsum_ofReal_gradSq_ne_top_iff G f).2 hf) (by norm_num)

theorem energyENN_toReal_eq_Energy {f : V → ℝ}
    (hf : G.HasFiniteEnergy f) :
    (energyENN G f).toReal = G.Energy f := by
  rw [energyENN, ENNReal.toReal_div]
  norm_num
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun p => G.gradSq_nonneg f p) hf]
  rw [ENNReal.toReal_ofReal (tsum_nonneg fun p => G.gradSq_nonneg f p)]
  rfl

theorem energyENN_eq_ofReal_Energy {f : V → ℝ}
    (hf : G.HasFiniteEnergy f) :
    energyENN G f = ENNReal.ofReal (G.Energy f) := by
  calc
    energyENN G f = ENNReal.ofReal (energyENN G f).toReal :=
      (ENNReal.ofReal_toReal ((energyENN_ne_top_iff G f).2 hf)).symm
    _ = ENNReal.ofReal (G.Energy f) := by
      rw [energyENN_toReal_eq_Energy G hf]

theorem energyENN_eq_top_iff_not_hasFiniteEnergy (f : V → ℝ) :
    energyENN G f = ∞ ↔ ¬ G.HasFiniteEnergy f := by
  constructor
  · intro htop hf
    exact (energyENN_ne_top_iff G f).2 hf htop
  · intro hf
    by_contra htop
    exact hf ((energyENN_ne_top_iff G f).1 htop)

section UnitEdgeNormalization

private def unitEdge : ReflectedWalk.ConductanceGraph Bool where
  c x y := if x = y then 0 else 1
  c_symm := by
    intro x y
    by_cases hxy : x = y
    · subst y
      simp
    · have hyx : y ≠ x := Ne.symm hxy
      simp [hxy, hyx]
  c_nonneg := by
    intro x y
    split_ifs <;> norm_num
  c_self := by
    intro x
    simp
  summable_c := by
    intro x
    exact Summable.of_finite

private theorem unitEdge_hasFiniteEnergy (f : Bool → ℝ) :
    unitEdge.HasFiniteEnergy f := by
  exact Summable.of_finite

example (f : Bool → ℝ) :
    energyENN unitEdge f =
      ENNReal.ofReal ((f true - f false) ^ 2) := by
  have hsquare : (f false - f true) ^ 2 =
      (f true - f false) ^ 2 := by
    ring
  simp only [energyENN, tsum_fintype]
  simp [Fintype.sum_prod_type, unitEdge,
    ReflectedWalk.ConductanceGraph.gradSq, hsquare]
  rw [← two_mul, mul_comm (2 : ℝ≥0∞), mul_div_assoc,
    ENNReal.div_self (by norm_num) (by norm_num), mul_one]

example (f : Bool → ℝ) :
    (energyENN unitEdge f).toReal = unitEdge.Energy f :=
  energyENN_toReal_eq_Energy unitEdge (unitEdge_hasFiniteEnergy f)

end UnitEdgeNormalization

end ReflectedGMS
