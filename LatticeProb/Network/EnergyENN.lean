/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: ReflectedGMS/Analysis/ExtendedEnergy.lean.
-/
import LatticeProb.Network.DirichletForm
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Extended-valued Dirichlet energy

For a conductance graph `G` and `f : V → ℝ`, `G.Energy f` is the real number
`½ ∑ c(x,y) (f y - f x) ^ 2`, a real `tsum` over ordered pairs. Lean's `tsum` of a non-summable
family is `0`, so `G.Energy f = 0` also when `f` has infinite energy. The real-valued `Energy`
alone therefore cannot tell such functions apart from functions of energy `0`.

`energyENN G f : ℝ≥0∞` is the same sum computed in `ℝ≥0∞`, where a divergent sum is `∞`. Hence
`energyENN G f = ∞` exactly when `G.HasFiniteEnergy f` fails
(`energyENN_eq_top_iff_not_hasFiniteEnergy`), and `energyENN G f = ENNReal.ofReal (G.Energy f)`
when `G.HasFiniteEnergy f` holds (`energyENN_eq_ofReal_Energy`).

The file proves that `energyENN` is unchanged by subtracting a constant, that it is multiplied by
`a ^ 2` when `f` is multiplied by `a`, and that it is finite exactly on the finite-energy
functions, where its `ENNReal.toReal` is `Energy`.
-/

open scoped ENNReal NNReal

namespace LatticeProb.Network

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-- The Dirichlet energy of `f` as an extended nonnegative real: the sum over ordered pairs of the
energy summands, computed in `ℝ≥0∞`, and halved. It is `∞` exactly when `f` does not have finite
energy. -/
noncomputable def energyENN (f : V → ℝ) : ℝ≥0∞ :=
  (∑' p : V × V, ENNReal.ofReal (G.gradSq f p)) / 2

/-- Subtracting a constant from `f` does not change the extended energy. -/
theorem energyENN_sub_const (f : V → ℝ) (a : ℝ) :
    energyENN G (fun x => f x - a) = energyENN G f := by
  unfold energyENN
  simp_rw [G.gradSq_sub_const f a]

/-- Scaling `f` by `a` multiplies the extended energy by `a ^ 2`. -/
theorem energyENN_smul (a : ℝ) (f : V → ℝ) :
    energyENN G (a • f) = ENNReal.ofReal (a ^ 2) * energyENN G f := by
  unfold energyENN
  simp_rw [G.gradSq_smul a f, ENNReal.ofReal_mul (sq_nonneg a)]
  rw [ENNReal.tsum_mul_left, mul_div_assoc]

/-- The extended-valued energy sum is finite exactly when `f` has finite energy. -/
lemma tsum_ofReal_gradSq_ne_top_iff (f : V → ℝ) :
    (∑' p : V × V, ENNReal.ofReal (G.gradSq f p)) ≠ ∞ ↔
      G.HasFiniteEnergy f := by
  simpa only [ENNReal.ofReal,
    Real.coe_toNNReal _ (G.gradSq_nonneg f _),
    ConductanceGraph.HasFiniteEnergy] using
    (ENNReal.tsum_coe_ne_top_iff_summable_coe
      (f := fun p : V × V => Real.toNNReal (G.gradSq f p)))

/-- The extended energy of `f` is finite exactly when `f` has finite energy. -/
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

/-- For a function of finite energy, the real part of the extended energy is the real energy. -/
theorem energyENN_toReal_eq_Energy {f : V → ℝ}
    (hf : G.HasFiniteEnergy f) :
    (energyENN G f).toReal = G.Energy f := by
  rw [energyENN, ENNReal.toReal_div]
  norm_num
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun p => G.gradSq_nonneg f p) hf]
  rw [ENNReal.toReal_ofReal (tsum_nonneg fun p => G.gradSq_nonneg f p)]
  rfl

/-- For a function of finite energy, the extended energy is the nonnegative real energy. -/
theorem energyENN_eq_ofReal_Energy {f : V → ℝ}
    (hf : G.HasFiniteEnergy f) :
    energyENN G f = ENNReal.ofReal (G.Energy f) := by
  calc
    energyENN G f = ENNReal.ofReal (energyENN G f).toReal :=
      (ENNReal.ofReal_toReal ((energyENN_ne_top_iff G f).2 hf)).symm
    _ = ENNReal.ofReal (G.Energy f) := by
      rw [energyENN_toReal_eq_Energy G hf]

/-- The extended energy is `∞` exactly when `f` does not have finite energy. -/
theorem energyENN_eq_top_iff_not_hasFiniteEnergy (f : V → ℝ) :
    energyENN G f = ∞ ↔ ¬ G.HasFiniteEnergy f := by
  constructor
  · intro htop hf
    exact (energyENN_ne_top_iff G f).2 hf htop
  · intro hf
    by_contra htop
    exact hf ((energyENN_ne_top_iff G f).1 htop)

section UnitEdgeNormalization

/-- Two vertices joined by an edge of conductance `1`: the conductance is `0` on the diagonal and
`1` off it. Used only for the examples below. -/
private def unitEdge : ConductanceGraph Bool where
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

/-- Every function on the two-point graph has finite energy. -/
private theorem unitEdge_hasFiniteEnergy (f : Bool → ℝ) :
    unitEdge.HasFiniteEnergy f := by
  exact Summable.of_finite

-- On the two-point graph, the extended energy is the squared difference of the two values.
example (f : Bool → ℝ) :
    energyENN unitEdge f =
      ENNReal.ofReal ((f true - f false) ^ 2) := by
  have hsquare : (f false - f true) ^ 2 =
      (f true - f false) ^ 2 := by
    ring
  simp only [energyENN, tsum_fintype]
  simp [Fintype.sum_prod_type, unitEdge,
    ConductanceGraph.gradSq, hsquare]
  rw [← two_mul, mul_comm (2 : ℝ≥0∞), mul_div_assoc,
    ENNReal.div_self (by norm_num) (by norm_num), mul_one]

-- On the two-point graph, the real part of the extended energy is the real energy.
example (f : Bool → ℝ) :
    (energyENN unitEdge f).toReal = unitEdge.Energy f :=
  energyENN_toReal_eq_Energy unitEdge (unitEdge_hasFiniteEnergy f)

end UnitEdgeNormalization

end ConductanceGraph

end LatticeProb.Network
