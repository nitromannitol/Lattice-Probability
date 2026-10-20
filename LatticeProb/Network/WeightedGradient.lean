/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: ReflectedGMS/Analysis/WeightedGradient.lean.
Source: ReflectedGMS/Forms/FullNetworkForm.lean.
-/
import LatticeProb.Network.Conductance
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Normalized weighted gradients on ordered pairs

For a conductance graph `G` and a function `f : V → ℝ`, the normalized gradient of `f` is the
family `(√(c x y / 2) * (f y - f x))_{(x, y)}` indexed by ordered pairs `(x, y) : V × V`. When `f`
has finite energy, this family is square-summable, so it is a vector of the Hilbert space
`lp (fun _ : V × V => ℝ) 2` (also written `GradientSpace V`).

The factor `½` is built into the coordinates, so the squared norm of the gradient is exactly the
energy `G.Energy f`. Pairs of zero conductance have zero coordinate. No connectedness,
countability, finite support, or boundary condition is assumed.

The declarations live in the namespace `ConductanceGraph` (`G.weightedGradient f hf`). They are
different from LP's finite-network edge field `LatticeProb.Network.weightedGradient c f`.
-/

namespace LatticeProb.Network

/-- The Hilbert space `ℓ²` of real families indexed by ordered pairs `(x, y) : V × V`. Normalized
gradients of finite-energy functions live here. Pairs of zero conductance have coordinate `0`. -/
abbrev GradientSpace (V : Type*) := lp (fun _ : V × V => ℝ) 2

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-- The normalized gradient coordinate `√(c x y / 2) * (f y - f x)` at the ordered pair
`p = (x, y)`. The space it lives in is `ℓ²` over ordered pairs, not over unoriented edges. A pair
of zero conductance has coordinate `0`, whatever the values of `f`. -/
noncomputable def weightedGradientCoord (f : V → ℝ) (p : V × V) : ℝ :=
  Real.sqrt (G.c p.1 p.2 / 2) * (f p.2 - f p.1)

/-- The square of the normalized gradient coordinate is half the energy density
`c x y * (f y - f x) ^ 2` of the ordered pair `(x, y)`. The factor `½` is built into the
normalization. Pairs of zero conductance contribute `0` on both sides. -/
theorem weightedGradientCoord_sq (f : V → ℝ) (p : V × V) :
    weightedGradientCoord G f p ^ 2 = G.gradSq f p / 2 := by
  rw [weightedGradientCoord, mul_pow,
    Real.sq_sqrt (div_nonneg (G.c_nonneg _ _) (by norm_num))]
  simp only [ConductanceGraph.gradSq]
  ring

/-- If `f` has finite energy, its normalized gradient is square-summable over ordered pairs. -/
theorem weightedGradientCoord_memℓp {f : V → ℝ} (hf : G.HasFiniteEnergy f) :
    Memℓp (weightedGradientCoord G f) 2 := by
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    weightedGradientCoord_sq] using hf.div_const 2

/-- The normalized gradient of a finite-energy function, as a vector of the Hilbert space `ℓ²`
over ordered pairs `(x, y)`. Pairs of zero conductance have coordinate `0`. -/
noncomputable def weightedGradient (f : V → ℝ) (hf : G.HasFiniteEnergy f) :
    lp (fun _ : V × V => ℝ) 2 :=
  ⟨weightedGradientCoord G f, weightedGradientCoord_memℓp G hf⟩

/-- The coordinates of the normalized gradient are `√(c x y / 2) * (f y - f x)` at each ordered
pair `(x, y)`. Pairs of zero conductance have coordinate `0`. -/
@[simp] theorem weightedGradient_apply (f : V → ℝ) (hf : G.HasFiniteEnergy f)
    (p : V × V) :
    weightedGradient G f hf p = Real.sqrt (G.c p.1 p.2 / 2) * (f p.2 - f p.1) := rfl

/-- The squared `ℓ²` norm of the normalized gradient is the energy `G.Energy f`. The factor `½`
of the energy is carried by the coordinates, so the sum runs over all ordered pairs, and each
unoriented edge contributes twice. -/
theorem weightedGradient_norm_sq (f : V → ℝ) (hf : G.HasFiniteEnergy f) :
    ‖weightedGradient G f hf‖ ^ 2 = G.Energy f := by
  have h := lp.norm_rpow_eq_tsum (E := fun _ : V × V => ℝ)
    (p := 2) (by norm_num) (weightedGradient G f hf)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h
  rw [h]
  change (∑' p, weightedGradientCoord G f p ^ 2) = _
  simp_rw [weightedGradientCoord_sq]
  exact tsum_div_const

/-- A function `f` has finite energy exactly when its normalized gradient is square-summable over
ordered pairs `(x, y)`. -/
theorem weightedGradientCoord_mem_iff (f : V → ℝ) :
    Memℓp (weightedGradientCoord G f) 2 ↔ G.HasFiniteEnergy f := by
  constructor
  · intro hf
    have hs := hf.summable (by norm_num : 0 < (2 : ENNReal).toReal)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      weightedGradientCoord_sq] at hs
    have ht := hs.mul_left 2
    exact ht.congr fun p => by ring
  · exact weightedGradientCoord_memℓp G

end ConductanceGraph

/-! ## Example

The path `0 – 1 – 2` with unit conductances has finite energy for every function, since its
ordered-pair index set is finite. Its normalized gradient is therefore a genuine vector of
`GradientSpace (Fin 3)`. -/

namespace WeightedGradient.Example

/-- On the edge `(0, 1)` of the unit path, the normalized gradient coordinate is
`√(1 / 2) * (f 1 - f 0)`. -/
example (f : Fin 3 → ℝ) (hf : ConductanceGraph.Example.path3.HasFiniteEnergy f) :
    ConductanceGraph.Example.path3.weightedGradient f hf (0, 1) =
      Real.sqrt (1 / 2) * (f 1 - f 0) := by
  simp [ConductanceGraph.weightedGradient_apply, ConductanceGraph.Example.path3]

/-- On the unit path, the squared norm of the normalized gradient equals the energy. -/
example (f : Fin 3 → ℝ) :
    ‖ConductanceGraph.Example.path3.weightedGradient f Summable.of_finite‖ ^ 2 =
      ConductanceGraph.Example.path3.Energy f :=
  ConductanceGraph.weightedGradient_norm_sq _ f Summable.of_finite

end WeightedGradient.Example

end LatticeProb.Network
