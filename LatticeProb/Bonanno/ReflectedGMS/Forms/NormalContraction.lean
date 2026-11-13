/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.NormalContraction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullNetworkForm
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Normal contractions of the full network form

A real 1-Lipschitz map fixing zero preserves the full speed-`L²`, finite-energy
domain and decreases its energy. The proof uses domination in the existing
`Memℓp` space and comparison of the original summable edge densities.
The usual Markov operation is a coercion of mathlib's existing `Set.projIcc`.
-/

set_option autoImplicit false

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} {C : ℝ → ℝ}

/-- A normal contraction decreases the absolute value at every vertex. -/
theorem norm_normalContraction_le (hC : LipschitzWith 1 C) (hzero : C 0 = 0)
    (x : ℝ) : ‖C x‖ ≤ ‖x‖ := by
  simpa only [dist_eq_norm, hzero, sub_zero, NNReal.coe_one, one_mul]
    using hC.dist_le_mul x 0

/-- Normal contractions preserve the full weighted square-summability condition.
No positive lower bound on the speed is needed. -/
theorem hasSpeedL2_normalContraction (m : V → ℝ) (f : V → ℝ)
    (hC : LipschitzWith 1 C) (hzero : C 0 = 0) (hf : HasSpeedL2 m f) :
    HasSpeedL2 m (C ∘ f) := by
  apply hf.mono'
  intro v
  simp only [Function.comp_apply, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_normalContraction_le hC hzero (f v))
    (norm_nonneg _)

variable (G : ReflectedWalk.ConductanceGraph V)

/-- Every individual edge-energy density decreases under a 1-Lipschitz map. -/
theorem gradSq_contraction_le (f : V → ℝ) (hC : LipschitzWith 1 C) (p : V × V) :
    G.gradSq (C ∘ f) p ≤ G.gradSq f p := by
  have hd : |C (f p.2) - C (f p.1)| ≤ |f p.2 - f p.1| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul]
      using hC.dist_le_mul (f p.2) (f p.1)
  exact mul_le_mul_of_nonneg_left (sq_le_sq.2 hd) (G.c_nonneg p.1 p.2)

/-- The full finite-energy domain is invariant under every 1-Lipschitz map. -/
theorem hasFiniteEnergy_contraction (f : V → ℝ) (hC : LipschitzWith 1 C)
    (hf : G.HasFiniteEnergy f) : G.HasFiniteEnergy (C ∘ f) :=
  Summable.of_nonneg_of_le (fun p => G.gradSq_nonneg (C ∘ f) p)
    (gradSq_contraction_le G f hC) hf

/-- Contraction of the original half-ordered-pair energy, with full summability. -/
theorem energy_contraction_le (f : V → ℝ) (hC : LipschitzWith 1 C)
    (hf : G.HasFiniteEnergy f) : G.Energy (C ∘ f) ≤ G.Energy f := by
  have hc := hasFiniteEnergy_contraction G f hC hf
  exact div_le_div_of_nonneg_right
    (hc.tsum_le_tsum (gradSq_contraction_le G f hC) hf) (by norm_num)

/-- Normal contractions preserve the exact full form domain and decrease energy. -/
theorem normalContraction (m : V → ℝ) (f : V → ℝ)
    (hC : LipschitzWith 1 C) (hzero : C 0 = 0)
    (hL2 : HasSpeedL2 m f) (hE : G.HasFiniteEnergy f) :
    HasSpeedL2 m (C ∘ f) ∧ G.HasFiniteEnergy (C ∘ f) ∧
      G.Energy (C ∘ f) ≤ G.Energy f :=
  ⟨hasSpeedL2_normalContraction m f hC hzero hL2,
    hasFiniteEnergy_contraction G f hC hE, energy_contraction_le G f hC hE⟩

/-- The usual Markov operation, using the existing closed-interval projection. -/
noncomputable def unitIntervalProjection (x : ℝ) : ℝ :=
  Set.projIcc 0 1 (by norm_num) x

@[simp] theorem unitIntervalProjection_zero : unitIntervalProjection 0 = 0 := by
  norm_num [unitIntervalProjection, Set.coe_projIcc]

theorem unitIntervalProjection_lipschitz : LipschitzWith 1 unitIntervalProjection := by
  unfold unitIntervalProjection
  simpa only [one_mul, Function.comp_def] using
    (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1)).comp
      (LipschitzWith.projIcc (by norm_num : (0 : ℝ) ≤ 1))

theorem unitIntervalProjection_mem (x : ℝ) :
    unitIntervalProjection x ∈ Set.Icc (0 : ℝ) 1 :=
  (Set.projIcc (0 : ℝ) 1 (by norm_num) x).property

end ReflectedGMS.FullNetworkForm
