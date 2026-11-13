/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.GridStoppingIncrement at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.GridStoppingTransfer
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppingIncrementProbability

/-! Clip a later grid stopping index at a bounded delay from the earlier one.
The existing bounded-increment estimate then controls the event that a large
excursion occurs within that delay. This is the short-gap term in the greedy
modulus estimate. -/

-- Merged from `ReflectedGMS/Limit/MartingaleArrayIncrements.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_MartingaleArrayIncrements

/-!
Stopping-time increments for a varying family of martingales. Uniform L¹
control of the error from a linear compensator gives the small-increment
condition used in tightness proofs. This does not infer L¹ convergence from
convergence in probability, nor assert path-space tightness or an FCLT.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A uniform error envelope for the bracket supplies a quantitative bound
at arbitrary ordered bounded stopping times. -/
theorem bounded_stopping_increment_probability_le_of_linear_bracket_error
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (T : ℝ≥0) (hστ : ∀ ω, σ ω ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2T : MemLp (M T) 2 P)
    {a : ℝ} (ha : 0 ≤ a) (δ : ℝ≥0)
    (hgap : ∀ ω, ((τ ω).untopA : ℝ) - ((σ ω).untopA : ℝ) ≤ δ)
    {R : Ω → ℝ} (hR : Integrable R P)
    (herror : ∀ᵐ ω ∂P, ∀ t ≤ T, |B t ω - a * (t : ℝ)| ≤ R ω)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |stoppedValue M τ ω - stoppedValue M σ ω|} ≤
      ENNReal.ofReal ((a * (δ : ℝ) + 2 * ∫ ω, R ω ∂P) / ε ^ 2) := by
  have hid := bounded_stopping_bracket_increment_integral
    hM hC hσ hτ T hστ hτT hrM hrC h2T
  have hb : ∀ᵐ ω ∂P,
      stoppedValue B τ ω - stoppedValue B σ ω ≤ a * (δ : ℝ) + 2 * R ω := by
    filter_upwards [herror] with ω hω
    have heτ := (abs_le.mp (hω (τ ω).untopA (WithTop.untopA_le (hτT ω)))).2
    have heσ := (abs_le.mp (hω (σ ω).untopA
      (WithTop.untopA_le ((hστ ω).trans (hτT ω))))).1
    have hg := mul_le_mul_of_nonneg_left (hgap ω) ha
    dsimp only [stoppedValue]
    nlinarith only [heτ, heσ, hg]
  have hmean :
      (∫ ω, stoppedValue B τ ω - stoppedValue B σ ω ∂P) ≤
        a * (δ : ℝ) + 2 * ∫ ω, R ω ∂P := by
    calc
      _ ≤ ∫ ω, a * (δ : ℝ) + 2 * R ω ∂P :=
        integral_mono_ae hid.2.1 ((integrable_const _).add (hR.const_mul 2)) hb
      _ = _ := by
        rw [integral_add (integrable_const _) (hR.const_mul 2)]
        simp [integral_const_mul]
  exact (bounded_stopping_increment_probability_le hM hC hσ hτ T hστ hτT
    hrM hrC h2T hε).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hmean (sq_nonneg ε)))

end ReflectedGMS.MartingaleLimit

end Merged_MartingaleArrayIncrements

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A large displacement between ordered grid stops over a short random gap
has the same bound as a stopping increment with a deterministic gap bound.
The short-gap condition is imposed on the event, rather than on every sample. -/
theorem grid_stopping_short_gap_probability_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 m} {G : Filtration ℕ m}
    {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    (d : ℝ≥0) (hGF : ∀ i, G i ≤ F ((i : ℝ≥0) * d))
    {σ ν : Ω → ℕ}
    (hσ : IsStoppingTime G (fun ω => (σ ω : WithTop ℕ)))
    (hν : IsStoppingTime G (fun ω => (ν ω : WithTop ℕ)))
    (N L : ℕ) (hσν : ∀ ω, σ ω ≤ ν ω) (hνN : ∀ ω, ν ω ≤ N)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2T : MemLp (M ((N : ℝ≥0) * d)) 2 P)
    {v : ℝ} (hv : 0 ≤ v) {R : Ω → ℝ} (hR : Integrable R P)
    (herror : ∀ᵐ ω ∂P, ∀ t ≤ (N : ℝ≥0) * d,
      |B t ω - v * (t : ℝ)| ≤ R ω)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ν ω ≤ σ ω + L ∧
      ε ≤ |M ((ν ω : ℝ≥0) * d) ω - M ((σ ω : ℝ≥0) * d) ω|} ≤
      ENNReal.ofReal ((v * ((L : ℝ≥0) * d : ℝ≥0) +
        2 * ∫ ω, R ω ∂P) / ε ^ 2) := by
  let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * d
  have hgrid : Monotone grid := fun i j hij =>
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (show 0 ≤ d from zero_le)
  let γ : Ω → ℕ := fun ω => min (ν ω) (σ ω + L)
  have hγ : IsStoppingTime G (fun ω => (γ ω : WithTop ℕ)) := by
    have heq : (fun ω => (γ ω : WithTop ℕ)) =
        (fun ω => min (ν ω : WithTop ℕ) ((σ ω : WithTop ℕ) + (L : WithTop ℕ))) := by
      funext ω
      rfl
    rw [heq]
    exact hν.min (hσ.add_const' L)
  let S : Ω → WithTop ℝ≥0 := fun ω => grid (σ ω)
  let Q : Ω → WithTop ℝ≥0 := fun ω => grid (γ ω)
  have hS : IsStoppingTime F S := isStoppingTime_deterministicGrid grid hGF hσ
  have hQ : IsStoppingTime F Q := isStoppingTime_deterministicGrid grid hGF hγ
  have hSQ : ∀ ω, S ω ≤ Q ω := by
    intro ω
    exact WithTop.coe_le_coe.mpr (hgrid (le_min (hσν ω) (Nat.le_add_right _ _)))
  have hQT : ∀ ω, Q ω ≤ grid N := by
    intro ω
    exact WithTop.coe_le_coe.mpr (hgrid ((min_le_left _ _).trans (hνN ω)))
  have hgap : ∀ ω, ((Q ω).untopA : ℝ) - ((S ω).untopA : ℝ) ≤
      ((L : ℝ≥0) * d : ℝ≥0) := by
    intro ω
    change (γ ω : ℝ) * (d : ℝ) - (σ ω : ℝ) * (d : ℝ) ≤
      (L : ℝ) * (d : ℝ)
    have hidx : (γ ω : ℝ) ≤ (σ ω : ℝ) + (L : ℝ) := by
      exact_mod_cast (min_le_right (ν ω) (σ ω + L))
    apply sub_le_iff_le_add.mpr
    calc
      (γ ω : ℝ) * (d : ℝ) ≤ ((σ ω : ℝ) + (L : ℝ)) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right hidx d.2
      _ = (L : ℝ) * (d : ℝ) + (σ ω : ℝ) * (d : ℝ) := by ring
  have hbound := bounded_stopping_increment_probability_le_of_linear_bracket_error
    hM hC hS hQ (grid N) hSQ hQT hrM hrC h2T hv ((L : ℝ≥0) * d)
    hgap hR herror hε
  refine (measure_mono ?_).trans hbound
  intro ω hω
  change ε ≤ |M (grid (γ ω)) ω - M (grid (σ ω)) ω|
  have hγν : γ ω = ν ω := min_eq_left hω.1
  rw [hγν]
  exact hω.2

end ReflectedGMS.MartingaleLimit
