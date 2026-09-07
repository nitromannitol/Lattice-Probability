/-
The law of the driving data is translation invariant.

The two factors are invariant for different reasons.  The uniform variables are
invariant because translation is an injective reindexing of the labels that
preserves the one-label law, and an i.i.d. field on the sites is invariant for
the same reason.  The stacks are the factor whose one-site laws are not all
equal: the instruction law at `y` lives on the neighbours of `y`.  Translating
the data reads the stack of `y + v` and translates its instructions back, and
translating a uniform choice of a neighbour of `y + v` by `-v` is a uniform
choice of a neighbour of `y`, so that factor is invariant too.
-/
import LatticeProb.Equivariance
import LatticeProb.Prob.ZeroOne

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### The instruction law is a probability measure -/

theorem instructionLaw_univ (hd : 1 ≤ d) (y : Site d) :
    instructionLaw y Set.univ = 1 := by
  have hcard : (Finset.univ : Finset (Fin d)).card = d := by simp
  simp only [instructionLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.coe_add, Pi.add_apply, Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, Finset.sum_const, smul_eq_mul, nsmul_eq_mul, hcard]
  have h2d : (2 * (d : ℝ≥0∞)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
    exact ⟨two_ne_zero, by omega⟩
  have h2d' : (2 * (d : ℝ≥0∞)) ≠ ⊤ := by simp [ENNReal.mul_eq_top]
  rw [show ((d : ℝ≥0∞) * (1 + 1)) = 2 * (d : ℝ≥0∞) by ring]
  exact ENNReal.inv_mul_cancel h2d h2d'

theorem instructionLaw_isProbability (hd : 1 ≤ d) (y : Site d) :
    IsProbabilityMeasure (instructionLaw y) := ⟨instructionLaw_univ hd y⟩

/-! ### The three factors -/

theorem stackLaw_isProbability (hd : 1 ≤ d) : IsProbabilityMeasure (stackLaw d) := by
  haveI : ∀ y : Site d, IsProbabilityMeasure (instructionLaw y) := fun y =>
    instructionLaw_isProbability hd y
  exact inferInstanceAs
    (IsProbabilityMeasure (Measure.infinitePi fun p : Site d × ℕ => instructionLaw p.1))

theorem uniformUnit_isProbability : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  simp

theorem rankLaw_isProbability (d : ℕ) : IsProbabilityMeasure (rankLaw d) := by
  haveI := uniformUnit_isProbability
  exact inferInstanceAs (IsProbabilityMeasure
    (Measure.infinitePi fun _ : Label d × ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)))

/-- Translating a uniform neighbour of `y + v` back by `v` is a uniform
neighbour of `y`. -/
theorem instructionLaw_map_sub (v y : Site d) :
    (instructionLaw (y + v)).map (fun z : Site d => z - v) = instructionLaw y := by
  have hmeas : Measurable (fun z : Site d => z - v) := measurable_id.sub measurable_const
  simp only [instructionLaw]
  rw [Measure.map_smul, Measure.map_finset_sum' hmeas.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_add _ _ hmeas, Measure.map_dirac' hmeas, Measure.map_dirac' hmeas,
    show y + v + unit i - v = y + unit i by abel, show y + v - unit i - v = y - unit i by abel]

theorem measurable_shiftStack (v : Site d) : Measurable (shiftStack (d := d) v) := by
  show Measurable fun σ : Site d × ℕ → Site d => fun q : Site d × ℕ => σ (q.1 + v, q.2) - v
  exact measurable_pi_lambda _ fun q => (measurable_pi_apply (q.1 + v, q.2)).sub measurable_const

theorem measurable_shiftRank (v : Site d) : Measurable (shiftRank (d := d) v) := by
  show Measurable fun r : Label d × ℕ → ℝ => fun q : Label d × ℕ => r (shiftLabel v q.1, q.2)
  exact measurable_pi_lambda _ fun q => measurable_pi_apply (shiftLabel v q.1, q.2)

/-- The i.i.d. configuration law is translation invariant. -/
theorem iidLaw_map_shiftConf {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (v : Site d) :
    (iidLaw d ν).map (fun η : Site d → α => fun x => η (x + v))
      = iidLaw d ν :=
  (measurePreserving_coordShift (fun _ : Site d => ν)
    (g := fun x : Site d => x + v) (fun _ _ h => add_right_cancel h) fun _ => rfl).map_eq

/-- The stack law is translation invariant. -/
theorem stackLaw_map_shiftStack (hd : 1 ≤ d) (v : Site d) :
    (stackLaw d).map (shiftStack v) = stackLaw d := by
  haveI : ∀ y : Site d, IsProbabilityMeasure (instructionLaw y) := fun y =>
    instructionLaw_isProbability hd y
  have hinj : Function.Injective fun q : Site d × ℕ => (q.1 + v, q.2) := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (add_right_cancel h.1) h.2
  have h1 : (stackLaw d).map
      (fun σ : Site d × ℕ → Site d => fun q : Site d × ℕ => σ (q.1 + v, q.2))
      = Measure.infinitePi fun q : Site d × ℕ => instructionLaw (q.1 + v) :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun p : Site d × ℕ => instructionLaw p.1) hinj
  have hmeas : Measurable (fun z : Site d => z - v) := measurable_id.sub measurable_const
  have h2 : (Measure.infinitePi fun q : Site d × ℕ => instructionLaw (q.1 + v)).map
      (fun τ : Site d × ℕ → Site d => fun q : Site d × ℕ => τ q - v)
      = Measure.infinitePi fun q : Site d × ℕ =>
          (instructionLaw (q.1 + v)).map (fun z : Site d => z - v) :=
    Measure.infinitePi_map_pi _ (f := fun _ : Site d × ℕ => fun z : Site d => z - v)
      fun _ => hmeas
  have h3 : (Measure.infinitePi fun q : Site d × ℕ =>
      (instructionLaw (q.1 + v)).map (fun z : Site d => z - v)) = stackLaw d := by
    rw [stackLaw]
    congr 1
    funext q
    exact instructionLaw_map_sub v q.1
  have hcomp : shiftStack (d := d) v
      = (fun τ : Site d × ℕ → Site d => fun q : Site d × ℕ => τ q - v) ∘
        (fun σ : Site d × ℕ → Site d => fun q : Site d × ℕ => σ (q.1 + v, q.2)) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1, h2, h3]

/-- The law of the uniform variables is translation invariant. -/
theorem rankLaw_map_shiftRank (v : Site d) :
    (rankLaw d).map (shiftRank v) = rankLaw d := by
  haveI := uniformUnit_isProbability
  have hinj : Function.Injective fun q : Label d × ℕ => (shiftLabel v q.1, q.2) := by
    rintro ⟨p, i⟩ ⟨q, j⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (shiftLabel_injective v h.1) h.2
  exact (measurePreserving_coordShift
    (fun _ : Label d × ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)) hinj fun _ => rfl).map_eq


end LatticeProb

end
