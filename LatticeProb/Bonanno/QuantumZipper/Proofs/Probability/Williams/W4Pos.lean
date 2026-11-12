/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W4Pos at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.OccupationHit2

/-!
# W4 (part 1): measurable surrogates for path events

Preparation for node W4 (`lintegral_shift_postLast`) of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1).
The events `∀ t ≤ r, 0 < w t` and `∃ t, w t = 0` are not measurable for the product σ-algebra on
`ℝ≥0 → ℝ`, but on continuous paths they agree with the countably described sets `posSet r`,
`posAllSet`, `zeroSet` below, which are measurable. Own elementary proofs (density of `ℚ` and the
extreme value theorem on `[0, r]`).
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

/-- Countable description of `∀ t ≤ r, 0 < w t` (for continuous `w`). -/
def posSet (r : ℝ≥0) : Set (ℝ≥0 → ℝ) :=
  ⋃ n : ℕ, ⋂ q : ℚ, {w | ((n : ℝ) + 1)⁻¹ ≤ w (min (Real.toNNReal q) r)}

/-- Countable description of `∀ t, 0 < w t` (for continuous `w`). -/
def posAllSet : Set (ℝ≥0 → ℝ) := ⋂ k : ℕ, posSet k

/-- Countable description of `∃ t, w t = 0` (for continuous `w`). -/
def zeroSet : Set (ℝ≥0 → ℝ) :=
  ⋃ k : ℕ, ⋂ j : ℕ, ⋃ q : ℚ, {w | |w (min (Real.toNNReal q) k)| < ((j : ℝ) + 1)⁻¹}

theorem measurableSet_posSet (r : ℝ≥0) : MeasurableSet (posSet r) :=
  MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun _ =>
    measurableSet_le measurable_const (measurable_pi_apply _)

theorem measurableSet_posAllSet : MeasurableSet posAllSet :=
  MeasurableSet.iInter fun _ => measurableSet_posSet _

theorem measurableSet_zeroSet : MeasurableSet zeroSet :=
  MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun _ =>
    measurableSet_lt (continuous_abs.measurable.comp (measurable_pi_apply (X := fun _ : ℝ≥0 => ℝ) _)) measurable_const

/-- Rational approximation of a point of `[0, k]` by points `min q k`. -/
theorem exists_rat_near {w : ℝ≥0 → ℝ} (hw : Continuous w) {k t : ℝ≥0} (ht : t ≤ k) {ε : ℝ}
    (hε : 0 < ε) : ∃ q : ℚ, |w (min (Real.toNNReal q) k) - w t| < ε := by
  have hφ : Continuous fun x : ℝ => w (min (Real.toNNReal x) k) :=
    hw.comp (continuous_real_toNNReal.min continuous_const)
  have hφt : (fun x : ℝ => w (min (Real.toNNReal x) k)) (t : ℝ) = w t := by
    simp [Real.toNNReal_coe, min_eq_left ht]
  have hopen : IsOpen ((fun x : ℝ => w (min (Real.toNNReal x) k)) ⁻¹' Metric.ball (w t) ε) :=
    Metric.isOpen_ball.preimage hφ
  have hne : ((fun x : ℝ => w (min (Real.toNNReal x) k)) ⁻¹' Metric.ball (w t) ε).Nonempty :=
    ⟨t, by simp only [mem_preimage, Real.toNNReal_coe, min_eq_left ht]; exact Metric.mem_ball_self hε⟩
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hopen hne
  refine ⟨q, ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using hq

theorem mem_posSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (r : ℝ≥0) :
    w ∈ posSet r ↔ ∀ t ≤ r, 0 < w t := by
  constructor
  · intro h t ht
    obtain ⟨n, hn⟩ := mem_iUnion.1 h
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    obtain ⟨q, hq⟩ := exists_rat_near hw ht hpos
    have h1 := mem_iInter.1 hn q
    simp only [mem_setOf_eq] at h1
    have := (abs_lt.1 hq).2
    linarith
  · intro h
    obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := r)).exists_isMinOn
      (nonempty_Icc.2 zero_le) hw.continuousOn
    have hm : 0 < w t0 := h t0 ht0.2
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hm
    refine mem_iUnion.2 ⟨n, mem_iInter.2 fun q => ?_⟩
    simp only [mem_setOf_eq]
    have h2 : w t0 ≤ w (min (Real.toNNReal q) r) :=
      hmin ⟨zero_le, min_le_right _ _⟩
    rw [one_div] at hn
    linarith

theorem mem_posAllSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) :
    w ∈ posAllSet ↔ ∀ t, 0 < w t := by
  simp only [posAllSet, mem_iInter, mem_posSet_iff hw]
  constructor
  · intro h t
    obtain ⟨k, hk⟩ := exists_nat_ge (t : ℝ)
    exact h k t (by exact_mod_cast hk)
  · intro h k t _
    exact h t

theorem mem_zeroSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) :
    w ∈ zeroSet ↔ ∃ t, w t = 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := mem_iUnion.1 h
    obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (k : ℝ≥0))).exists_isMinOn
      (nonempty_Icc.2 zero_le) hw.abs.continuousOn
    refine ⟨t0, abs_eq_zero.1 (le_antisymm ?_ (abs_nonneg _))⟩
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    obtain ⟨q, hq⟩ := mem_iUnion.1 (mem_iInter.1 hk j)
    simp only [mem_setOf_eq] at hq
    have h2 : |w t0| ≤ |w (min (Real.toNNReal q) (k : ℝ≥0))| :=
      hmin ⟨zero_le, min_le_right _ _⟩
    rw [one_div] at hj
    linarith
  · rintro ⟨t, ht⟩
    obtain ⟨k, hk⟩ := exists_nat_ge (t : ℝ)
    refine mem_iUnion.2 ⟨k, mem_iInter.2 fun j => ?_⟩
    have hpos : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
    obtain ⟨q, hq⟩ := exists_rat_near hw (show t ≤ (k : ℝ≥0) by exact_mod_cast hk) hpos
    refine mem_iUnion.2 ⟨q, ?_⟩
    simp only [mem_setOf_eq]
    rwa [ht, sub_zero] at hq

end QuantumZipper.Williams
