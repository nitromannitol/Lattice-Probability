import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Half-line càdlàg paths and the Ethier–Kurtz Skorokhod distance

Càdlàg paths on `[0,∞)` with values in a metric space, the time changes `Λ′` and `Λ` of
Ethier–Kurtz, *Markov Processes* (1986), Section 3.5, the logarithmic distortion `γ` of (5.1),
the stopped discrepancy (5.3) and the distance (5.2), with its bound by one.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal

noncomputable section

/-- The half-line time domain, with its usual metric and order. -/
abbrev Time := ℝ≥0

/-- Right continuity and genuine left limits at every positive half-line time. -/
def IsCadlag {E : Type*} [TopologicalSpace E] (x : Time → E) : Prop :=
  (∀ t, ContinuousWithinAt x (Ici t) t) ∧
  (∀ t, 0 < t → ∃ l : E, Tendsto x (𝓝[<] t) (𝓝 l))

/-- The actual half-line path carrier, before choosing its topology. -/
def D (E : Type*) [TopologicalSpace E] := {x : Time → E // IsCadlag x}

/-- A constant half-line path witnesses nonemptiness whenever the state space is inhabited. -/
def const {E : Type*} [TopologicalSpace E] (a : E) : D E :=
  ⟨fun _ => a, fun _ => continuousWithinAt_const,
    fun _ _ => ⟨a, tendsto_const_nhds⟩⟩

/-- EK's Lambda-prime: strictly increasing onto half-line time changes. -/
abbrev LambdaPrime := Time ≃o Time

/-- The logarithmic secant-slope formula in EK (5.1), allowing infinity. -/
def gamma (l : LambdaPrime) : ℝ≥0∞ :=
  ⨆ (s : Time) (t : Time) (_ : t < s),
    ENNReal.ofReal |Real.log (((l s : ℝ) - l t) / ((s : ℝ) - t))|

/-- EK's Lipschitz time changes with finite logarithmic distortion. -/
def Lambda := {l : LambdaPrime // (∃ K : ℝ≥0, LipschitzWith K l) ∧ gamma l < ∞}

/-- Identity has zero logarithmic distortion, with no empty-supremum convention in ℝ. -/
theorem gamma_identity : gamma (OrderIso.refl Time) = 0 := by
  apply le_antisymm _ bot_le
  unfold gamma
  apply iSup_le
  intro s
  apply iSup_le
  intro t
  apply iSup_le
  intro h
  have hne : (s : ℝ) - t ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  simp only [OrderIso.refl_apply, div_self hne, Real.log_one, abs_zero,
    ENNReal.ofReal_zero]
  exact le_rfl

/-- Identity is an admissible time change, so the infimum domain is inhabited. -/
def identityChange : Lambda :=
  ⟨OrderIso.refl Time, ⟨⟨1, LipschitzWith.id⟩, by
    rw [gamma_identity]; exact ENNReal.zero_lt_top⟩⟩

/-- The bounded state metric q = r wedge 1, in extended nonnegative form. -/
def q {E : Type*} [MetricSpace E] (a b : E) : ℝ≥0∞ := min (edist a b) 1

/-- EK (5.3); both paths stop at u, after applying the time change to the second. -/
def discrepancy {E : Type*} [MetricSpace E] (x y : D E)
    (l : LambdaPrime) (u : Time) : ℝ≥0∞ :=
  ⨆ t : Time, q (x.1 (min t u)) (y.1 (min (l t) u))

/-- Every stopped discrepancy is bounded by one. -/
theorem discrepancy_le_one {E : Type*} [MetricSpace E] (x y : D E)
    (l : LambdaPrime) (u : Time) : discrepancy x y l u ≤ 1 := by
  exact iSup_le fun _ => min_le_right _ _

/-- EK's exponentially weighted integral, written as a nonnegative Lebesgue integral. -/
def integratedDiscrepancy {E : Type*} [MetricSpace E] (x y : D E)
    (l : LambdaPrime) : ℝ≥0∞ :=
  ∫⁻ u : ℝ in Ioi 0,
    ENNReal.ofReal (Real.exp (-u)) * discrepancy x y l u.toNNReal

/-- The exponential weight has mass one on the positive half-line. -/
theorem exponential_mass :
    (∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-u))) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
    (Filter.Eventually.of_forall fun u => (Real.exp_pos (-u)).le)]
  rw [integral_exp_neg_Ioi_zero, ENNReal.ofReal_one]

/-- The integral is finite without any conversion of infinity to a real zero. -/
theorem integratedDiscrepancy_le_one {E : Type*} [MetricSpace E] (x y : D E)
    (l : LambdaPrime) : integratedDiscrepancy x y l ≤ 1 := by
  calc
    integratedDiscrepancy x y l ≤
        ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-u)) := by
      apply lintegral_mono
      intro u
      exact (mul_le_mul_right (discrepancy_le_one x y l u.toNNReal) _).trans_eq
        (mul_one _)
    _ = 1 := exponential_mass

/-- EK (5.2), initially in the complete lattice of extended nonnegative reals. -/
def skorohodDistanceExtended {E : Type*} [MetricSpace E] (x y : D E) : ℝ≥0∞ :=
  ⨅ l : Lambda, max (gamma l.1) (integratedDiscrepancy x y l.1)

/-- The identity time change proves finiteness of the actual infimum. -/
theorem skorohodDistanceExtended_le_one {E : Type*} [MetricSpace E] (x y : D E) :
    skorohodDistanceExtended x y ≤ 1 := by
  calc
    skorohodDistanceExtended x y ≤
        max (gamma identityChange.1) (integratedDiscrepancy x y identityChange.1) :=
      iInf_le _ identityChange
    _ ≤ 1 := by
      apply max_le
      · change gamma (OrderIso.refl Time) ≤ 1
        rw [gamma_identity]
        exact zero_le_one
      · exact integratedDiscrepancy_le_one x y _

/-- The real-valued EK distance; the preceding bound excludes infinity. -/
def skorohodDistance {E : Type*} [MetricSpace E] (x y : D E) : ℝ :=
  (skorohodDistanceExtended x y).toReal

/-- At an actual constant path the stopped discrepancy vanishes. -/
theorem discrepancy_const {E : Type*} [MetricSpace E] (a : E)
    (l : LambdaPrime) (u : Time) : discrepancy (const a) (const a) l u = 0 := by
  simp only [discrepancy, const, q, edist_self,
    min_eq_left (show (0 : ℝ≥0∞) ≤ 1 from zero_le_one),
    ENNReal.iSup_zero]

/-- The distance vanishes at every actual constant path. -/
theorem skorohodDistance_const {E : Type*} [MetricSpace E] (a : E) :
    skorohodDistance (const a) (const a) = 0 := by
  have h : skorohodDistanceExtended (const a) (const a) = 0 := by
    apply le_antisymm _ bot_le
    exact (iInf_le _ identityChange).trans (by
      simp only [identityChange, gamma_identity, integratedDiscrepancy,
        discrepancy_const, mul_zero, lintegral_zero, max_self]
      exact le_rfl)
  rw [skorohodDistance, h, ENNReal.toReal_zero]

/-- Distinct constant paths retain their genuine bounded state distance. -/
theorem skorohodDistanceExtended_const_pair {E : Type*} [MetricSpace E] (a b : E) :
    skorohodDistanceExtended (const a) (const b) = q a b := by
  have hi (l : LambdaPrime) : integratedDiscrepancy (const a) (const b) l = q a b := by
    have hq : q a b ≠ ∞ := ne_of_lt ((min_le_right _ _).trans_lt ENNReal.one_lt_top)
    simp only [integratedDiscrepancy, discrepancy, const, iSup_const]
    rw [lintegral_mul_const' _ _ hq, exponential_mass, one_mul]
  apply le_antisymm
  · exact (iInf_le _ identityChange).trans_eq (by
      rw [hi]
      change max (gamma (OrderIso.refl Time)) (q a b) = q a b
      rw [gamma_identity, max_eq_right (show (0 : ℝ≥0∞) ≤ q a b from zero_le)])
  · apply le_iInf
    intro l
    rw [hi]
    exact le_max_right _ _

/-- An actual Euclidean-valued half-line path, with the Euclidean norm unchanged. -/
def euclideanZero (d : ℕ) : D (EuclideanSpace ℝ (Fin d)) := const 0

end

end LatticeProb.Cadlag.HalfLine
