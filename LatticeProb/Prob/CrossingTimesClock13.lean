/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.CrossingTimesClock9
import LatticeProb.Prob.CrossingTimesClock12

/-!
# The inverse crossing clock at a real time is determined by the path read in its clock

Under the hypotheses of `exists_measurable_pathClockInv_ratTime` (continuity of `K`, the Markov
property at deterministic times, the shift identity, attainment of the infimum defining `A_t`, and
almost sure continuity of `u ↦ A_u`), the variable `A_s` is almost surely a measurable function of
the rational-time restriction `B` of the path read in its crossing clock, for every real time
`s ≥ 0`, not only for rational `s`.

* `exists_rat_seq_gt`: rational times decreasing to a real time from above.
* `exists_measurable_pathClockInv`: `A_s = g (B)` almost surely, with `g` the limit superior of the
  rational-time functionals `g_j` for `A_{q_j}`, `q_j ↓ s`.
* `exists_clockFunctional_of_attained`: the single functional `F` of `exists_clockFunctional`, with
  the determination hypothesis replaced by the attainment and continuity hypotheses.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

/-- Every nonnegative real time is the limit of the nonnegative parts of rational numbers
strictly above it. -/
theorem exists_rat_seq_gt (s : ℝ≥0) :
    ∃ q : ℕ → ℚ, (∀ j, (s : ℝ) < q j) ∧ Tendsto (fun j => ratTime (q j)) atTop (𝓝 s) := by
  have hex : ∀ j : ℕ, ∃ r : ℚ, (s : ℝ) < r ∧ (r : ℝ) < s + 1 / ((j : ℝ) + 1) := fun j =>
    exists_rat_btwn (by
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith)
  choose q hq1 hq2 using hex
  refine ⟨q, hq1, ?_⟩
  have hreal : Tendsto (fun j => (q j : ℝ)) atTop (𝓝 (s : ℝ)) := by
    have h0 : Tendsto (fun j : ℕ => (s : ℝ) + 1 / ((j : ℝ) + 1)) atTop (𝓝 ((s : ℝ) + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
      (fun j => (hq1 j).le) (fun j => (hq2 j).le)
  have := (continuous_real_toNNReal.tendsto (s : ℝ)).comp hreal
  simpa [ratTime, Function.comp_def] using this

/-- **A continuous good clock attains its inverse.**  If `c` is a good clock that is continuous, the
infimum defining `clockInv c t` is attained: `t ≤ c (clockInv c t)`. -/
theorem attained_of_continuous_clock {c : ℝ≥0 → ℝ≥0∞} (hgood : GoodClock c) (hc : Continuous c)
    (t : ℝ≥0) : (t : ℝ≥0∞) ≤ c (clockInv c t).toNNReal := by
  obtain ⟨r, hr⟩ := hgood.2.2.2 ⌈t⌉₊
  have hne : ({u : ℝ≥0 | (t : ℝ≥0∞) ≤ c u}).Nonempty :=
    ⟨ratTime r, le_trans (by exact_mod_cast Nat.le_ceil t) hr⟩
  have hcl : IsClosed {u : ℝ≥0 | (t : ℝ≥0∞) ≤ c u} := isClosed_le continuous_const hc
  have hmem : sInf {u : ℝ≥0 | (t : ℝ≥0∞) ≤ c u} ∈ {u : ℝ≥0 | (t : ℝ≥0∞) ≤ c u} :=
    hcl.csInf_mem hne (OrderBot.bddBelow _)
  have heq : clockInv c t = ((sInf {u : ℝ≥0 | (t : ℝ≥0∞) ≤ c u} : ℝ≥0) : ℝ≥0∞) := by
    unfold clockInv
    apply le_antisymm
    · exact iInf₂_le _ hmem
    · exact le_iInf₂ fun u hu => ENNReal.coe_le_coe.2 (csInf_le (OrderBot.bddBelow _) hu)
  rw [heq, ENNReal.toNNReal_coe]
  exact hmem

section

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

omit [SecondCountableTopology E] in
/-- **The inverse crossing clock at a real time.**  Under the hypotheses of
`exists_measurable_pathClockInv_ratTime`, for every real `s ≥ 0` the variable `A_s` is almost
surely a measurable function of the rational-time restriction of the path read in its crossing
clock. -/
theorem exists_measurable_pathClockInv [PolishSpace E]
    {K : E → ProbabilityMeasure C(ℝ≥0, E)} (hK : Continuous K) {z : E}
    (hM : ∀ t, MarkovAt K z t) (m : ℝ≥0∞)
    (hshift : ∀ t s : ℝ≥0, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), ShiftIdentity m t s x)
    (hatt : ∀ t : ℝ≥0, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
      (t : ℝ≥0∞) ≤ crossClock m (fun w => x w) (pathClockInv m x t).toNNReal)
    (hcont : ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
      Continuous fun u : ℝ≥0 => (pathClockInv m x u).toReal)
    (s : ℝ≥0) :
    ∃ g : (ℚ → E) → ℝ, Measurable g ∧ ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
      (pathClockInv m x s).toReal = g (ratPath fun t => clockPath m (fun u => x u) t) := by
  obtain ⟨q, -, hqlim⟩ := exists_rat_seq_gt s
  choose g hgm hg using fun j =>
    exists_measurable_pathClockInv_ratTime hK hM m hshift hatt hcont (q j)
  refine ⟨fun b => (limsup (fun j => ENNReal.ofReal (g j b)) atTop).toReal, ?_, ?_⟩
  · exact (Measurable.limsup fun j => (hgm j).ennreal_ofReal).ennreal_toReal
  · have hall := ae_all_iff.2 hg
    filter_upwards [hall, hcont] with x hx hc
    have hlim : Tendsto
        (fun j => g j (ratPath fun t => clockPath m (fun u => x u) t)) atTop
        (𝓝 (pathClockInv m x s).toReal) :=
      ((hc.tendsto s).comp hqlim).congr fun j => hx j
    have h2 := ENNReal.tendsto_ofReal hlim
    rw [h2.limsup_eq, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

omit [SecondCountableTopology E] in
/-- **One functional determines the inverse crossing clock (attainment form).**  The conclusion of
`exists_clockFunctional`, with the determination hypothesis `hdet` replaced by attainment of the
infimum defining `A_t` and almost sure continuity of `u ↦ A_u` under every start. -/
theorem exists_clockFunctional_of_attained [PolishSpace E]
    {K : E → ProbabilityMeasure C(ℝ≥0, E)} (hK : Continuous K)
    (hM : ∀ z t, MarkovAt K z t) (m : ℝ≥0∞)
    (hstart : ∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), x 0 = z)
    (hgood : ∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), GoodClock (crossClock m fun u => x u))
    (hshift : ∀ z (t s : ℝ≥0), ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), ShiftIdentity m t s x)
    (hatt : ∀ z (t : ℝ≥0), ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
      (t : ℝ≥0∞) ≤ crossClock m (fun w => x w) (pathClockInv m x t).toNNReal)
    (hcont : ∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
      Continuous fun u : ℝ≥0 => (pathClockInv m x u).toReal)
    (s : ℝ≥0) :
    ∃ F : (ℝ≥0 → E) → ℝ, Measurable F ∧
      (∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
        (pathClockInv m x s).toReal = F fun t => clockPath m (fun u => x u) t) ∧
      ∀ z (t : ℝ≥0), ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
        (pathClockInv m x (t + s)).toReal = (pathClockInv m x t).toReal +
          F fun q => clockPath m (fun u => x u) (t + q) :=
  exists_clockFunctional hK hM m hstart hgood hshift s fun z =>
    exists_measurable_pathClockInv hK (hM z) m (hshift z) (hatt z) (hcont z) s

end

end LatticeProb
