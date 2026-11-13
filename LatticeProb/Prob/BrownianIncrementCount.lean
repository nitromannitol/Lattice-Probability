import Mathlib.Probability.BrownianMotion.Basic
import LatticeProb.Prob.BoundedIncrementMaximal

/-!
# Large increments of a Brownian motion on a time grid

Let `Y` be a real Brownian motion, `s > 0` a window length and `c > 0`.  The increments
`Y ((j + 1) s) - Y (j s)` over the grid windows `[j s, (j + 1) s]` are independent and centred
Gaussian with variance `s`, so the events `c √s ≤ |Y ((j + 1) s) - Y (j s)|` are independent, each of
probability `q = gaussTail c` (the two-sided tail `ℙ[|Z| ≥ c]` of a standard Gaussian), which does
not depend on `s`.  By Hoeffding's maximal bound for the centred indicators `q - 1_{A_j}`, the
number of such windows among the first `m` is below `K ≤ m q / 2` with probability at most
`2 exp (-(m q² / 8))` (`measure_card_bigIncrement_lt_le`).
-/

open MeasureTheory ProbabilityTheory Set

open scoped NNReal ENNReal

namespace LatticeProb

/-- The two-sided tail `ℙ[|Z| ≥ c]` of a standard Gaussian variable. -/
noncomputable def gaussTail (c : ℝ) : ℝ := (gaussianReal 0 1).real {x : ℝ | c ≤ |x|}

lemma gaussTail_nonneg (c : ℝ) : 0 ≤ gaussTail c := measureReal_nonneg

lemma gaussTail_le_one (c : ℝ) : gaussTail c ≤ 1 := measureReal_le_one

/-- The two-sided Gaussian tail is positive at every level. -/
lemma gaussTail_pos (c : ℝ) : 0 < gaussTail c := by
  unfold gaussTail
  have h1 : (gaussianReal 0 1) (Ici c) ≠ 0 := by
    intro h0
    have h2 := (gaussianReal_absolutelyContinuous' 0 (one_ne_zero)) h0
    simp at h2
  have h2 : (gaussianReal 0 1) (Ici c) ≤ (gaussianReal 0 1) {x : ℝ | c ≤ |x|} :=
    measure_mono fun x hx => le_trans hx (le_abs_self x)
  exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 h1) h2))
    (measure_ne_top _ _)

/-- A centred Gaussian of variance `s` is `√s` times a standard Gaussian. -/
lemma gaussianReal_map_sqrt_mul (s : ℝ≥0) :
    (gaussianReal 0 1).map (fun x => Real.sqrt s * x) = gaussianReal 0 s := by
  have h := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt s)
  rw [h]
  congr 1
  · simp
  · ext
    simp

/-- **Scaling of the two-sided Gaussian tail.** -/
lemma gaussianReal_tail_scale {s : ℝ≥0} (hs : 0 < s) (c : ℝ) :
    (gaussianReal 0 s) {x : ℝ | c * Real.sqrt s ≤ |x|} = gaussianReal 0 1 {x : ℝ | c ≤ |x|} := by
  have hpos : 0 < Real.sqrt s := Real.sqrt_pos.2 (by exact_mod_cast hs)
  rw [← gaussianReal_map_sqrt_mul s,
    Measure.map_apply (by fun_prop : Measurable fun x : ℝ => Real.sqrt s * x)
      (measurableSet_le measurable_const continuous_abs.measurable)]
  congr 1
  ext x
  simp only [mem_preimage, Set.mem_ofPred_eq, abs_mul, abs_of_pos hpos]
  rw [mul_comm c]
  exact mul_le_mul_iff_of_pos_left hpos


variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The increment of a Brownian motion over the grid window `[j s, (j + 1) s]` is centred Gaussian
of variance `s`. -/
lemma hasLaw_gridIncrement {Y : ℝ≥0 → Ω → ℝ} (hY : IsPreBrownianReal Y P)
    (s : ℝ≥0) (j : ℕ) :
    HasLaw (fun ω => Y (((j + 1 : ℕ) : ℝ≥0) * s) ω - Y ((j : ℝ≥0) * s) ω)
      (gaussianReal 0 s) P := by
  have h := hY.hasLaw_sub (((j + 1 : ℕ) : ℝ≥0) * s) ((j : ℝ≥0) * s)
  have hn : nndist (((j + 1 : ℕ) : ℝ≥0) * s : ℝ≥0).1 (((j : ℝ≥0) * s : ℝ≥0)).1 = s := by
    apply NNReal.eq
    rw [coe_nndist, Real.dist_eq]
    simp only [NNReal.val_eq_coe]
    push_cast
    have e : ((j : ℝ) + 1) * (s : ℝ) - (j : ℝ) * (s : ℝ) = (s : ℝ) := by ring
    rw [e, abs_of_nonneg (NNReal.coe_nonneg s)]
  rw [hn] at h
  exact h

open Classical in
/-- **Few large increments on a grid.**  Let `Y` be a real Brownian motion on a probability space,
`s > 0`, `c ∈ ℝ`, and let `q = gaussTail c`.  If `K ≤ m q / 2`, the probability that fewer than `K`
of the first `m` grid windows `[j s, (j + 1) s]` have increment of absolute value at least
`c √s` is at most `2 exp (-(m q² / 8))`. -/
theorem measure_card_bigIncrement_lt_le [IsProbabilityMeasure P] {Y : ℝ≥0 → Ω → ℝ}
    (hY : IsPreBrownianReal Y P) {s : ℝ≥0} (hs : 0 < s) (c : ℝ) (m K : ℕ) (hm : 0 < m)
    (hK : (K : ℝ) ≤ m * gaussTail c / 2) :
    P {ω | ((Finset.range m).filter (fun j : ℕ =>
        c * Real.sqrt s ≤ |Y (((j + 1 : ℕ) : ℝ≥0) * s) ω - Y ((j : ℝ≥0) * s) ω|)).card < K}
      ≤ ENNReal.ofReal (2 * Real.exp (-(m * gaussTail c ^ 2 / 8))) := by
  set q := gaussTail c with hq
  have hq0 : 0 < q := gaussTail_pos c
  have hq1 : q ≤ 1 := gaussTail_le_one c
  set Δ : ℕ → Ω → ℝ := fun j ω => Y (((j + 1 : ℕ) : ℝ≥0) * s) ω - Y ((j : ℝ≥0) * s) ω with hΔ
  have hmono : Monotone (fun j : ℕ => (j : ℝ≥0) * s) := fun a b hab => by
    have : (a : ℝ≥0) ≤ b := Nat.cast_le.2 hab
    show (a : ℝ≥0) * s ≤ (b : ℝ≥0) * s
    gcongr
  have hind : iIndepFun Δ P := hY.hasIndepIncrements.nat hmono
  have hlaw : ∀ j, HasLaw (Δ j) (gaussianReal 0 s) P := fun j => hasLaw_gridIncrement hY s j
  have hΔm : ∀ j, AEMeasurable (Δ j) P := fun j => (hlaw j).aemeasurable
  set Δ' : ℕ → Ω → ℝ := fun j => (hΔm j).mk (Δ j) with hΔ'
  have hΔ'm : ∀ j, Measurable (Δ' j) := fun j => (hΔm j).measurable_mk
  have hae : ∀ j, Δ j =ᵐ[P] Δ' j := fun j => (hΔm j).ae_eq_mk
  have hind' : iIndepFun Δ' P := hind.congr hae
  set g : ℝ → ℝ := fun x => q - (if c * Real.sqrt s ≤ |x| then (1 : ℝ) else 0) with hg
  have hgm : Measurable g :=
    measurable_const.sub (Measurable.ite (measurableSet_le measurable_const
      continuous_abs.measurable) measurable_const measurable_const)
  set ξ : ℕ → Ω → ℝ := fun j ω => g (Δ' j ω) with hξ
  have hξind : iIndepFun ξ P := hind'.comp (fun _ => g) (fun _ => hgm)
  have hξmeas : ∀ j, Measurable (ξ j) := fun j => hgm.comp (hΔ'm j)
  have hξb : ∀ j, ∀ᵐ ω ∂P, |ξ j ω| ≤ ((1 : ℝ≥0) : ℝ) := by
    intro j
    refine Filter.Eventually.of_forall fun ω => ?_
    simp only [hξ, hg, NNReal.coe_one]
    split_ifs
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
  have hprob : ∀ j, P.real {ω | c * Real.sqrt s ≤ |Δ' j ω|} = q := by
    intro j
    have hS : MeasurableSet {x : ℝ | c * Real.sqrt s ≤ |x|} :=
      measurableSet_le measurable_const continuous_abs.measurable
    have h1 : P {ω | c * Real.sqrt s ≤ |Δ' j ω|} = P {ω | c * Real.sqrt s ≤ |Δ j ω|} := by
      refine measure_congr ?_
      filter_upwards [hae j] with ω hω
      simp [hω]
    have h2 : P {ω | c * Real.sqrt s ≤ |Δ j ω|} =
        (gaussianReal 0 s) {x : ℝ | c * Real.sqrt s ≤ |x|} := by
      rw [← (hlaw j).map_eq, Measure.map_apply_of_aemeasurable (hlaw j).aemeasurable hS]
      rfl
    rw [measureReal_def, h1, h2, gaussianReal_tail_scale hs c]
    rfl
  have h0 : ∀ j, ∫ ω, ξ j ω ∂P = 0 := by
    intro j
    have hS : MeasurableSet {ω | c * Real.sqrt s ≤ |Δ' j ω|} :=
      measurableSet_le measurable_const (continuous_abs.measurable.comp (hΔ'm j))
    have e : (fun ω => ξ j ω) = fun ω =>
        q - Set.indicator {ω | c * Real.sqrt s ≤ |Δ' j ω|} (fun _ => (1 : ℝ)) ω := by
      funext ω
      simp [hξ, hg, Set.indicator_apply]
    rw [e, integral_sub (integrable_const q) ((integrable_const (1 : ℝ)).indicator hS)]
    rw [integral_indicator_const (1 : ℝ) hS]
    simp [hprob j]
  have hH := measure_exists_abs_partialSum_ge_le (P := P) ξ hξind hξmeas (r := 1) hξb h0 m hm
    (n := m * q / 2) (by positivity)
  have hexp : -((m * q / 2) ^ 2) / (2 * m * ((1 : ℝ≥0) : ℝ) ^ 2) = -(m * q ^ 2 / 8) := by
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [NNReal.coe_one]
    field_simp
    ring
  rw [hexp] at hH
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | ((Finset.range m).filter (fun j : ℕ =>
        c * Real.sqrt s ≤ |Y (((j + 1 : ℕ) : ℝ≥0) * s) ω - Y ((j : ℝ≥0) * s) ω|)).card < K} →
      ω ∈ {ω | ∃ k ≤ m, m * q / 2 ≤ |∑ i ∈ Finset.range k, ξ i ω|} := by
    filter_upwards [ae_all_iff.2 hae] with ω hω hbad
    refine ⟨m, le_refl m, ?_⟩
    have hcard : (((Finset.range m).filter (fun j : ℕ =>
        c * Real.sqrt s ≤ |Δ' j ω|)).card : ℝ) < K := by
      have : ((Finset.range m).filter (fun j : ℕ =>
          c * Real.sqrt s ≤ |Y (((j + 1 : ℕ) : ℝ≥0) * s) ω - Y ((j : ℝ≥0) * s) ω|)) =
          (Finset.range m).filter (fun j : ℕ => c * Real.sqrt s ≤ |Δ' j ω|) := by
        refine Finset.filter_congr fun j _ => ?_
        have := hω j
        simp only [hΔ] at this
        rw [← this]
      rw [← this]
      exact_mod_cast hbad
    have hsum : ∑ i ∈ Finset.range m, ξ i ω =
        m * q - ((Finset.range m).filter (fun j : ℕ => c * Real.sqrt s ≤ |Δ' j ω|)).card := by
      simp only [hξ, hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, Finset.sum_boole]
    rw [hsum]
    refine le_trans ?_ (le_abs_self _)
    linarith
  calc P {ω | ((Finset.range m).filter (fun j : ℕ =>
        c * Real.sqrt s ≤ |Y (((j + 1 : ℕ) : ℝ≥0) * s) ω - Y ((j : ℝ≥0) * s) ω|)).card < K}
      ≤ P {ω | ∃ k ≤ m, m * q / 2 ≤ |∑ i ∈ Finset.range k, ξ i ω|} := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(m * q ^ 2 / 8))) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
        exact ENNReal.ofReal_le_ofReal hH

end LatticeProb
