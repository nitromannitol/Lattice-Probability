import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Finite-family stretched-exponential bounds

Exponential moment estimates imply pointwise stretched-exponential tails.
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- An exponential moment bounded by two controls the upper tail. -/
theorem measure_ge_le_of_exp_rpow_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (a s : ℝ)
    (ha : 0 < a) (hs : 0 < s)
    (hint : Integrable (fun ω => Real.exp ((X ω / a) ^ s)) μ)
    (hmom : (∫ ω, Real.exp ((X ω / a) ^ s) ∂μ) ≤ 2) {r : ℝ} (hr : 0 ≤ r) :
    μ {ω | r ≤ X ω} ≤ ENNReal.ofReal (2 * Real.exp (-((r / a) ^ s))) := by
  have hsub : {ω | r ≤ X ω} ⊆
      {ω | Real.exp ((r / a) ^ s) ≤ Real.exp ((X ω / a) ^ s)} := by
    intro ω hω
    apply Real.exp_le_exp.mpr
    exact Real.rpow_le_rpow (div_nonneg hr ha.le)
      (div_le_div_of_nonneg_right hω ha.le) hs.le
  have hpos : 0 < Real.exp ((r / a) ^ s) := Real.exp_pos _
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (ae_of_all μ fun ω => (Real.exp_pos ((X ω / a) ^ s)).le) hint
    (Real.exp ((r / a) ^ s))
  have hmeasure : μ.real {ω | r ≤ X ω} ≤ 2 * Real.exp (-((r / a) ^ s)) := by
    rw [Real.exp_neg, le_mul_inv_iff₀ hpos]
    calc
      μ.real {ω | r ≤ X ω} * Real.exp ((r / a) ^ s) ≤
          Real.exp ((r / a) ^ s) *
            μ.real {ω | Real.exp ((r / a) ^ s) ≤ Real.exp ((X ω / a) ^ s)} := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (measureReal_mono hsub (measure_ne_top _ _)) hpos.le
      _ ≤ ∫ ω, Real.exp ((X ω / a) ^ s) ∂μ := hmark
      _ ≤ 2 := hmom
  have h := ENNReal.ofReal_le_ofReal hmeasure
  rwa [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h

/-- The actual maximum of a nonempty finite family of real random variables. -/
noncomputable def finiteFieldMax {Ω : Type*} {n : ℕ} (T : Fin (n + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => T i ω)

/-- The finite maximum of measurable fields is measurable. -/
theorem measurable_finiteFieldMax {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (T : Fin (n + 1) → Ω → ℝ) (hT : ∀ i, Measurable (T i)) :
    Measurable (finiteFieldMax T) := by
  change Measurable (fun ω => Finset.univ.sup' Finset.univ_nonempty (fun i => T i ω))
  simp_rw [Finset.sup'_univ_eq_ciSup]
  exact Measurable.iSup hT

/-- A deterministic threshold for a finite maximum is covered by the coordinate events. -/
theorem measure_finiteFieldMax_ge_le {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (T : Fin (n + 1) → Ω → ℝ) (r : ℝ) :
    μ {ω | r ≤ finiteFieldMax T ω} ≤ ∑ i : Fin (n + 1), μ {ω | r ≤ T i ω} := by
  classical
  calc
    _ ≤ μ (⋃ i : Fin (n + 1), {ω | r ≤ T i ω}) := by
      apply measure_mono
      intro ω hω
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => T i ω)
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      change r ≤ T i ω
      change r ≤ finiteFieldMax T ω at hω
      change r ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => T i ω) at hω
      rw [hi] at hω
      exact hω
    _ ≤ _ := measure_iUnion_fintype_le μ _

/-- Above the deterministic floor, the maximum tail is covered by its coordinate tails. -/
theorem measure_ge_max_le {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Ω → ℝ) (T : Fin (n + 1) → Ω → ℝ)
    (B r : ℝ) (hr : B < r) :
    μ {ω | r ≤ max B (max (X ω) (2 * finiteFieldMax T ω))} ≤
      μ {ω | r ≤ X ω} + ∑ i : Fin (n + 1), μ {ω | r / 2 ≤ T i ω} := by
  have hsub : {ω | r ≤ max B (max (X ω) (2 * finiteFieldMax T ω))} ⊆
      {ω | r ≤ X ω} ∪ {ω | r / 2 ≤ finiteFieldMax T ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases (le_max_iff.mp hω) with h | h
    · exact (not_le_of_gt hr h).elim
    · rcases le_max_iff.mp h with h | h
      · exact Or.inl h
      · right
        linarith
  calc
    _ ≤ μ ({ω | r ≤ X ω} ∪ {ω | r / 2 ≤ finiteFieldMax T ω}) := measure_mono hsub
    _ ≤ μ {ω | r ≤ X ω} + μ {ω | r / 2 ≤ finiteFieldMax T ω} := measure_union_le _ _
    _ ≤ _ := add_le_add (le_refl _) (measure_finiteFieldMax_ge_le μ T (r / 2))

/-- A finite maximum of a bounded term, a moment-controlled field, and tail-controlled
variables has a uniform stretched-exponential tail with exponent `min s t`. -/
theorem finite_max_stretched_exp_tail {J : Type*} (n : ℕ) (B a s b t : ℝ)
    (_hB : 0 ≤ B) (ha : 0 < a) (hs : 0 < s) (hb : 0 < b) (ht : 0 < t) :
    ∃ A : ℝ, 0 < A ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (X : J → Ω → ℝ)
      (T : Fin (n + 1) → Ω → ℝ),
      (∀ j, Measurable (X j)) → (∀ j ω, 0 ≤ X j ω) →
      (∀ j, Integrable (fun ω => Real.exp ((X j ω / a) ^ s)) μ) →
      (∀ j, (∫ ω, Real.exp ((X j ω / a) ^ s) ∂μ) ≤ 2) →
      (∀ i, Measurable (T i)) → (∀ i ω, 0 ≤ T i ω) →
      (∀ i r, 0 < r → μ {ω | r ≤ T i ω} ≤
        ENNReal.ofReal (b * Real.exp (-(r ^ t) / b))) →
      ∀ j r, 0 < r → μ {ω | r ≤ max B (max (X j ω) (2 * finiteFieldMax T ω))} ≤
        ENNReal.ofReal (A * Real.exp (-(r ^ (min s t)) / A)) := by
  let u := min s t
  let D := max (a ^ s) (b * (2 : ℝ) ^ t)
  let K := 2 + (n + 1 : ℝ) * b
  let R := max B 1
  let A := max 2 (max K (max D (1 + R ^ u)))
  have hu : 0 < u := lt_min hs ht
  have hA : 0 < A := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  have hAK : K ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hAD : D ≤ A := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hAR : 1 + R ^ u ≤ A := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨A, hA, ?_⟩
  intro Ω _ μ _ X T _hXm _hXn hXi hXb _hTm _hTn htail j r hr
  by_cases hsmall : r ≤ R
  · have hrpow : r ^ u ≤ R ^ u := Real.rpow_le_rpow hr.le hsmall hu.le
    have hexp := Real.add_one_le_exp (-(r ^ u) / A)
    have hbound : 1 ≤ A * Real.exp (-(r ^ u) / A) := by
      have hm := mul_le_mul_of_nonneg_left hexp hA.le
      field_simp at hm
      calc
        1 ≤ A - R ^ u := (le_sub_iff_add_le).2 (by simpa only [add_comm] using hAR)
        _ ≤ A - r ^ u := sub_le_sub_left hrpow A
        _ ≤ _ := by simpa only [sub_eq_add_neg, add_comm, neg_div] using hm
    calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hbound
  · have hrR : R < r := lt_of_not_ge hsmall
    have hrB : B < r := lt_of_le_of_lt (le_max_left _ _) hrR
    have hr1 : 1 ≤ r := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hrR)
    have hrpow : 0 ≤ r ^ u := Real.rpow_nonneg hr.le _
    have hsu : u ≤ s := min_le_left _ _
    have htu : u ≤ t := min_le_right _ _
    have hsr : r ^ u ≤ r ^ s := Real.rpow_le_rpow_of_exponent_le hr1 hsu
    have htr : r ^ u ≤ r ^ t := Real.rpow_le_rpow_of_exponent_le hr1 htu
    have haS : 0 < a ^ s := Real.rpow_pos_of_pos ha _
    have hbT : 0 < b * (2 : ℝ) ^ t := mul_pos hb (Real.rpow_pos_of_pos (by norm_num) _)
    have hDA : a ^ s ≤ A := (le_max_left _ _).trans hAD
    have hDB : b * (2 : ℝ) ^ t ≤ A := (le_max_right _ _).trans hAD
    have hxdiv : r ^ u / A ≤ r ^ s / a ^ s := by
      calc
        _ ≤ r ^ u / a ^ s := div_le_div_of_nonneg_left hrpow haS hDA
        _ ≤ _ := div_le_div_of_nonneg_right hsr haS.le
    have htdiv : r ^ u / A ≤ r ^ t / (b * (2 : ℝ) ^ t) := by
      calc
        _ ≤ r ^ u / (b * (2 : ℝ) ^ t) := div_le_div_of_nonneg_left hrpow hbT hDB
        _ ≤ _ := div_le_div_of_nonneg_right htr hbT.le
    have hxexp : Real.exp (-((r / a) ^ s)) ≤ Real.exp (-(r ^ u) / A) := by
      apply Real.exp_le_exp.mpr
      rw [Real.div_rpow hr.le ha.le]
      simpa only [neg_div] using neg_le_neg hxdiv
    have htexp : Real.exp (-((r / 2) ^ t) / b) ≤ Real.exp (-(r ^ u) / A) := by
      apply Real.exp_le_exp.mpr
      rw [Real.div_rpow hr.le (by norm_num)]
      have hident : -((r ^ t / (2 : ℝ) ^ t)) / b =
          -(r ^ t / (b * (2 : ℝ) ^ t)) := by ring
      rw [hident]
      simpa only [neg_div] using neg_le_neg htdiv
    have hx := measure_ge_le_of_exp_rpow_moment μ (X j) a s ha hs (hXi j) (hXb j) hr.le
    have hT (i : Fin (n + 1)) : μ {ω | r / 2 ≤ T i ω} ≤
        ENNReal.ofReal (b * Real.exp (-(r ^ u) / A)) := by
      exact (htail i (r / 2) (by positivity)).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left htexp hb.le))
    calc
      _ ≤ μ {ω | r ≤ X j ω} + ∑ i : Fin (n + 1), μ {ω | r / 2 ≤ T i ω} :=
        measure_ge_max_le μ (X j) T B r hrB
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(r ^ u) / A)) +
          ∑ _i : Fin (n + 1), ENNReal.ofReal (b * Real.exp (-(r ^ u) / A)) := by
        exact add_le_add (hx.trans (ENNReal.ofReal_le_ofReal (by gcongr)))
          (Finset.sum_le_sum fun i _ => hT i)
      _ = ENNReal.ofReal (K * Real.exp (-(r ^ u) / A)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        dsimp [K]
        push_cast
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAK (Real.exp_nonneg _))

end LatticeProb
