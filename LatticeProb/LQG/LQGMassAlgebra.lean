import Mathlib

/-!
# Algebra of moments of a finite sum of `[0, ∞]`-valued random variables

Two elementary tools for bounding `E[(∑ X_i)^p]` by induction on the exponent.

* **Concave Jensen** (`lintegral_rpow_le_rpow_lintegral`): for a probability measure and
  `0 < s ≤ 1`, `∫ g^s ≤ (∫ g)^s`.
* **Decomposition of a power of a sum** (`rpow_sum_le_sum_rpow_add_cross`): for `0 < p ≤ N`,
  `(∑_{i∈s} x_i)^p ≤ ∑ x_i^p + (∑_f ∏_j x_{f j})^(p/N)`, where `f` runs over the non-constant
  maps `Fin N → s`. Here `(∑ x_i)^N = ∑ x_i^N + ∑_f ∏_j x_{f j}` is an exact identity in
  `[0, ∞]`, so no truncated subtraction is involved.
* The two combine into `lintegral_sum_rpow_le`:
  `E[(∑ X_i)^p] ≤ ∑ E[X_i^p] + (∑_f E[∏_j X_{f j}])^(p/N)`.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace LatticeProb

/-- **Concave Jensen** for `[0, ∞]`-valued functions on a probability space: for `0 < s ≤ 1`,
`∫ g^s ≤ (∫ g)^s`. -/
theorem lintegral_rpow_le_rpow_lintegral {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {g : α → ℝ≥0∞}
    (hg : AEMeasurable g ν) : ∫⁻ x, g x ^ s ∂ν ≤ (∫⁻ x, g x ∂ν) ^ s := by
  rcases hs1.eq_or_lt with rfl | hs1'
  · simp
  · have hp1 : 1 < 1 / s := by rw [lt_div_iff₀ hs0]; linarith
    have hpq : (1 / s).HolderConjugate (1 / (1 - s)) := by
      rw [Real.holderConjugate_iff]
      refine ⟨hp1, ?_⟩
      have : 1 - s ≠ 0 := by linarith
      field_simp
      ring
    have hgs : AEMeasurable (fun x => g x ^ s) ν := hg.pow_const s
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hgs
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
    have e : ∀ x, (g x ^ s) ^ s⁻¹ = g x := fun x => by
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hs0.ne', ENNReal.rpow_one]
    simpa [e] using h

/-- The non-constant maps `Fin N → ι` with values in `s`. -/
noncomputable def nonconstTuples {ι : Type*} (s : Finset ι) (N : ℕ) : Finset (Fin N → ι) := by
  classical
  exact (Fintype.piFinset fun _ : Fin N => s).filter (fun f => ∃ j j', f j ≠ f j')

theorem mem_nonconstTuples {ι : Type*} {s : Finset ι} {N : ℕ} {f : Fin N → ι} :
    f ∈ nonconstTuples s N ↔ (∀ j, f j ∈ s) ∧ ∃ j j', f j ≠ f j' := by
  classical
  unfold nonconstTuples
  simp [Fintype.mem_piFinset]

/-- A non-constant map `Fin N → ι` takes no value `N` times. -/
theorem nat_card_fibre_lt {ι : Type*} {s : Finset ι} {N : ℕ} {f : Fin N → ι}
    (hf : f ∈ nonconstTuples s N) (i : ι) : Nat.card {j : Fin N // f j = i} < N := by
  classical
  obtain ⟨-, j, j', hjj⟩ := mem_nonconstTuples.1 hf
  have hex : ∃ k, ¬ f k = i := by
    by_cases h : f j = i
    · exact ⟨j', fun h' => hjj (h.trans h'.symm)⟩
    · exact ⟨j, h⟩
  obtain ⟨k, hk⟩ := hex
  have := Fintype.card_subtype_lt (p := fun x : Fin N => f x = i) hk
  rw [Nat.card_eq_fintype_card]
  simpa using this

/-- Subadditivity of `t ↦ t ^ q` on finite sums in `[0, ∞]`, `0 ≤ q ≤ 1`. -/
theorem rpow_sum_le_sum_rpow {ι : Type*} (s : Finset ι) (x : ι → ℝ≥0∞) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q ≤ 1) : (∑ i ∈ s, x i) ^ q ≤ ∑ i ∈ s, x i ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hq0]
  | insert a t hat ih =>
    rw [Finset.sum_insert hat, Finset.sum_insert hat]
    calc (x a + ∑ i ∈ t, x i) ^ q ≤ x a ^ q + (∑ i ∈ t, x i) ^ q :=
          ENNReal.rpow_add_le_add_rpow _ _ hq0.le hq1
      _ ≤ x a ^ q + ∑ i ∈ t, x i ^ q := by gcongr

/-- **Multinomial identity** in `[0, ∞]`: `(∑ x_i)^N = ∑ x_i^N + ∑_f ∏_j x_{f j}`, the last sum
over the non-constant maps `f : Fin N → s`. -/
theorem sum_pow_eq_sum_pow_add_cross {ι : Type*} (s : Finset ι) (x : ι → ℝ≥0∞) {N : ℕ}
    (hN : N ≠ 0) :
    (∑ i ∈ s, x i) ^ N = ∑ i ∈ s, x i ^ N + ∑ f ∈ nonconstTuples s N, ∏ j, x (f j) := by
  classical
  have h1 : (∑ i ∈ s, x i) ^ N = ∑ f ∈ Fintype.piFinset (fun _ : Fin N => s), ∏ j, x (f j) := by
    rw [← Finset.prod_univ_sum (fun _ : Fin N => s) (fun _ i => x i)]
    simp
  have hsplit := Finset.sum_filter_add_sum_filter_not (Fintype.piFinset (fun _ : Fin N => s))
    (fun f : Fin N → ι => ∃ j j', f j ≠ f j') (fun f => ∏ j, x (f j))
  have hne : ∀ f ∈ Fintype.piFinset (fun _ : Fin N => s), (¬ ∃ j j', f j ≠ f j') ↔
      f ∈ s.image (fun i : ι => fun _ : Fin N => i) := by
    intro f hf
    rw [Fintype.mem_piFinset] at hf
    have : NeZero N := ⟨hN⟩
    constructor
    · intro h
      push Not at h
      simp only [Finset.mem_image]
      refine ⟨f 0, hf 0, funext fun j => (h j 0).symm⟩
    · intro h
      simp only [Finset.mem_image] at h
      obtain ⟨i, -, rfl⟩ := h
      simp
  have hconst : ∑ f ∈ (Fintype.piFinset (fun _ : Fin N => s)).filter
      (fun f => ¬ ∃ j j', f j ≠ f j'), ∏ j, x (f j) = ∑ i ∈ s, x i ^ N := by
    have : (Fintype.piFinset (fun _ : Fin N => s)).filter (fun f => ¬ ∃ j j', f j ≠ f j')
        = s.image (fun i : ι => fun _ : Fin N => i) := by
      ext f
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hf, h⟩
        exact (hne f hf).1 h
      · intro h
        have hf : f ∈ Fintype.piFinset (fun _ : Fin N => s) := by
          simp only [Finset.mem_image] at h
          obtain ⟨i, hi, rfl⟩ := h
          exact Fintype.mem_piFinset.2 fun _ => hi
        exact ⟨hf, (hne f hf).2 h⟩
    rw [this, Finset.sum_image]
    · simp
    · intro i _ i' _ h
      have : NeZero N := ⟨hN⟩
      exact congrFun h 0
  have hnc : (Fintype.piFinset (fun _ : Fin N => s)).filter (fun f => ∃ j j', f j ≠ f j')
      = nonconstTuples s N := by
    unfold nonconstTuples
    rfl
  rw [h1, ← hsplit, hnc, hconst, add_comm]

/-- **Decomposition of `(∑ x_i)^p` in `[0, ∞]`.** For `0 < p ≤ N`,
`(∑ x_i)^p ≤ ∑ x_i^p + (∑_f ∏_j x_{f j})^(p/N)`, `f` running over the non-constant maps
`Fin N → s`. -/
theorem rpow_sum_le_sum_rpow_add_cross {ι : Type*} (s : Finset ι) (x : ι → ℝ≥0∞) {N : ℕ}
    (hN : N ≠ 0) {p : ℝ} (hp0 : 0 < p) (hpN : p ≤ N) :
    (∑ i ∈ s, x i) ^ p ≤
      ∑ i ∈ s, x i ^ p + (∑ f ∈ nonconstTuples s N, ∏ j, x (f j)) ^ (p / N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hq0 : 0 < p / N := div_pos hp0 hNpos
  have hq1 : p / N ≤ 1 := (div_le_one hNpos).2 hpN
  have hSp : (∑ i ∈ s, x i) ^ p = ((∑ i ∈ s, x i) ^ N) ^ (p / N) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    field_simp
  have hAq : (∑ i ∈ s, x i ^ N) ^ (p / N) ≤ ∑ i ∈ s, x i ^ p := by
    calc (∑ i ∈ s, x i ^ N) ^ (p / N) ≤ ∑ i ∈ s, (x i ^ N) ^ (p / N) :=
          rpow_sum_le_sum_rpow s (fun i => x i ^ N) hq0 hq1
      _ = ∑ i ∈ s, x i ^ p := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          congr 1
          field_simp
  rw [hSp, sum_pow_eq_sum_pow_add_cross s x hN]
  calc (∑ i ∈ s, x i ^ N + ∑ f ∈ nonconstTuples s N, ∏ j, x (f j)) ^ (p / N)
      ≤ (∑ i ∈ s, x i ^ N) ^ (p / N) + (∑ f ∈ nonconstTuples s N, ∏ j, x (f j)) ^ (p / N) :=
        ENNReal.rpow_add_le_add_rpow _ _ hq0.le hq1
    _ ≤ _ := by gcongr

/-- **Moment decomposition.** For a probability measure, finitely many `[0, ∞]`-valued
a.e.-measurable `X_i` and `0 < p ≤ N`:
`E[(∑ X_i)^p] ≤ ∑ E[X_i^p] + (∑_f E[∏_j X_{f j}])^(p/N)`, `f` over the non-constant maps
`Fin N → s`. -/
theorem lintegral_sum_rpow_le {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (s : Finset ι) (X : ι → Ω → ℝ≥0∞)
    (hX : ∀ i, AEMeasurable (X i) P) {N : ℕ} (hN : N ≠ 0) {p : ℝ} (hp0 : 0 < p) (hpN : p ≤ N) :
    ∫⁻ ω, (∑ i ∈ s, X i ω) ^ p ∂P ≤
      ∑ i ∈ s, ∫⁻ ω, X i ω ^ p ∂P +
        (∑ f ∈ nonconstTuples s N, ∫⁻ ω, ∏ j, X (f j) ω ∂P) ^ (p / N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hq0 : 0 < p / N := div_pos hp0 hNpos
  have hq1 : p / N ≤ 1 := (div_le_one hNpos).2 hpN
  have hprod : ∀ f : Fin N → ι, AEMeasurable (fun ω => ∏ j, X (f j) ω) P := fun f =>
    Finset.aemeasurable_fun_prod _ fun j _ => hX (f j)
  have hB : AEMeasurable (fun ω => ∑ f ∈ nonconstTuples s N, ∏ j, X (f j) ω) P :=
    Finset.aemeasurable_fun_sum _ fun f _ => hprod f
  have hA : AEMeasurable (fun ω => ∑ i ∈ s, X i ω ^ p) P :=
    Finset.aemeasurable_fun_sum _ fun i _ => (hX i).pow_const p
  calc ∫⁻ ω, (∑ i ∈ s, X i ω) ^ p ∂P
      ≤ ∫⁻ ω, (∑ i ∈ s, X i ω ^ p +
          (∑ f ∈ nonconstTuples s N, ∏ j, X (f j) ω) ^ (p / N)) ∂P :=
        lintegral_mono fun ω => rpow_sum_le_sum_rpow_add_cross s (fun i => X i ω) hN hp0 hpN
    _ = ∫⁻ ω, ∑ i ∈ s, X i ω ^ p ∂P +
          ∫⁻ ω, (∑ f ∈ nonconstTuples s N, ∏ j, X (f j) ω) ^ (p / N) ∂P :=
        lintegral_add_left' hA _
    _ ≤ _ := by
        gcongr
        · rw [lintegral_finsetSum' _ fun i _ => (hX i).pow_const p]
        · calc ∫⁻ ω, (∑ f ∈ nonconstTuples s N, ∏ j, X (f j) ω) ^ (p / N) ∂P
              ≤ (∫⁻ ω, ∑ f ∈ nonconstTuples s N, ∏ j, X (f j) ω ∂P) ^ (p / N) :=
                lintegral_rpow_le_rpow_lintegral P hq0 hq1 hB
            _ = _ := by rw [lintegral_finsetSum' _ fun f _ => hprod f]

end LatticeProb
