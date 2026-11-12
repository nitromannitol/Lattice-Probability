import Mathlib

/-!
# Splitting and bootstrap for a recursive inequality on a Laplace envelope

Let `l : ℝ → ℝ` be nonincreasing on `(0, ∞)` with values in `[0, 1]`, let `β : ℝ → ℝ`, and let
`V₁, …, V_N` be positive random variables on a probability space `(Ω, P)`. We consider the
recursive inequality

  `l λ ≤ max (β λ) (E ∏ᵢ l (λ Vᵢ))`  for all `λ > 0`.      (rec)

* `LatticeProb.rec_split`: if `P (∃ i, Vᵢ < e^{-u}) ≤ τ`, then
  `l (λ e^u) ≤ max (β (λ e^u)) (τ + l(λ)^N)`.
* `LatticeProb.rec_moment_bound`: if `l x ≤ C x^{-a}` for `x > 0` and
  `E ∏ᵢ Vᵢ^{-a} ≤ M`, then `l λ ≤ max (β λ) ((C λ^{-a})^N M)`.
* `LatticeProb.rpowDecay_of_recursion`: if `β` has a polynomial bound of every order, all the
  negative moments `E ∏ᵢ Vᵢ^{-a}` are finite, `N ≥ 2`, and `l` has one polynomial bound
  `l x ≤ C x^{-a₀}` with `a₀ > 0`, then `l` has a polynomial bound of every order.
-/

noncomputable section

open MeasureTheory Real Filter Set

namespace LatticeProb

/-- `l` is bounded by `C x ^ (-a)` on `(0, ∞)` for some `C ≥ 0`. -/
def RpowDecay (l : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → l x ≤ C * x ^ (-a)

section Split

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [Fintype ι] {V : ι → Ω → ℝ} {l β : ℝ → ℝ}

/-- **Splitting.** If `l` is nonincreasing on `(0, ∞)` with values in `[0, 1]` and satisfies
`l λ ≤ max (β λ) (E ∏ᵢ l (λ Vᵢ))` for all `λ > 0`, and some `Vᵢ` is below `e^{-u}` with
probability at most `τ`, then `l (λ e^u) ≤ max (β (λ e^u)) (τ + l(λ)^N)`. -/
theorem rec_split (hVm : ∀ i, Measurable (V i)) (hV0 : ∀ i ω, 0 < V i ω)
    (hl0 : ∀ x, 0 < x → 0 ≤ l x) (hl1 : ∀ x, 0 < x → l x ≤ 1)
    (hanti : ∀ x y, 0 < x → x ≤ y → l y ≤ l x)
    (hrec : ∀ lam, 0 < lam → l lam ≤ max (β lam) (∫ ω, ∏ i, l (lam * V i ω) ∂P))
    {u τ lam : ℝ} (hlam : 0 < lam) (hP : P.real {ω | ∃ i, V i ω < exp (-u)} ≤ τ) :
    l (lam * exp u) ≤ max (β (lam * exp u)) (τ + l lam ^ Fintype.card ι) := by
  have hlam' : 0 < lam * exp u := mul_pos hlam (exp_pos u)
  refine (hrec _ hlam').trans (max_le_max le_rfl ?_)
  set B : Set Ω := {ω | ∃ i, V i ω < exp (-u)} with hB
  have hBm : MeasurableSet B := by
    have : B = ⋃ i, V i ⁻¹' Set.Iio (exp (-u)) := by ext ω; simp [hB]
    rw [this]; exact MeasurableSet.iUnion fun i => hVm i measurableSet_Iio
  have hind : Integrable (B.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hBm
  have hint : Integrable (fun ω => B.indicator (fun _ => (1 : ℝ)) ω + l lam ^ Fintype.card ι) P :=
    hind.add (integrable_const _)
  have hpos : ∀ ω i, 0 < lam * exp u * V i ω := fun ω i => mul_pos hlam' (hV0 i ω)
  have hc : 0 ≤ l lam ^ Fintype.card ι := pow_nonneg (hl0 _ hlam) _
  calc ∫ ω, ∏ i, l (lam * exp u * V i ω) ∂P
      ≤ ∫ ω, (B.indicator (fun _ => (1 : ℝ)) ω + l lam ^ Fintype.card ι) ∂P := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_) hint
          (Filter.Eventually.of_forall fun ω => ?_)
        · exact Finset.prod_nonneg fun i _ => hl0 _ (hpos ω i)
        · beta_reduce
          by_cases hω : ω ∈ B
          · rw [Set.indicator_of_mem hω]
            have h1 : ∏ i, l (lam * exp u * V i ω) ≤ 1 :=
              Finset.prod_le_one₀ (fun i _ => hl0 _ (hpos ω i)) (fun i _ => hl1 _ (hpos ω i))
            linarith
          · rw [Set.indicator_of_notMem hω, zero_add]
            have hge : ∀ i, exp (-u) ≤ V i ω := by
              intro i; by_contra h; exact hω ⟨i, not_le.1 h⟩
            have hle : ∀ i, l (lam * exp u * V i ω) ≤ l lam := by
              intro i
              refine hanti _ _ hlam ?_
              calc lam = lam * exp u * exp (-u) := by
                    rw [mul_assoc, ← Real.exp_add]; simp
                _ ≤ lam * exp u * V i ω := by gcongr; exact hge i
            calc ∏ i, l (lam * exp u * V i ω) ≤ ∏ _i : ι, l lam :=
                  Finset.prod_le_prod₀ (fun i _ => hl0 _ (hpos ω i)) (fun i _ => hle i)
              _ = l lam ^ Fintype.card ι := by simp
    _ = P.real B + l lam ^ Fintype.card ι := by
        rw [integral_add hind (integrable_const _), integral_indicator_const _ hBm]
        simp
    _ ≤ τ + l lam ^ Fintype.card ι := by linarith

omit [IsProbabilityMeasure P] in
/-- **Moment bound.** If `l x ≤ C x^{-a}` for `x > 0` (`C ≥ 0`), `l ≥ 0` on `(0, ∞)`, and
`E ∏ᵢ Vᵢ^{-a} ≤ M`, then `E ∏ᵢ l (λ Vᵢ) ≤ (C λ^{-a})^N M`. -/
theorem integral_prod_le_of_rpowDecay (hV0 : ∀ i ω, 0 < V i ω)
    (hl0 : ∀ x, 0 < x → 0 ≤ l x) {a C M : ℝ} (hC : 0 ≤ C)
    (hl : ∀ x, 0 < x → l x ≤ C * x ^ (-a))
    (hint : Integrable (fun ω => ∏ i, V i ω ^ (-a)) P)
    (hM : ∫ ω, ∏ i, V i ω ^ (-a) ∂P ≤ M) {lam : ℝ} (hlam : 0 < lam) :
    ∫ ω, ∏ i, l (lam * V i ω) ∂P ≤ (C * lam ^ (-a)) ^ Fintype.card ι * M := by
  have hc : 0 ≤ (C * lam ^ (-a)) ^ Fintype.card ι :=
    pow_nonneg (mul_nonneg hC (Real.rpow_nonneg hlam.le _)) _
  calc ∫ ω, ∏ i, l (lam * V i ω) ∂P
      ≤ ∫ ω, (C * lam ^ (-a)) ^ Fintype.card ι * ∏ i, V i ω ^ (-a) ∂P := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
          (hint.const_mul _) (Filter.Eventually.of_forall fun ω => ?_)
        · exact Finset.prod_nonneg fun i _ => hl0 _ (mul_pos hlam (hV0 i ω))
        · calc ∏ i, l (lam * V i ω)
              ≤ ∏ i, (C * lam ^ (-a) * V i ω ^ (-a)) := by
                refine Finset.prod_le_prod₀ (fun i _ => hl0 _ (mul_pos hlam (hV0 i ω))) ?_
                intro i _
                have := hl _ (mul_pos hlam (hV0 i ω))
                rwa [Real.mul_rpow hlam.le (hV0 i ω).le, ← mul_assoc] at this
            _ = (C * lam ^ (-a)) ^ Fintype.card ι * ∏ i, V i ω ^ (-a) := by
                rw [Finset.prod_mul_distrib]; simp
    _ = (C * lam ^ (-a)) ^ Fintype.card ι * ∫ ω, ∏ i, V i ω ^ (-a) ∂P := by
        rw [integral_const_mul]
    _ ≤ (C * lam ^ (-a)) ^ Fintype.card ι * M := mul_le_mul_of_nonneg_left hM hc

end Split

section Bootstrap

variable {l : ℝ → ℝ}

/-- A polynomial bound on `[1, ∞)` with a nonnegative exponent extends to `(0, ∞)` when
`l ≤ 1`. -/
theorem RpowDecay.of_ge_one (hl1 : ∀ x, 0 < x → l x ≤ 1) {a : ℝ} (ha : 0 ≤ a)
    (h : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → l x ≤ K * x ^ (-a)) : RpowDecay l a := by
  obtain ⟨K, hK, hKl⟩ := h
  refine ⟨max K 1, le_trans hK (le_max_left _ _), fun x hx => ?_⟩
  rcases le_total 1 x with h1 | h1
  · exact (hKl x h1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hx.le _))
  · have : 1 ≤ x ^ (-a) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx h1 (by linarith)
    calc l x ≤ 1 := hl1 x hx
      _ = 1 * 1 := by ring
      _ ≤ max K 1 * x ^ (-a) := mul_le_mul (le_max_right _ _) this zero_le_one
          (le_trans hK (le_max_left _ _))

/-- Weakening of the exponent of a polynomial bound, for `l ≤ 1`. -/
theorem RpowDecay.mono (hl1 : ∀ x, 0 < x → l x ≤ 1) {a a' : ℝ} (h : RpowDecay l a)
    (ha' : 0 ≤ a') (hle : a' ≤ a) : RpowDecay l a' := by
  obtain ⟨C, hC, hl⟩ := h
  refine RpowDecay.of_ge_one hl1 ha' ⟨C, hC, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  refine (hl x hx0).trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)

section Step

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ι : Type*} [Fintype ι] {V : ι → Ω → ℝ} {β : ℝ → ℝ}

/-- One step of the bootstrap: a polynomial bound of order `a > 0` for `l` gives a polynomial
bound of order `min q (a N)` for every `q > 0`. -/
theorem RpowDecay.step (hV0 : ∀ i ω, 0 < V i ω)
    (hl0 : ∀ x, 0 < x → 0 ≤ l x) (hl1 : ∀ x, 0 < x → l x ≤ 1)
    (hrec : ∀ lam, 0 < lam → l lam ≤ max (β lam) (∫ ω, ∏ i, l (lam * V i ω) ∂P))
    (hβ : ∀ q : ℝ, 0 < q → ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ x : ℝ, 0 < x → β x ≤ Cb * x ^ (-q))
    (hmom : ∀ a : ℝ, 0 ≤ a → ∃ M : ℝ, 0 ≤ M ∧
      Integrable (fun ω => ∏ i, V i ω ^ (-a)) P ∧ ∫ ω, ∏ i, V i ω ^ (-a) ∂P ≤ M)
    {a : ℝ} (ha : 0 < a) (hN : 1 ≤ Fintype.card ι) (h : RpowDecay l a) {q : ℝ} (hq : 0 < q) :
    RpowDecay l (min q (a * Fintype.card ι)) := by
  obtain ⟨C, hC, hl⟩ := h
  obtain ⟨M, hM0, hint, hM⟩ := hmom a ha.le
  obtain ⟨Cb, hCb, hβq⟩ := hβ q hq
  have hNpos : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have hq' : 0 < min q (a * Fintype.card ι) := lt_min hq (by positivity)
  refine RpowDecay.of_ge_one hl1 hq'.le ⟨max Cb (C ^ Fintype.card ι * M),
    le_trans hCb (le_max_left _ _), fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hmom' := integral_prod_le_of_rpowDecay hV0 hl0 hC hl hint hM hx0
  have hx1 : l x ≤ max (β x) ((C * x ^ (-a)) ^ Fintype.card ι * M) :=
    (hrec x hx0).trans (max_le_max le_rfl hmom')
  have hpow : (C * x ^ (-a)) ^ Fintype.card ι * M =
      C ^ Fintype.card ι * M * x ^ (-(a * Fintype.card ι)) := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ (-a)), ← Real.rpow_mul hx0.le,
      show -a * (Fintype.card ι : ℝ) = -(a * Fintype.card ι) by ring]
    ring
  have hxq : x ^ (-q) ≤ x ^ (-(min q (a * Fintype.card ι))) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith [min_le_left q (a * Fintype.card ι)])
  have hxa : x ^ (-(a * Fintype.card ι)) ≤ x ^ (-(min q (a * Fintype.card ι))) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith [min_le_right q (a * Fintype.card ι)])
  have hK : 0 ≤ C ^ Fintype.card ι * M := mul_nonneg (pow_nonneg hC _) hM0
  refine hx1.trans (max_le ?_ ?_)
  · calc β x ≤ Cb * x ^ (-q) := hβq x hx0
      _ ≤ Cb * x ^ (-(min q (a * Fintype.card ι))) := mul_le_mul_of_nonneg_left hxq hCb
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)
  · rw [hpow]
    calc C ^ Fintype.card ι * M * x ^ (-(a * Fintype.card ι))
        ≤ C ^ Fintype.card ι * M * x ^ (-(min q (a * Fintype.card ι))) :=
          mul_le_mul_of_nonneg_left hxa hK
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx0.le _)

/-- **Bootstrap.** Suppose `l` has values in `[0, 1]` on `(0, ∞)`, satisfies the recursive
inequality `l λ ≤ max (β λ) (E ∏ᵢ l (λ Vᵢ))` with `N ≥ 2` factors, `β` has a polynomial bound of
every order, all negative moments `E ∏ᵢ Vᵢ^{-a}` (`a ≥ 0`) are finite, and `l` has one
polynomial bound of positive order. Then `l` has a polynomial bound of every order. -/
theorem rpowDecay_of_recursion (hV0 : ∀ i ω, 0 < V i ω)
    (hl0 : ∀ x, 0 < x → 0 ≤ l x) (hl1 : ∀ x, 0 < x → l x ≤ 1)
    (hrec : ∀ lam, 0 < lam → l lam ≤ max (β lam) (∫ ω, ∏ i, l (lam * V i ω) ∂P))
    (hβ : ∀ q : ℝ, 0 < q → ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ x : ℝ, 0 < x → β x ≤ Cb * x ^ (-q))
    (hmom : ∀ a : ℝ, 0 ≤ a → ∃ M : ℝ, 0 ≤ M ∧
      Integrable (fun ω => ∏ i, V i ω ^ (-a)) P ∧ ∫ ω, ∏ i, V i ω ^ (-a) ∂P ≤ M)
    (hN : 2 ≤ Fintype.card ι) {a₀ : ℝ} (ha₀ : 0 < a₀) (h₀ : RpowDecay l a₀) {q : ℝ} (hq : 0 < q) :
    RpowDecay l q := by
  have hN1 : 1 ≤ Fintype.card ι := le_trans (by norm_num) hN
  have hN2 : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have key : ∀ k : ℕ, RpowDecay l (min q (a₀ * 2 ^ k)) := by
    intro k
    induction k with
    | zero =>
      have hle : min q (a₀ * 2 ^ 0) ≤ a₀ := by simp
      exact h₀.mono hl1 (lt_min hq (by positivity)).le hle
    | succ k ih =>
      have hpos : 0 < min q (a₀ * 2 ^ k) := lt_min hq (by positivity)
      have hs := RpowDecay.step hV0 hl0 hl1 hrec hβ hmom hpos hN1 ih hq
      refine hs.mono hl1 (lt_min hq (by positivity)).le ?_
      rcases le_total q (a₀ * 2 ^ k) with hk | hk
      · rw [min_eq_left hk]
        exact le_min (min_le_left _ _) (le_trans (min_le_left _ _) (by nlinarith))
      · rw [min_eq_right hk]
        refine le_min (min_le_left _ _) ?_
        calc min q (a₀ * 2 ^ (k + 1)) ≤ a₀ * 2 ^ (k + 1) := min_le_right _ _
          _ = a₀ * 2 ^ k * 2 := by ring
          _ ≤ a₀ * 2 ^ k * Fintype.card ι := by gcongr
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q / a₀ < 2 ^ k := pow_unbounded_of_one_lt _ (by norm_num)
  have hqk : q ≤ a₀ * 2 ^ k := by
    rw [div_lt_iff₀ ha₀] at hk; linarith
  simpa [min_eq_left hqk] using key k

end Step

end Bootstrap

end LatticeProb
