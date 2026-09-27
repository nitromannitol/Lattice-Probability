import LatticeProb.Prob.KingmanLinear.LinearSets
import LatticeProb.Prob.KingmanLinear.InducedFamily
import LatticeProb.Prob.KingmanLinear.Interpolation

/-!
# 4. From the induced family to all times

Assembles the induced-family limit and the return-time limit of stage 2, the deterministic
interpolation lemma of stage 3, and the a.e. positivity of the return time restated in
`LatticeProb.Prob.KingmanLinear.Restated`: at a.e. point, once `g n x / n` converges along the
induced subsequence `retSum T A j x`, and that subsequence is Lipschitz-compatible, it converges
along every `n`. Ranging over the sets `linSet g C k` of stage 1 removes the dependence on `k`.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- If `u j / j → Λ` and `v j / j → ρ ≠ 0`, then `u j / v j → Λ / ρ`. -/
private theorem tendsto_div_div_of_tendsto_div_of_ne_zero {u v : ℕ → ℝ} {Λ ρ : ℝ} (hρ : ρ ≠ 0)
    (hu : Tendsto (fun j : ℕ => u j / (j : ℝ)) atTop (𝓝 Λ))
    (hv : Tendsto (fun j : ℕ => v j / (j : ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun j : ℕ => u j / v j) atTop (𝓝 (Λ / ρ)) := by
  have h := hu.div hv hρ
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hj0]


omit [MeasurableSpace Ω] in
/-- At a point `x` where every iterate of `inducedMap T A` has positive return time, if the induced
family and the return-time Birkhoff sum both have linear limits along `j` and `g` is Lipschitz on
doubling windows, then `g n x / n` converges. -/
private theorem exists_tendsto_div_at_point_of_induced (T : Ω → Ω) (A : Set Ω) (g : ℕ → Ω → ℝ)
    (x : Ω) {C Λ ρ : ℝ}
    (hpos : ∀ i : ℕ, 0 < retTime T A ((inducedMap T A)^[i] x))
    (hΛ : Tendsto (fun j : ℕ => indG g T A j x / (j : ℝ)) atTop (𝓝 Λ))
    (hρ : Tendsto (fun j : ℕ => (retSum T A j x : ℝ) / (j : ℝ)) atTop (𝓝 ρ))
    (hlip : ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2*n →
      |g m x - g n x| ≤ C*((m:ℝ)-n) + ε*n) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 L) := by
  have hR0 : (fun j : ℕ => retSum T A j x) 0 = 0 := (by
    show birkhoffSum (inducedMap T A) (retTime T A) 0 x = 0
    simp)
  have hRlt : ∀ j, (fun j : ℕ => retSum T A j x) j < (fun j : ℕ => retSum T A j x) (j + 1) := (by
    intro j
    show birkhoffSum (inducedMap T A) (retTime T A) j x <
      birkhoffSum (inducedMap T A) (retTime T A) (j + 1) x
    rw [birkhoffSum_succ]
    exact Nat.lt_add_of_pos_right (hpos j))
  have hRmono : StrictMono (fun j : ℕ => retSum T A j x) := strictMono_nat_of_lt_succ hRlt
  have hρ1 : 1 ≤ ρ := (by
    refine ge_of_tendsto hρ ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hle : j ≤ retSum T A j x := le_apply_of_strictMono_of_zero_eq_zero hR0 hRmono j
    have hj' : (0 : ℝ) < (j : ℝ) := (by exact_mod_cast hj)
    rw [le_div_iff₀ hj']
    simp only [one_mul]
    exact_mod_cast hle)
  have hρne : ρ ≠ 0 := (by linarith)
  have hsubs : Tendsto (fun j : ℕ => g (retSum T A j x) x / (retSum T A j x : ℝ)) atTop
      (𝓝 (Λ / ρ)) :=
    tendsto_div_div_of_tendsto_div_of_ne_zero (u := fun j => indG g T A j x)
      (v := fun j => (retSum T A j x : ℝ)) hρne hΛ hρ
  have hgap : Tendsto (fun j : ℕ =>
      ((((fun k : ℕ => retSum T A k x) (j + 1) : ℕ) : ℝ) -
       (((fun k : ℕ => retSum T A k x) j : ℕ) : ℝ)) /
      (((fun k : ℕ => retSum T A k x) j : ℕ) : ℝ)) atTop (𝓝 0) := (by
    simpa using tendsto_sub_div_apply_atTop_zero_of_tendsto_div hR0 hRmono hρ)
  have hlip' : ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2 * n →
      |(fun n => g n x) m - (fun n => g n x) n| ≤ (max C 0) * ((m:ℝ) - (n:ℝ)) + ε * (n:ℝ) := (by
    intro ε hε
    filter_upwards [hlip ε hε] with n hn
    intro m hnm hmn
    have h1 := hn m hnm hmn
    have h2 : C * ((m:ℝ) - (n:ℝ)) ≤ (max C 0) * ((m:ℝ) - (n:ℝ)) := (by
      apply mul_le_mul_of_nonneg_right (le_max_left C 0)
      have hnm' : (n:ℝ) ≤ (m:ℝ) := (by exact_mod_cast hnm)
      linarith)
    linarith)
  exact ⟨Λ / ρ,
    tendsto_div_of_tendsto_div_subseq (R := fun j : ℕ => retSum T A j x) (a := fun n => g n x)
      hR0 hRmono (le_max_right C 0) hsubs hgap hlip'⟩


/-- For `μ`-a.e. `x`, if `x ∈ linSet g C k` then `g n x / n` converges, by assembling the
induced-family limit, the return-time limit, positivity of return times, and the Lipschitz
hypothesis at `x`. -/
theorem ae_exists_tendsto_div_of_mem_linSet {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : ∀ m n x, g (m+n) x ≤ g m x + g n (T^[m] x)) (hg : ∀ n x, 0 ≤ g n x)
    (hgm : ∀ n, Measurable (g n)) (C C' : ℝ)
    (hlip : ∀ᵐ x ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2*n →
              |g m x - g n x| ≤ C'*((m:ℝ)-n) + ε*n) (k : ℕ) :
    ∀ᵐ x ∂μ, x ∈ linSet g C k → ∃ L : ℝ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 L) := by
  have hAm : MeasurableSet (linSet g C k) := measurableSet_linSet hgm C k
  have h1 : ∀ᵐ x ∂μ, x ∈ linSet g C k →
      ∃ L : ℝ, Tendsto (fun j : ℕ => indG g T (linSet g C k) j x / (j : ℝ)) atTop (𝓝 L) :=
    (ae_restrict_iff' hAm).1 (ae_exists_tendsto_indG_div hT hsub hg hgm C k)
  have h2 : ∀ᵐ x ∂μ, x ∈ linSet g C k →
      ∃ ρ : ℝ, Tendsto (fun j : ℕ => (retSum T (linSet g C k) j x : ℝ) / (j : ℝ)) atTop (𝓝 ρ) :=
    (ae_restrict_iff' hAm).1 (ae_exists_tendsto_retSum_div hT hAm)
  have h3 : ∀ᵐ x ∂μ, x ∈ linSet g C k →
      ∀ i : ℕ, 0 < retTime T (linSet g C k) ((inducedMap T (linSet g C k))^[i] x) :=
    (ae_restrict_iff' hAm).1 (ae_forall_retTime_pos_iterate_inducedMap hT hAm)
  have h4 : ∀ᵐ x ∂μ, x ∈ linSet g C k → ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2 * n →
      |g m x - g n x| ≤ C' * ((m : ℝ) - n) + ε * n :=
    (ae_restrict_iff' hAm).1 (ae_restrict_of_ae hlip)
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4 hin
  obtain ⟨Λ, hΛ⟩ := hx1 hin
  obtain ⟨ρ, hρ⟩ := hx2 hin
  exact exists_tendsto_div_at_point_of_induced T (linSet g C k) g x (hx3 hin) hΛ hρ (hx4 hin)


/-- For `μ`-a.e. `x`, `g n x / n` converges, by picking the `k` with `x ∈ linSet g C k` from the
linear bound. -/
theorem ae_exists_tendsto_div {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : ∀ m n x, g (m+n) x ≤ g m x + g n (T^[m] x)) (hg : ∀ n x, 0 ≤ g n x)
    (hgm : ∀ n, Measurable (g n)) {C C' : ℝ}
    (hlin : ∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, g n x ≤ C * n + K)
    (hlip : ∀ᵐ x ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2*n →
              |g m x - g n x| ≤ C'*((m:ℝ)-n) + ε*n) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 L) := by
  have h_all : ∀ᵐ x ∂μ, ∀ k : ℕ, x ∈ linSet g C k →
      ∃ L : ℝ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 L) :=
    ae_all_iff.2 (fun k => ae_exists_tendsto_div_of_mem_linSet hT hsub hg hgm C C' hlip k)
  filter_upwards [h_all, ae_exists_mem_linSet_of_linear_bound hlin] with x hx hk
  exact hx hk.choose hk.choose_spec

end LatticeProb
