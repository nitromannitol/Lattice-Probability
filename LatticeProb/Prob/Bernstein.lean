/-
Bernstein's inequality for bounded independent centred random variables.

    P(|∑ Y_i| ≥ t) ≤ 2 exp( -(t²/2) / (B² + Mt/3) ) ,   |Y_i| ≤ M,  B² = ∑ E[Y_i²].

The only analytic input is the moment generating function bound
`E[e^{λY}] ≤ exp(λ² E[Y²] / (2(1 - λM/3)))` for `0 < λM < 3`, which comes from the
pointwise inequality

    e^u ≤ 1 + u + u²/(2(1-θ))   for  |u| ≤ 3θ,  θ < 1,

proved here by comparing the tail `∑_{k≥2} u^k/k!` of the exponential series with a
geometric series, using `k! ≥ 2·3^{k-2}`.  Integrating it against a centred variable
kills the linear term, and `1 + z ≤ e^z` puts the bound back in exponential form.

Independence enters only through `ProbabilityTheory.iIndepFun.mgf_sum₀`, which turns
the moment generating function of the sum into a product; Chernoff's bound
`ProbabilityTheory.measure_ge_le_exp_mul_mgf` then gives the one-sided inequality at
the optimal `λ = t/(B² + Mt/3)`, at which `1 - λM/3 = B²/(B² + Mt/3)` and the exponent
collapses to `-t²/(2(B² + Mt/3))`.  The two-sided form applies the one-sided one to
`-Y` as well.

This is the Bernstein inequality quoted for part (c) of `lem:fuk-nagaev` in `rwrs.tex`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal Nat

namespace LatticeProb

theorem two_mul_three_pow_le_factorial (n : ℕ) : 2 * 3 ^ n ≤ (n + 2)! := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h : (n + 3)! = (n + 3) * (n + 2)! := by
        rw [show n + 3 = (n + 2) + 1 from rfl, Nat.factorial_succ]
      calc 2 * 3 ^ (n + 1) = 3 * (2 * 3 ^ n) := by ring
        _ ≤ 3 * (n + 2)! := by exact Nat.mul_le_mul_left 3 ih
        _ ≤ (n + 3) * (n + 2)! := Nat.mul_le_mul_right _ (by omega)
        _ = (n + 3)! := h.symm

theorem exp_le_one_add_add_sq_div (θ u : ℝ) (hθ1 : θ < 1) (hu : |u| ≤ 3 * θ) :
    Real.exp u ≤ 1 + u + u ^ 2 / (2 * (1 - θ)) := by
  have habs : (0 : ℝ) ≤ |u| := abs_nonneg u
  have h3 : |u| / 3 ≤ θ := by linarith
  have hlt : |u| / 3 < 1 := lt_of_le_of_lt h3 hθ1
  have hθpos : (0 : ℝ) < 1 - θ := by linarith
  set f : ℕ → ℝ := fun n => u ^ n / (n)! with hf
  have hsum : Summable f := Real.summable_pow_div_factorial u
  have hsum1 : Summable (fun n => f (n + 1)) := (summable_nat_add_iff 1).mpr hsum
  have hsum2 : Summable (fun n => f (n + 2)) := (summable_nat_add_iff 2).mpr hsum
  have hexp : Real.exp u = ∑' n : ℕ, f n := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hf0 : f 0 = 1 := by simp [hf]
  have hf1 : f 1 = u := by simp [hf]
  have hpeel : ∑' n : ℕ, f n = 1 + u + ∑' n : ℕ, f (n + 2) := by
    rw [hsum.tsum_eq_zero_add, hsum1.tsum_eq_zero_add, hf0]
    show 1 + (f (0 + 1) + ∑' n : ℕ, f (n + 1 + 1)) = 1 + u + ∑' n : ℕ, f (n + 2)
    rw [show (0 : ℕ) + 1 = 1 from rfl, hf1]
    ring
  -- termwise bound on the tail
  have hterm : ∀ n : ℕ, |f (n + 2)| ≤ (u ^ 2 / 2) * (|u| / 3) ^ n := by
    intro n
    have hfact : (2 : ℝ) * 3 ^ n ≤ ((n + 2)! : ℝ) := by
      exact_mod_cast two_mul_three_pow_le_factorial n
    have hpos : (0 : ℝ) < 2 * 3 ^ n := by positivity
    have habs2 : |f (n + 2)| = |u| ^ (n + 2) / ((n + 2)! : ℝ) := by
      rw [hf]
      simp only [abs_div, abs_pow, Nat.abs_cast]
    rw [habs2]
    have h1 : |u| ^ (n + 2) / ((n + 2)! : ℝ) ≤ |u| ^ (n + 2) / (2 * 3 ^ n) := by
      refine div_le_div_of_nonneg_left (by positivity) hpos hfact
    refine h1.trans ?_
    have h2 : |u| ^ (n + 2) = u ^ 2 * |u| ^ n := by
      rw [pow_add, sq_abs]
      ring
    rw [h2, div_pow]
    rw [div_le_iff₀ hpos]
    have : (0:ℝ) ≤ u ^ 2 := sq_nonneg u
    field_simp
    ring_nf
    nlinarith [pow_nonneg habs n, sq_nonneg u]
  have hgeo : Summable (fun n : ℕ => (u ^ 2 / 2) * (|u| / 3) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hlt).mul_left _
  have h2 : ∀ n : ℕ, f (n + 2) ≤ (u ^ 2 / 2) * (|u| / 3) ^ n :=
    fun n => (le_abs_self _).trans (hterm n)
  have h3 : ∑' n : ℕ, f (n + 2) ≤ ∑' n : ℕ, (u ^ 2 / 2) * (|u| / 3) ^ n :=
    Summable.tsum_le_tsum h2 hsum2 hgeo
  have h4 : ∑' n : ℕ, (u ^ 2 / 2) * (|u| / 3) ^ n = (u ^ 2 / 2) * (1 - |u| / 3)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hlt]
  rw [h4] at h3
  have h5 : (0 : ℝ) < 1 - |u| / 3 := by linarith
  have h6 : (u ^ 2 / 2) * (1 - |u| / 3)⁻¹ ≤ u ^ 2 / (2 * (1 - θ)) := by
    have e1 : (u ^ 2 / 2) * (1 - |u| / 3)⁻¹ = u ^ 2 / (2 * (1 - |u| / 3)) := by
      field_simp
    rw [e1]
    exact div_le_div_of_nonneg_left (sq_nonneg u) (by linarith) (by linarith)
  rw [hexp, hpeel]
  linarith [h3, h6]


/-- **The Bernstein moment generating function bound.**  A centred variable
bounded by `M` has `E[e^{λX}] ≤ exp(λ²E[X²]/(2(1-λM/3)))` for `0 < λM < 3`. -/
theorem mgf_le_of_bounded {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hint : Integrable X P)
    (hmean : ∫ ω, X ω ∂P = 0) (M : ℝ) (hb : ∀ᵐ ω ∂P, |X ω| ≤ M)
    (hsq : Integrable (fun ω => X ω ^ 2) P)
    (lam : ℝ) (hlam : 0 < lam) (hlM : lam * M < 3) :
    mgf X P lam
      ≤ Real.exp (lam ^ 2 * (∫ ω, X ω ^ 2 ∂P) / (2 * (1 - lam * M / 3))) := by
  set θ : ℝ := lam * M / 3 with hθdef
  have hθ1 : θ < 1 := by rw [hθdef]; linarith
  have hθpos : (0 : ℝ) < 1 - θ := by linarith
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (lam * X ω)) P :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable
      hint.aestronglyMeasurable
  have hbdd : ∀ᵐ ω ∂P, ‖Real.exp (lam * X ω)‖ ≤ Real.exp (lam * M) := by
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have h1 : X ω ≤ M := (abs_le.mp hω).2
    nlinarith
  have hexpint : Integrable (fun ω => Real.exp (lam * X ω)) P :=
    Integrable.mono' (integrable_const _) hmeas hbdd
  have hpt : ∀ᵐ ω ∂P, Real.exp (lam * X ω)
      ≤ 1 + lam * X ω + (lam * X ω) ^ 2 / (2 * (1 - θ)) := by
    filter_upwards [hb] with ω hω
    refine exp_le_one_add_add_sq_div θ (lam * X ω) hθ1 ?_
    rw [abs_mul, abs_of_pos hlam, hθdef]
    have : lam * |X ω| ≤ lam * M := by nlinarith
    linarith
  have hrhsint : Integrable
      (fun ω => 1 + lam * X ω + (lam * X ω) ^ 2 / (2 * (1 - θ))) P := by
    refine ((integrable_const (1 : ℝ)).add (hint.const_mul lam)).add ?_
    have hfun : (fun ω => (lam * X ω) ^ 2 / (2 * (1 - θ)))
        = fun ω => (lam ^ 2 / (2 * (1 - θ))) * X ω ^ 2 := by
      funext ω; ring
    rw [hfun]
    exact hsq.const_mul _
  have hle : mgf X P lam
      ≤ ∫ ω, (1 + lam * X ω + (lam * X ω) ^ 2 / (2 * (1 - θ))) ∂P := by
    rw [mgf]
    exact integral_mono_ae hexpint hrhsint hpt
  have hval : ∫ ω, (1 + lam * X ω + (lam * X ω) ^ 2 / (2 * (1 - θ))) ∂P
      = 1 + lam ^ 2 * (∫ ω, X ω ^ 2 ∂P) / (2 * (1 - θ)) := by
    have h1 : ∀ ω, 1 + lam * X ω + (lam * X ω) ^ 2 / (2 * (1 - θ))
        = 1 + (lam * X ω + (lam ^ 2 / (2 * (1 - θ))) * X ω ^ 2) := by
      intro ω; ring
    simp_rw [h1]
    have e1 : ∫ ω, (1 + (lam * X ω + (lam ^ 2 / (2 * (1 - θ))) * X ω ^ 2)) ∂P
        = (∫ _ω, (1 : ℝ) ∂P)
          + ∫ ω, (lam * X ω + (lam ^ 2 / (2 * (1 - θ))) * X ω ^ 2) ∂P :=
      integral_add (integrable_const _)
        ((hint.const_mul lam).add (hsq.const_mul (lam ^ 2 / (2 * (1 - θ)))))
    have e2 : ∫ ω, (lam * X ω + (lam ^ 2 / (2 * (1 - θ))) * X ω ^ 2) ∂P
        = (∫ ω, lam * X ω ∂P) + ∫ ω, (lam ^ 2 / (2 * (1 - θ))) * X ω ^ 2 ∂P :=
      integral_add (hint.const_mul lam) (hsq.const_mul (lam ^ 2 / (2 * (1 - θ))))
    rw [e1, e2, integral_const_mul, integral_const_mul, hmean, integral_const]
    simp
    ring
  rw [hval] at hle
  refine hle.trans ?_
  have := Real.add_one_le_exp (lam ^ 2 * (∫ ω, X ω ^ 2 ∂P) / (2 * (1 - θ)))
  linarith


/-- The one-sided Bernstein inequality for a finite family of independent
centred variables bounded by `M`. -/
theorem bernstein_one_sided {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (hindep : iIndepFun Y P)
    (hint : ∀ i, Integrable (Y i) P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (M B : ℝ) (hM : 0 < M) (hB : 0 < B) (hb : ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M)
    (hB2 : B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P) (hsq : ∀ i, Integrable (fun ω => Y i ω ^ 2) P)
    (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ ∑ i, Y i ω}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))) := by
  classical
  set D : ℝ := B ^ 2 + M * t / 3 with hD
  have hDpos : (0 : ℝ) < D := by rw [hD]; positivity
  set lam : ℝ := t / D with hlamdef
  have hlampos : (0 : ℝ) < lam := by rw [hlamdef]; positivity
  have hlM : lam * M < 3 := by
    rw [hlamdef, div_mul_eq_mul_div, div_lt_iff₀ hDpos, hD]
    nlinarith [sq_nonneg B, hB, hM, ht]
  have hone : 1 - lam * M / 3 = B ^ 2 / D := by
    rw [hlamdef, hD]
    field_simp
    ring
  -- the sum
  set S : Ω → ℝ := fun ω => ∑ i, Y i ω with hS
  have hSint : Integrable S P := integrable_finsetSum _ fun i _ => hint i
  have hSb : ∀ᵐ ω ∂P, |S ω| ≤ (Fintype.card ι : ℝ) * M := by
    have hall : ∀ᵐ ω ∂P, ∀ i, |Y i ω| ≤ M := ae_all_iff.mpr hb
    filter_upwards [hall] with ω hω
    calc |S ω| ≤ ∑ i, |Y i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, M := Finset.sum_le_sum fun i _ => hω i
      _ = (Fintype.card ι : ℝ) * M := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hSexp : Integrable (fun ω => Real.exp (lam * S ω)) P := by
    refine Integrable.mono' (integrable_const (Real.exp (lam * ((Fintype.card ι : ℝ) * M))))
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable
        hSint.aestronglyMeasurable) ?_
    filter_upwards [hSb] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have h1 : S ω ≤ (Fintype.card ι : ℝ) * M := (abs_le.mp hω).2
    nlinarith
  -- the moment generating function of the sum
  have hmgfsum : mgf S P lam = ∏ i, mgf (Y i) P lam := by
    have h := hindep.mgf_sum₀ (t := lam) (fun i => (hint i).aemeasurable) Finset.univ
    have hfun : (∑ i ∈ Finset.univ, Y i) = S := by
      funext ω
      rw [hS]
      simp
    rwa [hfun] at h
  have hfac : ∀ i : ι, mgf (Y i) P lam
      ≤ Real.exp (lam ^ 2 * (∫ ω, Y i ω ^ 2 ∂P) / (2 * (B ^ 2 / D))) := by
    intro i
    have h := mgf_le_of_bounded P (Y i) (hint i) (hmean i) M (hb i) (hsq i) lam hlampos hlM
    rwa [hone] at h
  have hmgfnn : ∀ i : ι, 0 ≤ mgf (Y i) P lam := by
    intro i
    rw [mgf]
    exact integral_nonneg fun ω => (Real.exp_pos _).le
  have hprod : ∏ i, mgf (Y i) P lam
      ≤ Real.exp (lam ^ 2 * B ^ 2 / (2 * (B ^ 2 / D))) := by
    have h1 : ∏ i, mgf (Y i) P lam
        ≤ ∏ i : ι, Real.exp (lam ^ 2 * (∫ ω, Y i ω ^ 2 ∂P) / (2 * (B ^ 2 / D))) :=
      Finset.prod_le_prod (fun i _ => hmgfnn i) (fun i _ => hfac i)
    refine h1.trans (le_of_eq ?_)
    rw [← Real.exp_sum]
    congr 1
    rw [hB2, Finset.sum_div, ← Finset.sum_div]
    congr 1
    rw [Finset.mul_sum]
  have hmgfle : mgf S P lam ≤ Real.exp (lam ^ 2 * B ^ 2 / (2 * (B ^ 2 / D))) := by
    rw [hmgfsum]; exact hprod
  -- Chernoff
  have hchern := measure_ge_le_exp_mul_mgf (μ := P) (X := S) (t := lam) t hlampos.le hSexp
  have hexpnn : (0 : ℝ) ≤ Real.exp (-lam * t) := (Real.exp_pos _).le
  have hstep : P.real {ω | t ≤ S ω}
      ≤ Real.exp (-lam * t) * Real.exp (lam ^ 2 * B ^ 2 / (2 * (B ^ 2 / D))) := by
    refine hchern.trans ?_
    exact mul_le_mul_of_nonneg_left hmgfle hexpnn
  have hval : Real.exp (-lam * t) * Real.exp (lam ^ 2 * B ^ 2 / (2 * (B ^ 2 / D)))
      = Real.exp (-(t ^ 2 / 2) / D) := by
    rw [← Real.exp_add]
    congr 1
    rw [hlamdef]
    have hB2ne : (B : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hval] at hstep
  have hfin : P {ω | t ≤ S ω} ≠ ⊤ := measure_ne_top P _
  rw [measureReal_def, ← ENNReal.le_ofReal_iff_toReal_le hfin (Real.exp_pos _).le] at hstep
  exact hstep


/-- **Bernstein's inequality.**  For a finite family of independent centred
random variables bounded by `M` with total variance `B²`,

    P(|∑ Y_i| ≥ t) ≤ 2 exp(-(t²/2)/(B² + Mt/3)) .
-/
theorem bernstein {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (hindep : iIndepFun Y P)
    (hint : ∀ i, Integrable (Y i) P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (M B : ℝ) (hM : 0 < M) (hB : 0 < B) (hb : ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M)
    (hB2 : B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P) (hsq : ∀ i, Integrable (fun ω => Y i ω ^ 2) P)
    (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ |∑ i, Y i ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))) := by
  classical
  have hneg : iIndepFun (fun i => -Y i) P := by
    have h := hindep.comp (fun _ : ι => fun x : ℝ => -x) (fun _ => measurable_neg)
    exact h
  have hnegint : ∀ i, Integrable ((fun i => -Y i) i) P := fun i => (hint i).neg
  have hnegmean : ∀ i, ∫ ω, (-Y i) ω ∂P = 0 := by
    intro i
    show ∫ ω, -(Y i ω) ∂P = 0
    rw [integral_neg, hmean i, neg_zero]
  have hnegb : ∀ i, ∀ᵐ ω ∂P, |(-Y i) ω| ≤ M := by
    intro i
    filter_upwards [hb i] with ω hω
    show |-(Y i ω)| ≤ M
    rwa [abs_neg]
  have hnegB2 : B ^ 2 = ∑ i, ∫ ω, ((-Y i) ω) ^ 2 ∂P := by
    rw [hB2]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show (Y i ω) ^ 2 = (-(Y i ω)) ^ 2
    ring
  have hnegsq : ∀ i, Integrable (fun ω => ((-Y i) ω) ^ 2) P := by
    intro i
    have : (fun ω => ((-Y i) ω) ^ 2) = fun ω => (Y i ω) ^ 2 := by
      funext ω
      show (-(Y i ω)) ^ 2 = (Y i ω) ^ 2
      ring
    rw [this]
    exact hsq i
  have h1 := bernstein_one_sided P Y hindep hint hmean M B hM hB hb hB2 hsq t ht
  have h2 := bernstein_one_sided P (fun i => -Y i) hneg hnegint hnegmean M B hM hB hnegb
    hnegB2 hnegsq t ht
  have hsub : {ω | t ≤ |∑ i, Y i ω|}
      ⊆ {ω | t ≤ ∑ i, Y i ω} ∪ {ω | t ≤ ∑ i, (-Y i) ω} := by
    intro ω hω
    have hω' : t ≤ |∑ i, Y i ω| := hω
    have hsumneg : ∑ i, (-Y i) ω = -∑ i, Y i ω := by
      show ∑ i, -(Y i ω) = -∑ i, Y i ω
      rw [Finset.sum_neg_distrib]
    rcases abs_cases (∑ i, Y i ω) with ⟨he, _⟩ | ⟨he, _⟩
    · exact Or.inl (by rw [he] at hω'; exact hω')
    · refine Or.inr ?_
      show t ≤ ∑ i, (-Y i) ω
      rw [hsumneg, ← he]
      exact hω'
  calc P {ω | t ≤ |∑ i, Y i ω|}
      ≤ P ({ω | t ≤ ∑ i, Y i ω} ∪ {ω | t ≤ ∑ i, (-Y i) ω}) := measure_mono hsub
    _ ≤ P {ω | t ≤ ∑ i, Y i ω} + P {ω | t ≤ ∑ i, (-Y i) ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3)))
        + ENNReal.ofReal (Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        ring_nf

end LatticeProb
