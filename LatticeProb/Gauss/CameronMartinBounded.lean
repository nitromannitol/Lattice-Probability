import Mathlib
import LatticeProb.Prob.CameronMartin
import LatticeProb.Gauss.CameronMartinLimitShift
import LatticeProb.Gauss.GaussianSpaceShift

/-!
# Cameron–Martin shifts by bounded functionals

Let `Y : T → Ω → ℝ` be a centred Gaussian process and `m : T → ℝ`.  Suppose that `m` is bounded by
the standard deviation on finite linear combinations,
`|∑ σ_t m_t| ≤ C (E (∑ σ_t Y_t)²)^{1/2}`  (that is, `m` lies in the Cameron–Martin space of `Y`).
Then every measurable set of paths which is null for `Y` is null for the shifted process `Y + m`.

Proof: the quadratic functional `J(σ) = N(σ)/2 - ∑ σ_t m_t`, `N(σ) = E (∑ σ_t Y_t)²`, is bounded
below by `-C²/2`.  A minimizing sequence `σ_n` is Cauchy for `N` by the parallelogram law, and the
first variation at `σ_n` in the direction of `δ_t` shows `Cov(Y_t, ∑ σ_n Y) → m_t`.  The covariance-limit
form of the Cameron–Martin theorem then applies.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace LatticeProb.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : Type*} {Y : T → Ω → ℝ}

section Aux

theorem integral_sq_add_eq [IsProbabilityMeasure P] {f g : Ω → ℝ} (hf : MemLp f 2 P)
    (hg : MemLp g 2 P) :
    ∫ ω, (f ω + g ω) ^ 2 ∂P = ∫ ω, f ω ^ 2 ∂P + 2 * ∫ ω, f ω * g ω ∂P + ∫ ω, g ω ^ 2 ∂P := by
  have h1 : Integrable (fun ω => f ω ^ 2) P := hf.integrable_sq
  have h2 : Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg
  have h3 : Integrable (fun ω => g ω ^ 2) P := hg.integrable_sq
  calc ∫ ω, (f ω + g ω) ^ 2 ∂P = ∫ ω, (f ω ^ 2 + 2 * (f ω * g ω) + g ω ^ 2) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        ring
    _ = _ := by
        have key : Integrable (fun ω => f ω ^ 2 + 2 * (f ω * g ω)) P := h1.add (h2.const_mul 2)
        rw [integral_add key h3, integral_add h1 (h2.const_mul 2), integral_const_mul]

theorem integral_sq_sub_eq [IsProbabilityMeasure P] {f g : Ω → ℝ} (hf : MemLp f 2 P)
    (hg : MemLp g 2 P) :
    ∫ ω, (f ω - g ω) ^ 2 ∂P = ∫ ω, f ω ^ 2 ∂P - 2 * ∫ ω, f ω * g ω ∂P + ∫ ω, g ω ^ 2 ∂P := by
  have h1 : Integrable (fun ω => f ω ^ 2) P := hf.integrable_sq
  have h2 : Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg
  have h3 : Integrable (fun ω => g ω ^ 2) P := hg.integrable_sq
  calc ∫ ω, (f ω - g ω) ^ 2 ∂P = ∫ ω, (f ω ^ 2 - 2 * (f ω * g ω) + g ω ^ 2) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        ring
    _ = _ := by
        have key : Integrable (fun ω => f ω ^ 2 - 2 * (f ω * g ω)) P := h1.sub (h2.const_mul 2)
        rw [integral_add key h3, integral_sub h1 (h2.const_mul 2), integral_const_mul]

end Aux

/-- **Cameron–Martin shift by a bounded functional.** If `m` is bounded by the standard deviation on
finite linear combinations of a centred Gaussian process `Y`, every measurable set of paths that is
null for `Y` is null for `Y + m`. -/
theorem measure_add_eq_zero_of_abs_comb_le [IsProbabilityMeasure P] (hY : IsGaussianProcess Y P)
    (hYm : ∀ t, Measurable (Y t)) (hcen : ∀ t, P[Y t] = 0) (m : T → ℝ) {C : ℝ}
    (hb : ∀ σ : T →₀ ℝ, |∑ t ∈ σ.support, σ t * m t| ≤
      C * Real.sqrt (∫ ω, (∑ t ∈ σ.support, σ t * Y t ω) ^ 2 ∂P))
    {S : Set (T → ℝ)} (hS : MeasurableSet S) (h0 : P {ω | (fun t => Y t ω) ∈ S} = 0) :
    P {ω | (fun t => Y t ω + m t) ∈ S} = 0 := by
  classical
  -- the linear maps `σ ↦ ∑ σ_t Y_t` and `σ ↦ ∑ σ_t m_t`
  set Z : (T →₀ ℝ) →ₗ[ℝ] (Ω → ℝ) := Finsupp.linearCombination ℝ Y with hZdef
  set Λ : (T →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.linearCombination ℝ m with hΛdef
  have hZ : ∀ σ ω, Z σ ω = ∑ t ∈ σ.support, σ t * Y t ω := fun σ ω => by
    simp [hZdef, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
  have hΛ : ∀ σ, Λ σ = ∑ t ∈ σ.support, σ t * m t := fun σ => by
    simp [hΛdef, Finsupp.linearCombination_apply, Finsupp.sum]
  have hZL2 : ∀ σ, MemLp (Z σ) 2 P := fun σ => by
    have h := (LatticeProb.CameronMartin.hasGaussianLaw_finsetComb hY σ.support σ).memLp_two
    have : Z σ = fun ω => ∑ t ∈ σ.support, σ t * Y t ω := funext (hZ σ)
    rw [this]
    exact h
  have hYL2 : ∀ t, MemLp (Y t) 2 P := fun t => (hY.hasGaussianLaw_eval t).memLp_two
  set N : (T →₀ ℝ) → ℝ := fun σ => ∫ ω, (Z σ ω) ^ 2 ∂P with hNdef
  have hN0 : ∀ σ, 0 ≤ N σ := fun σ => integral_nonneg fun ω => sq_nonneg _
  have hb' : ∀ σ, |Λ σ| ≤ C * Real.sqrt (N σ) := fun σ => by
    rw [hΛ]
    have : N σ = ∫ ω, (∑ t ∈ σ.support, σ t * Y t ω) ^ 2 ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hZ])
    rw [this]
    exact hb σ
  -- the functional `J`
  set J : (T →₀ ℝ) → ℝ := fun σ => N σ / 2 - Λ σ with hJdef
  have hJlow : ∀ σ, -(C ^ 2 / 2) ≤ J σ := fun σ => by
    have h1 := hb' σ
    have h2 := Real.sq_sqrt (hN0 σ)
    have h3 := le_abs_self (Λ σ)
    have h4 : -(Λ σ) ≤ |Λ σ| := neg_le_abs _
    have hC : 0 ≤ Real.sqrt (N σ) := Real.sqrt_nonneg _
    simp only [hJdef]
    nlinarith [sq_nonneg (Real.sqrt (N σ) - C)]
  have hbdd : BddBelow (Set.range J) := ⟨-(C ^ 2 / 2), by rintro _ ⟨σ, rfl⟩; exact hJlow σ⟩
  set Jst : ℝ := ⨅ σ, J σ with hJst
  have hJst_le : ∀ σ, Jst ≤ J σ := fun σ => ciInf_le hbdd σ
  have hex : ∀ n : ℕ, ∃ σ, J σ < Jst + 1 / ((n : ℝ) + 1) := fun n =>
    exists_lt_of_ciInf_lt (by linarith [one_div_pos.2 (by positivity : (0 : ℝ) < (n : ℝ) + 1)])
  choose σs hσs using hex
  -- Cauchy property
  have hpar : ∀ a b : T →₀ ℝ, N (a - b) = 4 * (J a + J b - 2 * J ((1 / 2 : ℝ) • (a + b))) := by
    intro a b
    have hs : Z (a + b) = fun ω => Z a ω + Z b ω := by
      funext ω; simp [map_add]
    have hd : Z (a - b) = fun ω => Z a ω - Z b ω := by
      funext ω; simp [map_sub]
    have hsum : N (a + b) = N a + 2 * ∫ ω, Z a ω * Z b ω ∂P + N b := by
      simp only [hNdef, hs]
      exact integral_sq_add_eq (hZL2 a) (hZL2 b)
    have hdif : N (a - b) = N a - 2 * ∫ ω, Z a ω * Z b ω ∂P + N b := by
      simp only [hNdef, hd]
      exact integral_sq_sub_eq (hZL2 a) (hZL2 b)
    have hrho : N ((1 / 2 : ℝ) • (a + b)) = N (a + b) / 4 := by
      simp only [hNdef, map_smul, Pi.smul_apply, smul_eq_mul]
      rw [← integral_div]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      ring
    have hl : Λ ((1 / 2 : ℝ) • (a + b)) = (Λ a + Λ b) / 2 := by
      simp [map_smul, map_add]; ring
    simp only [hJdef, hrho, hl]
    rw [hdif, hsum]
    ring
  have hcauchy : ∀ ε > 0, ∃ N0 : ℕ, ∀ n ≥ N0, ∀ k ≥ N0,
      ∫ ω, (Z (σs n) ω - Z (σs k) ω) ^ 2 ∂P < ε := by
    intro ε hε
    obtain ⟨N0, hN0'⟩ := exists_nat_gt (8 / ε)
    refine ⟨N0, fun n hn k hk => ?_⟩
    have hd : (fun ω => Z (σs n) ω - Z (σs k) ω) = Z (σs n - σs k) := by
      funext ω; simp [map_sub]
    have e1 : ∫ ω, (Z (σs n) ω - Z (σs k) ω) ^ 2 ∂P = N (σs n - σs k) := by
      simp only [hNdef, ← hd]
    rw [e1, hpar]
    have h1 := hσs n
    have h2 := hσs k
    have h3 := hJst_le ((1 / 2 : ℝ) • (σs n + σs k))
    have hn' : 1 / ((n : ℝ) + 1) ≤ 1 / ((N0 : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    have hk' : 1 / ((k : ℝ) + 1) ≤ 1 / ((N0 : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    have hlt : 8 / ((N0 : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hN0'
      nlinarith
    have : 4 * (1 / ((N0 : ℝ) + 1)) * 2 = 8 / ((N0 : ℝ) + 1) := by ring
    nlinarith
  -- convergence of the covariances
  have hcov : ∀ t, Tendsto (fun n => cov[Y t, Z (σs n); P]) atTop (𝓝 (m t)) := by
    intro t
    set K : ℝ := ∫ ω, Y t ω ^ 2 ∂P with hK
    have hK0 : 0 ≤ K := integral_nonneg fun ω => sq_nonneg _
    have hcovB : ∀ n, cov[Y t, Z (σs n); P] = ∫ ω, Y t ω * Z (σs n) ω ∂P := fun n => by
      rw [covariance_eq_sub (hYL2 t) (hZL2 _)]
      have e : P[Z (σs n)] = 0 := by
        have h := LatticeProb.CameronMartin.integral_finsetComb hY hcen (σs n).support (σs n)
        have : Z (σs n) = fun ω => ∑ t ∈ (σs n).support, (σs n) t * Y t ω := funext (hZ _)
        rw [this]
        exact h
      rw [e, hcen t]
      simp
    set s : ℕ → ℝ := fun n => Real.sqrt (1 / ((n : ℝ) + 1)) with hs
    have hspos : ∀ n, 0 < s n := fun n => Real.sqrt_pos.2 (by positivity)
    have hs2 : ∀ n, s n ^ 2 = 1 / ((n : ℝ) + 1) := fun n => Real.sq_sqrt (by positivity)
    have hsl : Tendsto s atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      rw [Real.sqrt_zero] at h
      exact h
    have hbound : ∀ n, |cov[Y t, Z (σs n); P] - m t| ≤ (1 + K / 2) * s n := by
      intro n
      set B : ℝ := cov[Y t, Z (σs n); P] with hB
      have hvar : ∀ ε : ℝ, J (σs n + ε • Finsupp.single t 1) =
          J (σs n) + ε * (B - m t) + ε ^ 2 * K / 2 := by
        intro ε
        have hzs : Z (σs n + ε • Finsupp.single t 1) = fun ω => Z (σs n) ω + ε * Y t ω := by
          funext ω; simp [map_add, hZdef, Finsupp.linearCombination_single]
        have hN : N (σs n + ε • Finsupp.single t 1) =
            N (σs n) + 2 * (ε * ∫ ω, Z (σs n) ω * Y t ω ∂P) + ε ^ 2 * K := by
          simp only [hNdef, hzs]
          rw [integral_sq_add_eq (hZL2 _) ((hYL2 t).const_mul ε)]
          have e1 : ∫ ω, (ε * Y t ω) ^ 2 ∂P = ε ^ 2 * K := by
            rw [hK, ← integral_const_mul]
            exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
          have e2 : ∫ ω, Z (σs n) ω * (ε * Y t ω) ∂P = ε * ∫ ω, Z (σs n) ω * Y t ω ∂P := by
            rw [← integral_const_mul]
            exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
          rw [e1, e2]
        have hB' : ∫ ω, Z (σs n) ω * Y t ω ∂P = B := by
          rw [hB, hcovB]
          exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
        have hl : Λ (σs n + ε • Finsupp.single t 1) = Λ (σs n) + ε * m t := by
          simp [map_add, hΛdef, Finsupp.linearCombination_single]
        simp only [hJdef, hN, hl, hB']
        ring
      have hlow : ∀ ε : ℝ, J (σs n) - 1 / ((n : ℝ) + 1) < J (σs n) + ε * (B - m t) + ε ^ 2 * K / 2 :=
        fun ε => by
          have h1 := hσs n
          have h2 := hJst_le (σs n + ε • Finsupp.single t 1)
          rw [hvar] at h2
          linarith
      have hp := hlow (s n)
      have hm := hlow (-(s n))
      have hspos' := hspos n
      have hs2' := hs2 n
      rw [abs_le]
      constructor
      · -- from `ε = s`
        nlinarith [mul_pos hspos' hspos']
      · nlinarith [mul_pos hspos' hspos']
    have hlim : Tendsto (fun n => (1 + K / 2) * s n) atTop (𝓝 0) := by
      simpa using hsl.const_mul (1 + K / 2)
    have : Tendsto (fun n => cov[Y t, Z (σs n); P] - m t) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by simpa [Real.norm_eq_abs] using hbound n) hlim
    simpa using this.add_const (m t)
  -- conclusion
  have hM := isCentredGaussianSpace_span_range hY hYm hcen
  refine measure_add_eq_zero_of_tendsto_covariance_of_cauchy hM (R := Y) (ζ := fun n => Z (σs n))
    (fun t => Submodule.subset_span ⟨t, rfl⟩) (fun n => ?_) hcauchy (c := m) hcov hS h0
  exact (Finsupp.mem_span_range_iff_exists_finsupp).2 ⟨σs n, by
    funext ω; simp [hZdef, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]⟩

end LatticeProb.Gauss
