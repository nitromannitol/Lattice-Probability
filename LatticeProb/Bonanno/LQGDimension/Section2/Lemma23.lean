/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Section2.Lemma23 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Section2.Lemma23Aux

/-!
# Lemma 2.3: a finite near-optimal family

We prove `Blueprint.Lemma23` from `MaxConcentration` (Gaussian concentration for finite
maxima), `ZSupBound` ((2.2)) and `ZVarBound` ((2.3)).  The hypotheses `AOneFinite` and
`ASubadditiveE` are not needed: when `a_n` is not finite, `a n = 0` and the empty family
already gives `a n - 1/4 ≤ 0`.

## Proof

Fix `n` large, `M = 16ⁿ`, `K = 8 C²` (with `C` the constant of (2.2)) and `η = M⁻³`.
Start from a finite `F₀ ⊆ V_n` with `E max_{F₀} (Z_f - E(f)) ≥ a_n - 1/4`.  Split
`F₀ = L ∪ H` with `L = {E(f) ≤ K n}`.  Let `R f` be the linear interpolation of the mesh values
of `f` rounded to `η ℤ`, and `F = {0} ∪ R(L)`.  Realise `Z` on `F₀ ∪ F` by Gram vectors.
Pointwise,

`max_{F₀} (Z_f - E(f)) ≤ max_F (Z_g - E(g)) + T + W + ε`,

where
* `T = ∑_j (max_{S_j} Z - 2^j K n)⁺` over the energy shells `S_j` of `H` (`high_part`):
  by (2.2), (2.3) and concentration, `E T ≤ ∑_j exp(-2^j K n / 2) ≤ 1/4`;
* `W = max_c max_{f ∈ cell c} (Z_f - Z_c)` over the rounding cells `c ∈ R(L)` (`low_part`):
  within a cell `Var (Z_f - Z_c) ≤ π η`, and `(Z_f - Z_c)_f` has the law of `(Z_{f-c})_f`, so
  (2.2) bounds its mean by `C n / M`; with the number of cells `≤ (M⁵)^M` and concentration,
  `E W ≤ 5 n log 16 / M + C n / M + π³ / (8M) ≤ 1/4`;
* `ε ≥ E(R f) - E(f)` is the energy change of rounding, `≤ 1/4`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.L23

/-- (2.2) in finite-subfamily form, with an explicit constant. -/
def ZSup (CS : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ R : ℝ, 0 < R → ∀ F : Finset (V n), (∀ f ∈ F, energy f ≤ R) →
    gaussianExpectedMax F (fun f g => zCov f g) 0 ≤
      CS * (n : ℝ) ^ (3 / 4 : ℝ) * R ^ (1 / 4 : ℝ)

section Parts

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **High energies.**  The contribution of the functions with `E(f) > K n`. -/
theorem high_part (hC : Blueprint.MaxConcentration) {CS CV K : ℝ} (hCS1 : 1 ≤ CS)
    (hCV0 : 0 ≤ CV) (hZS : ZSup CS)
    (hZV : ∀ n : ℕ, ∀ f ∈ V n, zCov f f ≤ CV * Real.sqrt (energy f)) (hK : K = 8 * CS ^ 2)
    {n : ℕ} (hn14 : 14 ≤ n) (hnV : π ^ 4 * CV ^ 2 / 2 ≤ n)
    (G : Finset (V n)) (v : V n → E) (hv : ∀ f ∈ G, ∀ g ∈ G, ⟪v f, v g⟫ = zCov f g)
    (H : Finset (V n)) (hHG : H ⊆ G) (hH : ∀ f ∈ H, K * n < energy f) :
    ∃ T : E → ℝ, Integrable T (stdGaussian E) ∧ (∀ x, 0 ≤ T x) ∧
      ∫ x, T x ∂(stdGaussian E) ≤ 1 / 4 ∧ ∀ f ∈ H, ∀ x, ⟪v f, x⟫ - energy f ≤ T x := by
  classical
  have hK1 : 1 ≤ K := by rw [hK]; nlinarith
  have hK0 : 0 < K := by linarith
  have hCS0 : 0 < CS := by linarith
  have hn1 : 1 ≤ n := by omega
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hKn : 0 < K * n := by positivity
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt ((∑ f ∈ H, |energy f|) / (K * n))
    (by norm_num : (1 : ℝ) < 2)
  set S : ℕ → Finset (V n) := fun j => H.filter
    (fun f => 2 ^ j * (K * n) ≤ energy f ∧ energy f < 2 ^ (j + 1) * (K * n)) with hSdef
  have hSG : ∀ j, S j ⊆ G := fun j => (Finset.filter_subset _ _).trans hHG
  have hint : ∀ j, Integrable (fun x => max ((⨆ f : S j, ⟪v f, x⟫) - 2 ^ j * (K * n)) 0)
      (stdGaussian E) := fun j =>
    ((integrable_fsup_inner (S j) v).sub (integrable_const _)).pos_part
  have shell : ∀ j : ℕ, ∫ x, max ((⨆ f : S j, ⟪v f, x⟫) - 2 ^ j * (K * n)) 0
      ∂(stdGaussian E) ≤ Real.exp (-(2 ^ j * (K * n)) / 2) := by
    intro j
    have hj1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    set u : ℝ := 2 ^ j * (K * n) with hu
    have hnu : (n : ℝ) ≤ u := by
      calc (n : ℝ) = 1 * (1 * n) := by ring
        _ ≤ 2 ^ j * (K * n) := by gcongr
    have hσ : ∀ f ∈ S j, ‖v f‖ ≤ Real.sqrt (CV * Real.sqrt (2 * u)) := by
      intro f hf
      have hfS := (Finset.mem_filter.1 hf).2
      have hfG := hSG j hf
      apply Real.le_sqrt_of_sq_le
      rw [← real_inner_self_eq_norm_sq, hv f hfG f hfG]
      have h2u : energy f ≤ 2 * u := by
        have := hfS.2
        rw [pow_succ] at this
        linarith [hu]
      calc zCov f f ≤ CV * Real.sqrt (energy f) := hZV n f f.2
        _ ≤ CV * Real.sqrt (2 * u) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2u) hCV0
    have hconc := integral_max_sub_zero_le hC (S j) v hσ u
    have hmean : vecExpectedMax (S j) v (fun _ => 0) ≤ u / 4 := by
      rw [← gEM_eq_vec (hSG j) v hv]
      have hA0 : 0 < 2 ^ j * K / (4 * CS) := by positivity
      have hR : 0 < (2 ^ j * K / (4 * CS)) ^ 4 * n := mul_pos (pow_pos hA0 4) hn0
      have hen : ∀ f ∈ S j, energy f ≤ (2 ^ j * K / (4 * CS)) ^ 4 * n := by
        intro f hf
        have := (Finset.mem_filter.1 hf).2.2
        have h2 := shell_energy_le hCS1 hK j (Nat.cast_nonneg n)
        linarith
      have h := hZS n hn1 _ hR (S j) hen
      rw [mul_assoc CS, rpow_aux (Nat.cast_nonneg n) hA0.le] at h
      calc _ ≤ CS * (2 ^ j * K / (4 * CS) * n) := h
        _ = u / 4 := by
          rw [hu]
          field_simp
    have hσ2 : Real.sqrt (CV * Real.sqrt (2 * u)) ^ 2 = CV * Real.sqrt (2 * u) :=
      Real.sq_sqrt (by positivity)
    refine hconc.trans (Real.exp_le_exp.2 ?_)
    rw [hσ2]
    have hvar := var_bound hCV0 (hnV.trans hnu)
    linarith
  refine ⟨fun x => ∑ j ∈ Finset.range J, max ((⨆ f : S j, ⟪v f, x⟫) - 2 ^ j * (K * n)) 0,
    integrable_finsetSum _ fun j _ => hint j,
    fun x => Finset.sum_nonneg fun j _ => le_max_right _ _, ?_, ?_⟩
  · rw [integral_finsetSum _ fun j _ => hint j]
    exact (Finset.sum_le_sum fun j _ => shell j).trans (sum_exp_le hK1 hn14 J)
  · intro f hf x
    have hE := hH f hf
    have hx1 : 1 ≤ energy f / (K * n) := by
      rw [le_div_iff₀ hKn]
      linarith
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2)
    have hjJ : j < J := by
      have h1 : energy f / (K * n) ≤ (∑ g ∈ H, |energy g|) / (K * n) := by
        apply div_le_div_of_nonneg_right _ hKn.le
        exact (le_abs_self _).trans (Finset.single_le_sum (f := fun g : V n => |energy g|)
          (fun g _ => abs_nonneg _) hf)
      have h2 : (2 : ℝ) ^ j < 2 ^ J := lt_of_le_of_lt hj1 (lt_of_le_of_lt h1 hJ)
      exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h2
    have hfS : f ∈ S j := by
      rw [Finset.mem_filter]
      refine ⟨hf, ?_, ?_⟩
      · rw [le_div_iff₀ hKn] at hj1
        exact hj1
      · rw [div_lt_iff₀ hKn] at hj2
        exact hj2
    have h1 : ⟪v f, x⟫ ≤ ⨆ g : S j, ⟪v g, x⟫ := le_fsup (fun g => ⟪v g, x⟫) hfS
    have h2 : 2 ^ j * (K * n) ≤ energy f := (Finset.mem_filter.1 hfS).2.1
    calc ⟪v f, x⟫ - energy f ≤ max ((⨆ g : S j, ⟪v g, x⟫) - 2 ^ j * (K * n)) 0 :=
          le_max_of_le_left (by linarith)
      _ ≤ ∑ j ∈ Finset.range J, max ((⨆ f : S j, ⟪v f, x⟫) - 2 ^ j * (K * n)) 0 :=
          Finset.single_le_sum
            (f := fun j => max ((⨆ g : S j, ⟪v g, x⟫) - 2 ^ j * (K * n)) 0)
            (fun j _ => le_max_right _ _) (Finset.mem_range.2 hjJ)

/-- **Low energies.**  The rounding error `Z_f - Z_{R f}`, maximised over the cells. -/
theorem low_part (hC : Blueprint.MaxConcentration) {CS : ℝ} (hCS1 : 1 ≤ CS) (hZS : ZSup CS)
    {n : ℕ} [DecidableEq (V n)] (hn1 : 1 ≤ n) (G : Finset (V n)) (v : V n → E)
    (hv : ∀ f ∈ G, ∀ g ∈ G, ⟪v f, v g⟫ = zCov f g) (L : Finset (V n)) (hLG : L ⊆ G)
    {η : ℝ} (hηdef : η = 1 / ((16 : ℝ) ^ n) ^ 3)
    (hRG : ∀ f ∈ L, roundV η f ∈ G) {N : ℝ} (hN1 : 1 ≤ N)
    (hN : ((L.image (roundV η)).card : ℝ) ≤ N)
    (hsmall : Real.log N / ((16 : ℝ) ^ n) ^ 2 + CS * n / 16 ^ n + π ^ 3 / (8 * 16 ^ n) ≤
      1 / 4) :
    ∃ W : E → ℝ, Integrable W (stdGaussian E) ∧ (∀ x, 0 ≤ W x) ∧
      ∫ x, W x ∂(stdGaussian E) ≤ 1 / 4 ∧
      ∀ f ∈ L, ∀ x, ⟪v f - v (roundV η f), x⟫ ≤ W x := by
  classical
  have hM1 : (1 : ℝ) ≤ (16 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hM0 : (0 : ℝ) < (16 : ℝ) ^ n := by positivity
  have hη : 0 < η := by rw [hηdef]; positivity
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hCS0 : 0 < CS := by linarith
  set C := L.image (roundV η) with hCdef
  set cell : V n → Finset (V n) := fun c => insert c (L.filter (fun f => roundV η f = c))
    with hcelldef
  have hCG : ∀ c ∈ C, c ∈ G := by
    intro c hc
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hc
    exact hRG f hf
  have hcellG : ∀ c ∈ C, ∀ f ∈ cell c, f ∈ G := by
    intro c hc f hf
    rcases Finset.mem_insert.1 hf with rfl | hf
    · exact hCG f hc
    · exact hLG (Finset.mem_filter.1 hf).1
  have hnode : ∀ c ∈ C, ∀ f ∈ cell c, ∀ k : ℕ, k ≤ 16 ^ n →
      |(f : ℝ → ℝ) ((k : ℝ) / 16 ^ n) - (c : ℝ → ℝ) ((k : ℝ) / 16 ^ n)| ≤ η / 2 := by
    intro c hc f hf k hk
    rcases Finset.mem_insert.1 hf with rfl | hf
    · rw [sub_self, abs_zero]
      positivity
    · obtain ⟨-, rfl⟩ := Finset.mem_filter.1 hf
      rw [abs_sub_comm]
      exact roundV_node_err hη f hk
  have hclose : ∀ c ∈ C, ∀ f ∈ cell c, ∀ x, |(f : ℝ → ℝ) x - (c : ℝ → ℝ) x| ≤ η / 2 := by
    intro c hc f hf x
    have := abs_le_of_nodes (V_sub f.2 c.2) (by positivity) (hnode c hc f hf) x
    simpa only [Pi.sub_apply] using this
  have hnorm : ∀ c ∈ C, ∀ f ∈ cell c, ‖v f - v c‖ ≤ Real.sqrt (π * η) := by
    intro c hc f hf
    apply Real.le_sqrt_of_sq_le
    have hfG := hcellG c hc f hf
    have hcG := hCG c hc
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      hv f hfG f hfG, hv c hcG c hcG, hv f hfG c hcG]
    have hd := zCov_dist (mem_V_intervalIntegrable f.2) (mem_V_intervalIntegrable c.2)
    have hint : ∫ x in (0 : ℝ)..1, |(f : ℝ → ℝ) x - (c : ℝ → ℝ) x| ≤ η / 2 := by
      have := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
        (((Subadd.V_continuous f.2).sub (Subadd.V_continuous c.2)).abs.intervalIntegrable 0 1)
        (continuous_const.intervalIntegrable 0 1) (fun x _ => hclose c hc f hf x)
      simpa using this
    nlinarith [mul_le_mul_of_nonneg_left hint Real.pi_pos.le]
  have hmean : ∀ c ∈ C, vecExpectedMax (cell c) (fun f => v f - v c) (fun _ => 0) ≤
      CS * n / 16 ^ n := by
    intro c hc
    have hcG := hCG c hc
    obtain ⟨u, hu, hgem⟩ := exists_vecExpectedMax_eq_gaussianExpectedMax
      ((cell c).image (subV c)) (fun f g => zCov f g) (zCovPSD_V n _)
    have hR : (0 : ℝ) < (1 / (16 : ℝ) ^ n) ^ 4 * n := mul_pos (by positivity) hn0
    have henergy : ∀ g ∈ (cell c).image (subV c), energy g ≤ (1 / (16 : ℝ) ^ n) ^ 4 * n := by
      intro g hg
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
      have h1 := energy_le_of_nodes (V_sub f.2 c.2) (δ := η / 2)
        (fun k hk => by simpa only [Pi.sub_apply] using hnode c hc f hf k hk)
      have h2 : 2 * ((16 : ℝ) ^ n) ^ 2 * (η / 2) ^ 2 = (1 / (16 : ℝ) ^ n) ^ 4 * (1 / 2) := by
        rw [hηdef]
        field_simp
      have h3 : (1 / (16 : ℝ) ^ n) ^ 4 * (1 / 2) ≤ (1 / (16 : ℝ) ^ n) ^ 4 * n :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      calc energy ((subV c f : V n) : ℝ → ℝ) = energy ((f : ℝ → ℝ) - c) := rfl
        _ ≤ _ := h1
        _ ≤ _ := by rw [h2]; exact h3
    have h1 := hZS n hn1 _ hR _ henergy
    rw [mul_assoc CS, rpow_aux (x := (n : ℝ)) (A := 1 / (16 : ℝ) ^ n) (Nat.cast_nonneg _)
      (by positivity)] at h1
    have h2 : gaussianExpectedMax ((cell c).image (subV c)) (fun f g => zCov f g) 0 =
        vecExpectedMax (cell c) (fun f => u (subV c f)) (fun _ => 0) := by
      rw [hgem]
      exact vecExpectedMax_image (cell c) (subV c) u 0
    have h3 : vecExpectedMax (cell c) (fun f => u (subV c f)) (fun _ => 0) =
        vecExpectedMax (cell c) (fun f => v f - v c) (fun _ => 0) := by
      apply vecExpectedMax_eq_of_gram_eq
      intro f hf g hg
      show ⟪u (subV c f), u (subV c g)⟫ = ⟪v f - v c, v g - v c⟫
      have hf' : subV c f ∈ (cell c).image (subV c) := Finset.mem_image_of_mem _ hf
      have hg' : subV c g ∈ (cell c).image (subV c) := Finset.mem_image_of_mem _ hg
      rw [hu _ hf' _ hg']
      have hfG := hcellG c hc f hf
      have hgG := hcellG c hc g hg
      rw [inner_sub_left, inner_sub_right, inner_sub_right, hv f hfG g hgG, hv f hfG c hcG,
        hv c hcG g hgG, hv c hcG c hcG]
      have key := zCov_sub_sub (mem_V_intervalIntegrable f.2) (mem_V_intervalIntegrable g.2)
        (mem_V_intervalIntegrable c.2)
      show zCov ((f : ℝ → ℝ) - c) ((g : ℝ → ℝ) - c) = _
      rw [key]
      ring
    rw [← h3, ← h2]
    calc _ ≤ CS * (1 / (16 : ℝ) ^ n * n) := h1
      _ = CS * n / 16 ^ n := by field_simp
  have hB0 : 0 ≤ CS * n / (16 : ℝ) ^ n :=
    div_nonneg (mul_nonneg hCS0.le (Nat.cast_nonneg n)) (by positivity)
  have hmain := integral_fsup_fsup_le hC C cell (fun c f => v f - v c)
    (σ := Real.sqrt (π * η)) (t := ((16 : ℝ) ^ n) ^ 2) (by positivity) hB0 hnorm hmean
  have hcell0 : ∀ x, ∀ c : C, 0 ≤ ⨆ f : cell c, ⟪v f - v c, x⟫ := by
    intro x c
    have h := le_fsup (fun f => ⟪v f - v c, x⟫) (Finset.mem_insert_self (c : V n)
      (L.filter (fun f => roundV η f = c)))
    simp only [sub_self, inner_zero_left] at h
    exact h
  refine ⟨fun x => ⨆ c : C, ⨆ f : cell c, ⟪v f - v c, x⟫, ?_, ?_, ?_, ?_⟩
  · exact integrable_fsup C (fun c x => ⨆ f : cell c, ⟪v f - v c, x⟫)
      fun c _ => integrable_fsup_inner (cell c) (fun f => v f - v c)
  · intro x
    exact Real.iSup_nonneg (hcell0 x)
  · refine hmain.trans ?_
    have hσ2 : Real.sqrt (π * η) ^ 2 = π * η := Real.sq_sqrt (by positivity)
    rw [hσ2]
    have hlog : Real.log C.card ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos C.card with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg hN1
      · exact Real.log_le_log (by exact_mod_cast hpos) hN
    have e : π ^ 2 / 8 * ((16 : ℝ) ^ n) ^ 2 * (π * η) = π ^ 3 / (8 * 16 ^ n) := by
      rw [hηdef]
      field_simp
    rw [e]
    have : Real.log C.card / ((16 : ℝ) ^ n) ^ 2 ≤ Real.log N / ((16 : ℝ) ^ n) ^ 2 :=
      div_le_div_of_nonneg_right hlog (by positivity)
    linarith
  · intro f hf x
    have hc : roundV η f ∈ C := Finset.mem_image_of_mem _ hf
    have hfc : f ∈ cell (roundV η f) :=
      Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hf, rfl⟩)
    exact (le_fsup (fun g => ⟪v g - v (roundV η f), x⟫) hfc).trans
      (le_fsup (fun c => ⨆ g : cell c, ⟪v g - v c, x⟫) hc)

end Parts

/-- **The construction for a fixed large `n`.** -/
theorem main_step (hC : Blueprint.MaxConcentration) {CS CV K : ℝ} (hCS1 : 1 ≤ CS)
    (hCV0 : 0 ≤ CV) (hZS : ZSup CS)
    (hZV : ∀ n : ℕ, ∀ f ∈ V n, zCov f f ≤ CV * Real.sqrt (energy f)) (hK : K = 8 * CS ^ 2)
    {n : ℕ} (hn14 : 14 ≤ n) (hnV : π ^ 4 * CV ^ 2 / 2 ≤ n)
    (hgrid : 2 * ((⌈Real.sqrt (2 * K * n) / (1 / ((16 : ℝ) ^ n) ^ 3)⌉₊ : ℝ) + 1) + 1 ≤
      ((16 : ℝ) ^ n) ^ 5)
    (hcell : 5 * n * Real.log 16 / 16 ^ n + CS * n / 16 ^ n + π ^ 3 / (8 * 16 ^ n) ≤ 1 / 4)
    (henergy : 1 / ((16 : ℝ) ^ n) ^ 3 / 2 * (K * n) + 2 * ((16 : ℝ) ^ n) ^ 2 *
      (1 / ((16 : ℝ) ^ n) ^ 3 / 2 + (1 / ((16 : ℝ) ^ n) ^ 3 / 2) ^ 2) ≤ 1 / 4)
    (F₀ : Finset (V n)) :
    ∃ F : Finset (V n), zeroV n ∈ F ∧ (∀ f ∈ F, energy f ≤ 2 * K * n) ∧
      (∀ f ∈ F, ∀ x, |(f : ℝ → ℝ) x| ≤ Real.sqrt (2 * K) * Real.sqrt n + 1) ∧
      (F.card : ℝ) ≤ (((16 : ℝ) ^ n) ^ 5) ^ (16 ^ n) + 1 ∧
      gaussianExpectedMax F₀ (fun f g => zCov f g) (fun f => -energy f) ≤
        gaussianExpectedMax F (fun f g => zCov f g) (fun f => -energy f) + 3 / 4 := by
  classical
  set η : ℝ := 1 / ((16 : ℝ) ^ n) ^ 3 with hηdef
  have hn1 : 1 ≤ n := by omega
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hM1 : (1 : ℝ) ≤ (16 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hη : 0 < η := by positivity
  have hK1 : 1 ≤ K := by rw [hK]; nlinarith
  have hK0 : 0 < K := by linarith
  set L := F₀.filter (fun f : V n => energy f ≤ K * n) with hLdef
  set H := F₀.filter (fun f : V n => ¬ energy f ≤ K * n) with hHdef
  set C := L.image (roundV η) with hCdef
  set F := insert (zeroV n) C with hFdef
  set G := F₀ ∪ F with hGdef
  obtain ⟨v, hv, -⟩ := exists_vecExpectedMax_eq_gaussianExpectedMax G
    (fun f g => zCov f g) (zCovPSD_V n G)
  have hF₀G : F₀ ⊆ G := Finset.subset_union_left
  have hFG : F ⊆ G := Finset.subset_union_right
  have hLG : L ⊆ G := (Finset.filter_subset _ _).trans hF₀G
  have hHG : H ⊆ G := (Finset.filter_subset _ _).trans hF₀G
  have hRF : ∀ f ∈ L, roundV η f ∈ F := fun f hf =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hf)
  have h0F : zeroV n ∈ F := Finset.mem_insert_self _ _
  have hv0 : v (zeroV n) = 0 := by
    have h := hv _ (hFG h0F) _ (hFG h0F)
    rw [real_inner_self_eq_norm_sq] at h
    have h0 : zCov ((zeroV n : V n) : ℝ → ℝ) (zeroV n) = 0 := zCov_zero
    rw [h0] at h
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)
  have hE0 : energy ((zeroV n : V n) : ℝ → ℝ) = 0 := energy_zero
  have hnodeL : ∀ f ∈ L, ∀ k : ℕ, k ≤ 16 ^ n →
      |(f : ℝ → ℝ) ((k : ℝ) / 16 ^ n)| ≤ Real.sqrt (2 * K * n) := by
    intro f hf k hk
    apply Real.abs_le_sqrt
    have h1 := node_sq_le f.2 hk
    have h2 := (Finset.mem_filter.1 hf).2
    linarith
  set ε : ℝ := η / 2 * (K * n) + 2 * ((16 : ℝ) ^ n) ^ 2 * (η / 2 + (η / 2) ^ 2) with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hER : ∀ f ∈ L, energy (roundV η f : ℝ → ℝ) ≤ energy f + ε := by
    intro f hf
    have hE := (Finset.mem_filter.1 hf).2
    have h := energy_le_of_near f.2 (roundV η f).2 (δ := η / 2) (by positivity)
      (fun k hk => roundV_node_err hη f hk)
    have h2 := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ η / 2)
    linarith
  obtain ⟨T, hTint, hT0, hTle, hTpt⟩ := high_part hC hCS1 hCV0 hZS hZV hK hn14 hnV G v hv H
    hHG (fun f hf => not_le.1 (Finset.mem_filter.1 hf).2)
  have hcard : (C.card : ℝ) ≤ (((16 : ℝ) ^ n) ^ 5) ^ (16 ^ n) := by
    have h := card_image_roundV_le hη L (⌈Real.sqrt (2 * K * n) / η⌉₊ + 1)
      (fun f hf k hk => by
        have := abs_round_roundV_le hη f hk (hnodeL f hf k hk)
        push_cast
        exact this)
    refine h.trans (pow_le_pow_left₀ (by positivity) ?_ _)
    push_cast
    exact hgrid
  have hlogN : Real.log ((((16 : ℝ) ^ n) ^ 5) ^ (16 ^ n)) / ((16 : ℝ) ^ n) ^ 2 =
      5 * n * Real.log 16 / 16 ^ n := by
    rw [Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    field_simp
  obtain ⟨W, hWint, hW0, hWle, hWpt⟩ := low_part hC hCS1 hZS hn1 G v hv L hLG hηdef
    (fun f hf => hFG (hRF f hf)) (one_le_pow₀ (one_le_pow₀ hM1)) hcard
    (by rw [hlogN]; exact hcell)
  have hΦ0 : ∀ x, 0 ≤ ⨆ g : F, ⟪v g, x⟫ + -energy g := by
    intro x
    have h := le_fsup (fun g => ⟪v g, x⟫ + -energy g) h0F
    simp only [hv0, inner_zero_left, hE0, neg_zero, add_zero] at h
    exact h
  have hpt : ∀ x, (⨆ f : F₀, ⟪v f, x⟫ + -energy f) ≤
      (⨆ g : F, ⟪v g, x⟫ + -energy g) + T x + W x + ε := by
    intro x
    refine fsup_le (g := fun f => ⟪v f, x⟫ + -energy f) (by linarith [hΦ0 x, hT0 x, hW0 x]) ?_
    intro f hf
    by_cases hE : energy f ≤ K * n
    · have hfL : f ∈ L := Finset.mem_filter.2 ⟨hf, hE⟩
      have h1 := le_fsup (fun g => ⟪v g, x⟫ + -energy g) (hRF f hfL)
      have h2 := hWpt f hfL x
      have h3 := hER f hfL
      have h4 : ⟪v f, x⟫ = ⟪v (roundV η f), x⟫ + ⟪v f - v (roundV η f), x⟫ := by
        rw [inner_sub_left]
        ring
      linarith [hT0 x]
    · have hfH : f ∈ H := Finset.mem_filter.2 ⟨hf, hE⟩
      have := hTpt f hfH x
      linarith [hΦ0 x, hW0 x]
  refine ⟨F, h0F, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases Finset.mem_insert.1 hg with rfl | hg
    · rw [hE0]
      positivity
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
      have h := hER f hf
      have hE := (Finset.mem_filter.1 hf).2
      have hKn : 1 ≤ K * n := by nlinarith
      have hε : ε ≤ 1 / 4 := henergy
      linarith
  · intro g hg x
    rcases Finset.mem_insert.1 hg with rfl | hg
    · simp only [zeroV, Pi.zero_apply, abs_zero]
      positivity
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
      have h1 := roundV_err hη f x
      have h2 := abs_le_of_nodes f.2 (Real.sqrt_nonneg _) (hnodeL f hf) x
      have h3 : η / 2 ≤ 1 := by
        rw [hηdef, div_le_one (by norm_num), div_le_iff₀ (by positivity)]
        nlinarith [one_le_pow₀ (n := 3) hM1]
      have h4 : Real.sqrt (2 * K * n) = Real.sqrt (2 * K) * Real.sqrt n :=
        Real.sqrt_mul (by positivity) _
      rw [h4] at h2
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
  · have h1 : (F.card : ℝ) ≤ C.card + 1 := by exact_mod_cast Finset.card_insert_le _ _
    linarith
  · have hΦ₀int := integrable_iSup_inner_add F₀ v (fun f => -energy f)
    have hΦint := integrable_iSup_inner_add F v (fun f => -energy f)
    rw [gEM_eq_vec hF₀G v hv, gEM_eq_vec hFG v hv]
    simp only [vecExpectedMax]
    have iΦT : Integrable (fun x => (⨆ g : F, ⟪v g, x⟫ + -energy g) + T x)
        (stdGaussian (EuclideanSpace ℝ G)) := hΦint.add hTint
    have iΦTW : Integrable (fun x => (⨆ g : F, ⟪v g, x⟫ + -energy g) + T x + W x)
        (stdGaussian (EuclideanSpace ℝ G)) := iΦT.add hWint
    have hI : Integrable (fun x => (⨆ g : F, ⟪v g, x⟫ + -energy g) + T x + W x + ε)
        (stdGaussian (EuclideanSpace ℝ G)) := iΦTW.add (integrable_const ε)
    have hmono := integral_mono hΦ₀int hI hpt
    rw [integral_add iΦTW (integrable_const ε), integral_add iΦT hWint,
      integral_add hΦint hTint, integral_const] at hmono
    simp only [probReal_univ, one_smul] at hmono
    have hε : ε ≤ 1 / 4 := henergy
    linarith

/-- The three smallness conditions of `main_step` follow from `n / 16ⁿ ≤ 1 / (4 (K + C + 100))`. -/
lemma smallness {CS K : ℝ} (hCS1 : 1 ≤ CS) (hK : K = 8 * CS ^ 2) {n : ℕ} (hn1 : 1 ≤ n)
    (hr : (n : ℝ) / 16 ^ n ≤ 1 / (4 * (K + CS + 100))) :
    2 * ((⌈Real.sqrt (2 * K * n) / (1 / ((16 : ℝ) ^ n) ^ 3)⌉₊ : ℝ) + 1) + 1 ≤
        ((16 : ℝ) ^ n) ^ 5 ∧
      5 * n * Real.log 16 / 16 ^ n + CS * n / 16 ^ n + π ^ 3 / (8 * 16 ^ n) ≤ 1 / 4 ∧
      1 / ((16 : ℝ) ^ n) ^ 3 / 2 * (K * n) + 2 * ((16 : ℝ) ^ n) ^ 2 *
        (1 / ((16 : ℝ) ^ n) ^ 3 / 2 + (1 / ((16 : ℝ) ^ n) ^ 3 / 2) ^ 2) ≤ 1 / 4 := by
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hK0 : 0 < K := by rw [hK]; nlinarith
  have hCS0 : 0 < CS := by linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 16 ^ n := ⟨_, rfl⟩
  rw [← hMdef] at hr ⊢
  have hM16 : 16 ≤ M := by
    rw [hMdef]
    calc (16 : ℝ) = 16 ^ 1 := by norm_num
      _ ≤ 16 ^ n := pow_le_pow_right₀ (by norm_num) hn1
  have hM0 : 0 < M := by linarith
  have hD : 0 < 4 * (K + CS + 100) := by linarith
  have hnM : (n : ℝ) * (4 * (K + CS + 100)) ≤ 1 * M := (div_le_div_iff₀ hM0 hD).1 hr
  have hr0 : 0 ≤ (n : ℝ) / M := by positivity
  have hinvM : 1 / M ≤ (n : ℝ) / M := div_le_div_of_nonneg_right hn1' hM0.le
  refine ⟨?_, ?_, ?_⟩
  · have hsq0 : 0 ≤ 2 * K * n := by positivity
    have hsq : Real.sqrt (2 * K * n) ≤ 2 * K * n + 1 := by
      nlinarith [Real.sq_sqrt hsq0, Real.sqrt_nonneg (2 * K * n),
        sq_nonneg (Real.sqrt (2 * K * n) - 1 / 2)]
    have hy : Real.sqrt (2 * K * n) / (1 / M ^ 3) = Real.sqrt (2 * K * n) * M ^ 3 := by
      field_simp
    rw [hy]
    have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.sqrt (2 * K * n) * M ^ 3 by positivity)
    have hM3 : 1 ≤ M ^ 3 := one_le_pow₀ (by linarith)
    have h4 : 4 * K * n + 7 ≤ M := by nlinarith [mul_pos hCS0 hn0]
    have h5 : Real.sqrt (2 * K * n) * M ^ 3 ≤ (2 * K * n + 1) * M ^ 3 :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    calc 2 * ((⌈Real.sqrt (2 * K * n) * M ^ 3⌉₊ : ℝ) + 1) + 1
        ≤ 2 * ((2 * K * n + 1) * M ^ 3 + 2) + 1 := by linarith
      _ ≤ (4 * K * n + 7) * M ^ 3 := by nlinarith
      _ ≤ M * M ^ 3 := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = M ^ 4 := by ring
      _ ≤ M ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  · have hlog : Real.log 16 ≤ 15 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)
      linarith
    have hpi3 : π ^ 3 ≤ 64 := by
      have := pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 3
      norm_num at this
      linarith
    have e1 : 5 * n * Real.log 16 / M = 5 * Real.log 16 * ((n : ℝ) / M) := by ring
    have e2 : CS * n / M = CS * ((n : ℝ) / M) := by ring
    have e3 : π ^ 3 / (8 * M) = π ^ 3 / 8 * (1 / M) := by field_simp
    rw [e1, e2, e3]
    have h1 : 5 * Real.log 16 * ((n : ℝ) / M) ≤ 75 * ((n : ℝ) / M) := by
      nlinarith [mul_le_mul_of_nonneg_right hlog hr0]
    have h2 : π ^ 3 / 8 * (1 / M) ≤ 8 * ((n : ℝ) / M) := by
      have : π ^ 3 / 8 ≤ 8 := by linarith
      calc π ^ 3 / 8 * (1 / M) ≤ 8 * (1 / M) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ ≤ 8 * ((n : ℝ) / M) := by linarith
    have h3 : (83 + CS) * ((n : ℝ) / M) ≤ 1 / 4 := by
      calc (83 + CS) * ((n : ℝ) / M) ≤ (83 + CS) * (1 / (4 * (K + CS + 100))) :=
            mul_le_mul_of_nonneg_left hr (by linarith)
        _ ≤ 1 / 4 := by
            rw [mul_one_div, div_le_div_iff₀ hD (by norm_num)]
            linarith
    linarith
  · have e : 1 / M ^ 3 / 2 * (K * n) + 2 * M ^ 2 * (1 / M ^ 3 / 2 + (1 / M ^ 3 / 2) ^ 2) =
        K * ((n : ℝ) / M) * (1 / (2 * M ^ 2)) + 1 / M + 1 / (2 * M ^ 4) := by
      field_simp
      ring
    rw [e]
    have h1 : K * ((n : ℝ) / M) * (1 / (2 * M ^ 2)) ≤ K * ((n : ℝ) / M) := by
      have : 1 / (2 * M ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
      exact mul_le_of_le_one_right (by positivity) this
    have h2 : 1 / (2 * M ^ 4) ≤ 1 / M := by
      apply one_div_le_one_div_of_le hM0
      nlinarith [pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ M) (by norm_num : 1 ≤ 4)]
    have h3 : (K + 2) * ((n : ℝ) / M) ≤ 1 / 4 := by
      calc (K + 2) * ((n : ℝ) / M) ≤ (K + 2) * (1 / (4 * (K + CS + 100))) :=
            mul_le_mul_of_nonneg_left hr (by linarith)
        _ ≤ 1 / 4 := by
            rw [mul_one_div, div_le_div_iff₀ hD (by norm_num)]
            linarith
    linarith

/-- A finite family whose expected maximum is within `1/4` of `a_n`. -/
lemma exists_F0 (n : ℕ) : ∃ F₀ : Finset (V n),
    a n - 1 / 4 ≤ gaussianExpectedMax F₀ (fun f g => zCov f g) (fun f => -energy f) := by
  by_cases htop : aE n = ⊤
  · refine ⟨∅, ?_⟩
    rw [gEM_empty]
    norm_num [a, htop]
  by_cases hbot : aE n = ⊥
  · refine ⟨∅, ?_⟩
    rw [gEM_empty]
    norm_num [a, hbot]
  have heq : aE n = ((a n : ℝ) : EReal) := (EReal.coe_toReal htop hbot).symm
  have hlt : ((a n - 1 / 4 : ℝ) : EReal) < aE n := by
    rw [heq]
    exact EReal.coe_lt_coe_iff.2 (by linarith)
  unfold aE at hlt
  obtain ⟨F, hF⟩ := lt_iSup_iff.1 hlt
  exact ⟨F, (EReal.coe_lt_coe_iff.1 hF).le⟩

end LQGDimension.L23

namespace LQGDimension

open L23

/-- **Lemma 2.3.**  For all sufficiently large `n` there is a finite `F ⊆ V_n` containing `0`,
with `E(f) ≤ C n`, `‖f‖_∞ ≤ C √n`, `log |F| ≤ C M log M` and
`E max_F (Z_f - E(f)) ≥ a_n - 1`.  (`AOneFinite` and `ASubadditiveE` are not used.) -/
theorem lemma23_of (hC : Blueprint.MaxConcentration) (hS : Blueprint.ZSupBound)
    (hV : Blueprint.ZVarBound) (_h1 : Blueprint.AOneFinite) (_h2 : Blueprint.ASubadditiveE) :
    Blueprint.Lemma23 := by
  obtain ⟨CS₀, hCS₀⟩ := hS
  obtain ⟨CV₀, hCV₀⟩ := hV
  obtain ⟨CS, hCSdef⟩ : ∃ CS : ℝ, CS = max CS₀ 1 := ⟨_, rfl⟩
  obtain ⟨CV, hCVdef⟩ : ∃ CV : ℝ, CV = max CV₀ 0 := ⟨_, rfl⟩
  have hCS1 : 1 ≤ CS := by rw [hCSdef]; exact le_max_right _ _
  have hCV0 : 0 ≤ CV := by rw [hCVdef]; exact le_max_right _ _
  have hCSle : CS₀ ≤ CS := by rw [hCSdef]; exact le_max_left _ _
  have hCVle : CV₀ ≤ CV := by rw [hCVdef]; exact le_max_left _ _
  have hZS : ZSup CS := by
    intro n hn R hR F hF
    refine (hCS₀ n hn R hR F hF).trans ?_
    have h0 : 0 ≤ (n : ℝ) ^ (3 / 4 : ℝ) * R ^ (1 / 4 : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_right hCSle h0
    simpa only [mul_assoc] using h
  have hZV : ∀ n : ℕ, ∀ f ∈ V n, zCov f f ≤ CV * Real.sqrt (energy f) := fun n f hf =>
    (hCV₀ n f hf).trans (mul_le_mul_of_nonneg_right hCVle (Real.sqrt_nonneg _))
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 8 * CS ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; nlinarith
  have hρ : 0 < 1 / (4 * (K + CS + 100)) := by
    apply div_pos one_pos
    linarith
  have hev : ∀ᶠ n : ℕ in atTop, 14 ≤ n ∧ π ^ 4 * CV ^ 2 / 2 ≤ (n : ℝ) ∧
      (n : ℝ) / 16 ^ n ≤ 1 / (4 * (K + CS + 100)) := by
    refine (eventually_ge_atTop 14).and
      (((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _).and ?_)
    have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 16)
    simp only [pow_one] at ht
    exact ht.eventually (Iic_mem_nhds hρ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨2 * K + 7, N, fun n hn => ?_⟩
  obtain ⟨h14, hnV, hr⟩ := hN n hn
  have hn1 : 1 ≤ n := by omega
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  obtain ⟨hgrid, hcell, henergy⟩ := smallness hCS1 hKdef hn1 hr
  obtain ⟨F₀, hF₀⟩ := exists_F0 n
  obtain ⟨F, h0F, hE, hsup, hcard, hgem⟩ :=
    main_step hC hCS1 hCV0 hZS hZV hKdef h14 hnV hgrid hcell henergy F₀
  refine ⟨F, ⟨zeroV n, h0F, fun x => rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro f hf
    have := hE f hf
    nlinarith
  · intro f hf x
    have h := hsup f hf x
    have hsn : 1 ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by rw [one_pow]; exact hn1')
    have hsK : Real.sqrt (2 * K) ≤ 2 * K + 1 := by
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * K), Real.sqrt_nonneg (2 * K),
        sq_nonneg (Real.sqrt (2 * K) - 1 / 2)]
    have h2 := mul_le_mul_of_nonneg_right hsK (Real.sqrt_nonneg (n : ℝ))
    nlinarith
  · obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 16 ^ n := ⟨_, rfl⟩
    rw [← hMdef] at hcard ⊢
    have hM2 : 2 ≤ M := by
      rw [hMdef]
      calc (2 : ℝ) ≤ 16 ^ 1 := by norm_num
        _ ≤ 16 ^ n := pow_le_pow_right₀ (by norm_num) hn1
    have hM1 : 1 ≤ M := by linarith
    have hcard0 : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.2 ⟨_, h0F⟩
    have hA : (1 : ℝ) ≤ (M ^ 5) ^ (16 ^ n) := one_le_pow₀ (one_le_pow₀ hM1)
    have hlog1 : Real.log F.card ≤ Real.log (2 * (M ^ 5) ^ (16 ^ n)) :=
      Real.log_le_log hcard0 (by linarith)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at hlog1
    have hc : ((16 ^ n : ℕ) : ℝ) = M := by simp [hMdef]
    rw [hc] at hlog1
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
    have hlog2 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hM2
    have h3 : Real.log M ≤ M * Real.log M := le_mul_of_one_le_left hlogM hM1
    have h4 : 0 ≤ (2 * K + 1) * (M * Real.log M) := by positivity
    push_cast at hlog1
    nlinarith
  · linarith

end LQGDimension
