/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.RegularityCond5b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityCond5
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityProb
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordsAux1

/-!
# GM Lemma 4.11, condition 5 (existence of good annuli): grid union bound and dyadic sum

Source: GM (arXiv:1905.00383v3) `uniqueness-final.tex`, proof of Lemma 4.11, l. 1987: "By Lemma 2.6
[= LM Lemma 3.1], conditions (2) and (3) of Theorem 4.2, and a union bound over all
`z ∈ (λ_1ε^{1+ν}𝕣/4)ℤ² ∩ V`, if `𝕡` is chosen sufficiently close to 1 (in a manner depending only
on `μ, ν`) then the probability of condition 5 … tends to 1 as `a → 0`, uniformly over the choice
of `𝕣`."

The per-point step is `gm_c5_point_rr` (`RegularityCond5.lean`). Here:
* `gm_grid_union_le`: union bound over the points of `sℤ² ∩ cl B_ρ(0)`, at most `(2ρ/s + 1)²` of
  them (LQGDimension `card_gridBox_le`, as in `DFGPS.lem3_4`);
* `gm_regC5_prob`: condition 5. The exponent `a` of LM Lemma 3.1 (1) is chosen so that the
  per-point failure bound `≲ ε^{2(1+ν)+2}` beats the `≲ ε^{−2(1+ν)}` grid points; the sum over
  dyadic `ε = 2^{−n} ≤ a` is then `≲ a` (as in `gm_regC6_prob`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- union bound over the grid `sℤ² ∩ cl B_ρ(0)`, which has at most `(2ρ/s + 1)²` points -/
theorem gm_grid_union_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {s ρ β : ℝ} (hs : 0 < s)
    (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (B : ℂ → Set Ω) (hB : ∀ z, P (B z) ≤ ENNReal.ofReal β) :
    P (⋃ z ∈ gridPts s ∩ Metric.closedBall 0 ρ, B z) ≤ ENNReal.ofReal ((2 * ρ / s + 1) ^ 2 * β) := by
  classical
  set G := LQGDimension.LFPPRecords.gridBox s 0 ρ
  have hsub : (⋃ z ∈ gridPts s ∩ Metric.closedBall 0 ρ, B z) ⊆
      ⋃ a ∈ G, B (LQGDimension.LFPPRecords.gridPt s a) := by
    intro ω hω
    obtain ⟨z, ⟨⟨a, b, rfl⟩, hzb⟩, hω⟩ := mem_iUnion₂.1 hω
    have hpt : LQGDimension.LFPPRecords.gridPt s (a, b) = ⟨a * s, b * s⟩ := rfl
    refine mem_biUnion (x := (a, b)) ?_ ?_
    · refine LQGDimension.LFPPRecords.mem_gridBox hs ?_
      rw [hpt, sub_zero]; exact mem_closedBall_zero_iff.1 hzb
    · rw [hpt]; exact hω
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  refine (Finset.sum_le_card_nsmul _ _ _ fun a _ => hB _).trans ?_
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (LQGDimension.LFPPRecords.card_gridBox_le hs hρ 0) hβ)

theorem gm_dyadic_eq_exp (n : ℕ) : (2 : ℝ)⁻¹ ^ n = Real.exp (-(n * Real.log 2)) := by
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n), Real.log_pow, Real.log_inv]
  ring_nf

theorem gm_dyadic_rpow (n : ℕ) (t : ℝ) :
    ((2 : ℝ)⁻¹ ^ n) ^ t = Real.exp (-(n * Real.log 2) * t) := by
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, Real.log_inv]
  ring_nf

theorem gm_logb8_dyadic (n : ℕ) : Real.logb 8 ((2 : ℝ)⁻¹ ^ n)⁻¹ = n / 3 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [inv_pow, inv_inv, Real.logb, Real.log_pow, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  field_simp
  push_cast
  ring

/-- **GM Lemma 4.11, condition 5** (l. 1987): with `𝕡` from LM Lemma 3.1 (1) (applied with
`s₁ = λ_1/λ_5`, `s₂ = λ_4/λ_5` to every `m`-th radius, `gm_c5_point_rr`), if the radii
`r^ε_k = R.rr 𝕣 ε k` satisfy T4.2 (1) (in `[ε^{1+ν}𝕣, ε𝕣] ∩ Rad 𝕣`, ratio `≥ λ_4/λ_1`), the events
`E_r(z)` satisfy T4.2 (2) (a.s. determined by `(h − h_{λ_5 r}(z))|_{A_{λ_1 r, λ_4 r}(z)}`) and
`P[E_r(z)] ≥ 𝕡` (T4.2 (3)), then condition 5 holds with probability `→ 1` as `a → 0`, uniformly
in `𝕣`. -/
theorem gm_regC5_prob (h31a : LMLem3_1a) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) {lam : Fin 5 → ℝ}
    (h0 : 0 < lam 0) (h01 : lam 0 < lam 1) (h12 : lam 1 ≤ lam 2) (h23 : lam 2 ≤ lam 3)
    (h34 : lam 3 < lam 4) :
    ∃ 𝕡 ∈ Ioo (0 : ℝ) 1, ∀ {V : Set ℂ} {ℓ : ℝ}, Bornology.IsBounded V → ∀ ε₀ : ℝ, 0 < ε₀ →
      ∀ q < 1, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P → ∀ R : RegPar, R.μ = μ →
      R.ν = ν → R.lam = lam → R.V = V → R.ℓ = ℓ → ∀ Rad : ℝ → Set ℝ,
      (∀ 𝕣 > 0, ∀ ε ∈ Ioc (0 : ℝ) ε₀, (∀ k < ⌊μ * Real.logb 8 ε⁻¹⌋₊,
          R.rr 𝕣 ε k ∈ Icc (ε ^ (1 + ν) * 𝕣) (ε * 𝕣) ∧ R.rr 𝕣 ε k ∈ Rad 𝕣) ∧
        ∀ k, k + 1 < ⌊μ * Real.logb 8 ε⁻¹⌋₊ → lam 3 / lam 0 ≤ R.rr 𝕣 ε k / R.rr 𝕣 ε (k + 1)) →
      (∀ 𝕣 > 0, ∀ z, ∀ r ∈ Rad 𝕣, AEEventIn P (fieldSigma (fun ω => addConst (h ω)
          (-circleAvg (h ω) (lam 4 * r) z)) (annulus z (lam 0 * r) (lam 3 * r))) (h ⁻¹' R.E r z)) →
      (∀ 𝕣 > 0, ∀ z, ∀ r ∈ Rad 𝕣, ENNReal.ofReal 𝕡 ≤ P (h ⁻¹' R.E r z)) →
      RegCondAt P (regC5 h R) q a₀ := by
  have hl03 : lam 0 < lam 3 := by linarith
  have hl4 : 0 < lam 4 := by linarith
  -- `m` with `(λ_1/λ_4)^m ≤ λ_1/λ_5`
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos h0 hl4)
    (show lam 0 / lam 3 < 1 by rw [div_lt_one (by linarith)]; exact hl03)
  have hm0 : 1 ≤ m := by
    by_contra h'
    have : m = 0 := by omega
    rw [this, pow_zero, lt_div_iff₀ hl4] at hm
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  set L := Real.log 2 with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  set aLM : ℝ := 3 * m * ((2 * (1 + ν) + 2) * L) / μ with haLM
  have haLM0 : 0 < aLM := by positivity
  obtain ⟨pt, cc, hpt0, hpt1, hcc, HLM⟩ := h31a (lam 0 / lam 4) (lam 3 / lam 4) (div_pos h0 hl4)
    (div_lt_div_of_pos_right hl03 hl4) (by rw [div_lt_one hl4]; exact h34) aLM haLM0 (1 / 2)
    (by norm_num) (by norm_num)
  refine ⟨pt, ⟨hpt0, hpt1⟩, ?_⟩
  intro V ℓ hV ε₀ hε₀
  obtain ⟨ρ₀, hρ₀⟩ := hV.subset_ball (0 : ℂ)
  set ρ' : ℝ := max (ρ₀ + 4 * ℓ) 0 with hρ'
  have hρ'0 : 0 ≤ ρ' := le_max_right _ _
  set A : ℝ := (8 * ρ' / lam 0 + 1) ^ 2 with hA
  set C : ℝ := A * (cc * Real.exp (3 * aLM)) with hC
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [show 0 ≤ 8 * ρ' / lam 0 by positivity]
  have hC0 : 0 < C := by positivity
  -- `n₀` with `μ n₀ / 3 ≥ m + 2`
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, (3 : ℝ) * ((m : ℝ) + 2) / μ ≤ n₀ := ⟨_, Nat.le_ceil _⟩
  intro q hq
  have hq' : 0 < 1 - q := by linarith
  refine ⟨min (min ε₀ ((2 : ℝ)⁻¹ ^ n₀)) ((1 - q) / (2 * C)),
    lt_min (lt_min hε₀ (by positivity)) (by positivity), ?_⟩
  intro Ω _ P _ h hh R hRμ hRν hRlam hRV hRℓ Rad hrr hEm hEp
  subst hRV hRℓ
  rintro a ⟨ha0, ha⟩ 𝕣 h𝕣
  have haε : a ≤ ε₀ := ha.trans ((min_le_left _ _).trans (min_le_left _ _))
  have han : a ≤ (2 : ℝ)⁻¹ ^ n₀ := ha.trans ((min_le_left _ _).trans (min_le_right _ _))
  have haq : 2 * C * a ≤ 1 - q := by
    have := ha.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  -- the bad event at scale `n`
  set K : ℕ → ℕ := fun n => ⌊μ * Real.logb 8 ((2 : ℝ)⁻¹ ^ n)⁻¹⌋₊ with hK
  set Bz : ℕ → ℂ → Set Ω := fun n z =>
    {ω | ∀ k < K n, ω ∉ h ⁻¹' R.E (R.rr 𝕣 ((2 : ℝ)⁻¹ ^ n) k) z} with hBz
  set s : ℕ → ℝ := fun n => lam 0 * ((2 : ℝ)⁻¹ ^ n) ^ (1 + ν) * 𝕣 / 4 with hs
  have hsub : (regC5 h R 𝕣 a)ᶜ ⊆ ⋃ n, ⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a),
      ⋃ z ∈ gridPts (s n) ∩ Metric.closedBall 0 (𝕣 * ρ'), Bz n z := by
    intro ω hω
    simp only [regC5, hRν, hRμ, hRlam, mem_compl_iff, mem_ofPred_eq, not_forall, not_exists,
      not_and] at hω
    obtain ⟨n, hn, z, hz, hno⟩ := hω
    refine mem_iUnion₂.2 ⟨n, hn, mem_iUnion₂.2 ⟨z, ⟨hz.1, ?_⟩, fun k hk => hno k hk⟩⟩
    have hz2 := gm_regRegion_subset h𝕣 hρ₀ hz.2
    obtain ⟨x, hx, rfl⟩ := hz2
    rw [mem_closedBall_zero_iff]
    show ‖(𝕣 : ℂ) * x + 0‖ ≤ 𝕣 * ρ'
    rw [add_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos h𝕣]
    exact mul_le_mul_of_nonneg_left ((mem_closedBall_zero_iff.1 hx).trans (le_max_left _ _))
      h𝕣.le
  have hterm : ∀ n, P (⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a),
      ⋃ z ∈ gridPts (s n) ∩ Metric.closedBall 0 (𝕣 * ρ'), Bz n z) ≤
      ENNReal.ofReal (C * a * (2 : ℝ)⁻¹ ^ n) := by
    intro n
    by_cases hn : (2 : ℝ)⁻¹ ^ n ≤ a
    swap
    · have : (⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a),
          ⋃ z ∈ gridPts (s n) ∩ Metric.closedBall 0 (𝕣 * ρ'), Bz n z) = ∅ :=
        eq_empty_of_subset_empty (iUnion_subset fun h' => (hn h').elim)
      rw [this, measure_empty]; exact bot_le
    refine (measure_mono (iUnion_subset fun _ => subset_rfl)).trans ?_
    set ε : ℝ := (2 : ℝ)⁻¹ ^ n with hε
    have hε0 : 0 < ε := by positivity
    have hεI : ε ∈ Ioc (0 : ℝ) ε₀ := ⟨hε0, hn.trans haε⟩
    -- `n ≥ n₀`, hence `K n ≥ m + 1`
    have hnn₀ : n₀ ≤ n := by
      by_contra h'
      have : (2 : ℝ)⁻¹ ^ n₀ < (2 : ℝ)⁻¹ ^ n :=
        pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
      linarith
    have hKeq : K n = ⌊μ * (n / 3)⌋₊ := by simp only [hK, gm_logb8_dyadic]
    have hnR : (3 : ℝ) * ((m : ℝ) + 2) / μ ≤ n := hn₀.trans (Nat.cast_le.2 hnn₀)
    have hμn : (m : ℝ) + 2 ≤ μ * (n / 3) := by
      rw [div_le_iff₀ hμ] at hnR; linarith
    have hKlow : μ * (n / 3) - 1 < K n := by
      rw [hKeq]; linarith [Nat.lt_floor_add_one (μ * (n / 3))]
    have hKm : m + 1 ≤ K n := by
      have : (m : ℝ) + 1 < K n := by linarith
      exact_mod_cast this.le
    -- the per-point bound
    obtain ⟨hrI, hrat⟩ := hrr 𝕣 h𝕣 ε hεI
    have hrpos : ∀ k < K n, 0 < R.rr 𝕣 ε k := fun k hk =>
      lt_of_lt_of_le (by positivity) (hrI k hk).1.1
    have hpoint : ∀ z, P (Bz n z) ≤ ENNReal.ofReal (cc * Real.exp (3 * aLM) *
        Real.exp (-(n * L) * (2 * (1 + ν) + 2))) := by
      intro z
      have key := gm_c5_point_rr (l0 := lam 0) (l3 := lam 3) (l4 := lam 4) h0 hl03 h34
        (fun P _ h hN r E hAI hE K => HLM P h hN r E hAI hE K) hpt1.le hm.le P h hh z (K n) hKm
        (R.rr 𝕣 ε) hrpos hrat (fun k => h ⁻¹' R.E (R.rr 𝕣 ε k) z)
        (fun k hk => hEm 𝕣 h𝕣 z _ (hrI k hk).2) (fun k hk => hEp 𝕣 h𝕣 z _ (hrI k hk).2)
      refine (measure_mono (fun ω hω => hω)).trans (key.trans (ENNReal.ofReal_le_ofReal ?_))
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hcc.le
      -- `(K−1)/m ≥ μn/(3m) − 3`
      set N : ℕ := (K n - 1) / m with hNdef
      have hdm : m * N + (K n - 1) % m = K n - 1 := Nat.div_add_mod (K n - 1) m
      have hmod := Nat.mod_lt (K n - 1) (by omega : 0 < m)
      have hKN : ((K n - 1 : ℕ) : ℝ) < m * N + m := by
        have : K n - 1 < m * N + m := by omega
        exact_mod_cast this
      have hK1 : ((K n - 1 : ℕ) : ℝ) = K n - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hK1] at hKN
      have hNlow : μ * (n / 3) / m - 3 ≤ N := by
        have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm0
        rw [sub_le_iff_le_add, div_le_iff₀ hmR]
        nlinarith
      have e : aLM * (μ * (n / 3) / m) = n * L * (2 * (1 + ν) + 2) := by
        rw [haLM]; field_simp
      have := mul_le_mul_of_nonneg_left hNlow haLM0.le
      rw [mul_sub, e] at this
      linarith
    refine (gm_grid_union_le P (by positivity) (by positivity) (by positivity) (Bz n) hpoint).trans
      (ENNReal.ofReal_le_ofReal ?_)
    -- counting: `(2𝕣ρ'/s + 1)² ≤ A ε^{−2(1+ν)}`
    set e1 : ℝ := Real.exp (-(n * L) * (1 + ν)) with he1
    have hsn : s n = lam 0 * e1 * 𝕣 / 4 := by simp only [hs, gm_dyadic_rpow]; rfl
    have he10 : 0 < e1 := Real.exp_pos _
    have he11 : e1 ≤ 1 := by
      rw [he1, Real.exp_le_one_iff]
      have : 0 ≤ (n : ℝ) * L * (1 + ν) := by positivity
      linarith
    have hcount : (2 * (𝕣 * ρ') / s n + 1) ^ 2 ≤ A / e1 ^ 2 := by
      rw [hsn, hA]
      have e : 2 * (𝕣 * ρ') / (lam 0 * e1 * 𝕣 / 4) = 8 * ρ' / lam 0 / e1 := by
        have h1 : 𝕣 ≠ 0 := h𝕣.ne'
        have h2 : lam 0 ≠ 0 := h0.ne'
        have h3 : e1 ≠ 0 := he10.ne'
        field_simp; ring
      rw [e]
      refine (pow_le_pow_left₀ (by positivity) ?_ 2).trans (le_of_eq (div_pow _ _ 2))
      rw [add_div]
      gcongr
      exact (one_le_div he10).2 he11
    have hexp : Real.exp (-(n * L) * (2 * (1 + ν) + 2)) = e1 ^ 2 * ε ^ 2 := by
      rw [he1, hε, gm_dyadic_eq_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; push_cast; ring
    rw [hexp]
    have hεa : ε ^ 2 ≤ a * ε := by rw [sq]; exact mul_le_mul_of_nonneg_right hn hε0.le
    calc (2 * (𝕣 * ρ') / s n + 1) ^ 2 * (cc * Real.exp (3 * aLM) * (e1 ^ 2 * ε ^ 2))
        ≤ A / e1 ^ 2 * (cc * Real.exp (3 * aLM) * (e1 ^ 2 * ε ^ 2)) :=
          mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = C * ε ^ 2 := by rw [hC]; field_simp
      _ ≤ C * (a * ε) := mul_le_mul_of_nonneg_left hεa hC0.le
      _ = C * a * ε := by ring
  have hsum : HasSum (fun n : ℕ => C * a * (2 : ℝ)⁻¹ ^ n) (C * a * 2) := by
    have := (hasSum_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_left
      (C * a)
    have e : (1 - (2 : ℝ)⁻¹)⁻¹ = 2 := by norm_num
    rwa [e] at this
  calc P (regC5 h R 𝕣 a)ᶜ ≤ P (⋃ n, ⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a),
        ⋃ z ∈ gridPts (s n) ∩ Metric.closedBall 0 (𝕣 * ρ'), Bz n z) := measure_mono hsub
    _ ≤ ∑' n, P (⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a),
        ⋃ z ∈ gridPts (s n) ∩ Metric.closedBall 0 (𝕣 * ρ'), Bz n z) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (C * a * (2 : ℝ)⁻¹ ^ n) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (C * a * 2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable, hsum.tsum_eq]
    _ ≤ ENNReal.ofReal (1 - q) := ENNReal.ofReal_le_ofReal (by linarith)

end LQGMetric.GM
