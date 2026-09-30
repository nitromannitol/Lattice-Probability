import LatticeProb.Prob.AkcogluKrengelAE.CoarseGraining

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# Back to all cube sizes, and the assembly (Step 4, part F, and the theorem)

Nested cubes give `liminf_k cubeRatio f (k m) ≤ liminf_n cubeRatio f n`. Choosing a scale `m` at
which `∫ cubeRatio f m` nearly attains its infimum `γ` over `m`, and applying the unit-scale lower
bound to the coarse-grained process, proves the Akcoglu-Krengel lower bound `γ ≤ ∫ liminf_n
cubeRatio f n`. Together with the upper bound of Step 3, this gives `liminf = limsup` almost
everywhere, and hence the almost-everywhere theorem `akcoglu_krengel` itself.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `n ≤ (n / m + 1) * m`. -/
theorem le_add_one_mul_of_div {m n : ℕ} (hm : 1 ≤ m) : n ≤ (n / m + 1) * m := by
  have h : n < n / m * m + m := Nat.lt_div_mul_add (by omega : 0 < m)
  rw [Nat.add_mul, one_mul]
  omega

/-- Real-algebra step turning `F ≤ G + C (a - b)` into `F / a * (a / b) - C (a / b - 1) ≤ G / b`. -/
theorem div_mul_div_sub_mul_sub_le_div_of_le_add_mul {F G C a b : ℝ} (ha : 0 < a) (hb : 0 <
    b)
    (h : F ≤ G + C * (a - b)) : F / a * (a / b) - C * (a / b - 1) ≤ G / b := by
  have h1 : F / a * (a / b) = F / b := by
    field_simp
  have h2 : C * (a / b - 1) = C * (a - b) / b := by
    field_simp
  rw [h1, h2, ← sub_div]
  exact div_le_div_of_nonneg_right (by linarith) hb.le

omit [MeasurableSpace Ω] in
/-- `cubeRatio f ((n/m+1)m) * (((n/m+1)m)^d / n^d) - C (((n/m+1)m)^d / n^d - 1) ≤ cubeRatio f n`. -/
theorem cubeRatio_mul_div_sub_le_cubeRatio {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (ω : Ω) :
    cubeRatio f ((n / m + 1) * m) ω * ((((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) -
        C * ((((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d - 1) ≤ cubeRatio f n ω := by
  have hle := le_add_one_mul_of_div (n := n) hm
  have h11 := boxFun_cube_le_cube_add_defect (d := d) hC hsub hle ω
  have hn0 : (0 : ℝ) < (n : ℝ) ^ d := pow_pos (Nat.cast_pos.mpr (by omega)) d
  have ha0 : (0 : ℝ) < (((n / m + 1) * m : ℕ) : ℝ) ^ d := pow_pos (Nat.cast_pos.mpr (by omega)) d
  unfold cubeRatio
  exact div_mul_div_sub_mul_sub_le_div_of_le_add_mul ha0 hn0 h11

/-- `(1 + m / n) ^ d → 1` as `n → ∞`. -/
theorem tendsto_one_add_div_pow_one (d : ℕ) {m : ℕ} (_unused_hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => (1 + (m : ℝ) / (n : ℝ)) ^ d) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) + (m : ℝ) / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ))
  simpa using h1.pow d

/-- Eventually in `n`, `1 ≤ ((n/m+1)m) ^ d / n ^ d`. -/
theorem eventually_one_le_pow_add_one_mul_div_pow (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d := by
  rw [eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : n ≤ (n / m + 1) * m := by
    have h := Nat.lt_div_mul_add (a := n) (b := m) hm
    rw [Nat.add_mul, one_mul]
    omega
  have hcast : (n : ℝ) ≤ (((n / m + 1) * m : ℕ) : ℝ) := by exact_mod_cast hle
  have hpow : (n : ℝ) ^ d ≤ (((n / m + 1) * m : ℕ) : ℝ) ^ d :=
    pow_le_pow_left₀ (Nat.cast_nonneg n) hcast d
  rw [le_div_iff₀ (pow_pos hnpos d)]
  linarith

/-- Eventually in `n`, `((n/m+1)m) ^ d / n ^ d ≤ (1 + m/n) ^ d`. -/
theorem eventually_pow_add_one_mul_div_pow_le (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ∀ᶠ n : ℕ in atTop,
      (((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d ≤ (1 + (m : ℝ) / (n : ℝ)) ^ d := by
  rw [eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (n / m + 1) * m ≤ n + m := by
    have h := Nat.div_mul_le_self n m
    rw [Nat.add_mul, one_mul]
    omega
  have hcast : (((n / m + 1) * m : ℕ) : ℝ) ≤ (n : ℝ) + (m : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hle
    rwa [Nat.cast_add] at h
  have hAn : (((n / m + 1) * m : ℕ) : ℝ) / (n : ℝ) ≤ 1 + (m : ℝ) / (n : ℝ) := by
    rw [div_le_iff₀ hnpos]
    have e : (1 + (m : ℝ) / (n : ℝ)) * (n : ℝ) = (n : ℝ) + (m : ℝ) := by
      field_simp
    rw [e]
    exact hcast
  rw [← div_pow]
  exact pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hnpos.le) hAn d

/-- `((n/m+1)m) ^ d / n ^ d → 1` as `n → ∞`, squeezed between `1` and `(1 + m/n) ^ d`. -/
theorem tendsto_pow_add_one_mul_div_pow_one (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => (((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) atTop (𝓝 1) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => (1 : ℝ))
    tendsto_const_nhds (tendsto_one_add_div_pow_one d hm) (eventually_one_le_pow_add_one_mul_div_pow
        d hm) (eventually_pow_add_one_mul_div_pow_le d hm)


/-- `C (((n/m+1)m)^d / n^d - 1) → 0` as `n → ∞`. -/
theorem tendsto_mul_pow_add_one_mul_div_pow_sub_one_zero (d : ℕ) {m : ℕ} (hm : 1 ≤ m) (C :
    ℝ) :
    Tendsto (fun n : ℕ => C * ((((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d - 1)) atTop (𝓝 0) := by
  have h := ((tendsto_pow_add_one_mul_div_pow_one d hm).sub_const 1).const_mul C
  simpa only [sub_self, mul_zero] using h

omit [MeasurableSpace Ω] in
/-- `liminf_k cubeRatio f (km) ≤ liminf_n cubeRatio f ((n/m+1)m)`, via the subsequence `n ↦ n/m +
1`. -/
theorem liminf_mul_le_liminf_div_add_one_mul {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω →
    ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) {m : ℕ} (hm : 1 ≤ m) (ω : Ω) :
    liminf (fun k : ℕ => cubeRatio f (k * m) ω) atTop ≤
      liminf (fun n : ℕ => cubeRatio f ((n / m + 1) * m) ω) atTop := by
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  have hv : Tendsto (fun n : ℕ => n / m + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (Nat.tendsto_div_const_atTop hm0)
  refine liminf_le_of_le (u := fun k : ℕ => cubeRatio f (k * m) ω)
    (isBoundedUnder_ge_of (fun k => (cubeRatio_nonneg_le hd hC (k * m) ω).1)) ?_
  intro A hA
  refine le_liminf_of_le (u := fun n : ℕ => cubeRatio f ((n / m + 1) * m) ω)
    ((isBoundedUnder_le_of (fun n => (cubeRatio_nonneg_le hd hC ((n / m + 1) * m)
        ω).2)).isCoboundedUnder_ge) ?_
  obtain ⟨K, hK⟩ := eventually_atTop.mp hA
  filter_upwards [hv.eventually (eventually_ge_atTop K)] with n hn
  exact hK _ hn

omit [MeasurableSpace Ω] in
/-- Eventually in `n`, `cubeRatio f ((n/m+1)m) ≤ cubeRatio f n + C (((n/m+1)m)^d/n^d - 1)`. -/
theorem eventually_cubeRatio_div_add_one_mul_le_add {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site
    d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    {m : ℕ} (hm : 1 ≤ m) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop, cubeRatio f ((n / m + 1) * m) ω ≤
      cubeRatio f n ω + C * ((((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d - 1) := by
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h49 := cubeRatio_mul_div_sub_le_cubeRatio hC hsub hm hn ω
  have hnm : n ≤ (n / m + 1) * m := by
    have hlt : n < n / m * m + m := Nat.lt_div_mul_add (Nat.pos_of_ne_zero hm0)
    rw [Nat.add_mul, one_mul]
    omega
  have hq1 : 1 ≤ (((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d := by
    rw [one_le_div (pow_pos (by exact_mod_cast hn : (0 : ℝ) < n) d)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (by exact_mod_cast hnm) d
  have hB0 : 0 ≤ cubeRatio f ((n / m + 1) * m) ω := (cubeRatio_nonneg_le hd hC ((n / m + 1) * m)
      ω).1
  linarith [le_mul_of_one_le_right hB0 hq1]

omit [MeasurableSpace Ω] in
/-- `liminf_k cubeRatio f (km) ≤ liminf_n cubeRatio f n`, since cubes of side a multiple of `m` are
cofinal and nested inside nearby general cubes. -/
theorem liminf_cubeRatio_mul_le_liminf_cubeRatio {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) →
    Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    {m : ℕ} (hm : 1 ≤ m) (ω : Ω) :
    liminf (fun k => cubeRatio f (k * m) ω) atTop ≤ liminf (fun n => cubeRatio f n ω) atTop := by
  have h1 := liminf_mul_le_liminf_div_add_one_mul hd hC hm ω
  have h2 := liminf_le_liminf_of_le_add (u := fun n : ℕ => cubeRatio f n ω)
    (v := fun n : ℕ => cubeRatio f ((n / m + 1) * m) ω)
    (isBoundedUnder_le_of (fun n => (cubeRatio_nonneg_le hd hC n ω).2))
    (isBoundedUnder_ge_of (fun n => (cubeRatio_nonneg_le hd hC ((n / m + 1) * m) ω).1))
    (tendsto_mul_pow_add_one_mul_div_pow_sub_one_zero d hm C)
        (eventually_cubeRatio_div_add_one_mul_le_add hd hC hsub hm ω)
  exact h1.trans h2


/-- `liminf_k cubeRatio f (φ k)` is integrable for any subsequence `φ`. -/
theorem integrable_liminf_cubeRatio_comp {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ} (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (φ : ℕ → ℕ) :
    Integrable (fun ω => liminf (fun k => cubeRatio f (φ k) ω) atTop) μ := by
  have hcu : ∀ n ω, 0 ≤ cubeRatio f n ω ∧ cubeRatio f n ω ≤ C :=
    fun n ω => cubeRatio_nonneg_le hd hC n ω
  have hnn : ∀ ω, 0 ≤ liminf (fun k => cubeRatio f (φ k) ω) atTop := fun ω =>
    Filter.le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun n => (hcu (φ n) ω).2))
      (Filter.Eventually.of_forall (fun n => (hcu (φ n) ω).1))
  have hle : ∀ ω, liminf (fun k => cubeRatio f (φ k) ω) atTop ≤ C := fun ω =>
    Filter.liminf_le_of_le (isBoundedUnder_ge_of (fun n => (hcu (φ n) ω).1))
      (fun b hb => by
        rcases Filter.eventually_atTop.mp hb with ⟨N, hN⟩
        exact le_trans (hN _ le_rfl) (hcu (φ N) ω).2)
  exact Integrable.of_bound
    (Measurable.liminf (fun i => measurable_cubeRatio hmeas (φ i))).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn ω)]; exact hle ω))

/-- For `δ > 0` there is a scale `m ≥ 1` with `∫ cubeRatio f m - δ ≤ ∫ cubeRatio f (N m)` for every
`N ≥ 1`, since `∫ cubeRatio f m` nearly attains its infimum over `m`. -/
theorem exists_scale_integral_cubeRatio_le {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} {f : Finset
    (Site d) → Ω → ℝ}
    {C : ℝ} (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ ω, cubeRatio f m ω ∂μ - δ ≤ ∫ ω, cubeRatio f (N * m) ω ∂μ := by
  have hnn : ∀ n, 0 ≤ ∫ ω, cubeRatio f n ω ∂μ :=
    fun n => integral_nonneg fun ω => (cubeRatio_nonneg_le hd hC n ω).1
  have hbdd : BddBelow (Set.range fun n : ℕ => ∫ ω, cubeRatio f (n + 1) ω ∂μ) :=
    ⟨0, fun _ ⟨n, hn⟩ => hn ▸ hnn _⟩
  obtain ⟨n, hn⟩ := exists_lt_of_ciInf_lt
    (lt_add_of_pos_right (⨅ n : ℕ, ∫ ω, cubeRatio f (n + 1) ω ∂μ) hδ)
  refine ⟨n + 1, by omega, fun N hN => ?_⟩
  have h := ciInf_le hbdd (N * (n + 1) - 1)
  rw [show N * (n + 1) - 1 + 1 = N * (n + 1) by
    have : 1 ≤ N * (n + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega] at h
  linarith

/-- At the scale `m` of `exists_scale_integral_cubeRatio_le`, `∫ cubeRatio f m ≤ ∫ liminf_n
cubeRatio f n + α + C (akMaxConst d * δ / α)`, applying the unit-scale bound to the
coarse-grained process. -/
theorem integral_cubeRatio_scale_le_integral_liminf_add {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    {m : ℕ} (hm : 1 ≤ m) {δ : ℝ}
    (hmδ : ∀ N : ℕ, 1 ≤ N → ∫ ω, cubeRatio f m ω ∂μ - δ ≤ ∫ ω, cubeRatio f (N * m) ω ∂μ)
    {α : ℝ} (hα : 0 < α) :
    ∫ ω, cubeRatio f m ω ∂μ ≤
      ∫ ω, liminf (fun n => cubeRatio f n ω) atTop ∂μ + α + C * (akMaxConst d * δ / α) := by
  obtain ⟨hσ, hσadd⟩ := measurePreserving_smul_action τ hτ hτadd m
  obtain ⟨hFm, hFC, hFsub, hFstat⟩ := coarse_isBoxSplit_and_stat τ hmeas hC hsub hstat hm
  have hr : ∀ k ω, cubeRatio (coarse f m) k ω = cubeRatio f (k * m) ω :=
    fun k ω => cubeRatio_coarse_eq_cubeRatio_mul f hm k ω
  have hFη : ∀ N : ℕ, 1 ≤ N → ∫ ω, cubeRatio (coarse f m) 1 ω ∂μ - δ ≤
      ∫ ω, cubeRatio (coarse f m) N ω ∂μ := fun N hN => by
    simp only [hr, one_mul]; exact hmδ N hN
  have h := integral_cubeRatio_one_le_integral_liminf_add hd (fun z => τ ((m : ℤ) • z)) hσ (fun z w
      ω => hσadd z w ω) hFm hFC
    hFsub hFstat hFη hα
  simp only [hr, one_mul] at h
  have hmono : ∫ ω, liminf (fun k => cubeRatio f (k * m) ω) atTop ∂μ ≤
      ∫ ω, liminf (fun n => cubeRatio f n ω) atTop ∂μ :=
    integral_mono (integrable_liminf_cubeRatio_comp hd hmeas hC (fun k => k * m))
      (integrable_liminf_cubeRatio_comp hd hmeas hC id) fun ω =>
          liminf_cubeRatio_mul_le_liminf_cubeRatio hd hC hsub hm ω
  linarith

/-- Real-algebra bound used in the assembly: with `K = akMaxConst d`, `C * (K * (ε² / (4(C+1)K)) /
(ε/2)) ≤ ε / 2`. -/
theorem mul_div_le_half_of_pos {C K ε : ℝ} (hC : 0 ≤ C) (hK : 0 < K) (hε : 0 < ε) :
    C * (K * (ε ^ 2 / (4 * (C + 1) * K)) / (ε / 2)) ≤ ε / 2 := by
  have hC1 : 0 < C + 1 := by linarith
  have e : C * (K * (ε ^ 2 / (4 * (C + 1) * K)) / (ε / 2)) = C * ε / (2 * (C + 1)) := by
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity)]
  nlinarith

/-- The Akcoglu-Krengel lower bound: for every `ε > 0` there is a scale `m ≥ 1` with `∫ cubeRatio f
m ≤ ∫ liminf_n cubeRatio f n + ε`, hence `γ ≤ ∫ liminf cubeRatio f n` for `γ = inf_m ∫ cubeRatio
f m`. -/
theorem exists_integral_cubeRatio_le_integral_liminf_add {d : ℕ} (hd : 1 ≤ d) {μ : Measure
    Ω} [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧
      ∫ ω, cubeRatio f m ω ∂μ ≤ ∫ ω, liminf (fun n => cubeRatio f n ω) atTop ∂μ + ε := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hC0 : 0 ≤ C := nonneg_of_boxFun_bound hC ω0
  have hK := akMaxConst_pos hd
  have hδ : 0 < ε ^ 2 / (4 * (C + 1) * akMaxConst d) := by positivity
  obtain ⟨m, hm, hmδ⟩ := exists_scale_integral_cubeRatio_le (μ := μ) hd hC hδ
  refine ⟨m, hm, ?_⟩
  have h := integral_cubeRatio_scale_le_integral_liminf_add hd τ hτ hτadd hmeas hC hsub hstat hm hmδ
      (half_pos hε)
  have hs := mul_div_le_half_of_pos hC0 hK hε
  linarith

/-- `liminf_n cubeRatio f n = limsup_n cubeRatio f n` almost everywhere, since their difference is
nonnegative with integral `0` by the upper and lower bounds
`integral_limsup_cubeRatio_le_integral_cubeRatio` and
`exists_integral_cubeRatio_le_integral_liminf_add`. -/
theorem liminf_cubeRatio_eq_limsup_cubeRatio_ae {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω)) :
    ∀ᵐ ω ∂μ, liminf (fun n => cubeRatio f n ω) atTop = limsup (fun n => cubeRatio f n ω) atTop := by
  have hcu : ∀ n ω, 0 ≤ cubeRatio f n ω ∧ cubeRatio f n ω ≤ C :=
    fun n ω => cubeRatio_nonneg_le hd hC n ω
  have hls_nonneg : ∀ ω, 0 ≤ limsup (fun n => cubeRatio f n ω) atTop := fun ω =>
    Filter.le_limsup_of_le (isBoundedUnder_le_of (fun n => (hcu n ω).2))
      (fun b hb => by
        rcases Filter.eventually_atTop.mp hb with ⟨N, hN⟩
        exact le_trans (hcu (max N 1) ω).1 (hN _ (le_max_left _ _)))
  have hls_le : ∀ ω, limsup (fun n => cubeRatio f n ω) atTop ≤ C := fun ω =>
    Filter.limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun n => (hcu n ω).1))
      (Filter.Eventually.of_forall (fun n => (hcu n ω).2))
  have hli_nonneg : ∀ ω, 0 ≤ liminf (fun n => cubeRatio f n ω) atTop := fun ω =>
    Filter.le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun n => (hcu n ω).2))
      (Filter.Eventually.of_forall (fun n => (hcu n ω).1))
  have hli_le : ∀ ω, liminf (fun n => cubeRatio f n ω) atTop ≤ C := fun ω =>
    Filter.liminf_le_of_le (isBoundedUnder_ge_of (fun n => (hcu n ω).1))
      (fun b hb => by
        rcases Filter.eventually_atTop.mp hb with ⟨N, hN⟩
        exact le_trans (hN _ (le_max_left _ _)) (hcu (max N 1) ω).2)
  have hlimsup_meas : Measurable (fun ω => limsup (fun n => cubeRatio f n ω) atTop) :=
    Measurable.limsup (fun i => measurable_cubeRatio hmeas i)
  have hliminf_meas : Measurable (fun ω => liminf (fun n => cubeRatio f n ω) atTop) :=
    Measurable.liminf (fun i => measurable_cubeRatio hmeas i)
  have hls_int : Integrable (fun ω => limsup (fun n => cubeRatio f n ω) atTop) μ :=
    Integrable.of_bound hlimsup_meas.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hls_nonneg ω)]
        exact hls_le ω))
  have hli_int : Integrable (fun ω => liminf (fun n => cubeRatio f n ω) atTop) μ :=
    Integrable.of_bound hliminf_meas.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hli_nonneg ω)]
        exact hli_le ω))
  set D : Ω → ℝ := fun ω => limsup (fun n => cubeRatio f n ω) atTop -
      liminf (fun n => cubeRatio f n ω) atTop with hD
  have hDnn : ∀ ω, 0 ≤ D ω := fun ω => by
    have hle := liminf_le_limsup
      (isBoundedUnder_le_of (fun n => (hcu n ω).2))
      (isBoundedUnder_ge_of (fun n => (hcu n ω).1))
    simp only [hD]
    linarith
  have hDint : Integrable D μ :=
    Integrable.of_bound (hlimsup_meas.sub hliminf_meas).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hDnn ω)]
        simp only [hD]
        linarith [hls_le ω, hli_nonneg ω]))
  have hDle : ∀ ε : ℝ, 0 < ε → ∫ ω, D ω ∂μ ≤ ε := fun ε hε => by
    obtain ⟨m, hm1, hme⟩ := exists_integral_cubeRatio_le_integral_liminf_add hd τ hτ hτadd hmeas hC
        hsub hstat hε
    have hup := integral_limsup_cubeRatio_le_integral_cubeRatio hd τ hτ hτadd hmeas hC hsub hstat
        hm1
    simp only [hD]
    rw [integral_sub hls_int hli_int]
    linarith [hme, hup]
  have hDz : ∫ ω, D ω ∂μ = 0 :=
    le_antisymm
      (le_of_forall_pos_le_add (fun ε hε => by
        have := hDle ε hε
        linarith))
      (integral_nonneg (fun ω => hDnn ω))
  have hDae : ∀ᵐ ω ∂μ, D ω = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => hDnn ω) hDint).1 hDz
  filter_upwards [hDae] with ω hω
  simp only [hD] at hω
  linarith


/-- The almost sure half. -/
theorem akcoglu_krengel (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω))
    (f : Finset (Site d) → Ω → ℝ) (hmeas : ∀ A, Measurable (f A))
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    (hbd : ∃ C, ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω) :
    ∃ L : Ω → ℝ, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => f (latticeCube d n) ω / (n : ℝ) ^ d) atTop (𝓝 (L ω)) := by
  obtain ⟨C, hC⟩ := hbd
  refine ⟨fun ω => limsup (fun n => cubeRatio f n ω) atTop, ?_⟩
  filter_upwards [liminf_cubeRatio_eq_limsup_cubeRatio_ae hd τ hτ hτadd hmeas hC hsub hstat] with ω
      hω
  have hb := fun n => cubeRatio_nonneg_le hd hC n ω
  exact tendsto_of_liminf_eq_limsup hω rfl (isBoundedUnder_le_of fun n => (hb n).2)
    (isBoundedUnder_ge_of fun n => (hb n).1)

end LatticeProb
