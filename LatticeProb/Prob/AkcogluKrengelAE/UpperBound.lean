import LatticeProb.Prob.AkcogluKrengelAE.BoundedErgodic

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# The upper bound (Step 3)

Applying the bounded pointwise ergodic theorem to the sublattice action `z ↦ τ (m • z)` and the grid
bound of Step 1 gives, for every `m ≥ 1`, an a.e. bound `limsup_n cubeRatio f n ≤ G_m` with `∫ G_m =
∫ cubeRatio f m`.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The sublattice action `z ↦ τ (m • z)` is measure-preserving in each coordinate and additive. -/
theorem measurePreserving_smul_action {d : ℕ} {μ : Measure Ω} (τ : Site d → Ω → Ω)
    (hτ : ∀ z, MeasurePreserving (τ z) μ μ) (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω))
    (m : ℕ) :
    (∀ z, MeasurePreserving (fun ω => τ ((m : ℤ) • z) ω) μ μ) ∧
      ∀ z w ω, τ ((m : ℤ) • (z + w)) ω = τ ((m : ℤ) • z) (τ ((m : ℤ) • w) ω) := by
  refine ⟨fun z => hτ ((m : ℤ) • z), ?_⟩
  intro z w ω
  rw [smul_add, hτadd]


omit [MeasurableSpace Ω] in
/-- The trivial case `k = 0` of the grid bound: `f` of the empty cube is at most `0`. -/
theorem boxFun_cube_zero_le {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (m : ℕ) (X : ℝ) (ω : Ω) :
    f (latticeCube d (0 * m)) ω ≤ ((0 * m : ℕ) : ℝ) ^ d * X := by
  have he : latticeCube d (0 * m) = ∅ :=
    Finset.Icc_eq_empty (fun h => by have := h ⟨0, hd⟩; simp at this)
  rw [he, boxFun_empty_eq_zero hC ω, zero_mul, Nat.cast_zero, zero_pow (by omega), zero_mul]

omit [MeasurableSpace Ω] in
/-- Unfolding `gridAvg` of the sublattice action applied to `cubeRatio f m` as an explicit sum
divided by `m ^ d` and `k ^ d`. -/
theorem gridAvg_smul_eq_sum_div_pow {d : ℕ} (τ : Site d → Ω → Ω) (f : Finset (Site d) → Ω →
    ℝ) (m k : ℕ)
    (ω : Ω) :
    gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m) Finset.univ k ω =
      (∑ w ∈ gridSet d Finset.univ k, f (latticeCube d m) (τ ((m : ℤ) • natToSite w) ω)) /
        (m : ℝ) ^ d / (k : ℝ) ^ d := by
  simp only [gridAvg, cubeRatio, Finset.card_univ, Fintype.card_fin, Finset.sum_div]

/-- Clearing denominators in `((k * m) ^ d) * (S / m ^ d / k ^ d) = S`. -/
theorem pow_mul_div_pow_pow_eq (d : ℕ) {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (S : ℝ) :
    ((k * m : ℕ) : ℝ) ^ d * (S / (m : ℝ) ^ d / (k : ℝ) ^ d) = S := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_mul, mul_pow]
  field_simp

omit [MeasurableSpace Ω] in
/-- `f` of the cube of side `k * m` is at most `(k * m) ^ d` times the grid average of `cubeRatio f
m` along the sublattice action `z ↦ τ (m • z)`. -/
theorem boxFun_cube_le_pow_mul_gridAvg {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω → ℝ} {C
    : ℝ}
    (τ : Site d → Ω → Ω)
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (ω : Ω) :
    f (latticeCube d (k * m)) ω ≤
      ((k * m : ℕ) : ℝ) ^ d *
        gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m) Finset.univ k ω := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact boxFun_cube_zero_le hd hC m _ ω
  · rw [gridAvg_smul_eq_sum_div_pow, pow_mul_div_pow_pow_eq d hm hk]
    exact boxFun_cube_le_sum_stat τ hC hsub hstat m k ω

/-- Real-algebra step turning `F ≤ K * A + C * (N - K)` into `F / N ≤ A + C * (1 - K / N)`. -/
theorem div_le_add_of_le_add_mul {F K N A C : ℝ} (hA : 0 ≤ A) (hK : K ≤ N) (hN : 0 < N)
    (h : F ≤ K * A + C * (N - K)) : F / N ≤ A + C * (1 - K / N) := by
  rw [div_le_iff₀ hN]
  have e : (A + C * (1 - K / N)) * N = A * N + C * (N - K) := by field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hK hA]

omit [MeasurableSpace Ω] in
/-- The grid average of `cubeRatio f m` along the sublattice action is nonnegative. -/
theorem gridAvg_smul_cubeRatio_nonneg {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω → ℝ} {C
    : ℝ}
    (τ : Site d → Ω → Ω) (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (m k : ℕ) (ω : Ω) :
    0 ≤ gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m) Finset.univ k ω := by
  exact div_nonneg (Finset.sum_nonneg fun w _ => (cubeRatio_nonneg_le hd hC m _).1) (by positivity)

/-- `(n / m * m) ^ d ≤ n ^ d`, since `n / m * m ≤ n`. -/
theorem pow_div_mul_le_pow (d n m : ℕ) : ((n / m * m : ℕ) : ℝ) ^ d ≤ (n : ℝ) ^ d := by
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_mul_le_self n m) d

omit [MeasurableSpace Ω] in
/-- Pointwise upper bound: `cubeRatio f n` is at most the grid average of `cubeRatio f m` over `n /
m` grid steps, plus a defect term `C * (1 - (n / m * m) ^ d / n ^ d)`. -/
theorem cubeRatio_le_gridAvg_add_defect {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω → ℝ}
    {C : ℝ}
    (τ : Site d → Ω → Ω)
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (ω : Ω) :
    cubeRatio f n ω ≤
      gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m) Finset.univ (n / m) ω +
        C * (1 - ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) := by
  have h11 := boxFun_cube_le_cube_add_defect (d := d) hC hsub (Nat.div_mul_le_self n m) ω
  have h40 := boxFun_cube_le_pow_mul_gridAvg hd τ hC hsub hstat hm (n / m) ω
  have hN : (0 : ℝ) < (n : ℝ) ^ d := pow_pos (by exact_mod_cast hn) d
  show f (latticeCube d n) ω / (n : ℝ) ^ d ≤ _
  exact div_le_add_of_le_add_mul (gridAvg_smul_cubeRatio_nonneg hd τ hC m (n / m) ω)
      (pow_div_mul_le_pow d n m) hN
    (by linarith)

/-- The volume ratio `(n / m * m) ^ d / n ^ d` tends to `1` as `n → ∞`, squeezed between `(1 - m /
n) ^ d` and `1`. -/
theorem tendsto_pow_div_mul_div_pow_one (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) atTop (𝓝 1) := by
  have hglow : Tendsto (fun n : ℕ => (1 - (m : ℝ) / (n : ℝ)) ^ d) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => 1 - (m : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ))
    simpa using h1.pow d
  have hhigh : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hev1 : ∀ᶠ n : ℕ in atTop,
      (1 - (m : ℝ) / (n : ℝ)) ^ d ≤ ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d := by
    filter_upwards [eventually_ge_atTop m, eventually_ge_atTop 1] with n hmn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hmnc : ((n - m : ℕ) : ℝ) ≤ ((n / m * m : ℕ) : ℝ) := by
      have hlt : n - m ≤ n / m * m := by
        have hh := Nat.lt_div_mul_add (a := n) (b := m) hm
        omega
      exact_mod_cast hlt
    have hbase : 1 - (m : ℝ) / (n : ℝ) ≤ ((n / m * m : ℕ) : ℝ) / (n : ℝ) := by
      have hsub : (1 : ℝ) - (m : ℝ) / (n : ℝ) = ((n - m : ℕ) : ℝ) / (n : ℝ) := by
        rw [Nat.cast_sub hmn, sub_div, div_self hnne]
      rw [hsub]
      exact div_le_div_of_nonneg_right hmnc hnpos.le
    have hnn : (0 : ℝ) ≤ 1 - (m : ℝ) / (n : ℝ) := by
      have hmle : (m : ℝ) / (n : ℝ) ≤ 1 := by
        rw [div_le_one hnpos]
        exact_mod_cast hmn
      linarith
    calc (1 - (m : ℝ) / (n : ℝ)) ^ d
        ≤ (((n / m * m : ℕ) : ℝ) / (n : ℝ)) ^ d := pow_le_pow_left₀ hnn hbase d
      _ = ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d := div_pow _ _ d
  have hev2 : ∀ᶠ n : ℕ in atTop, ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d ≤ (1 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_le_one (pow_pos hnpos d)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg (n / m * m))
      (by exact_mod_cast Nat.div_mul_le_self n m) d
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hglow hhigh hev1 hev2

/-- The volume ratio `(n / m * m) ^ d / n ^ d` tends to `1` as `n → ∞`. -/
theorem tendsto_pow_div_mul_div_pow_one' (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) atTop (𝓝 1) := by
  exact tendsto_pow_div_mul_div_pow_one d hm


/-- If the grid average of `cubeRatio f m` converges a.e. to `G`, then a.e. `limsup_n cubeRatio f n
≤ G`, by passing `cubeRatio_le_gridAvg_add_defect` to the limit along `n / m → ∞` and the defect
term to `0`. -/
theorem ae_limsup_cubeRatio_le {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} {f : Finset (Site d) → Ω
    → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω)
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    {m : ℕ} (hm : 1 ≤ m) {G : Ω → ℝ}
    (hG : ∀ᵐ ω ∂μ, Tendsto (fun k => gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m)
      Finset.univ k ω) atTop (𝓝 (G ω))) :
    ∀ᵐ ω ∂μ, limsup (fun n => cubeRatio f n ω) atTop ≤ G ω := by
  refine Filter.Eventually.mono hG fun ω hω => ?_
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  have hcomp : Tendsto (fun n : ℕ => gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m)
      Finset.univ (n / m) ω) atTop (𝓝 (G ω)) :=
    hω.comp (Nat.tendsto_div_const_atTop hm0)
  have hratio : Tendsto (fun n : ℕ => ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) atTop (𝓝 1) :=
    tendsto_pow_div_mul_div_pow_one' d hm
  have hlim : Tendsto (fun n : ℕ => gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m)
      Finset.univ (n / m) ω + C * (1 - ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d))
      atTop (𝓝 (G ω + C * (1 - 1))) :=
    hcomp.add ((hratio.const_sub 1).const_mul C)
  have hz : C * (1 - (1 : ℝ)) = 0 :=
    Eq.trans (congrArg (fun t : ℝ => C * t) (sub_self (1 : ℝ))) (mul_zero C)
  have hlim' : Tendsto (fun n : ℕ => gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m)
      Finset.univ (n / m) ω + C * (1 - ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d))
      atTop (𝓝 (G ω)) := add_zero (G ω) ▸ (hz ▸ hlim)
  have hle : (fun n : ℕ => cubeRatio f n ω) ≤ᶠ[atTop]
      (fun n : ℕ => gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m)
        Finset.univ (n / m) ω + C * (1 - ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d)) :=
    eventually_atTop.mpr ⟨1, fun n hn => cubeRatio_le_gridAvg_add_defect hd τ hC hsub hstat hm hn ω⟩
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => cubeRatio f n ω) :=
    (isBoundedUnder_ge_of fun n => (cubeRatio_nonneg_le hd hC n ω).1).isCoboundedUnder_le
  exact hlim'.limsup_eq ▸ limsup_le_limsup hle hcob hlim'.isBoundedUnder_le


/-- `limsup_n cubeRatio f n` is integrable, being measurable and valued in `[0, C]`. -/
theorem integrable_limsup_cubeRatio {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ} (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) :
    Integrable (fun ω => limsup (fun n => cubeRatio f n ω) atTop) μ := by
  have hcu : ∀ n ω, 0 ≤ cubeRatio f n ω ∧ cubeRatio f n ω ≤ C :=
    fun n ω => cubeRatio_nonneg_le hd hC n ω
  have hnn : ∀ ω, 0 ≤ limsup (fun n => cubeRatio f n ω) atTop := fun ω =>
    Filter.le_limsup_of_le (isBoundedUnder_le_of (fun n => (hcu n ω).2))
      (fun b hb => by
        rcases Filter.eventually_atTop.mp hb with ⟨N, hN⟩
        exact le_trans (hcu (max N 1) ω).1 (hN _ (le_max_left _ _)))
  have hle : ∀ ω, limsup (fun n => cubeRatio f n ω) atTop ≤ C := fun ω =>
    Filter.limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun n => (hcu n ω).1))
      (Filter.Eventually.of_forall (fun n => (hcu n ω).2))
  exact Integrable.of_bound (Measurable.limsup (fun i => measurable_cubeRatio hmeas
      i)).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn ω)]; exact hle ω))

/-- The grid average of `cubeRatio f m` along the sublattice action `z ↦ τ (m • z)` converges a.e.
to some bounded measurable `G` with `∫ G = ∫ cubeRatio f m`, by the bounded ergodic theorem
`exists_ae_tendsto_gridAvg_univ_with_integral`. -/
theorem exists_ae_tendsto_gridAvg_smul_cubeRatio {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (m : ℕ) :
    ∃ G : Ω → ℝ, Measurable G ∧ (∀ x, |G x| ≤ C) ∧
      ∫ ω, G ω ∂μ = ∫ ω, cubeRatio f m ω ∂μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun k => gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m)
        Finset.univ k ω) atTop (𝓝 (G ω)) := by
  obtain ⟨hσ, hσadd⟩ := measurePreserving_smul_action τ hτ hτadd m
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hb : ∀ x, |cubeRatio f m x| ≤ C := fun x => abs_le.2
    ⟨by
        linarith [(cubeRatio_nonneg_le hd hC m x).1, nonneg_of_boxFun_bound hC x],
            (cubeRatio_nonneg_le hd hC m x).2⟩
  exact exists_ae_tendsto_gridAvg_univ_with_integral hσ (fun z w ω => hσadd z w ω)
      (measurable_cubeRatio hmeas m) (nonneg_of_boxFun_bound hC ω0) hb

/-- The upper bound in integral form: `∫ limsup_n cubeRatio f n ≤ ∫ cubeRatio f m`, for every `m ≥
1`. -/
theorem integral_limsup_cubeRatio_le_integral_cubeRatio {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    {m : ℕ} (hm : 1 ≤ m) :
    ∫ ω, limsup (fun n => cubeRatio f n ω) atTop ∂μ ≤ ∫ ω, cubeRatio f m ω ∂μ := by
  obtain ⟨G, hGm, hGb, hGint, hG⟩ := exists_ae_tendsto_gridAvg_smul_cubeRatio hd τ hτ hτadd hmeas hC
      m
  have hle := ae_limsup_cubeRatio_le hd τ hC hsub hstat hm hG
  rw [← hGint]
  exact integral_mono_ae (integrable_limsup_cubeRatio hd hmeas hC)
    (Integrable.of_bound hGm.aestronglyMeasurable C
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hGb x)) hle

end LatticeProb
