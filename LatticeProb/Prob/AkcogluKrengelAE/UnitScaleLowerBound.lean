import LatticeProb.Prob.AkcogluKrengelAE.MaximalInequalityCore

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# From the maximal inequality to the integral, and the unit-scale lower bound (Step 4, parts C-D)

The maximal inequality controls the tail of a bounded random variable in integral form: `∫ X ≤ α + C
* akMaxConst d * ρ / α` for every `α > 0`. Applied to `boxDefect F`, this bounds `∫ limsup_k
boxDefect F (Q_k) / k ^ d`. Combined with the bounded pointwise ergodic theorem of Step 2, this
gives the unit-scale lower bound: if `∫ cubeRatio F N ≥ ∫ cubeRatio F 1 - η` for every `N ≥ 1`, then
`∫ cubeRatio F 1 ≤ ∫ liminf_k cubeRatio F k + α + C * akMaxConst d * η / α`.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- For bounded measurable `X` with a tail bound `μ.real {α < X} ≤ c / α`, `∫ X ≤ α + M * (c / α)`
for every `α > 0`. -/
theorem integral_le_add_mul_div_of_tail_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure
    Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) {M c : ℝ} (hXb : ∀ ω, 0 ≤ X ω ∧ X ω ≤ M)
    (htail : ∀ α, 0 < α → μ.real {ω | α < X ω} ≤ c / α) {α : ℝ} (hα : 0 < α) :
    ∫ ω, X ω ∂μ ≤ α + M * (c / α) := by
  have hTm : MeasurableSet {ω | α < X ω} := measurableSet_lt measurable_const hX
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hM0 : (0 : ℝ) ≤ M := le_trans (hXb ω0).1 (hXb ω0).2
  have hXint : Integrable X μ := Integrable.of_bound hX.aestronglyMeasurable M (ae_of_all _ fun ω =>
      by
    rw [Real.norm_eq_abs, abs_of_nonneg (hXb ω).1]
    exact (hXb ω).2)
  have hind : Integrable (Set.indicator {ω | α < X ω} (fun _ => M)) μ :=
    (integrable_const M).indicator hTm
  have hgint : Integrable (fun ω => α + Set.indicator {ω | α < X ω} (fun _ => M) ω) μ :=
    (integrable_const α).add hind
  have hpoint : ∀ ω, X ω ≤ α + Set.indicator {ω | α < X ω} (fun _ => M) ω := fun ω => by
    rw [Set.indicator_apply]
    split_ifs with h
    · linarith [(hXb ω).2]
    · have hle : X ω ≤ α := not_lt.1 h
      linarith
  have hInt2 : ∫ ω, (α + Set.indicator {ω | α < X ω} (fun _ => M) ω) ∂μ
      = α + M * μ.real {ω | α < X ω} := by
    rw [integral_add (integrable_const α) hind, integral_const,
      integral_indicator_const M hTm, probReal_univ]
    simp only [smul_eq_mul]
    ring
  have hkey : ∫ ω, X ω ∂μ ≤ α + M * μ.real {ω | α < X ω} := by
    rw [← hInt2]
    exact integral_mono hXint hgint hpoint
  exact le_trans hkey (by linarith [mul_le_mul_of_nonneg_left (htail α hα) hM0])

/-- For bounded measurable `X` with a tail bound `μ.real {α < X} ≤ c / α`, `∫ X ≤ α + M * (c / α)`
for every `α > 0`. -/
theorem integral_le_add_mul_div_of_tail_bound' {μ : Measure Ω} [IsProbabilityMeasure μ] {X :
    Ω → ℝ} (hX : Measurable X)
    {M c : ℝ} (hXb : ∀ ω, 0 ≤ X ω ∧ X ω ≤ M)
    (htail : ∀ α, 0 < α → μ.real {ω | α < X ω} ≤ c / α) {α : ℝ} (hα : 0 < α) :
    ∫ ω, X ω ∂μ ≤ α + M * (c / α) := by
  exact integral_le_add_mul_div_of_tail_bound hX hXb htail hα


omit [MeasurableSpace Ω] in
/-- If `α` is exceeded by the limsup of `R (cube k) / k ^ d`, some `k ≥ 1` has `α k ^ d < R (cube
k)`. -/
theorem subset_bad_of_lt_limsup {d : ℕ} {R : Finset (Site d) → Ω → ℝ} {M : ℝ}
    (hR : ∀ (k : ℕ) ω, 0 ≤ R (latticeCube d k) ω / (k : ℝ) ^ d ∧
      R (latticeCube d k) ω / (k : ℝ) ^ d ≤ M) {α : ℝ} (_unused_hα : 0 < α) :
    {ω | α < limsup (fun k : ℕ => R (latticeCube d k) ω / (k : ℝ) ^ d) atTop} ⊆
      {ω | ∃ k : ℕ, 1 ≤ k ∧ α * (k : ℝ) ^ d < R (latticeCube d k) ω} := by
  intro ω hω
  have hcob : IsCoboundedUnder (· ≤ ·) atTop
      (fun k : ℕ => R (latticeCube d k) ω / (k : ℝ) ^ d) :=
    isCoboundedUnder_le_of_le atTop (fun k => (hR k ω).1)
  have hfreq : ∃ᶠ k in atTop, α < R (latticeCube d k) ω / (k : ℝ) ^ d :=
    frequently_lt_of_lt_limsup hcob hω
  have hall : ∃ᶠ k : ℕ in atTop,
      1 ≤ k ∧ α < R (latticeCube d k) ω / (k : ℝ) ^ d :=
    (hfreq.and_eventually (eventually_ge_atTop 1)).mono fun k h => ⟨h.2, h.1⟩
  obtain ⟨k, hk1, hklt⟩ := hall.exists
  refine ⟨k, hk1, ?_⟩
  have hpos : (0 : ℝ) < (k : ℝ) ^ d := pow_pos (by exact_mod_cast hk1) d
  exact (lt_div_iff₀ hpos).mp hklt


/-! #### (D) The unit-scale lower bound -/

/-- If the mean of `cubeRatio F N` is within `η` of the mean at `N = 1` for every `N`, then `∫
boxDefect F (cube N) ≤ η N ^ d`. -/
theorem integral_boxDefect_cube_le_mul_pow {d : ℕ} (_unused_hd : 1 ≤ d) {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hmeas : ∀ A, Measurable (F A))
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω))
    {η : ℝ} (hFη : ∀ N : ℕ, 1 ≤ N → ∫ ω, cubeRatio F 1 ω ∂μ - η ≤ ∫ ω, cubeRatio F N ω ∂μ)
    {N : ℕ} (hN : 1 ≤ N) :
    ∫ ω, boxDefect F (latticeCube d N) ω ∂μ ≤ η * (N : ℝ) ^ d := by
  have hb1 : ∀ x, |F (latticeCube d 1) x| ≤ C := by
    intro x
    have h := hC (latticeCube d 1) x
    have hc : ((latticeCube d 1).card : ℝ) = 1 := by
      rw [card_latticeCube_eq_pow' d 1, one_pow, Nat.cast_one]
    rw [hc, mul_one] at h
    exact abs_le.2 ⟨by linarith [h.1], h.2⟩
  have hAPm : Measurable (fun ω => addPart F (latticeCube d N) ω) := by
    unfold addPart
    exact Finset.measurable_sum _ fun z _ => hmeas {z}
  have hAPint : Integrable (fun ω => addPart F (latticeCube d N) ω) μ := by
    refine Integrable.of_bound hAPm.aestronglyMeasurable (C * ((latticeCube d N).card : ℝ)) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (addPart_nonneg_le hC _ ω).1]
    exact (addPart_nonneg_le hC _ ω).2
  have hFint : Integrable (fun ω => F (latticeCube d N) ω) μ := by
    refine Integrable.of_bound (hmeas _).aestronglyMeasurable (C * ((latticeCube d N).card : ℝ)) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hC _ ω).1]
    exact (hC _ ω).2
  have hEq : ∫ ω, boxDefect F (latticeCube d N) ω ∂μ =
      ∫ ω, addPart F (latticeCube d N) ω ∂μ - ∫ ω, F (latticeCube d N) ω ∂μ := by
    simp only [boxDefect]
    exact integral_sub hAPint hFint
  have hAP : ∫ ω, addPart F (latticeCube d N) ω ∂μ =
      (N : ℝ) ^ d * ∫ ω, cubeRatio F 1 ω ∂μ := by
    have hfun : (fun ω => addPart F (latticeCube d N) ω) =
        fun ω => (N : ℝ) ^ d * gridAvg τ (F (latticeCube d 1)) Finset.univ N ω :=
      funext fun ω => addPart_cube_eq_pow_mul_gridAvg τ hstat hN ω
    rw [hfun, integral_const_mul, integral_gridAvg_univ_eq_integral hτ (hmeas (latticeCube d 1)) hb1
        hN]
    congr 1
    simp [cubeRatio]
  have hF' : ∫ ω, cubeRatio F N ω ∂μ =
      (∫ ω, F (latticeCube d N) ω ∂μ) / (N : ℝ) ^ d := by
    have hfun : (fun ω => cubeRatio F N ω) =
        fun ω => F (latticeCube d N) ω / (N : ℝ) ^ d := rfl
    rw [hfun, integral_div]
  have hNd : (N : ℝ) ^ d ≠ 0 := pow_ne_zero d (by positivity)
  have hF : ∫ ω, F (latticeCube d N) ω ∂μ =
      (N : ℝ) ^ d * ∫ ω, cubeRatio F N ω ∂μ := by
    rw [hF']
    exact (mul_div_cancel₀ _ hNd).symm
  have hexp : (N : ℝ) ^ d * (∫ ω, cubeRatio F 1 ω ∂μ) -
        (N : ℝ) ^ d * (∫ ω, cubeRatio F N ω ∂μ) ≤ η * (N : ℝ) ^ d := by
    have h1 := mul_le_mul_of_nonneg_left (hFη N hN) (pow_nonneg (Nat.cast_nonneg N) d)
    have e : (N : ℝ) ^ d * (∫ ω, cubeRatio F 1 ω ∂μ - η) =
        (N : ℝ) ^ d * (∫ ω, cubeRatio F 1 ω ∂μ) - (N : ℝ) ^ d * η := by ring
    rw [e] at h1
    rw [mul_comm η]
    linarith
  rw [hEq, hAP, hF]
  exact hexp


omit [MeasurableSpace Ω] in
/-- `cubeRatio F k` equals the grid average of `F` on unit cells minus `boxDefect F (cube k) / k ^
d`. -/
theorem cubeRatio_eq_gridAvg_sub_boxDefect_div_pow {d : ℕ} {F : Finset (Site d) → Ω → ℝ} (τ
    : Site d → Ω → Ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω)) {k : ℕ} (hk : 1 ≤ k) (ω : Ω) :
    cubeRatio F k ω =
      gridAvg τ (F (latticeCube d 1)) Finset.univ k ω -
        boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d := by
  have hk0 : (k : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : k ≠ 0))
  unfold cubeRatio boxDefect
  rw [addPart_cube_eq_pow_mul_gridAvg τ hstat hk ω, sub_div, mul_div_cancel_left₀ _ hk0]
  ring

/-- If `u = v - w` eventually, `v → H`, and `w` is bounded, then `H - limsup w ≤ liminf u`. -/
theorem sub_limsup_le_liminf_of_eq_sub {u v w : ℕ → ℝ} {H M : ℝ} (huvw : ∀ k, 1 ≤ k → u k =
    v k - w k)
    (hv : Tendsto v atTop (𝓝 H)) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ M) :
    H - limsup w atTop ≤ liminf u atTop := by
  have huub : ∀ᶠ k in atTop, u k ≤ H + 1 := by
    obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hv 1 one_pos
    filter_upwards [eventually_ge_atTop N1, eventually_ge_atTop 1] with k hk1 hk2
    have h := hN1 k hk1
    rw [Real.dist_eq] at h
    have hb := (abs_lt.mp h).2
    rw [huvw k hk2]
    linarith [(hw k).1]
  have hcob : IsCoboundedUnder (· ≥ ·) atTop u :=
    isCoboundedUnder_ge_of_eventually_le atTop huub
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hv (ε / 2) hε2
  have h1 : ∀ᶠ k in atTop, H - ε / 2 < v k := by
    filter_upwards [eventually_ge_atTop N] with k hk
    have h := hN k hk
    rw [Real.dist_eq] at h
    linarith [(abs_lt.mp h).1]
  have h2 : ∀ᶠ k in atTop, w k < limsup w atTop + ε / 2 :=
    eventually_lt_of_limsup_lt (by linarith) (isBoundedUnder_le_of fun k => (hw k).2)
  have h3 : ∀ᶠ k in atTop, H - limsup w atTop - ε ≤ u k := by
    filter_upwards [h1, h2, eventually_ge_atTop 1] with k hk1 hk2 hk3
    rw [huvw k hk3]
    linarith
  have h4 : H - limsup w atTop - ε ≤ liminf u atTop :=
    @le_liminf_of_le ℝ ℕ _ atTop u _ hcob h3
  linarith

/-- If `u = v - w` eventually, `v → H`, and `w` is bounded, then `H - limsup w ≤ liminf u`. -/
theorem sub_limsup_le_liminf_of_eq_sub' {u v w : ℕ → ℝ} {H M : ℝ} (huvw : ∀ k, 1 ≤ k → u k =
    v k - w k)
    (hv : Tendsto v atTop (𝓝 H)) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ M) :
    H - limsup w atTop ≤ liminf u atTop := by
  exact sub_limsup_le_liminf_of_eq_sub huvw hv hw


/-- Under the unit-scale hypothesis `hFη`, `∫ limsup_k boxDefect F (cube k) / k ^ d ≤ α + C *
(akMaxConst d * η / α)`, by the maximal inequality applied to `boxDefect F`. -/
theorem integral_limsup_boxDefect_div_pow_le {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hmeas : ∀ A, Measurable (F A))
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω))
    {η : ℝ} (hFη : ∀ N : ℕ, 1 ≤ N → ∫ ω, cubeRatio F 1 ω ∂μ - η ≤ ∫ ω, cubeRatio F N ω ∂μ)
    {α : ℝ} (hα : 0 < α) :
    ∫ ω, limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop ∂μ ≤
      α + C * (akMaxConst d * η / α) := by
  exact (
    let hC0 : (0 : ℝ) ≤ C := nonneg_of_boxFun_bound hC (Classical.choice
        (nonempty_of_isProbabilityMeasure μ));
    let h7a : ∀ a b ω, 0 ≤ boxDefect F (latticeBox a b) ω := (boxDefect_latticeBox_nonneg_le hC
        hsub).1;
    let h7b : ∀ B ω, boxDefect F B ω ≤ C * (B.card : ℝ) := (boxDefect_latticeBox_nonneg_le hC
        hsub).2;
    let hgb : ∀ k ω, 0 ≤ boxDefect F (latticeCube d k) ω ∧ boxDefect F (latticeCube d k) ω ≤ C * (k
        : ℝ) ^ d :=
      fun k ω => ⟨h7a 0 (fun _ : Fin d => (k : ℤ) - 1) ω,
        by simpa [card_latticeCube_eq_pow', Nat.cast_pow] using h7b (latticeCube d k) ω⟩;
    let hg : ∀ k ω, 0 ≤ boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d ∧
        boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d ≤ C :=
      fun k ω => ⟨div_nonneg (hgb k ω).1 (pow_nonneg (Nat.cast_nonneg k) d),
        if hk : k = 0
          then by
              subst hk; simp only [Nat.cast_zero, zero_pow (by omega : d ≠ 0), div_zero]; exact hC0
          else by
            rw [div_le_iff₀ (pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)) d)]
            exact (hgb k ω).2⟩;
    integral_le_add_mul_div_of_tail_bound'
      (Measurable.limsup fun k => (measurable_boxDefect hmeas (latticeCube d k)).div_const _)
      (fun ω => ⟨
        le_limsup_of_frequently_le (Frequently.of_forall fun k => (hg k ω).1)
          (isBoundedUnder_le_of fun k => (hg k ω).2),
        limsup_le_of_le (isCoboundedUnder_le_of_le atTop fun k => (hg k ω).1)
          (Eventually.of_forall fun k => (hg k ω).2)⟩)
      (fun β hβ => le_trans
        (measureReal_mono (subset_bad_of_lt_limsup (R := boxDefect F) (M := C) hg hβ))
        (measureReal_exists_heavy_le_akMaxConst_mul_div hd τ hτ (boxDefect F) (measurable_boxDefect
            hmeas) (boxDefect_map_addRight_eq τ hstat)
          h7a h7b (fun B B₁ B₂ ω h => boxDefect_superadditive_of_isBoxSplit hsub h ω)
          (fun a b a' b' ω ha hb => boxDefect_mono_of_subset hC hsub a b a' b' ha hb ω)
          (fun N hN => integral_boxDefect_cube_le_mul_pow hd τ hτ hmeas hC hstat hFη hN) hβ))
      hα)


/-- If `0 ≤ u k ≤ C` for all `k`, then `|limsup u| ≤ C`. -/
theorem abs_limsup_le_of_forall_le {u : ℕ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hu : ∀ k, 0 ≤ u k ∧ u k ≤ C) : |limsup u atTop| ≤ C := by
  refine abs_le.2 ⟨?_, ?_⟩
  · refine le_trans (neg_nonpos.mpr hC0) ?_
    exact le_limsup_of_le (isBoundedUnder_le_of fun n => (hu n).2) fun b hb => by
      rcases eventually_atTop.mp hb with ⟨N, hN⟩
      exact le_trans (hu (max N 1)).1 (hN _ (le_max_left N 1))
  · exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop fun n => (hu n).1)
      (Eventually.of_forall fun n => (hu n).2)

/-- If `0 ≤ u k ≤ C` for all `k`, then `0 ≤ liminf u ≤ C`. -/
theorem liminf_nonneg_le_of_forall_le {u : ℕ → ℝ} {C : ℝ} (_unused_hC0 : 0 ≤ C)
    (hu : ∀ k, 0 ≤ u k ∧ u k ≤ C) : 0 ≤ liminf u atTop ∧ liminf u atTop ≤ C := by
  refine ⟨?_, ?_⟩
  · exact le_liminf_of_le ((isBoundedUnder_le_of fun n => (hu n).2).isCoboundedUnder_ge)
      (Eventually.of_forall fun n => (hu n).1)
  · exact liminf_le_of_le (isBoundedUnder_ge_of fun n => (hu n).1) fun b hb => by
      rcases eventually_atTop.mp hb with ⟨N, hN⟩
      exact le_trans (hN _ (le_max_left N 1)) (hu (max N 1)).2

omit [MeasurableSpace Ω] in
/-- `boxDefect F (cube k) / k ^ d` lies in `[0, C]`. -/
theorem boxDefect_cube_div_pow_nonneg_le {d : ℕ} (hd : 1 ≤ d) {F : Finset (Site d) → Ω → ℝ}
    {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω) (hC0 : 0 ≤ C)
    (k : ℕ) (ω : Ω) :
    0 ≤ boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d ∧
      boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d ≤ C := by
  obtain ⟨h7nn, h7bd⟩ := boxDefect_latticeBox_nonneg_le hC hsub
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Nat.cast_zero, zero_pow (by omega : d ≠ 0), div_zero]
    exact ⟨le_rfl, hC0⟩
  · have hnn : 0 ≤ boxDefect F (latticeCube d k) ω :=
      h7nn (0 : Site d) (fun _ => (k : ℤ) - 1) ω
    have hup : boxDefect F (latticeCube d k) ω ≤ C * (k : ℝ) ^ d := by
      have h := h7bd (latticeCube d k) ω
      rw [card_latticeCube_eq_pow' d k, Nat.cast_pow] at h
      exact h
    refine ⟨div_nonneg hnn (by positivity), ?_⟩
    rw [div_le_iff₀ (pow_pos (by exact_mod_cast hk) d)]
    exact hup

/-- The unit-scale lower bound: `∫ cubeRatio F 1 ≤ ∫ liminf_k cubeRatio F k + α + C * (akMaxConst d
* η / α)`, combining the bounded ergodic theorem with
`cubeRatio_eq_gridAvg_sub_boxDefect_div_pow`, `sub_limsup_le_liminf_of_eq_sub'` and
`integral_limsup_boxDefect_div_pow_le`. -/
theorem integral_cubeRatio_one_le_integral_liminf_add {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (hmeas : ∀ A, Measurable (F A))
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω))
    {η : ℝ} (hFη : ∀ N : ℕ, 1 ≤ N → ∫ ω, cubeRatio F 1 ω ∂μ - η ≤ ∫ ω, cubeRatio F N ω ∂μ)
    {α : ℝ} (hα : 0 < α) :
    ∫ ω, cubeRatio F 1 ω ∂μ ≤
      ∫ ω, liminf (fun k => cubeRatio F k ω) atTop ∂μ + α + C * (akMaxConst d * η / α) := by
  have hC0 : 0 ≤ C := (by
    obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
    exact nonneg_of_boxFun_bound hC ω0)
  obtain ⟨G, hGm, hGb, hGint, hGconv⟩ :=
    exists_ae_tendsto_gridAvg_univ_with_integral hτ hτadd (hmeas (latticeCube d 1)) hC0
      (fun x => by
        have h0 := (cubeRatio_nonneg_le hd hC 1 x).1
        have h1 := (cubeRatio_nonneg_le hd hC 1 x).2
        simp only [cubeRatio, Nat.cast_one, one_pow, div_one] at h0 h1
        exact abs_le.2 ⟨(by linarith), h1⟩)
  have hXm : Measurable (fun ω : Ω =>
      limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop) :=
    Measurable.limsup fun k =>
      (measurable_boxDefect hmeas (latticeCube d k)).div_const ((k : ℝ) ^ d)
  have hXb : ∀ ω : Ω,
      |limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop| ≤ C :=
    fun ω => abs_limsup_le_of_forall_le hC0 (fun k => boxDefect_cube_div_pow_nonneg_le hd hC hsub
        hC0 k ω)
  have hXint : Integrable (fun ω : Ω =>
      limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop) μ :=
    Integrable.of_bound hXm.aestronglyMeasurable C (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact hXb x)
  have hLb : ∀ ω : Ω, 0 ≤ liminf (fun k : ℕ => cubeRatio F k ω) atTop ∧
      liminf (fun k : ℕ => cubeRatio F k ω) atTop ≤ C :=
    fun ω => liminf_nonneg_le_of_forall_le hC0 (fun k => cubeRatio_nonneg_le hd hC k ω)
  have hLm : Measurable (fun ω : Ω => liminf (fun k : ℕ => cubeRatio F k ω) atTop) :=
    Measurable.liminf fun k => measurable_cubeRatio hmeas k
  have hLint : Integrable (fun ω : Ω => liminf (fun k : ℕ => cubeRatio F k ω) atTop) μ :=
    Integrable.of_bound hLm.aestronglyMeasurable C (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hLb x).1]
      exact (hLb x).2)
  have hGint' : Integrable G μ :=
    Integrable.of_bound hGm.aestronglyMeasurable C (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact hGb x)
  have hcr1 : (∫ ω, cubeRatio F 1 ω ∂μ) = ∫ ω, F (latticeCube d 1) ω ∂μ := (by
    refine integral_congr_ae ?_
    filter_upwards with ω
    simp [cubeRatio])
  have hpt : ∀ᵐ ω ∂μ, G ω -
      limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop ≤
      liminf (fun k : ℕ => cubeRatio F k ω) atTop := (by
    filter_upwards [hGconv] with ω hω
    exact sub_limsup_le_liminf_of_eq_sub' (u := fun k => cubeRatio F k ω)
      (v := fun k => gridAvg τ (F (latticeCube d 1)) Finset.univ k ω)
      (w := fun k => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d)
      (fun k hk => cubeRatio_eq_gridAvg_sub_boxDefect_div_pow τ hstat hk ω) hω
      (fun k => boxDefect_cube_div_pow_nonneg_le hd hC hsub hC0 k ω))
  have hmono : (∫ ω, G ω ∂μ) -
      (∫ ω, limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop ∂μ) ≤
      ∫ ω, liminf (fun k : ℕ => cubeRatio F k ω) atTop ∂μ := (by
    have h := integral_mono_ae (hGint'.sub hXint) hLint hpt
    have hsub' := integral_sub hGint' hXint
    simp only [Pi.sub_apply] at h
    rwa [hsub'] at h)
  have h39 : ∫ ω, limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop ∂μ ≤
      α + C * (akMaxConst d * η / α) :=
    integral_limsup_boxDefect_div_pow_le hd τ hτ hmeas hC hsub hstat hFη hα
  rw [hGint] at hmono
  rw [hcr1]
  exact (by linarith)

end LatticeProb
