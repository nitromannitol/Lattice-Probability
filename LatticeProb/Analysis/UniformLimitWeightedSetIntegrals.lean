import Mathlib

/-!
# Uniform convergence of weighted integrals over initial intervals

Let `μ k` (`k : ℕ`) and `ν` be finite measures on `ℝ` whose distribution functions over an
interval `[a, b]` converge uniformly:
`sup_{t ∈ [a, b]} |μ k (a, t] - ν (a, t]| → 0`. If weights `w k` converge uniformly on `[a, b]`
to a function `v` that is continuous on `[a, b]`, then
`∫_{(a, t]} w k dμ k → ∫_{(a, t]} v dν`, uniformly in `t ∈ [a, b]`.

For monotone integrators `A k, F` (`μ k (a, t] = A k t - A k a`) this is the continuity of the
Riemann–Stieltjes integral `(w, A) ↦ ∫ w dA` under uniform convergence of both arguments. It
transfers the uniform convergence `A k → F` of a sequence of time changes to the weighted time
changes `∫ w k dA k → ∫ v dF`.

## Main results

* `LatticeProb.abs_setIntegral_Ioc_sub_stieltjesSum_le`: comparison of `∫_{(a, t]} v dm` with the
  Riemann–Stieltjes sum of `v` over a grid on which `v` oscillates by at most `η`.
* `LatticeProb.tendstoUniformlyOn_setIntegral_Ioc_of_measureReal`: fixed continuous weight.
* `LatticeProb.tendstoUniformlyOn_setIntegral_Ioc_weighted`: weights converging uniformly to a
  continuous weight.
-/

open MeasureTheory Set Filter Finset

namespace LatticeProb

/-- Summation by parts bound: if each increment of `F` is within `η` times the increment of `R`
of `c i` times that increment, then the same holds for the total increments. -/
private theorem abs_sub_sum_mul_sub_le_of_forall {F R c : ℕ → ℝ} {n : ℕ} {η : ℝ}
    (h : ∀ i < n, |(F (i + 1) - F i) - c i * (R (i + 1) - R i)| ≤ η * (R (i + 1) - R i)) :
    |(F n - F 0) - ∑ i ∈ range n, c i * (R (i + 1) - R i)| ≤ η * (R n - R 0) := by
  rw [← Finset.sum_range_sub F, ← Finset.sum_range_sub R, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i hi => h i (Finset.mem_range.1 hi))

/-- If `v` stays within `η` of the constant `c` on `(x, y]`, then `∫_{(x, y]} v dm` is within
`η m (x, y]` of `c m (x, y]`. -/
theorem abs_setIntegral_Ioc_sub_const_mul_le {m : Measure ℝ} [IsFiniteMeasure m] {v : ℝ → ℝ}
    {x y c η : ℝ} (hv : IntegrableOn v (Ioc x y) m) (hc : ∀ s ∈ Ioc x y, |v s - c| ≤ η) :
    |∫ s in Ioc x y, v s ∂m - c * m.real (Ioc x y)| ≤ η * m.real (Ioc x y) := by
  have h1 : ∫ s in Ioc x y, v s ∂m - c * m.real (Ioc x y) = ∫ s in Ioc x y, (v s - c) ∂m := by
    rw [integral_sub hv (integrableOn_const (measure_ne_top _ _)), setIntegral_const, smul_eq_mul,
      mul_comm]
  rw [h1]
  have h2 := norm_setIntegral_le_of_norm_le_const (μ := m) (s := Ioc x y)
    (f := fun s => v s - c) (measure_lt_top _ _) (fun s hs => by
      rw [Real.norm_eq_abs]; exact hc s hs)
  rwa [Real.norm_eq_abs] at h2

/-- Riemann–Stieltjes approximation of `∫_{(a, t]} v dm` along a monotone grid `g` starting at
`a`: if `v` oscillates by at most `η` against its right endpoint value on every grid cell, the
error is at most `η m (a, t]`. -/
theorem abs_setIntegral_Ioc_sub_stieltjesSum_le {a : ℝ} {m : Measure ℝ} [IsFiniteMeasure m]
    {v : ℝ → ℝ} {g : ℕ → ℝ} {n : ℕ} {t η : ℝ} (hg : Monotone g) (hg0 : g 0 = a) (hat : a ≤ t)
    (htn : t ≤ g n) (hv : IntegrableOn v (Ioc a t) m)
    (hη : ∀ i < n, ∀ s ∈ Ioc (g i) (g (i + 1)), |v s - v (g (i + 1))| ≤ η) :
    |∫ s in Ioc a t, v s ∂m - ∑ i ∈ range n, v (g (i + 1)) *
        (m.real (Ioc a (min (g (i + 1)) t)) - m.real (Ioc a (min (g i) t)))| ≤
      η * m.real (Ioc a t) := by
  have hmin_ge : ∀ i, a ≤ min (g i) t := fun i => le_min (hg0 ▸ hg (Nat.zero_le i)) hat
  have hsplit : ∀ {x y : ℝ}, a ≤ x → x ≤ y → y ≤ t →
      ∫ s in Ioc a y, v s ∂m = ∫ s in Ioc a x, v s ∂m + ∫ s in Ioc x y, v s ∂m ∧
      m.real (Ioc a y) = m.real (Ioc a x) + m.real (Ioc x y) := by
    intro x y hax hxy hyt
    have hd : Disjoint (Ioc a x) (Ioc x y) :=
      Set.disjoint_left.2 fun s h1 h2 => (not_lt.2 h1.2) h2.1
    refine ⟨?_, ?_⟩
    · rw [← setIntegral_union hd measurableSet_Ioc
        (hv.mono_set (Ioc_subset_Ioc le_rfl (hxy.trans hyt)))
        (hv.mono_set (Ioc_subset_Ioc hax hyt)), Ioc_union_Ioc_eq_Ioc hax hxy]
    · rw [← measureReal_union hd measurableSet_Ioc, Ioc_union_Ioc_eq_Ioc hax hxy]
  have key := abs_sub_sum_mul_sub_le_of_forall (n := n) (η := η)
    (F := fun i => ∫ s in Ioc a (min (g i) t), v s ∂m)
    (R := fun i => m.real (Ioc a (min (g i) t))) (c := fun i => v (g (i + 1))) (by
      intro i hi
      have hmono : min (g i) t ≤ min (g (i + 1)) t := min_le_min_right t (hg (Nat.le_succ i))
      obtain ⟨h1, h2⟩ := hsplit (hmin_ge i) hmono (min_le_right _ _)
      rw [h1, h2, add_sub_cancel_left, add_sub_cancel_left]
      refine abs_setIntegral_Ioc_sub_const_mul_le
        (hv.mono_set (Ioc_subset_Ioc (hmin_ge i) (min_le_right _ _))) fun s hs => ?_
      refine hη i hi s ⟨?_, hs.2.trans (min_le_left _ _)⟩
      rcases min_lt_iff.1 hs.1 with h | h
      · exact h
      · exact absurd (hs.2.trans (min_le_right _ _)) (not_le.2 h))
  simpa only [min_eq_right htn, hg0, min_eq_left hat, Set.Ioc_self, Measure.restrict_empty,
    integral_zero_measure, measureReal_empty, sub_zero] using key

/-- **Fixed continuous weight.** If the distribution functions `t ↦ μ k (a, t]` of finite
measures converge uniformly on `[a, b]` to `t ↦ ν (a, t]`, then for every `v` continuous on
`[a, b]` the integrals `∫_{(a, t]} v dμ k` converge to `∫_{(a, t]} v dν` uniformly in
`t ∈ [a, b]`. -/
theorem tendstoUniformlyOn_setIntegral_Ioc_of_measureReal {a b : ℝ} {μ : ℕ → Measure ℝ}
    [∀ k, IsFiniteMeasure (μ k)] {ν : Measure ℝ} [IsFiniteMeasure ν] {v : ℝ → ℝ}
    (hμ : TendstoUniformlyOn (fun k t => (μ k).real (Ioc a t)) (fun t => ν.real (Ioc a t))
      atTop (Icc a b))
    (hv : ContinuousOn v (Icc a b)) :
    TendstoUniformlyOn (fun k t => ∫ s in Ioc a t, v s ∂μ k) (fun t => ∫ s in Ioc a t, v s ∂ν)
      atTop (Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · rw [Icc_eq_empty (not_le.2 hba)]
    exact tendstoUniformlyOn_empty
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨le_rfl, hab⟩)
  set N := ν.real (Ioc a b) with hN
  have hN0 : 0 ≤ N := measureReal_nonneg
  set η := ε / (2 * (2 * N + 1)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨δ, hδ, hvδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hv) η hηpos
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (sub_nonneg.2 hab) hδ.le) hn
  set h := (b - a) / n with hh
  have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.2 hab) hnpos.le
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ hnpos]
    rw [div_lt_iff₀ hδ] at hn
    linarith
  set g : ℕ → ℝ := fun i => a + i * h with hgdef
  have hg : Monotone g := fun i j hij => by
    have : (i : ℝ) ≤ j := Nat.cast_le.2 hij
    simp only [hgdef]
    nlinarith
  have hg0 : g 0 = a := by simp [hgdef]
  have hgn : g n = b := by
    simp only [hgdef, hh]
    field_simp
    ring
  have hgmem : ∀ i ≤ n, g i ∈ Icc a b := fun i hi => ⟨hg0 ▸ hg (Nat.zero_le i), hgn ▸ hg hi⟩
  have hpiece : ∀ i < n, ∀ s ∈ Ioc (g i) (g (i + 1)), |v s - v (g (i + 1))| ≤ η := by
    intro i hi s hs
    have hs' : s ∈ Icc a b := ⟨(hgmem i hi.le).1.trans hs.1.le, hs.2.trans (hgmem (i + 1) hi).2⟩
    have hgi : g (i + 1) - g i = h := by
      simp only [hgdef]
      push_cast
      ring
    have hd : dist s (g (i + 1)) < δ := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hs.2)]
      linarith [hs.1]
    have := hvδ s hs' (g (i + 1)) (hgmem (i + 1) hi) hd
    rw [Real.dist_eq] at this
    exact this.le
  set θ := min 1 (ε / (4 * (n * M + 1))) with hθ
  have hθpos : 0 < θ := lt_min one_pos (by positivity)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hnMθ : n * M * θ < ε / 4 := by
    have h1 : n * M * θ ≤ n * M * (ε / (4 * (n * M + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    have h2 : n * M * (ε / (4 * (n * M + 1))) < ε / 4 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hint : ∀ (m : Measure ℝ) [IsFiniteMeasure m] (t : ℝ), t ∈ Icc a b →
      IntegrableOn v (Ioc a t) m := fun m _ t ht =>
    (hv.integrableOn_compact isCompact_Icc).mono_set
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hμ θ hθpos] with k hk t ht
  have hΔ : ∀ x ∈ Icc a b, |(μ k).real (Ioc a x) - ν.real (Ioc a x)| < θ := fun x hx => by
    have := hk x hx
    rwa [Real.dist_eq, abs_sub_comm] at this
  have hμb : (μ k).real (Ioc a b) ≤ N + 1 := by
    have := (abs_lt.1 (hΔ b ⟨hab, le_rfl⟩)).2
    linarith
  have hμt : (μ k).real (Ioc a t) ≤ N + 1 :=
    (measureReal_mono (Ioc_subset_Ioc_right ht.2)).trans hμb
  have hνt : ν.real (Ioc a t) ≤ N := measureReal_mono (Ioc_subset_Ioc_right ht.2)
  have hCμ := abs_setIntegral_Ioc_sub_stieltjesSum_le (m := μ k) hg hg0 ht.1 (hgn ▸ ht.2)
    (hint (μ k) t ht) hpiece
  have hCν := abs_setIntegral_Ioc_sub_stieltjesSum_le (m := ν) hg hg0 ht.1 (hgn ▸ ht.2)
    (hint ν t ht) hpiece
  have hS : |∑ i ∈ range n, v (g (i + 1)) *
        ((μ k).real (Ioc a (min (g (i + 1)) t)) - (μ k).real (Ioc a (min (g i) t))) -
      ∑ i ∈ range n, v (g (i + 1)) *
        (ν.real (Ioc a (min (g (i + 1)) t)) - ν.real (Ioc a (min (g i) t)))| ≤
      n * (2 * M * θ) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _i ∈ range n, 2 * M * θ := Finset.sum_le_sum fun i hi => ?_
      _ = n * (2 * M * θ) := by simp
    have hi' := Finset.mem_range.1 hi
    have hm1 : min (g (i + 1)) t ∈ Icc a b :=
      ⟨le_min (hgmem _ hi').1 ht.1, (min_le_right _ _).trans ht.2⟩
    have hm0 : min (g i) t ∈ Icc a b :=
      ⟨le_min (hgmem _ hi'.le).1 ht.1, (min_le_right _ _).trans ht.2⟩
    have hc : |v (g (i + 1))| ≤ M := by
      have := hM _ (hgmem _ hi')
      rwa [Real.norm_eq_abs] at this
    have e1 := abs_lt.1 (hΔ _ hm1)
    have e0 := abs_lt.1 (hΔ _ hm0)
    rw [← mul_sub, abs_mul]
    have hd : |(μ k).real (Ioc a (min (g (i + 1)) t)) - (μ k).real (Ioc a (min (g i) t)) -
        (ν.real (Ioc a (min (g (i + 1)) t)) - ν.real (Ioc a (min (g i) t)))| ≤ 2 * θ :=
      abs_le.2 ⟨by linarith, by linarith⟩
    calc |v (g (i + 1))| * _ ≤ M * (2 * θ) :=
          mul_le_mul hc hd (abs_nonneg _) hM0
      _ = 2 * M * θ := by ring
  rw [Real.dist_eq, abs_sub_comm]
  have hημ : η * (μ k).real (Ioc a t) ≤ η * (N + 1) :=
    mul_le_mul_of_nonneg_left hμt hηpos.le
  have hην : η * ν.real (Ioc a t) ≤ η * N := mul_le_mul_of_nonneg_left hνt hηpos.le
  have hηN : η * (N + 1) + η * N = ε / 2 := by
    rw [hη]
    field_simp
    ring
  have a1 := abs_le.1 hCμ
  have a2 := abs_le.1 hCν
  have a3 := abs_le.1 hS
  rw [abs_lt]
  constructor <;> linarith

/-- **Weighted version.** If the distribution functions `t ↦ μ k (a, t]` of finite measures
converge uniformly on `[a, b]` to `t ↦ ν (a, t]`, and the weights `w k` converge uniformly on
`[a, b]` to a function `v` continuous on `[a, b]`, then `∫_{(a, t]} w k dμ k` converges to
`∫_{(a, t]} v dν` uniformly in `t ∈ [a, b]`. -/
theorem tendstoUniformlyOn_setIntegral_Ioc_weighted {a b : ℝ} {μ : ℕ → Measure ℝ}
    [∀ k, IsFiniteMeasure (μ k)] {ν : Measure ℝ} [IsFiniteMeasure ν] {w : ℕ → ℝ → ℝ}
    {v : ℝ → ℝ}
    (hμ : TendstoUniformlyOn (fun k t => (μ k).real (Ioc a t)) (fun t => ν.real (Ioc a t))
      atTop (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (hw : TendstoUniformlyOn w v atTop (Icc a b))
    (hwm : ∀ k, AEStronglyMeasurable (w k) ((μ k).restrict (Ioc a b))) :
    TendstoUniformlyOn (fun k t => ∫ s in Ioc a t, w k s ∂μ k)
      (fun t => ∫ s in Ioc a t, v s ∂ν) atTop (Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · rw [Icc_eq_empty (not_le.2 hba)]
    exact tendstoUniformlyOn_empty
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  set N := ν.real (Ioc a b) with hN
  have hN0 : 0 ≤ N := measureReal_nonneg
  set θ := min 1 (ε / (2 * (N + 2))) with hθ
  have hθpos : 0 < θ := lt_min one_pos (by positivity)
  have hθN : θ * (N + 1) < ε / 2 := by
    have h1 : θ * (N + 1) ≤ ε / (2 * (N + 2)) * (N + 1) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
    have h2 : ε / (2 * (N + 2)) * (N + 1) < ε / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  filter_upwards [Metric.tendstoUniformlyOn_iff.1
      (tendstoUniformlyOn_setIntegral_Ioc_of_measureReal hμ hv) (ε / 2) (by positivity),
    Metric.tendstoUniformlyOn_iff.1 hμ 1 one_pos,
    Metric.tendstoUniformlyOn_iff.1 hw θ hθpos] with k h1 h2 h3 t ht
  have hsub : Ioc a t ⊆ Icc a b := Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2)
  have hμb : (μ k).real (Ioc a b) ≤ N + 1 := by
    have := h2 b ⟨hab, le_rfl⟩
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).1
    linarith
  have hμt : (μ k).real (Ioc a t) ≤ N + 1 :=
    (measureReal_mono (Ioc_subset_Ioc_right ht.2)).trans hμb
  have hwv : ∀ s ∈ Ioc a t, ‖w k s - v s‖ ≤ θ := fun s hs => by
    have := h3 s (hsub hs)
    rw [Real.dist_eq, abs_sub_comm] at this
    rw [Real.norm_eq_abs]
    exact this.le
  have hvint : IntegrableOn v (Ioc a t) (μ k) :=
    (hv.integrableOn_compact isCompact_Icc).mono_set hsub
  have hwint : IntegrableOn (w k) (Ioc a t) (μ k) := by
    refine Integrable.of_bound ((hwm k).mono_measure
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2))) (M + 1) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    have e1 := hwv s hs
    have e2 := hM s (hsub hs)
    rw [Real.norm_eq_abs] at e1 e2 ⊢
    have := abs_sub_abs_le_abs_sub (w k s) (v s)
    have hθ1 : θ ≤ 1 := min_le_left _ _
    linarith
  have hdiff : |∫ s in Ioc a t, w k s ∂μ k - ∫ s in Ioc a t, v s ∂μ k| ≤
      θ * (μ k).real (Ioc a t) := by
    rw [← integral_sub hwint hvint, ← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hwv
  have hk := h1 t ht
  rw [Real.dist_eq, abs_sub_comm] at hk
  rw [Real.dist_eq, abs_sub_comm]
  have hθμ : θ * (μ k).real (Ioc a t) ≤ θ * (N + 1) := mul_le_mul_of_nonneg_left hμt hθpos.le
  have a1 := abs_le.1 hdiff
  have a2 := abs_lt.1 hk
  rw [abs_lt]
  constructor <;> linarith

end LatticeProb
