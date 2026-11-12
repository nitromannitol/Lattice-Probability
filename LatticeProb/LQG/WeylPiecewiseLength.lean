import LatticeProb.LQG.LengthMetricDerived
import LatticeProb.LQG.WeylLogTruncation

/-!
# Weyl-scaled length of a curve with piecewise weight bounds

Let `D` be a Euclidean length metric on `ℂ` and let `E` be its Weyl scaling `e^{ξ f} · D` (`weylScaling`), with real
values. For a curve `p`, continuous on `[0, 1]` and of finite `D`-length, the `E`-length of `p` is at most the integral of
the weight `e^{ξ f}` against `D`-arclength along `p`: every increment `E(p(tᵢ), p(tᵢ₊₁))` is at most the weighted
`D`-length of the arc of `p` between the two times, because the arclength parametrization of that arc is a competitor in
the definition of the Weyl scaling.

Consequently, if `0 = τ₀ ≤ τ₁ ≤ ⋯ → 1` and `ξ f ≤ Bₖ` on `p([τₖ, τₖ₊₁])`, then
`len(p; E) ≤ ∑ₖ e^{Bₖ} len(p|[τₖ, τₖ₊₁]; D)`. No bound on the weight along the whole curve is needed, so this applies to
curves ending at a singularity of `f`, such as the point `0` for the weight `f = -α log |·|`.

## Main statements

* `LatticeProb.LQG.IsEuclideanLengthMetric.curveLength_weylScaling_le_lintegral`: the `E`-length is at most the
  weighted `D`-arclength integral.
* `LatticeProb.LQG.IsEuclideanLengthMetric.curveLength_weylScaling_le_tsum`: the piecewise bound
  `len(p; E) ≤ ∑ₖ e^{Bₖ} len(p|[τₖ, τₖ₊₁]; D)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LatticeProb.LQG

/-- Integrals over consecutive intervals add up: `∑_{i < N} ∫_{(σᵢ, σᵢ₊₁]} g = ∫_{(σ₀, σ_N]} g` for monotone `σ`. -/
theorem sum_setLIntegral_Ioc_eq (g : ℝ → ℝ≥0∞) {σ : ℕ → ℝ} (hσ : Monotone σ) (N : ℕ) :
    ∑ i ∈ Finset.range N, ∫⁻ s in Ioc (σ i) (σ (i + 1)), g s = ∫⁻ s in Ioc (σ 0) (σ N), g s := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, ← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
      Ioc_union_Ioc_eq_Ioc (hσ (Nat.zero_le N)) (hσ (Nat.le_succ N))]

/-- **Weyl-scaled length against the weighted arclength.** Let `D` be a Euclidean length metric, `E = e^{ξ f} · D`,
and `p` a curve continuous on `[0, 1]` of finite `D`-length `L`, with arclength parametrization `q` on `[0, L]`
(`q (len(p|[0, t]; D)) = p t`). Then `len(p; E) ≤ ∫_0^L e^{ξ f(q s)} ds`. -/
theorem IsEuclideanLengthMetric.curveLength_weylScaling_le_lintegral {D E : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {f : ℂ → ℝ}
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) {p : ℝ → ℂ}
    (hp : ContinuousOn p (Icc 0 1)) (hfin : curveLength D p 0 1 < ⊤) {q : ℝ → ℂ}
    (hq : IsLengthParametrized D q (curveLength D p 0 1).toReal)
    (htrack : ∀ t ∈ Icc (0 : ℝ) 1, q (curveLength D p 0 t).toReal = p t) :
    curveLength E p 0 1 ≤
      ∫⁻ s in Icc 0 (curveLength D p 0 1).toReal, ENNReal.ofReal (Real.exp (ξ * f (q s))) := by
  obtain ⟨-, hmono, -, -⟩ := hD.cumulative_curveLength_properties zero_le_one hp hfin
  refine curveLength_le_of_partition_bound fun N u hu hI => ?_
  set σ : ℕ → ℝ := fun i => (curveLength D p 0 (u i)).toReal with hσdef
  have hσ : Monotone σ := fun i j hij => hmono (hI i) (hI j) (hu hij)
  have hσ0 : ∀ i, 0 ≤ σ i := fun i => ENNReal.toReal_nonneg
  have hσL : ∀ i, σ i ≤ (curveLength D p 0 1).toReal := fun i =>
    hmono (hI i) (right_mem_Icc.2 zero_le_one) (hI i).2
  have hterm : ∀ i, ENNReal.ofReal (E (p (u (i + 1))) (p (u i))) ≤
      ∫⁻ s in Ioc (σ i) (σ (i + 1)), ENNReal.ofReal (Real.exp (ξ * f (q s))) := by
    intro i
    rw [hscale, ← htrack _ (hI (i + 1)), ← htrack _ (hI i), hD.weylScaling_symm,
      setLIntegral_congr Ioc_ae_eq_Icc]
    exact hD.weylScaling_le_lintegral_subarc ξ f hq (hσ0 i) (hσ (Nat.le_succ i)) (hσL (i + 1))
  calc ∑ i ∈ Finset.range N, ENNReal.ofReal (E (p (u (i + 1))) (p (u i)))
      ≤ ∑ i ∈ Finset.range N, ∫⁻ s in Ioc (σ i) (σ (i + 1)), ENNReal.ofReal (Real.exp (ξ * f (q s))) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ∫⁻ s in Ioc (σ 0) (σ N), ENNReal.ofReal (Real.exp (ξ * f (q s))) := sum_setLIntegral_Ioc_eq _ hσ N
    _ ≤ ∫⁻ s in Icc 0 (curveLength D p 0 1).toReal, ENNReal.ofReal (Real.exp (ξ * f (q s))) :=
        lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc (hσ0 0) (hσL N)))

/-- **Weyl-scaled length with piecewise weight bounds.** Let `D` be a Euclidean length metric, `E = e^{ξ f} · D`, and
`p` a curve continuous on `[0, 1]` of finite `D`-length. Let `0 = τ₀ ≤ τ₁ ≤ ⋯ ≤ 1` with `τₖ → 1`, and `ξ f(p t) ≤ Bₖ`
for `t ∈ [τₖ, τₖ₊₁]`. Then `len(p; E) ≤ ∑ₖ e^{Bₖ} len(p|[τₖ, τₖ₊₁]; D)`. The weight may be unbounded along `p`
(for instance at the endpoint `p 1`), since the point `p 1` carries no arclength. -/
theorem IsEuclideanLengthMetric.curveLength_weylScaling_le_tsum {D E : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {f : ℂ → ℝ}
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) {p : ℝ → ℂ}
    (hp : ContinuousOn p (Icc 0 1)) (hfin : curveLength D p 0 1 < ⊤) {τ : ℕ → ℝ} (hτ : Monotone τ)
    (hτ0 : τ 0 = 0) (hτ1 : ∀ k, τ k ≤ 1) (hτlim : Tendsto τ atTop (𝓝 1)) {B : ℕ → ℝ}
    (hB : ∀ k, ∀ t ∈ Icc (τ k) (τ (k + 1)), ξ * f (p t) ≤ B k) :
    curveLength E p 0 1 ≤
      ∑' k, ENNReal.ofReal (Real.exp (B k)) * curveLength D p (τ k) (τ (k + 1)) := by
  obtain ⟨q, hq, -, -, htrack⟩ := hD.exists_lengthParametrized_with_tracking zero_le_one hp hfin
  obtain ⟨hcont, -, h0, -⟩ := hD.cumulative_curveLength_properties zero_le_one hp hfin
  set φ : ℝ → ℝ := fun t => (curveLength D p 0 t).toReal with hφ
  have h00 : φ 0 = 0 := h0
  have hτI : ∀ k, τ k ∈ Icc (0 : ℝ) 1 := fun k => ⟨by simpa [hτ0] using hτ (Nat.zero_le k), hτ1 k⟩
  -- the `D`-lengths of the pieces
  have hlen0 : ∀ b ∈ Icc (0 : ℝ) 1, curveLength D p 0 b ≠ ⊤ := fun b hb =>
    ne_top_of_le_ne_top hfin.ne (by rw [← hD.curveLength_add p hb.1 hb.2]; exact le_self_add)
  have hpiece : ∀ k, ENNReal.ofReal (φ (τ (k + 1)) - φ (τ k)) = curveLength D p (τ k) (τ (k + 1)) := by
    intro k
    have hadd := hD.curveLength_add p (hτI k).1 (hτ (Nat.le_succ k))
    have h1 := hlen0 _ (hτI k)
    have h2 := hlen0 _ (hτI (k + 1))
    have h3 : curveLength D p (τ k) (τ (k + 1)) ≠ ⊤ := by
      intro h
      rw [h, add_top] at hadd
      exact h2 hadd.symm
    show ENNReal.ofReal ((curveLength D p 0 (τ (k + 1))).toReal - (curveLength D p 0 (τ k)).toReal) = _
    rw [← hadd, ENNReal.toReal_add h1 h3, add_sub_cancel_left, ENNReal.ofReal_toReal h3]
  -- the arclength intervals of the pieces cover `[0, L)`
  have hlimφ : Tendsto (fun k => φ (τ k)) atTop (𝓝 (φ 1)) :=
    ((hcont 1 (right_mem_Icc.2 zero_le_one)).tendsto).comp
      (tendsto_nhdsWithin_iff.2 ⟨hτlim, Eventually.of_forall hτI⟩)
  have hcover : Icc 0 (φ 1) ⊆ {φ 1} ∪ ⋃ k, Icc (φ (τ k)) (φ (τ (k + 1))) := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with h | h
    · exact Or.inl h
    · right
      have hex : ∃ k, s < φ (τ k) := (hlimφ.eventually (lt_mem_nhds h)).exists
      classical
      have hk0 : Nat.find hex ≠ 0 := by
        intro hk0
        have h' := Nat.find_spec hex
        rw [hk0, hτ0, h00] at h'
        linarith [hs.1]
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_one_of_ne_zero hk0
      have hjle : ¬ s < φ (τ j) := Nat.find_min hex (by omega)
      have hk : s < φ (τ (j + 1)) := hj ▸ Nat.find_spec hex
      exact mem_iUnion.2 ⟨j, not_lt.1 hjle, hk.le⟩
  -- the weight bound on each arclength interval
  have hpw : ∀ k, ∀ s ∈ Icc (φ (τ k)) (φ (τ (k + 1))),
      ENNReal.ofReal (Real.exp (ξ * f (q s))) ≤ ENNReal.ofReal (Real.exp (B k)) := by
    intro k s hs
    have hsub : Icc (τ k) (τ (k + 1)) ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc (hτI k).1 (hτI (k + 1)).2
    obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc (hτ (Nat.le_succ k)) (hcont.mono hsub) hs
    show ENNReal.ofReal (Real.exp (ξ * f (q (curveLength D p 0 t).toReal))) ≤ _
    rw [htrack t (hsub ht)]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hB k t ht))
  calc curveLength E p 0 1
      ≤ ∫⁻ s in Icc 0 (φ 1), ENNReal.ofReal (Real.exp (ξ * f (q s))) :=
        hD.curveLength_weylScaling_le_lintegral hscale hp hfin hq htrack
    _ ≤ ∫⁻ s in {φ 1} ∪ ⋃ k, Icc (φ (τ k)) (φ (τ (k + 1))), ENNReal.ofReal (Real.exp (ξ * f (q s))) :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ s in {φ 1}, ENNReal.ofReal (Real.exp (ξ * f (q s)))) +
          ∫⁻ s in ⋃ k, Icc (φ (τ k)) (φ (τ (k + 1))), ENNReal.ofReal (Real.exp (ξ * f (q s))) :=
        lintegral_union_le _ _ _
    _ = ∫⁻ s in ⋃ k, Icc (φ (τ k)) (φ (τ (k + 1))), ENNReal.ofReal (Real.exp (ξ * f (q s))) := by
        rw [Measure.restrict_eq_zero.2 Real.volume_singleton, lintegral_zero_measure, zero_add]
    _ ≤ ∑' k, ∫⁻ s in Icc (φ (τ k)) (φ (τ (k + 1))), ENNReal.ofReal (Real.exp (ξ * f (q s))) :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' k, ENNReal.ofReal (Real.exp (B k)) * curveLength D p (τ k) (τ (k + 1)) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        calc ∫⁻ s in Icc (φ (τ k)) (φ (τ (k + 1))), ENNReal.ofReal (Real.exp (ξ * f (q s)))
            ≤ ∫⁻ _ in Icc (φ (τ k)) (φ (τ (k + 1))), ENNReal.ofReal (Real.exp (B k)) :=
              setLIntegral_mono' measurableSet_Icc (hpw k)
          _ = ENNReal.ofReal (Real.exp (B k)) * curveLength D p (τ k) (τ (k + 1)) := by
              rw [setLIntegral_const, Real.volume_Icc, hpiece]

end LatticeProb.LQG
