/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P3B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P3A

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2: truncated local limits from Lemma 2.1 (Weyl input W2–W3)

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), Lemma 2.1 (T:648–650:
`D̂^ε_h(·,·;U)` and `D^ε_h(·,·;U)` differ by a factor tending to `1`) and proof of Theorem 1.2,
Step 2 (T:1368–1372). Deterministic for a fixed field `g`:

* `truncW_le_mul` / `dist_truncW_le_of_ratio` — `truncW` respects multiplicative closeness:
  `d' ≤ c d`, `d ≤ c d'` give `‖truncW d' − truncW d‖ ≤ (c−1) c ‖truncW d‖`;
* `locSqC_closure_apply` — the value of the localized LFPP on `W̄`;
* `truncLim_eq_of_mollify` — if `𝔞⁻¹D^{ε_k}_g → D'` locally uniformly and the localized and the
  heat-kernel mollifications of `g` are uniformly close on `W̄`, then `truncLim W g = truncD W D'`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint MetricGeometry LFPP

theorem truncW_le_mul (W : dyadicDomainsC) {d d' : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ)}
    {c : ℝ} (hc : 0 ≤ c) (hle : ∀ p, d' p ≤ c * d p) (p : closure (W : Set ℂ) × closure (W : Set ℂ)) :
    truncW W d' p ≤ c * truncW W d p := by
  rw [truncW_apply, truncW_apply, mul_min_of_nonneg _ _ hc]
  refine min_le_min (hle p) ?_
  rcases isEmpty_or_nonempty (α := {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)}) with
    he | hne
  · simp only [infFr, Real.iInf_of_isEmpty, mul_zero, le_refl]
  have hbd : BddBelow (range fun w : {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)} =>
      d' (p.1, w.1)) := by
    have : CompactSpace (closure (W : Set ℂ)) :=
      isCompact_iff_compactSpace.1 W.2.1.isBounded.isCompact_closure
    refine ⟨-‖d'‖, ?_⟩
    rintro _ ⟨w, rfl⟩
    have := d'.norm_coe_le_norm (p.1, w.1)
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (d' (p.1, w.1))]
  simp only [infFr]
  rw [Real.mul_iInf_of_nonneg hc]
  exact le_ciInf fun w => (ciInf_le hbd w).trans (hle _)

theorem dist_truncW_le_of_ratio (W : dyadicDomainsC)
    {d d' : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ)} {c : ℝ} (hc1 : 1 ≤ c)
    (h0 : ∀ p, 0 ≤ truncW W d p) (h1 : ∀ p, d' p ≤ c * d p) (h2 : ∀ p, d p ≤ c * d' p) :
    dist (truncW W d') (truncW W d) ≤ (c - 1) * c * ‖truncW W d‖ := by
  have : CompactSpace (closure (W : Set ℂ)) :=
    isCompact_iff_compactSpace.1 W.2.1.isBounded.isCompact_closure
  have hc0 : 0 ≤ c := by linarith
  refine (ContinuousMap.dist_le (by positivity)).2 fun p => ?_
  have a1 := truncW_le_mul W hc0 h1 p
  have a2 := truncW_le_mul W hc0 h2 p
  have hn : truncW W d p ≤ ‖truncW W d‖ := by
    have := (truncW W d).norm_coe_le_norm p
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hp := h0 p
  rw [Real.dist_eq, abs_le]
  have k1 : (c - 1) * truncW W d p ≤ (c - 1) * c * ‖truncW W d‖ := by
    have : (c - 1) * truncW W d p ≤ (c - 1) * ‖truncW W d‖ :=
      mul_le_mul_of_nonneg_left hn (by linarith)
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c - 1)
      (by linarith : (0 : ℝ) ≤ c - 1)) (norm_nonneg (truncW W d))]
  constructor
  · -- `truncW d ≤ c truncW d'`, so `truncW d - truncW d' ≤ (1 - 1/c) truncW d`
    have key : 0 ≤ c * (truncW W d' p - (2 - c) * truncW W d p) := by
      nlinarith [mul_nonneg (sq_nonneg (c - 1)) hp]
    have key2 := (mul_nonneg_iff_of_pos_left (by linarith : (0 : ℝ) < c)).1 key
    nlinarith
  · linarith

theorem locSqC_closure_apply {ξ ε : ℝ} (hε : 0 < ε) {g : DistC} (W : dyadicDomainsC)
    (p : closure (W : Set ℂ) × closure (W : Set ℂ)) :
    L217.locSqC ξ ε hε g (closure W) p =
      (aEpsDF ξ ε)⁻¹ * (lfppLocOn ξ ε hε g (closure W) p.1 p.2).toReal := by
  have hcont : Continuous fun p : closure (W : Set ℂ) × closure (W : Set ℂ) =>
      (aEpsDF ξ ε)⁻¹ * (lfppLocOn ξ ε hε g (closure W) p.1 p.2).toReal := by
    obtain ⟨𝒮, h𝒮, he0⟩ := id W.2.1
    have hWc := W.2.2
    have he := closure_dyadicDomain_eq h𝒮
    rw [← he0] at he
    rw [he] at hWc ⊢
    exact continuous_lfppDOn_union_toReal (continuous_locMollify ε hε g) 𝒮
      (dyadic_squares_closedSq h𝒮) hWc.isPreconnected _
  exact toCMap_apply_of_continuous hcont p

theorem truncW_nonneg (W : dyadicDomainsC) {d : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ)}
    (hd : ∀ p, 0 ≤ d p) (p : closure (W : Set ℂ) × closure (W : Set ℂ)) : 0 ≤ truncW W d p := by
  rw [truncW_apply]
  exact le_min (hd p) (Real.iInf_nonneg fun w => hd _)

/-- **W2–W3 (deterministic)**: Lemma 2.1 in the form "localized and heat-kernel mollifications
uniformly close on `W̄`" plus `𝔞⁻¹D^{ε_k}_g → D'` give `truncLim W g = truncD W D'`. -/
theorem truncLim_eq_of_mollify {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k} (W : dyadicDomainsC)
    {g : DistC} (hc : ∀ k, Continuous (heatMollify (εs k) g)) {D' : C(ℂ × ℂ, ℝ)}
    (hA : Tendsto (fun k => lfppC ξ (εs k) g) atTop (𝓝 D'))
    (hM : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, ∀ z ∈ closure (W : Set ℂ),
      |locMollify (εs k) (hεs k) g z - heatMollify (εs k) g z| ≤ δ) :
    truncLim ξ εs hεs W g = truncD W D' := by
  refine Tendsto.limUnder_eq ?_
  have h1 : Tendsto (fun k => truncW W (lfppSqC ξ (εs k) g (closure W))) atTop
      (𝓝 (truncD W D')) := by
    refine (((truncD W).continuous.tendsto D').comp hA).congr fun k => ?_
    exact (truncW_lfppSqC_eq (hc k) W).symm
  -- the truncated localized and non-localized LFPP are close
  have h2 : Tendsto (fun k => dist (truncW W (L217.locSqC ξ (εs k) (hεs k) g (closure W)))
      (truncW W (lfppSqC ξ (εs k) g (closure W)))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set B := ‖truncD W D'‖ + 1 with hB
    have hB0 : 0 < B := by positivity
    have hcont : Tendsto (fun δ : ℝ => (Real.exp (|ξ| * δ) - 1) * Real.exp (|ξ| * δ) * B)
        (𝓝[>] 0) (𝓝 0) := by
      have : Continuous fun δ : ℝ => (Real.exp (|ξ| * δ) - 1) * Real.exp (|ξ| * δ) * B := by
        fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨δ, hδη, hδ⟩ := ((hcont.eventually (gt_mem_nhds hη)).and self_mem_nhdsWithin).exists
    have hδ0 : (0 : ℝ) < δ := hδ
    have hnB : ∀ᶠ k in atTop, ‖truncW W (lfppSqC ξ (εs k) g (closure W))‖ ≤ B := by
      have := (continuous_norm.tendsto _).comp h1
      filter_upwards [this.eventually (gt_mem_nhds (lt_add_one ‖truncD W D'‖))] with k hk
      exact hk.le
    filter_upwards [hM δ hδ0, hnB] with k hk hkB
    set c := Real.exp (|ξ| * δ) with hcdef
    have hc1 : 1 ≤ c := Real.one_le_exp (by positivity)
    have hval1 := fun p => lfppSqC_closure_apply (ξ := ξ) W.2.1 W.2.2 (hc k) p
    have hval2 := fun p => locSqC_closure_apply (ξ := ξ) (hεs k) (g := g) W p
    have hA0 : 0 ≤ (aEpsDF ξ (εs k))⁻¹ := inv_nonneg.2 (aEpsDF_nonneg_sq _ _)
    have r1 : ∀ p, L217.locSqC ξ (εs k) (hεs k) g (closure W) p ≤
        c * lfppSqC ξ (εs k) g (closure W) p := fun p => by
      rw [hval1, hval2, mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ hA0
      exact lfppDOn_toReal_le_of_abs_sub_le (fun x hx => hk x hx)
        (lfppDOn_closure_ne_top W.2.1 W.2.2 (hc k) _ p.1.2 _ p.2.2)
    have r2 : ∀ p, lfppSqC ξ (εs k) g (closure W) p ≤
        c * L217.locSqC ξ (εs k) (hεs k) g (closure W) p := fun p => by
      rw [hval1, hval2, mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ hA0
      refine lfppDOn_toReal_le_of_abs_sub_le (fun x hx => ?_)
        (lfppDOn_closure_ne_top W.2.1 W.2.2 (continuous_locMollify _ _ g) _ p.1.2 _ p.2.2)
      rw [abs_sub_comm]; exact hk x hx
    have h0 : ∀ p, 0 ≤ truncW W (lfppSqC ξ (εs k) g (closure W)) p :=
      truncW_nonneg W fun p => by rw [hval1]; exact mul_nonneg hA0 ENNReal.toReal_nonneg
    have hd := dist_truncW_le_of_ratio W hc1 h0 r1 r2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
    calc _ ≤ (c - 1) * c * ‖truncW W (lfppSqC ξ (εs k) g (closure W))‖ := hd
      _ ≤ (c - 1) * c * B := mul_le_mul_of_nonneg_left hkB
          (mul_nonneg (by linarith) (by linarith))
      _ < η := hδη
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun k => dist_nonneg)
    (fun k => dist_triangle _ (truncW W (lfppSqC ξ (εs k) g (closure W))) _) ?_)
  simpa using h2.add (tendsto_iff_dist_tendsto_zero.1 h1)

end LQGMetric.DFGPS.T12
