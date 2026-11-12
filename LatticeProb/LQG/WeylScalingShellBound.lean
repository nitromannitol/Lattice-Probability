import LatticeProb.LQG.WeylShellChaining
import LatticeProb.LQG.WeylLogTruncation

/-!
# Bounds on the extended Weyl scaling along curves and over shells

Let `D` be a Euclidean length metric on `ℂ`, `ξ ∈ ℝ` and `f : ℂ → ℝ`. The Weyl scaling `e^{ξ f} · D` (`weylScaling`)
takes values in `[0, ∞]`. The bounds of `LatticeProb.LQG.WeylPiecewiseLength` and `LatticeProb.LQG.WeylShellChaining`
bound the length of a curve for a real-valued metric `E` with `E = e^{ξ f} · D`, which presupposes that the Weyl
scaling is finite everywhere. This file proves the same bounds for the extended value of the Weyl scaling itself, so
that they apply before finiteness is known. For the weight `f = -α log |·|` of a logarithmic singularity at `0` with
`ξ α > 0`, they are the means to prove that the scaled metric is finite at `0` and continuous there
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, Proposition 3.17).

## Main statements

* `LatticeProb.LQG.IsEuclideanLengthMetric.lintegral_le_tsum_curveLength`: for a curve `p` of finite `D`-length with
  arclength parametrization `q` on `[0, L]`, `∫_0^L e^{ξ f(q s)} ds ≤ ∑ₖ e^{Bₖ} len(p|[τₖ, τₖ₊₁]; D)` when
  `ξ f(p t) ≤ Bₖ` for `t ∈ [τₖ, τₖ₊₁]`.
* `LatticeProb.LQG.IsEuclideanLengthMetric.weylScaling_le_tsum_curveLength`:
  `e^{ξ f} · D (p 0, p 1) ≤ ∑ₖ e^{Bₖ} len(p|[τₖ, τₖ₊₁]; D)`.
* `LatticeProb.LQG.IsEuclideanLengthMetric.weylScaling_le_tsum_of_shells`: chaining to a point `z` over shells. If
  `Aₖ ∩ Aₖ₊₁ ≠ ∅`, `D(x, y; Sₖ) ≤ Mₖ` for `x, y ∈ Aₖ`, `ξ f ≤ Bₖ` on `Sₖ` with `Bₖ ≥ 0`, and `Sₖ ⊆ B(z, ρₖ)` with
  `ρₖ → 0`, then `e^{ξ f} · D (u, z) ≤ ∑_{k ≥ 0} e^{B_{m+k}} M_{m+k}` for every `u ∈ Aₘ`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace LatticeProb.LQG

/-- A curve has length zero on a degenerate parameter interval. -/
private theorem IsEuclideanLengthMetric.curveLength_self_eq_zero' {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (p : ℝ → ℂ) (t : ℝ) : curveLength D p t t = 0 := by
  unfold curveLength
  refine le_antisymm (iSup_le fun q => (Finset.sum_eq_zero fun i _ => ?_).le) zero_le
  have h1 := q.2.2.2 (i + 1)
  have h2 := q.2.2.2 i
  rw [le_antisymm h1.2 h1.1, le_antisymm h2.2 h2.1, hD.self_eq_zero, ENNReal.ofReal_zero]

/-- **Piecewise bound on the weighted arclength integral.** Let `p` be continuous on `[0, 1]` with finite `D`-length
`L`, and let `q` be its arclength parametrization (`q (len(p|[0, t]; D)) = p t`). If `0 = τ₀ ≤ τ₁ ≤ ... → 1` and
`ξ f(p t) ≤ Bₖ` for `t ∈ [τₖ, τₖ₊₁]`, then `∫_0^L e^{ξ f(q s)} ds ≤ ∑ₖ e^{Bₖ} len(p|[τₖ, τₖ₊₁]; D)`. -/
theorem IsEuclideanLengthMetric.lintegral_le_tsum_curveLength {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {f : ℂ → ℝ} {p : ℝ → ℂ}
    (hp : ContinuousOn p (Icc 0 1)) (hfin : curveLength D p 0 1 < ⊤) {q : ℝ → ℂ}
    (htrack : ∀ t ∈ Icc (0 : ℝ) 1, q (curveLength D p 0 t).toReal = p t) {τ : ℕ → ℝ} (hτ : Monotone τ)
    (hτ0 : τ 0 = 0) (hτ1 : ∀ k, τ k ≤ 1) (hτlim : Tendsto τ atTop (𝓝 1)) {B : ℕ → ℝ}
    (hB : ∀ k, ∀ t ∈ Icc (τ k) (τ (k + 1)), ξ * f (p t) ≤ B k) :
    ∫⁻ s in Icc 0 (curveLength D p 0 1).toReal, ENNReal.ofReal (Real.exp (ξ * f (q s))) ≤
      ∑' k, ENNReal.ofReal (Real.exp (B k)) * curveLength D p (τ k) (τ (k + 1)) := by
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
  calc ∫⁻ s in Icc 0 (φ 1), ENNReal.ofReal (Real.exp (ξ * f (q s)))
      ≤ ∫⁻ s in {φ 1} ∪ ⋃ k, Icc (φ (τ k)) (φ (τ (k + 1))), ENNReal.ofReal (Real.exp (ξ * f (q s))) :=
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

/-- **Piecewise bound on the Weyl scaling between the endpoints of a curve.** Let `p` be continuous on `[0, 1]` with
finite `D`-length. If `0 = τ₀ ≤ τ₁ ≤ ... → 1` and `ξ f(p t) ≤ Bₖ` for `t ∈ [τₖ, τₖ₊₁]`, then
`e^{ξ f} · D (p 0, p 1) ≤ ∑ₖ e^{Bₖ} len(p|[τₖ, τₖ₊₁]; D)`, as an inequality in `[0, ∞]`. -/
theorem IsEuclideanLengthMetric.weylScaling_le_tsum_curveLength {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (ξ : ℝ) (f : ℂ → ℝ) {p : ℝ → ℂ}
    (hp : ContinuousOn p (Icc 0 1)) (hfin : curveLength D p 0 1 < ⊤) {τ : ℕ → ℝ} (hτ : Monotone τ)
    (hτ0 : τ 0 = 0) (hτ1 : ∀ k, τ k ≤ 1) (hτlim : Tendsto τ atTop (𝓝 1)) {B : ℕ → ℝ}
    (hB : ∀ k, ∀ t ∈ Icc (τ k) (τ (k + 1)), ξ * f (p t) ≤ B k) :
    weylScaling D ξ f (p 0) (p 1) ≤
      ∑' k, ENNReal.ofReal (Real.exp (B k)) * curveLength D p (τ k) (τ (k + 1)) := by
  obtain ⟨q, hq, hq0, hq1, htrack⟩ := hD.exists_lengthParametrized_with_tracking zero_le_one hp hfin
  rw [← hq0, ← hq1]
  exact (hD.weylScaling_le_lintegral_subarc ξ f hq le_rfl hq.1 le_rfl).trans
    (hD.lintegral_le_tsum_curveLength hp hfin htrack hτ hτ0 hτ1 hτlim hB)

/-- **Chaining to a point over shells, for the extended Weyl scaling.** Let `D` be a Euclidean length metric, and let
`Aₖ, Sₖ ⊆ ℂ` with `Aₖ ∩ Aₖ₊₁ ≠ ∅` and `Sₖ ⊆ B(z, ρₖ)`, `ρₖ → 0`. If `ξ f ≤ Bₖ` on `Sₖ` with `Bₖ ≥ 0`, and
`D(x, y; Sₖ) ≤ Mₖ` for `x, y ∈ Aₖ`, then `e^{ξ f} · D (u, z) ≤ ∑_{k ≥ 0} e^{B_{m+k}} M_{m+k}` for every `u ∈ Aₘ`. No
finiteness or regularity of `e^{ξ f} · D` is assumed. -/
theorem IsEuclideanLengthMetric.weylScaling_le_tsum_of_shells {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (ξ : ℝ) (f : ℂ → ℝ) {z : ℂ} {A S : ℕ → Set ℂ}
    (hmeet : ∀ k, (A k ∩ A (k + 1)).Nonempty) {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0))
    (hSρ : ∀ k, S k ⊆ Metric.ball z (ρ k)) {B : ℕ → ℝ} (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ k, ∀ w ∈ S k, ξ * f w ≤ B k) {M : ℕ → ℝ≥0∞}
    (hM : ∀ k, ∀ u ∈ A k, ∀ v ∈ A k, internalMetric D (S k) u v ≤ M k) {m : ℕ} {u : ℂ} (hu : u ∈ A m) :
    weylScaling D ξ f u z ≤ ∑' k, ENNReal.ofReal (Real.exp (B (m + k))) * M (m + k) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hS => ?_
  obtain ⟨ε', hε'0, hε'⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.coe_ne_zero.2 hε.ne') ℕ
  -- the slack allowed on the `k`-th piece, in units of `D`-length
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ≥0∞, ∀ k, δ k = ENNReal.ofReal (Real.exp (-B (m + k))) * ε' k :=
    ⟨_, fun _ => rfl⟩
  have hδ0 : ∀ k, δ k ≠ 0 := fun k => by
    rw [hδ k]
    exact (ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      (ENNReal.coe_pos.2 (hε'0 k)).ne').ne'
  have hwδ : ∀ k, ENNReal.ofReal (Real.exp (B (m + k))) * δ k = ε' k := fun k => by
    rw [hδ k, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, ENNReal.ofReal_one, one_mul]
  have hw1 : ∀ k, 1 ≤ ENNReal.ofReal (Real.exp (B (m + k))) := fun k =>
    ENNReal.one_le_ofReal.2 (Real.one_le_exp (hB0 _))
  have hMfin : ∀ k, M (m + k) ≠ ⊤ := fun k h => by
    have hle := ENNReal.le_tsum (f := fun k => ENNReal.ofReal (Real.exp (B (m + k))) * M (m + k)) k
    simp only [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne', top_le_iff] at hle
    exact hS.ne hle
  -- chain points `c k, c (k + 1) ∈ A (m + k)`, starting at `u`
  choose x hx using hmeet
  obtain ⟨c, hc0, hcs⟩ : ∃ c : ℕ → ℂ, c 0 = u ∧ ∀ j, c (j + 1) = x (m + j) :=
    ⟨fun k => Nat.rec u (fun j _ => x (m + j)) k, rfl, fun _ => rfl⟩
  have hc : ∀ k, c k ∈ A (m + k) := by
    intro k
    cases k with
    | zero => rw [hc0]; simpa using hu
    | succ j => rw [hcs]; exact (hx (m + j)).2
  have hc' : ∀ k, c (k + 1) ∈ A (m + k) := fun k => by rw [hcs]; exact (hx (m + k)).1
  -- nearly optimal `D`-paths inside the sets `S (m + k)`
  have hex : ∀ k, ∃ P : Path (c k) (c (k + 1)), (∀ t, P t ∈ S (m + k)) ∧ pathLength D P < M (m + k) + δ k := by
    intro k
    have h := (hM (m + k) (c k) (hc k) (c (k + 1)) (hc' k)).trans_lt
      (ENNReal.lt_add_right (hMfin k) (hδ0 k))
    unfold internalMetric at h
    obtain ⟨P, hP⟩ := iInf_lt_iff.1 h
    obtain ⟨hPR, hPlen⟩ := iInf_lt_iff.1 hP
    exact ⟨P, hPR, hPlen⟩
  choose γ hγS hγlen using hex
  have hext : ∀ k s, (γ k).extend s ∈ S (m + k) := fun k s => hγS k (Set.projIcc 0 1 zero_le_one s)
  -- the concatenated curve
  have hρ' : Tendsto (fun n => ρ (m + n)) atTop (𝓝 0) :=
    hρ.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn => hn.trans (Nat.le_add_left n m)⟩)
  obtain ⟨β, hβc, hβ1, -, hβI⟩ :=
    LatticeProb.Topology.exists_continuousOn_Icc_of_tendsto_paths_grid γ hρ' fun n s => hSρ (m + n) (hγS n s)
  -- the time grid
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℕ → ℝ, ∀ k, τ k = 1 - 2⁻¹ ^ k := ⟨_, fun _ => rfl⟩
  have hτmono : Monotone τ := fun i j hij => by
    rw [hτdef, hτdef]
    linarith [pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num) hij]
  have hτ0 : τ 0 = 0 := by rw [hτdef]; norm_num
  have hτ0' : ∀ k, 0 ≤ τ k := fun k => hτ0 ▸ hτmono (Nat.zero_le k)
  have hτ1 : ∀ k, τ k ≤ 1 := fun k => by
    rw [hτdef]
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) k]
  have hτlim : Tendsto τ atTop (𝓝 1) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).const_sub 1
    rw [sub_zero] at h
    exact h.congr fun k => (hτdef k).symm
  have hβI' : ∀ k, ∀ t ∈ Icc (τ k) (τ (k + 1)),
      β t = (γ k).extend ((t - (1 - 2⁻¹ ^ k)) / 2⁻¹ ^ (k + 1)) := fun k t ht =>
    hβI k t (by rwa [hτdef, hτdef] at ht)
  -- the `D`-length of the `k`-th piece of the curve is the `D`-length of `γ k`
  have hpiece : ∀ k, curveLength D β (τ k) (τ (k + 1)) = pathLength D (γ k) := by
    intro k
    have hlt : (0 : ℝ) < 2⁻¹ ^ (k + 1) := by positivity
    let φ : ℝ → ℝ := fun t => (t - (1 - 2⁻¹ ^ k)) / 2⁻¹ ^ (k + 1)
    have hEq : EqOn β ((γ k).extend ∘ φ) (Icc (τ k) (τ (k + 1))) := fun t ht => hβI' k t ht
    have hφc : ContinuousOn φ (Icc (τ k) (τ (k + 1))) :=
      ((continuous_id.sub continuous_const).div_const _).continuousOn
    have hφm : MonotoneOn φ (Icc (τ k) (τ (k + 1))) := fun s _ t _ hst => by
      simp only [φ]
      gcongr
    rw [curveLength_eq_of_eqOn hEq,
      hD.curveLength_comp_of_monotoneOn (γ k).extend φ (hτmono (Nat.le_succ k)) hφc hφm]
    have h0 : φ (τ k) = 0 := by simp only [φ, hτdef, sub_self, zero_div]
    have h1 : φ (τ (k + 1)) = 1 := by
      simp only [φ, hτdef]
      rw [div_eq_one_iff_eq hlt.ne']
      ring
    rw [h0, h1]
    rfl
  have hpartial : ∀ n, curveLength D β 0 (τ n) = ∑ k ∈ Finset.range n, pathLength D (γ k) := by
    intro n
    induction n with
    | zero => rw [hτ0, Finset.sum_range_zero]; exact hD.curveLength_self_eq_zero' β 0
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, ← hpiece n]
      exact (hD.curveLength_add β (hτ0' n) (hτmono (Nat.le_succ n))).symm
  -- the slack budget
  have hT : ∑' k, ENNReal.ofReal (Real.exp (B (m + k))) * (M (m + k) + δ k) ≤
      (∑' k, ENNReal.ofReal (Real.exp (B (m + k))) * M (m + k)) + ε := by
    calc ∑' k, ENNReal.ofReal (Real.exp (B (m + k))) * (M (m + k) + δ k)
        = ∑' k, (ENNReal.ofReal (Real.exp (B (m + k))) * M (m + k) + ε' k) :=
          tsum_congr fun k => by rw [mul_add, hwδ k]
      _ = (∑' k, ENNReal.ofReal (Real.exp (B (m + k))) * M (m + k)) + ∑' k, (ε' k : ℝ≥0∞) :=
          ENNReal.tsum_add
      _ ≤ (∑' k, ENNReal.ofReal (Real.exp (B (m + k))) * M (m + k)) + ε := add_le_add le_rfl hε'.le
  have hlen : ∀ k, pathLength D (γ k) ≤ ENNReal.ofReal (Real.exp (B (m + k))) * (M (m + k) + δ k) :=
    fun k => (hγlen k).le.trans (le_mul_of_one_le_left zero_le (hw1 k))
  -- the curve has finite `D`-length
  have hfin : curveLength D β 0 1 < ⊤ := by
    refine (hD.curveLength_le_iSup_of_tendsto_of_mem_Icc hβc (fun n => ⟨hτ0' n, hτ1 n⟩) hτlim).trans_lt ?_
    refine lt_of_le_of_lt (iSup_le fun n => ?_)
      (((ENNReal.tsum_le_tsum hlen).trans hT).trans_lt (ENNReal.add_lt_top.2 ⟨hS, ENNReal.coe_lt_top⟩))
    rw [hpartial n]
    exact ENNReal.sum_le_tsum _
  -- the weight bound along the curve
  have hBβ : ∀ k, ∀ t ∈ Icc (τ k) (τ (k + 1)), ξ * f (β t) ≤ B (m + k) := fun k t ht => by
    rw [hβI' k t ht]
    exact hB _ _ (hext k _)
  have hβ0 : β 0 = u := by
    have h := hβI 0 0 ⟨by norm_num, by norm_num⟩
    rw [h, show ((0 : ℝ) - (1 - 2⁻¹ ^ 0)) / 2⁻¹ ^ (0 + 1) = 0 by norm_num, Path.extend_zero, hc0]
  calc weylScaling D ξ f u z = weylScaling D ξ f (β 0) (β 1) := by rw [hβ0, hβ1]
    _ ≤ ∑' k, ENNReal.ofReal (Real.exp (B (m + k))) * curveLength D β (τ k) (τ (k + 1)) :=
        hD.weylScaling_le_tsum_curveLength ξ f hβc hfin hτmono hτ0 hτ1 hτlim hBβ
    _ = ∑' k, ENNReal.ofReal (Real.exp (B (m + k))) * pathLength D (γ k) :=
        tsum_congr fun k => by rw [hpiece k]
    _ ≤ ∑' k, ENNReal.ofReal (Real.exp (B (m + k))) * (M (m + k) + δ k) :=
        ENNReal.tsum_le_tsum fun k => by gcongr; exact (hγlen k).le
    _ ≤ _ := hT

end LatticeProb.LQG
