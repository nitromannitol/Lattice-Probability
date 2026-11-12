import LatticeProb.LQG.WeylPiecewiseLength
import LatticeProb.LQG.CurveLengthLimit
import LatticeProb.Topology.PathGluing

/-!
# Chaining to a singular point over shells, for a Weyl-scaled metric

Let `D` be a Euclidean length metric on `ℂ` and let `E` be its Weyl scaling `e^{ξ f} · D` (`weylScaling`), with real
values. The weight `e^{ξ f}` may blow up at a point `z`, so `E` is not known to be a Euclidean length metric near `z`
(for the weight `f = -α log |·|` of a logarithmic singularity at `z = 0`, the continuity of `E` at `0` is exactly what
one wants to prove). The chaining argument is therefore carried out at the level of `D`.

Let `R₀, R₁, …` be subsets of a set `C ∋ z`, with `Rₖ ∩ Rₖ₊₁ ≠ ∅` and `Rₖ ⊆ B(z, ρₖ)` for some `ρₖ → 0`. Suppose that
`D(u, v; Rₖ) ≤ Mₖ` for `u, v ∈ Rₖ` and that `ξ f ≤ Bₖ` on `Rₖ`, with constants `Bₖ ≥ 0`. Then every point `u ∈ Rₘ` satisfies `E(u, z; C) ≤ ∑_{k ≥ 0} e^{B_{m+k}} M_{m+k}`.

The proof joins consecutive chain points by `D`-paths in the sets `R_{m+k}`, concatenates these paths into one curve
ending at `z` (`LatticeProb.Topology.exists_continuousOn_Icc_of_tendsto_paths_grid`), checks that this curve has finite
`D`-length (here `Bₖ ≥ 0` is used), and bounds its `E`-length piece by piece
(`IsEuclideanLengthMetric.curveLength_weylScaling_le_tsum`).

This is the deterministic chaining step of the proof that the metric of a whole-plane GFF plus a logarithmic
singularity at `0` has finite diameter near `0` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, Proposition
3.17, last paragraph of the proof), in a form which uses only that the unweighted metric `D` is a length metric.

## Main statements

* `LatticeProb.LQG.IsEuclideanLengthMetric.internalMetric_weylScaling_le_tsum_of_shells`:
  `E(u, z; C) ≤ ∑ₖ e^{B_{m+k}} M_{m+k}` for `u ∈ Rₘ`.
-/

open Filter Set Topology
open scoped ENNReal NNReal

namespace LatticeProb.LQG

/-- A curve has length zero on a degenerate parameter interval (as `curveLength_self_eq_zero` of
`LatticeProb.LQG.WeylChainLower`, restated here to keep the imports of this file small). -/
private theorem IsEuclideanLengthMetric.curveLength_self {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (p : ℝ → ℂ) (t : ℝ) : curveLength D p t t = 0 := by
  unfold curveLength
  refine le_antisymm (iSup_le fun q => (Finset.sum_eq_zero fun i _ => ?_).le) zero_le
  have h1 := q.2.2.2 (i + 1)
  have h2 := q.2.2.2 i
  rw [le_antisymm h1.2 h1.1, le_antisymm h2.2 h2.1, hD.self_eq_zero, ENNReal.ofReal_zero]

/-- **Chaining to a singular point over shells, for a Weyl-scaled metric.** Let `D` be a Euclidean length metric and
`E = e^{ξ f} · D`. Let `z ∈ C` and `Rₖ ⊆ C` with `Rₖ ∩ Rₖ₊₁ ≠ ∅` and `Rₖ ⊆ B(z, ρₖ)`, `ρₖ → 0`. If `ξ f ≤ Bₖ` on `Rₖ`
with `Bₖ ≥ 0`, and `D(u, v; Rₖ) ≤ Mₖ` for `u, v ∈ Rₖ`, then `E(u, z; C) ≤ ∑_{k ≥ 0} e^{B_{m+k}} M_{m+k}` for every
`u ∈ Rₘ`. No regularity of `E` at `z` is assumed. -/
theorem IsEuclideanLengthMetric.internalMetric_weylScaling_le_tsum_of_shells {D E : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {f : ℂ → ℝ}
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) {C : Set ℂ} {z : ℂ} (hz : z ∈ C)
    {R : ℕ → Set ℂ} (hRC : ∀ k, R k ⊆ C) (hmeet : ∀ k, (R k ∩ R (k + 1)).Nonempty) {ρ : ℕ → ℝ}
    (hρ : Tendsto ρ atTop (𝓝 0)) (hRρ : ∀ k, R k ⊆ Metric.ball z (ρ k)) {B : ℕ → ℝ} (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ k, ∀ w ∈ R k, ξ * f w ≤ B k) {M : ℕ → ℝ≥0∞}
    (hM : ∀ k, ∀ u ∈ R k, ∀ v ∈ R k, internalMetric D (R k) u v ≤ M k) {m : ℕ} {u : ℂ} (hu : u ∈ R m) :
    internalMetric E C u z ≤ ∑' k, ENNReal.ofReal (Real.exp (B (m + k))) * M (m + k) := by
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
  -- chain points `c k, c (k + 1) ∈ R (m + k)`, starting at `u`
  choose x hx using hmeet
  obtain ⟨c, hc0, hcs⟩ : ∃ c : ℕ → ℂ, c 0 = u ∧ ∀ j, c (j + 1) = x (m + j) :=
    ⟨fun k => Nat.rec u (fun j _ => x (m + j)) k, rfl, fun _ => rfl⟩
  have hc : ∀ k, c k ∈ R (m + k) := by
    intro k
    cases k with
    | zero => rw [hc0]; simpa using hu
    | succ j => rw [hcs]; exact (hx (m + j)).2
  have hc' : ∀ k, c (k + 1) ∈ R (m + k) := fun k => by rw [hcs]; exact (hx (m + k)).1
  -- nearly optimal `D`-paths inside the shells
  have hex : ∀ k, ∃ P : Path (c k) (c (k + 1)), (∀ t, P t ∈ R (m + k)) ∧ pathLength D P < M (m + k) + δ k := by
    intro k
    have h := (hM (m + k) (c k) (hc k) (c (k + 1)) (hc' k)).trans_lt
      (ENNReal.lt_add_right (hMfin k) (hδ0 k))
    unfold internalMetric at h
    obtain ⟨P, hP⟩ := iInf_lt_iff.1 h
    obtain ⟨hPR, hPlen⟩ := iInf_lt_iff.1 hP
    exact ⟨P, hPR, hPlen⟩
  choose γ hγR hγlen using hex
  have hext : ∀ k s, (γ k).extend s ∈ R (m + k) := fun k s => hγR k (Set.projIcc 0 1 zero_le_one s)
  -- the concatenated curve
  have hρ' : Tendsto (fun n => ρ (m + n)) atTop (𝓝 0) :=
    hρ.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn => hn.trans (Nat.le_add_left n m)⟩)
  obtain ⟨β, hβc, hβ1, hβr, hβI⟩ :=
    LatticeProb.Topology.exists_continuousOn_Icc_of_tendsto_paths_grid γ hρ' fun n s => hRρ (m + n) (hγR n s)
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
    | zero => rw [hτ0, Finset.sum_range_zero]; exact hD.curveLength_self β 0
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
  have hEβ := hD.curveLength_weylScaling_le_tsum hscale hβc hfin hτmono hτ0 hτ1 hτlim hBβ
  -- the curve as a path from `u` to `z` inside `C`
  have hβ0 : β 0 = u := by
    have h := hβI 0 0 ⟨by norm_num, by norm_num⟩
    rw [h, show ((0 : ℝ) - (1 - 2⁻¹ ^ 0)) / 2⁻¹ ^ (0 + 1) = 0 by norm_num, Path.extend_zero, hc0]
  let P : Path u z :=
    { toFun := (Icc (0 : ℝ) 1).domRestrict β
      continuous_toFun := hβc.domRestrict
      source' := by show β 0 = u; exact hβ0
      target' := by show β 1 = z; exact hβ1 }
  have hPβ : EqOn P.extend β (Icc 0 1) := fun t ht => by rw [Path.extend_apply P ht]; rfl
  have hPC : ∀ t, P t ∈ C := by
    intro t
    show β t ∈ C
    rcases eq_or_lt_of_le t.2.2 with h | h
    · rw [h, hβ1]
      exact hz
    · obtain ⟨n, s, hs⟩ := hβr t ⟨t.2.1, h⟩
      rw [← hs]
      exact hRC _ (hγR n s)
  calc internalMetric E C u z ≤ pathLength E P := iInf₂_le P hPC
    _ = curveLength E β 0 1 := curveLength_eq_of_eqOn hPβ
    _ ≤ ∑' k, ENNReal.ofReal (Real.exp (B (m + k))) * curveLength D β (τ k) (τ (k + 1)) := hEβ
    _ = ∑' k, ENNReal.ofReal (Real.exp (B (m + k))) * pathLength D (γ k) :=
        tsum_congr fun k => by rw [hpiece k]
    _ ≤ ∑' k, ENNReal.ofReal (Real.exp (B (m + k))) * (M (m + k) + δ k) :=
        ENNReal.tsum_le_tsum fun k => by gcongr; exact (hγlen k).le
    _ ≤ _ := hT

end LatticeProb.LQG
