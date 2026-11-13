import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiA3

/-!
# The upper bound of the Liouville graph distance exponent with a wall around the segment

Ding-Zeitouni-Zhang (arXiv:1807.00422, Proposition 5.1, upper bound) bound the Liouville graph
distance `D_δ(u, v)` of two points `u ≠ v` of the open unit square by chaining the points
`u + (i/l)(v − u)`, `0 ≤ i ≤ l`, along the segment `[u, v]`: each link is bounded by the distance
walled at the box `𝕍̃` of the link, and these boxes lie within twice the step length of the
segment. Taking the chain fine enough, every link box lies in any prescribed neighbourhood `K` of
the segment, so the same polynomial rate holds for the distance walled at `K`, which only uses balls
inside `K`.

* `LatticeProb.LQG.hasRate_dzzWall_upper_interior`: the walled form of
  `LQGMetric.DZZ.hasRate_dzzMuIn_upper_interior`, whose proof it follows (the chain is refined so
  that its link boxes lie in `K`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric

open DZZ WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **The upper bound of DZZ Proposition 5.1 with a wall around the segment.** For `u ≠ v` in the
open unit square and a set `K` containing the closed `m'`-neighbourhood of the segment `[u, v]`,
`P[D^K_δ(u, v) > δ^{−χ−ι}] ≤ C(δ^c + e^{−(log δ⁻¹)^{0.7}})` for the walled measure
`D^K = D(μ + ∞ · Leb|_{Kᶜ})`, given DZZ Lemma 5.3 at `μIn` and the walled Proposition 3.17. -/
theorem _root_.LatticeProb.LQG.hasRate_dzzWall_upper_interior (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {χ : ℝ} (hL : DZZLem53Exp P (dzzMuIn γ W) χ)
    (hwalls : ∃ ξ₂ : ℝ, 0 < ξ₂ ∧ ∀ ξ, 0 < ξ → ξ < ξ₂ → DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls)
    {u v : ℂ} (hu : u ∈ openSquare) (hv : v ∈ openSquare) (huv : u ≠ v) {K : Set ℂ} {m' : ℝ}
    (hm' : 0 < m')
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, ‖z - (u + (t : ℂ) * (v - u))‖ ≤ m' → z ∈ K)
    {ι : ℝ} (hι : 0 < ι) :
    HasRate P (fun δ => {ω | ((lgdDZZ (dzzWall K (dzzMuIn γ W ω)) δ u v : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (δ ^ (-(χ + ι)))}) := by
  obtain ⟨m, hm0, hm1, hseg⟩ := exists_margin_openSquare hu hv
  set d := ‖v - u‖ with hd
  have hd0 : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 huv.symm)
  set n : ℕ := ⌈(20 + 4 / m + 2 / m') * d⌉₊ with hn
  set l : ℕ := n + 1 with hl
  have hl0 : (0 : ℝ) < l := by positivity
  have hlb : (20 + 4 / m + 2 / m') * d ≤ l := by
    rw [hl, Nat.cast_add, Nat.cast_one]; linarith [Nat.le_ceil ((20 + 4 / m + 2 / m') * d)]
  have h4m : 0 ≤ 4 / m * d := by positivity
  have h2m : 0 ≤ 2 / m' * d := by positivity
  have hstep : ∀ i, ‖chiChain u v l (i + 1) - chiChain u v l i‖ = d / l := by
    intro i
    rw [chiChain_succ_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    ring
  have hstep20 : d / l ≤ 1 / 20 := by
    rw [div_le_iff₀ hl0]; nlinarith
  have hstepm : 2 * (d / l) ≤ m / 2 := by
    have h1 : 4 / m * d * m = 4 * d := by field_simp
    have h2 := mul_le_mul_of_nonneg_left hlb hm0.le
    rw [mul_div_assoc', div_le_iff₀ hl0]
    nlinarith [mul_nonneg hm0.le h2m, mul_nonneg hm0.le hd0.le]
  have hstepm' : 2 * (d / l) ≤ m' := by
    have h1 : 2 / m' * d * m' = 2 * d := by field_simp
    have h2 := mul_le_mul_of_nonneg_left hlb hm'.le
    rw [mul_div_assoc', div_le_iff₀ hl0]
    nlinarith [mul_nonneg hm'.le h4m, mul_nonneg hm'.le hd0.le]
  set ξc := min (m / 2) (1 / 4) with hξc
  have hξc0 : 0 < ξc := lt_min (by linarith) (by norm_num)
  have hne : ∀ i, chiChain u v l i ≠ chiChain u v l (i + 1) := by
    intro i h
    have := hstep i
    rw [← h, sub_self, norm_zero] at this
    exact (div_pos hd0 hl0).ne' this.symm
  -- the midpoint parameter of the `i`-th link lies in `[0, 1]`
  have hmid : ∀ i < l, (0 : ℝ) ≤ ((i : ℝ) + 1 / 2) / l ∧ ((i : ℝ) + 1 / 2) / l ≤ 1 := by
    intro i hi
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hl0]
    have : ((i + 1 : ℕ) : ℝ) ≤ l := by exact_mod_cast hi
    push_cast at this; linarith
  have hbox : ∀ i < l, tildeBox (chiChain u v l i) (chiChain u v l (i + 1)) ⊆ dzzVXi ξc := by
    intro i hi z hz
    have hz' := norm_sub_mid_le_of_mem_tildeBox (hne i) hz
    rw [hstep, chiChain_mid] at hz'
    obtain ⟨ht0, ht1⟩ := hmid i hi
    obtain ⟨g1, g2, g3, g4⟩ := hseg _ ht0 ht1
    exact dzzVXi_anti_chi (min_le_left _ _)
      (mem_dzzVXi_of_near_point hm0 g1 g2 g3 g4 (hz'.trans hstepm))
  have hboxK : ∀ i < l, tildeBox (chiChain u v l i) (chiChain u v l (i + 1)) ⊆ K := by
    intro i hi z hz
    have hz' := norm_sub_mid_le_of_mem_tildeBox (hne i) hz
    rw [hstep, chiChain_mid] at hz'
    obtain ⟨ht0, ht1⟩ := hmid i hi
    exact hK _ ht0 ht1 z (hz'.trans hstepm')
  have href := fun ι' (hι' : 0 < ι') => hasRate_ref_upper hW hγ hγ2 hL hwalls hι'
  have hlink : ∀ i < l, HasRate P (fun δ => {ω |
      ((lgdDZZ (dzzWall (tildeBox (chiChain u v l i) (chiChain u v l (i + 1))) (dzzMuIn γ W ω)) δ
        (chiChain u v l i) (chiChain u v l (i + 1)) : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (δ ^ (-(χ + ι / 2)))}) := fun i hi =>
    hasRate_tilde_link hW hγ hγ2 chiRefU_mem chiRefV_mem chiRef_ne (hne i)
      (by rw [hstep, chiRef_norm]; exact hstep20) hξc0 (min_le_right _ _) (hbox i hi) href
      (by positivity)
  refine (hasRate_biInter_range l hlink).mono ?_
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (l : ℝ) ≤ δ ^ (-(ι / 2)) :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith : -(ι / 2) < 0)).eventually_ge_atTop _
  filter_upwards [hev, self_mem_nhdsWithin] with δ hδl hδ ω hω
  have hδ0 : 0 < δ := hδ
  simp only [mem_iInter, Finset.mem_range, mem_ofPred_eq] at hω ⊢
  have hchain := lgdDZZ_chain_le_chi (dzzWall K (dzzMuIn γ W ω)) δ (chiChain u v l) n
  have h0 : chiChain u v l 0 = u := by simp [chiChain]
  have hlast : chiChain u v l (n + 1) = v := by
    simp only [chiChain]
    rw [← hl, div_self hl0.ne']; simp
  rw [h0, hlast] at hchain
  have hp : 0 ≤ δ ^ (-(χ + ι / 2)) := (Real.rpow_pos_of_pos hδ0 _).le
  calc ((lgdDZZ (dzzWall K (dzzMuIn γ W ω)) δ u v : ℕ∞) : ℝ≥0∞) ≤ _ := hchain
    _ ≤ ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (δ ^ (-(χ + ι / 2))) :=
        Finset.sum_le_sum fun i hi =>
          (ENat.toENNReal_le.2 (lgdDZZ_mono_measure
            (dzzWall_anti (hboxK i (Finset.mem_range.1 hi)) _) _ _ _)).trans
            (hω i (Finset.mem_range.1 hi))
    _ = ENNReal.ofReal (l * δ ^ (-(χ + ι / 2))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (δ ^ (-(χ + ι))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : δ ^ (-(χ + ι)) = δ ^ (-(ι / 2)) * δ ^ (-(χ + ι / 2)) := by
          rw [← Real.rpow_add hδ0]; ring_nf
        rw [this]
        exact mul_le_mul_of_nonneg_right hδl hp

end LQGMetric
