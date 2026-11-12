/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53GA1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J8
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53F1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B11
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53V1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53L1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13Reg

/-!
# DZZ Lemma 5.3 part 1: geometric glue G-G3, G-A1, G-G1 (P2-DZZ53GA, DEC-131-IF §3)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 5.3, l. 2361–2548.

* **G-G3** `l53_frontier_closedBox_eq`: `μH¹(∂𝖡̄) = 4 s_𝖡` (DZZ l. 2425–2429 use `𝓛₁(∂𝖡) = 4 s/K`).
  `≤` is `l53_frontier_closedBox_le` (S5L53J8); `≥` from the two closed horizontal sides and the
  two open vertical sides, pairwise disjoint (same segment computations as `l53J_vline_eq`).
* **G-A1** `l53_side_ratio`: consecutive boxes of a Lemma 3.13 box sequence (`L313Q`) have
  side ratio `≥ ε²` in both directions. Own elementary proof of the tacit fact behind DZZ
  l. 1314–1340 (a neighbour of `b` inside a cell smaller than `b` would be an explored box whose
  coarse region `boxReg` meets the fine region of `b`, contradicting the explored clause of `L313Q`).
* **G-G1** `l53_sqBox_five_subset_tildeBox`: for large `k`, every box of side `≤ δ^{C_Mc}` meeting
  the doubly thickened region `R'' = cthick(2δ^{C_Mc}) (cthick(8δ^{C_Mc}) ⋃𝕍̃_{w_{i−1},w_i})` has
  `sqBox(c_b, 5 s_b) ⊆ 𝕍̃_{u,v}` (DV-D131-4). Basis `l53_thickening_region_sub_tildeBox`:
  the `|u−v|/3`-thickening of `⋃_i 𝕍̃_{w_{i−1},w_i}` lies in `𝕍̃_{u,v}`. Own elementary proof.
  `l53_ball_sub_openSquare_of_tildeBox`: such balls lie in `𝕍°` (via `tildeBox_subset_dzzVXi`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-! ### G-G3: the length of the boundary of a closed box -/

/-! ### G-A1: side ratio of meeting boxes of an `L313Q` sequence -/

/-- **G-A1, general form**: two boxes of an `L313Q` sequence (cell predicate of `𝒱_δ`) whose
closures meet have side ratio `≥ ε²`. -/
lemma l53_side_ratio_of_meet {m : DyBox → ℝ} {δ ε : ℝ} {u v : ℂ} {l : List DyBox}
    (hQ : L313Q ε u v (IsCell m δ) l) {b b' : DyBox} (hb : b ∈ l) (hb' : b' ∈ l)
    (hm : (b.closedBox ∩ b'.closedBox).Nonempty) : ε ^ 2 * b.side ≤ b'.side := by
  obtain ⟨C', hC', hsub, hside⟩ := hQ.2.1 b' hb'
  by_contra hlt
  push Not at hlt
  have hb0 := side_pos' b
  have hb'0 := side_pos' b'
  have hC0 := side_pos' C'
  have hε : 0 < ε ^ 2 := by
    rcases (sq_nonneg ε).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hside; linarith
  have hCb : C'.side < b.side := by
    rw [hside] at hlt
    nlinarith
  have hexp : Explored (IsCell m δ) C' := fun i hi hc => by
    have := hC'.2 i hi
    linarith [hc.1]
  have hdis := hQ.2.2 C' hexp
  have hb1 : b.side ≤ 1 := by
    unfold DyBox.side; exact pow_le_one₀ (by norm_num) (by norm_num)
  set t : ℝ := (C'.side ^ 2 + b.side ^ 2) / 2 with ht
  have hsq : C'.side ^ 2 < b.side ^ 2 := by nlinarith
  have ht1 : C'.side ^ 2 < t := by rw [ht]; linarith
  have ht2 : t < b.side ^ 2 := by rw [ht]; linarith
  have ht0 : 0 < t := by positivity
  have hr : 0 < etaRad t := etaRad_pos_of_lt_one ht0 (by nlinarith)
  obtain ⟨p, hpb, hpb'⟩ := hm
  have hpC := hsub hpb'
  obtain ⟨a1, a2, a3, a4⟩ := hpb
  obtain ⟨c1, c2, c3, c4⟩ := hpC
  have hcen : C'.center ∈ b.largeBox := by
    simp only [DyBox.largeBox, DyBox.center, mem_ofPred_eq]
    constructor <;> rw [abs_le] <;> constructor <;> nlinarith
  exact Set.disjoint_left.1 hdis (show (t, C'.center) ∈ boxReg C' from ⟨ht1, mem_ball_self hr⟩)
    ⟨b, hb, C'.center, hcen, ⟨ht0, ht2⟩, mem_ball_self hr⟩

/-- **G-A1** (DEC-131-IF §3): consecutive boxes of an `L313Q` sequence have side ratio `≥ ε²`
(both directions). -/
lemma l53_side_ratio {m : DyBox → ℝ} {δ ε : ℝ} {u v : ℂ} {l : List DyBox}
    (hQ : L313Q ε u v (fun b => IsCell m δ b) l) (i : ℕ) (hi : i + 1 < l.length) :
    ε ^ 2 * (l.getD i root).side ≤ (l.getD (i + 1) root).side ∧
      ε ^ 2 * (l.getD (i + 1) root).side ≤ (l.getD i root).side := by
  have hN : Neighbour l[i] l[i + 1] := hQ.1.2.getElem i hi
  have hne : (l[i].closedBox ∩ l[i + 1].closedBox).Nonempty := by
    by_contra h
    exact hN.2 (Set.not_nonempty_iff_eq_empty.1 h ▸ Set.subsingleton_empty)
  have e1 : l.getD i root = l[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have e2 : l.getD (i + 1) root = l[i + 1] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [e1, e2]
  exact ⟨l53_side_ratio_of_meet hQ (List.getElem_mem _) (List.getElem_mem _) hne,
    l53_side_ratio_of_meet hQ (List.getElem_mem _) (List.getElem_mem _)
      (by rw [inter_comm]; exact hne)⟩

/-! ### G-G1: the sub-box neighbourhoods lie in `𝕍̃_{u,v}` -/

/-- **The `|u−v|/3`-thickening of `⋃_{i=1}^9 𝕍̃_{w_{i−1},w_i}` lies in `𝕍̃_{u,v}`**: in the frame
of `v − u`, `𝕍̃_{w_{i−1},w_i}` lies within `5|u−v|/9` of the midpoint along `v − u` and within
`|u−v|/9` across. -/
lemma l53_thickening_region_sub_tildeBox {u v : ℂ} {r : ℝ} (hr : r ≤ ‖v - u‖ / 3) :
    thickening r (l53Region u v) ⊆ tildeBox u v := by
  intro z hz
  obtain ⟨p, hp, hzp⟩ := mem_thickening_iff.1 hz
  obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.1 hp
  obtain ⟨hi1, hi9⟩ := Finset.mem_Icc.1 hi
  set d : ℂ := v - u with hd
  set D : ℝ := ‖d‖ ^ 2 with hD
  have hdn : 0 ≤ ‖d‖ := norm_nonneg _
  have hcast : ((i - 1 : ℕ) : ℂ) = (i : ℂ) - 1 := by
    rw [Nat.cast_sub hi1]; simp
  have hww : l53W u v i - l53W u v (i - 1) = d / 9 := by
    simp only [l53W, hcast, hd]; ring
  have hmid : (l53W u v (i - 1) + l53W u v i) / 2 = u + ((2 * (i : ℂ) - 1) / 18) * d := by
    simp only [l53W, hcast, hd]; ring
  have hdd : d * starRingEnd ℂ d = ((‖d‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- the membership of `p` in `𝕍̃_{w_{i−1},w_i}`
  obtain ⟨hp1, hp2⟩ := hpi
  rw [hww, hmid] at hp1 hp2
  set Y : ℂ := (p - (u + ((2 * (i : ℂ) - 1) / 18) * d)) * starRingEnd ℂ d with hY
  have eY : (p - (u + ((2 * (i : ℂ) - 1) / 18) * d)) * starRingEnd ℂ (d / 9) = Y / 9 := by
    rw [hY, map_div₀, map_ofNat]; ring
  have en : ‖d / 9‖ ^ 2 = D / 81 := by
    rw [norm_div, hD, div_pow]; norm_num
  rw [eY, en] at hp1 hp2
  rw [Complex.div_ofNat_re, abs_div] at hp1
  rw [Complex.div_ofNat_im, abs_div] at hp2
  norm_num at hp1 hp2
  have hY1 : |Y.re| ≤ D / 9 := by linarith
  have hY2 : |Y.im| ≤ D / 9 := by linarith
  -- the shift `z − p`
  set X : ℂ := (z - p) * starRingEnd ℂ d with hX
  have hXn : ‖X‖ ≤ D / 3 := by
    rw [hX, norm_mul, Complex.norm_conj, hD]
    have : ‖z - p‖ ≤ r := by rw [← dist_eq_norm]; exact hzp.le
    have := mul_le_mul_of_nonneg_right (this.trans hr) hdn
    nlinarith
  have hX1 := (Complex.abs_re_le_norm X).trans hXn
  have hX2 := (Complex.abs_im_le_norm X).trans hXn
  -- the decomposition
  have he : (z - (u + v) / 2) * starRingEnd ℂ d =
      X + Y + ((((i : ℝ) - 5) / 9 * D : ℝ) : ℂ) := by
    have : v = u + d := by rw [hd]; ring
    have hdd' : ((‖d‖ : ℂ)) ^ 2 = d * starRingEnd ℂ d := by rw [hdd]; push_cast; ring
    rw [hX, hY, hD]
    push_cast
    rw [hdd', this]
    ring
  have hi5 : |((i : ℝ) - 5) / 9 * D| ≤ 4 * D / 9 := by
    have h1 : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    have h9 : (i : ℝ) ≤ 9 := by exact_mod_cast hi9
    have hD0 : 0 ≤ D := by positivity
    rw [abs_le]; constructor <;> nlinarith
  have hD0 : 0 ≤ D := by positivity
  refine ⟨?_, ?_⟩
  · rw [he, Complex.add_re, Complex.add_re, Complex.ofReal_re]
    calc |X.re + Y.re + ((i : ℝ) - 5) / 9 * D| ≤ |X.re| + |Y.re| + |((i : ℝ) - 5) / 9 * D| := by
          linarith [abs_add_le (X.re + Y.re) (((i : ℝ) - 5) / 9 * D), abs_add_le X.re Y.re]
      _ ≤ ‖v - u‖ ^ 2 := by rw [← hd]; linarith
  · rw [he, Complex.add_im, Complex.add_im, Complex.ofReal_im, add_zero]
    calc |X.im + Y.im| ≤ |X.im| + |Y.im| := abs_add_le _ _
      _ ≤ ‖v - u‖ ^ 2 := by rw [← hd]; linarith

/-- **G-G1** (DEC-131-IF §3): for large `k`, every box of side `≤ δ_k^{C_Mc}` meeting the doubly
thickened region has `sqBox(c_b, 5 s_b) ⊆ 𝕍̃_{u,v}`. -/
theorem l53_sqBox_five_subset_tildeBox (γ : ℝ) {u v : ℂ} (huv : u ≠ v) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ b : DyBox, b.side ≤ ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ →
      b ∈ cellsMeeting (cthickening (2 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ)
        (cthickening (8 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) (l53Region u v))) →
      sqBox b.center (5 * b.side) ⊆ tildeBox u v := by
  have hd : 0 < ‖v - u‖ := norm_pos_iff.2 (sub_ne_zero.2 huv.symm)
  have ht : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).rpow_const_nhds_zero
      (dzzCMc_pos γ)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (ht.eventually (ge_mem_nhds
    (show (0 : ℝ) < ‖v - u‖ / 60 by positivity)))
  refine ⟨k₀, fun k hk b hb hmeet z hz => ?_⟩
  set e : ℝ := ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ with he
  have he0 : 0 < e := Real.rpow_pos_of_pos (by positivity) _
  have hek : e ≤ ‖v - u‖ / 60 := hk₀ k hk
  obtain ⟨p, hpb, hpR⟩ := hmeet
  have hpR' : p ∈ thickening (11 * e) (l53Region u v) := by
    have h1 := cthickening_cthickening_subset (by positivity : (0 : ℝ) ≤ 2 * e)
      (by positivity : (0 : ℝ) ≤ 8 * e) (l53Region u v) hpR
    exact cthickening_subset_thickening' (by positivity) (by linarith) _ h1
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.1 hpR'
  have hs := side_pos' b
  have hzc : ‖z - b.center‖ ≤ 5 * b.side := by
    obtain ⟨z1, z2⟩ := hz
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im]; linarith
  have hpc : ‖p - b.center‖ ≤ b.side := by
    obtain ⟨a1, a2, a3, a4⟩ := hpb
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im]
    simp only [DyBox.center]
    have h1 : |p.re - (b.j + 1 / 2) * b.side| ≤ b.side / 2 := by
      rw [abs_le]; constructor <;> nlinarith
    have h2 : |p.im - (b.k + 1 / 2) * b.side| ≤ b.side / 2 := by
      rw [abs_le]; constructor <;> nlinarith
    linarith
  refine l53_thickening_region_sub_tildeBox (r := 17 * e) (by linarith) ?_
  refine mem_thickening_iff.2 ⟨q, hq, ?_⟩
  rw [dist_eq_norm] at hpq ⊢
  calc ‖z - q‖ = ‖(z - b.center) - (p - b.center) + (p - q)‖ := by ring_nf
    _ ≤ ‖z - b.center‖ + ‖p - b.center‖ + ‖p - q‖ := by
        linarith [norm_add_le ((z - b.center) - (p - b.center)) (p - q),
          norm_sub_le (z - b.center) (p - b.center)]
    _ < 17 * e := by linarith

/-- The balls inside `𝕍̃_{u,v}` lie in `𝕍°` (`u ≠ v ∈ 𝕍̄`; via `tildeBox_subset_dzzVXi`). -/
lemma l53_sub_openSquare_of_tildeBox {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar)
    (huv : u ≠ v) {S : Set ℂ} (hS : S ⊆ tildeBox u v) : S ⊆ openSquare := fun z hz =>
  ball_subset_openSquare_of_dzzVXi (tildeBox_subset_dzzVXi hu hv huv (hS hz))
    (mem_ball_self (by norm_num))

end DZZ
end LQGMetric
