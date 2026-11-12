/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54F1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54C
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls2

/-!
# DZZ Lemma 5.4, lower half, from the corrected point-to-segment bound (P2-DZZ61K, D117 P-54U)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 5.4, union bound
l. 2571–2578: "`∂𝕍̄_u` is the union of `≈ δ^{−2ι}` segments … by Proposition 3.17 … with
probability `1 − δ^{cι}` … `E log min ≥ (χ − 2ι − Cι^{1/2}) log δ⁻¹`."

Changes of DEC-117 §2(a) (DV-D117 items 1, 2), with the corrected `DZZLem54SegQ` (S5D117):
* segments of length `δ^{Kι}` (`Kχ ≥ 2`), so `≈ 4·20⁻¹ δ^{−Kι}` of them;
* deviation `ι' = (2K/c)^{1/2} ι^{1/2}` (DZZ's `Cι^{1/2}`), so that `c ι'² = 2Kι > Kι`;
* the segment quantity is `Q(u,L) = min_{x ∈ L} D^{legWall u λ L}_δ(u,x)`; on the big-balls event
  (`DZZBigBalls`, radius `λ/4 = 1/80`, DZZ l. 2562) the truncation of a `D̄^{u,2λ}`-geodesic at its
  first ball meeting `∂𝕍_{u,λ}` gives `min_{∂𝕍_{u,λ}} D̄^{u,2λ}(u,·) ≥ min_L Q(u,L)`
  (`DZZLegTrunc`, deterministic; proved in S5L54F3, `dzzLegTrunc_of_mem`).

The concentration of `Q(u,L)` (DZZ Proposition 3.17 at the walled measures of Remark 5.2, wall
`legWall u λ L`, with a constant uniform in the segment) is the exact hypothesis
`DZZProp317Leg`. DZZ apply Proposition 3.17 to `D̄^{u,2λ}(u, L_δ)` (one wall); with the corrected
leg the wall depends on the segment (DEC-117 §2(a)(ii)), so the uniformity in `L` must be part of
the statement.

* `dzzLem54_lowerQ`: `liminf E log min_{∂𝕍_{u,1/20}} D̄^{u,1/10}_δ(u,·) / log δ⁻¹ ≥ χ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The concentration event (eq-concentration-1) at `ι` for
`Q(u,L) = min_{x ∈ L} D^{legWall}_δ(u,x)`. -/
def legConc (P : Measure Ω) (μ : Ω → Measure ℂ) (u : ℂ) (δ ι : ℝ) (L : Set ℂ) : Set Ω :=
  conc1Event (fun ω => dzzWall (legWall u (1 / 20) L) (μ ω)) P δ ι {u} L

/-- **DZZ Proposition 3.17 (eq-concentration-1) for the leg walls** (DZZ Remark 5.2, wall
`legWall u λ L_δ` moving with the segment `L_δ ⊆ ∂𝕍_{u,λ}`), with a constant `c` uniform in the
family of segments. -/
def DZZProp317Leg (P : Measure Ω) (μ : Ω → Measure ℂ) (ξ : ℝ) (u : ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ → Set ℂ,
    (∀ δ ∈ Ioo (0 : ℝ) 1, L δ ⊆ frontier (sqBox u (1 / 20)) ∧ IsXiAdmissibleSet ξ δ (L δ)) →
    ∀ ι ∈ Ioo (0 : ℝ) 1, AlphaHighProb P (c * ι ^ 2) fun δ => legConc P μ u δ ι (L δ)

/-- **Truncation at the first ball meeting `∂𝕍_{u,λ}`** (DEC-117 §2(a)(ii), P-BIG; DZZ l. 2562
and (eq-geodesic-range) l. 2340–2345): if every ball of radius `≥ λ/4 = 1/80` inside `𝕍` has mass
`> 2δ²`, then for every cover of `∂𝕍_{u,λ}` by subsets `S i`,
`min_i min_{x ∈ S i} D^{legWall u λ (S i)}_δ(u,x) ≤ min_{x ∈ ∂𝕍_{u,λ}} D̄^{u,2λ}_δ(u,x)`. -/
def DZZLegTrunc (u : ℂ) : Prop :=
  ∀ (ν : Measure ℂ) (δ : ℝ), (∀ (x : ℂ) (ρ : ℝ), 1 / 80 ≤ ρ → Metric.ball x ρ ⊆ dzzV →
      ENNReal.ofReal (2 * δ ^ 2) < ν (Metric.ball x ρ)) →
    ∀ {I : Type} (S : I → Set ℂ), (∀ i, S i ⊆ frontier (sqBox u (1 / 20))) →
      frontier (sqBox u (1 / 20)) ⊆ ⋃ i, S i →
      ∃ i, lgdMinSet (dzzWall (legWall u (1 / 20) (S i)) ν) δ {u} (S i) ≤
        lgdMinSet (dzzWall (sqBox u (1 / 10)) ν) δ {u} (frontier (sqBox u (1 / 20)))

lemma logMinLGD_le_of_lgdMinSet_le {μ₁ μ₂ : Measure ℂ} {δ : ℝ} {A₁ B₁ A₂ B₂ : Set ℂ}
    (hle : lgdMinSet μ₁ δ A₁ B₁ ≤ lgdMinSet μ₂ δ A₂ B₂) (hfin : lgdMinSet μ₂ δ A₂ B₂ < ⊤) :
    logMinLGD μ₁ δ A₁ B₁ ≤ logMinLGD μ₂ δ A₂ B₂ := by
  have h1 := one_le_lgdMinSet μ₁ δ A₁ B₁
  have hne : lgdMinSet μ₁ δ A₁ B₁ ≠ ⊤ := (hle.trans_lt hfin).ne
  have hm := ENat.toNat_le_toNat hle hfin.ne
  have hpos : (0 : ℝ) < (lgdMinSet μ₁ δ A₁ B₁).toNat := by
    have : 1 ≤ (lgdMinSet μ₁ δ A₁ B₁).toNat := by
      rw [← ENat.natCast_le_natCast, ENat.natCast_toNat hne]; exact_mod_cast h1
    exact_mod_cast this
  exact Real.log_le_log hpos (by exact_mod_cast hm)

lemma l54Piece_isBdrySeg (u : ℂ) {h ℓ : ℝ} (hh : 0 ≤ h) (σ : ℕ) {k : ℕ}
    (hk : ((k : ℝ) + 1) * h ≤ 1 / 20) (h1 : ℓ / 2 ≤ h) (h2 : h ≤ ℓ) :
    IsBdrySeg u (1 / 20) ℓ (l54Piece u h σ k) := by
  refine ⟨l54Piece_subset_frontier u hh σ hk, ?_⟩
  obtain ⟨a, c, hac⟩ := l54Piece_seg u h σ k
  exact ⟨a, a + h, c, hac, by linarith, by linarith⟩

/-- **DZZ Lemma 5.4, lower half** (DZZ l. 2571–2578, corrected as in DEC-117 §2(a)): from the
point-to-segment bound `DZZLem54SegQ`, Proposition 3.17 for `D̄^{u,2λ}(u, ∂𝕍_{u,λ})`, the
concentration of the leg quantities (`DZZProp317Leg`), the big balls (`DZZBigBalls`, P-BIG), the
truncation (`DZZLegTrunc`, P-BIG) and a.s. finiteness of `D̃(u, l54Pt u)`. -/
theorem dzzLem54_lowerQ {P : Measure Ω} [IsProbabilityMeasure P] {μ : Ω → Measure ℂ}
    {χ ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 40) {u : ℂ} (hu : u ∈ dzzVbar)
    (h317 : DZZProp317In P (fun ω => dzzWall (sqBox u (1 / 10)) (μ ω)) (sqBox u (1 / 10)) ξ)
    (h317Q : DZZProp317Leg P μ ξ u) (hbig : DZZBigBalls P μ (1 / 80)) (htr : DZZLegTrunc u)
    (hfin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P,
      lgdDZZ (dzzWall (tildeBox u (l54Pt u)) (μ ω)) δ u (l54Pt u) < ⊤)
    (hseg : DZZLem54SegQ P μ χ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), χ - ε < (∫ ω, logMinLGD (dzzWall (sqBox u (1 / 10)) (μ ω)) δ {u}
      (frontier (sqBox u (1 / 20))) ∂P) / Real.log δ⁻¹ := by
  classical
  obtain ⟨c, hc, hP⟩ := h317
  obtain ⟨cQ, hcQ, hPQ⟩ := h317Q
  obtain ⟨ι₀, K, hι₀, hK, -, hsegu⟩ := hseg u hu
  -- the segment exponent `ι`, `κ = Kι`, and the deviation `ι' = (2κ/c_Q)^{1/2}` (DZZ's `Cι^{1/2}`)
  set m : ℝ := min (ε / 4) (1 / 2) with hmdef
  have hm0 : 0 < m := lt_min (by linarith) (by norm_num)
  set ι : ℝ := min (min (ι₀ / 2) (ε / 8)) (min (ξ / (4 * K)) (cQ * m ^ 2 / (2 * K))) with hιdef
  have hι0 : 0 < ι := lt_min (lt_min (by linarith) (by linarith))
    (lt_min (by positivity) (by positivity))
  have hι₀' : ι < ι₀ := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hιε : ι ≤ ε / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have hιξ : ι * (4 * K) ≤ ξ :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hιm : ι * (2 * K) ≤ cQ * m ^ 2 :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  set κ : ℝ := K * ι with hκdef
  have hκ0 : 0 < κ := by positivity
  have hκξ : κ ≤ ξ / 4 := by rw [hκdef]; nlinarith
  set ι' : ℝ := Real.sqrt (2 * κ / cQ) with hι'def
  have hι'sq : cQ * ι' ^ 2 = 2 * κ := by
    rw [hι'def, Real.sq_sqrt (by positivity)]; field_simp
  have hι'0 : 0 < ι' := Real.sqrt_pos.mpr (by positivity)
  have hι'm : ι' ≤ m := by
    rw [hι'def, show m = Real.sqrt (m ^ 2) from (Real.sqrt_sq hm0.le).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ hcQ]; nlinarith
  have hι'1 : ι' < 1 := hι'm.trans_lt ((min_le_right _ _).trans_lt (by norm_num))
  have hι'ε : ι' ≤ ε / 4 := hι'm.trans (min_le_left _ _)
  -- small-`δ` facts, on an interval `(0, δ₁)`
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo (0 : ℝ) 1 ∧ δ ^ (2 * (κ / 2)) < 1 / 20 ∧
      δ ^ (ξ - 2 * (κ / 2)) < 1 / 2 ∧ δ ^ (cQ * ι' ^ 2 - κ) < 1 / 4 ∧ δ ^ (c * ι' ^ 2) < 1 / 4 :=
    (show ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhdsGT one_pos).and
      ((eventually_rpow_lt (by linarith) (by norm_num)).and
      ((eventually_rpow_lt (by linarith) (by norm_num)).and
        ((eventually_rpow_lt (by rw [hι'sq]; linarith) (by norm_num)).and
          (eventually_rpow_lt (by positivity) (by norm_num)))))
  obtain ⟨δ₁, hδ₁, hδ₁s⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  have hδ₁0 : (0 : ℝ) < δ₁ := hδ₁
  have h2κ : 2 * (κ / 2) = κ := by ring
  set N : ℝ → ℕ := fun δ => ⌈1 / 20 * (δ ^ κ)⁻¹⌉₊ with hNdef
  have hcnt : ∀ δ ∈ Ioo (0 : ℝ) δ₁, 1 ≤ N δ ∧ δ ^ κ / 2 ≤ 1 / 20 / N δ ∧
      1 / 20 / N δ ≤ δ ^ κ ∧ (4 * N δ : ℝ) ≤ (δ ^ κ)⁻¹ ∧ δ ^ ξ ≤ 1 / 20 / N δ := fun δ hδ => by
    have := l54_count (n := N δ) hδ.1 (hδ₁s hδ).2.1 (hδ₁s hδ).2.2.1 (by rw [h2κ])
    rwa [h2κ] at this
  set Sq : ℝ → ℕ × ℕ → Set ℂ := fun δ q => l54Piece u (1 / 20 / N δ) q.1 q.2 with hSqdef
  -- the worst segment at each scale
  have hex : ∀ δ : ℝ, ∃ q : ℕ × ℕ, δ ∈ Ioo (0 : ℝ) δ₁ →
      q ∈ Finset.range 4 ×ˢ Finset.range (N δ) ∧
      ∀ q' ∈ Finset.range 4 ×ˢ Finset.range (N δ),
        P (legConc P μ u δ ι' (Sq δ q'))ᶜ ≤ P (legConc P μ u δ ι' (Sq δ q))ᶜ := by
    intro δ
    by_cases hδ : δ ∈ Ioo (0 : ℝ) δ₁
    · have hne : (Finset.range 4 ×ˢ Finset.range (N δ)).Nonempty :=
        ⟨(0, 0), Finset.mem_product.mpr ⟨by simp, by
          have := (hcnt δ hδ).1; simp only [Finset.mem_range]; omega⟩⟩
      obtain ⟨q, hq, hmax⟩ := (Finset.range 4 ×ˢ Finset.range (N δ)).exists_max_image
        (fun q' => P (legConc P μ u δ ι' (Sq δ q'))ᶜ) hne
      exact ⟨q, fun _ => ⟨hq, hmax⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hδ⟩
  choose idx hidx using hex
  have hpiece : ∀ δ ∈ Ioo (0 : ℝ) δ₁, ∀ q ∈ Finset.range 4 ×ˢ Finset.range (N δ),
      IsBdrySeg u (1 / 20) (δ ^ κ) (Sq δ q) ∧ IsXiAdmissibleSet ξ δ (Sq δ q) := by
    intro δ hδ q hq
    have hk := succ_mul_div_le (Finset.mem_range.mp (Finset.mem_product.mp hq).2)
    have hh : (0 : ℝ) ≤ 1 / 20 / N δ := by positivity
    exact ⟨l54Piece_isBdrySeg u hh q.1 hk (hcnt δ hδ).2.1 (hcnt δ hδ).2.2.1,
      Or.inr ⟨isConnected_l54Piece u hh q.1 q.2,
        (hcnt δ hδ).2.2.2.2.trans (le_diam_l54Piece u hh q.1 hk)⟩⟩
  -- concentration for the worst segments (`DZZProp317Leg`) and for `(u, ∂𝕍_{u,λ})`
  obtain ⟨δw, hδw, hw⟩ := hPQ (fun δ => if δ < δ₁ then Sq δ (idx δ) else {l54Pt u})
    (fun δ hδ => by
      split_ifs with h
      · have := hpiece δ ⟨hδ.1, h⟩ _ (hidx δ ⟨hδ.1, h⟩).1
        exact ⟨this.1.1, this.2⟩
      · exact ⟨singleton_subset_iff.mpr (l54Pt_mem_frontier u), Or.inl ⟨_, rfl⟩⟩)
    ι' ⟨hι'0, hι'1⟩
  have hadmF := l54_isXiAdmissible hξ hξ1 hu (fun _ => frontier (sqBox u (1 / 20)))
    (fun δ hδ hlt => ⟨le_rfl, Or.inr ⟨isConnected_frontier_sqBox u (by norm_num),
      ((hcnt δ ⟨hδ.1, hlt⟩).2.2.2.2.trans (div_le_self (by norm_num)
        (by exact_mod_cast (hcnt δ ⟨hδ.1, hlt⟩).1))).trans
        (side_le_diam_frontier_sqBox u (by norm_num))⟩⟩)
  obtain ⟨δf, hδf, hf⟩ := (hP _ _ hadmF (l54_pair_kXi hξ1 _ fun _ _ _ => subset_rfl)).1 ι'
    ⟨hι'0, hι'1⟩
  have hq4 : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 4) := ENNReal.ofReal_pos.mpr (by norm_num)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ₁0 (lt_min hδw hδf)),
    hsegu ι ⟨hι0, hι₀'⟩, hbig.eventually (gt_mem_nhds hq4), hfin] with δ hδ hsegδ hbigδ hfinδ
  have hδ0 : 0 < δ := hδ.1
  have hlt1 : δ < δ₁ := hδ.2.trans_le (min_le_left _ _)
  have hδI : δ ∈ Ioo (0 : ℝ) δ₁ := ⟨hδ0, hlt1⟩
  have hwδ := hw δ ⟨hδ0, hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hfδ := hf δ ⟨hδ0, hδ.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  simp only [if_pos hlt1] at hwδ hfδ
  obtain ⟨hn1, -, -, hcount, -⟩ := hcnt δ hδI
  obtain ⟨-, -, -, hsa, hsb⟩ := hδ₁s hδI
  have hL : 0 < Real.log δ⁻¹ := Real.log_pos ((one_lt_inv₀ hδ0).mpr (hδ₁s hδI).1.2)
  -- the bad event and its probability
  set S := Finset.range 4 ×ˢ Finset.range (N δ) with hS
  set Bbig : Set Ω := {ω | ¬ ∀ (x : ℂ) (ρ : ℝ), 1 / 80 ≤ ρ → Metric.ball x ρ ⊆ dzzV →
    ENNReal.ofReal (2 * δ ^ 2) < μ ω (Metric.ball x ρ)} with hBbig
  set Bfin : Set Ω := {ω | ¬ lgdDZZ (dzzWall (tildeBox u (l54Pt u)) (μ ω)) δ u (l54Pt u) < ⊤}
    with hBfin
  have hPfin : P Bfin = 0 := ae_iff.mp hfinδ
  set G : Set Ω := (⋃ q ∈ S, (legConc P μ u δ ι' (Sq δ q))ᶜ) ∪
    (conc1Event (fun ω => dzzWall (sqBox u (1 / 10)) (μ ω)) P δ ι' {u}
      (frontier (sqBox u (1 / 20))))ᶜ ∪ Bbig ∪ Bfin with hG
  have hGlt : P G < 1 := by
    have hcard : S.card = 4 * N δ := by rw [hS, Finset.card_product]; simp
    have hreal : (4 * N δ : ℝ) * δ ^ (cQ * ι' ^ 2) + δ ^ (c * ι' ^ 2) + 1 / 4 < 1 := by
      have hy0 : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ0 _
      have hsub : δ ^ (cQ * ι' ^ 2 - κ) = (δ ^ κ)⁻¹ * δ ^ (cQ * ι' ^ 2) := by
        rw [Real.rpow_sub hδ0, div_eq_inv_mul]
      have : (4 * N δ : ℝ) * δ ^ (cQ * ι' ^ 2) ≤ (δ ^ κ)⁻¹ * δ ^ (cQ * ι' ^ 2) :=
        mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hδ0.le _)
      linarith
    calc P G ≤ P (⋃ q ∈ S, (legConc P μ u δ ι' (Sq δ q))ᶜ) +
          ENNReal.ofReal (δ ^ (c * ι' ^ 2)) + ENNReal.ofReal (1 / 4) + 0 := by
          refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
            (add_le_add ((measure_union_le _ _).trans (add_le_add le_rfl hfδ)) hbigδ.le))
            hPfin.le)
      _ ≤ S.card • P (legConc P μ u δ ι' (Sq δ (idx δ)))ᶜ +
          ENNReal.ofReal (δ ^ (c * ι' ^ 2)) + ENNReal.ofReal (1 / 4) + 0 := by
          gcongr
          exact (measure_biUnion_finset_le _ _).trans
            (Finset.sum_le_card_nsmul _ _ _ fun q hq => (hidx δ hδI).2 q hq)
      _ ≤ (4 * N δ : ℕ) • ENNReal.ofReal (δ ^ (cQ * ι' ^ 2)) +
          ENNReal.ofReal (δ ^ (c * ι' ^ 2)) + ENNReal.ofReal (1 / 4) + 0 := by
          rw [hcard]; gcongr
      _ = ENNReal.ofReal ((4 * N δ : ℝ) * δ ^ (cQ * ι' ^ 2) + δ ^ (c * ι' ^ 2) + 1 / 4) := by
          rw [add_zero, ENNReal.ofReal_add (by positivity) (by norm_num),
            ENNReal.ofReal_add (by positivity) (Real.rpow_nonneg hδ0.le _),
            ENNReal.ofReal_mul (by positivity), nsmul_eq_mul]
          norm_cast
      _ < 1 := ENNReal.ofReal_lt_one.mpr hreal
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ G := by
    by_contra h
    push_neg at h
    rw [eq_univ_of_forall h, measure_univ] at hGlt
    exact lt_irrefl _ hGlt
  simp only [hG, mem_union, mem_iUnion, mem_compl_iff, not_or, not_exists, not_not] at hω
  obtain ⟨⟨⟨hωq, hωF⟩, hωbig⟩, hωfin⟩ := hω
  simp only [hBbig, hBfin, mem_setOf_eq, not_not] at hωbig hωfin
  -- the truncation: some segment `q` has `Q(u, S_q) ≤ min_{∂𝕍_{u,λ}} D̄^{u,2λ}(u,·)`
  obtain ⟨⟨q, hqS⟩, hq⟩ := htr (μ ω) δ hωbig (I := {q // q ∈ S}) (fun q => Sq δ q.1)
    (fun q => (hpiece δ hδI q.1 q.2).1.1) (fun z hz => by
      obtain ⟨σ, hσ, k, hk, hzk⟩ := exists_l54Piece_of_mem_frontier u hn1 hz
      exact mem_iUnion.mpr ⟨⟨(σ, k), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hσ, Finset.mem_range.mpr hk⟩⟩, hzk⟩)
  have hFfin : lgdMinSet (dzzWall (sqBox u (1 / 10)) (μ ω)) δ {u}
      (frontier (sqBox u (1 / 20))) < ⊤ := by
    refine lt_of_le_of_lt ?_ hωfin
    refine le_trans ?_ (lgdDZZ_mono_measure (dzzWall_anti (tildeBox_l54Pt_subset u) (μ ω)) δ u
      (l54Pt u))
    exact iInf₂_le_of_le u (mem_singleton u) (iInf₂_le (l54Pt u) (l54Pt_mem_frontier u))
  have hlogq := logMinLGD_le_of_lgdMinSet_le hq hFfin
  have hcq := hωq q hqS
  have hcF := hωF
  simp only [legConc, conc1Event, mem_setOf_eq, abs_le] at hcq hcF
  have hseq := hsegδ (Sq δ q) (hpiece δ hδI q hqS).1
  rw [lt_div_iff₀ hL]
  have : (χ - ε) * Real.log δ⁻¹ < (χ - 2 * ι - 2 * ι') * Real.log δ⁻¹ :=
    mul_lt_mul_of_pos_right (by linarith) hL
  linarith [hcq.1, hcq.2, hcF.1, hcF.2]

end DZZ
end LQGMetric
