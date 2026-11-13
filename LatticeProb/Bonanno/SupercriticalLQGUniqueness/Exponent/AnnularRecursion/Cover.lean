/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Cover at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Families




 
















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal Convex

namespace SupercriticalLQGUniqueness.Exponent.AnnularRecursion

open LQGMetric LQGMetric.LFPP

 
def tileUniv (m : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(2 : ℤ) ^ m - 2) (2 * 2 ^ m + 2) ×ˢ Finset.Icc (-(2 : ℤ) ^ m - 2) (2 * 2 ^ m + 2)

 
def segSum (a : ℝ) (G : Exponent.PolygonalCost.RatPolygonFamily) (ij : ℤ × ℤ) : ℝ≥0∞ :=
  ∑ e ∈ famEdges G, segLen (block a ij) (famA G e) (famB G e)

open Classical in
 
def longTiles (m : ℕ) (G : Exponent.PolygonalCost.RatPolygonFamily) : Finset (ℤ × ℤ) :=
  (tileUniv m).filter fun ij => ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) ≤ segSum (((2 : ℝ) ^ m)⁻¹) G ij

theorem longTiles_subset (m : ℕ) (G : Exponent.PolygonalCost.RatPolygonFamily) : longTiles m G ⊆ tileUniv m :=
  Finset.filter_subset _ _

private theorem index_cover {a : ℝ} (ha : 0 < a) (m : ℕ) (hm : a = ((2 : ℝ) ^ m)⁻¹) {x : ℝ}
    (h0 : -1 ≤ x) (h1 : x ≤ 2) :
    ⌊x / a⌋ ∈ Finset.Icc (-(2 : ℤ) ^ m - 2) (2 * 2 ^ m + 2) ∧
      (⌊x / a⌋ : ℝ) * a ≤ x ∧ x ≤ ((⌊x / a⌋ : ℝ) + 1) * a := by
  have hxa : x / a = x * 2 ^ m := by rw [hm, div_inv_eq_mul]
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  refine ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, ?_, ?_⟩
  · have : (-(2 : ℝ) ^ m - 2 : ℝ) ≤ x / a := by rw [hxa]; nlinarith
    have h := Int.le_floor.2 (show ((-(2 : ℤ) ^ m - 2 : ℤ) : ℝ) ≤ x / a by push_cast; exact this)
    exact h
  · have : x / a ≤ (2 * 2 ^ m + 2 : ℝ) := by rw [hxa]; nlinarith
    have h := Int.floor_le (x / a)
    have h' : (⌊x / a⌋ : ℝ) ≤ ((2 * 2 ^ m + 2 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h'
  · have := Int.floor_le (x / a)
    rw [le_div_iff₀ ha] at this; exact this
  · have := Int.lt_floor_add_one (x / a)
    rw [div_lt_iff₀ ha] at this; linarith

 
theorem tileUniv_cover (m : ℕ) {z : ℂ} (hre : z.re ∈ Icc (-1 : ℝ) 2) (him : z.im ∈ Icc (-1 : ℝ) 2) :
    ∃ ij ∈ tileUniv m, z ∈ tile (((2 : ℝ) ^ m)⁻¹) ij := by
  have ha : (0 : ℝ) < ((2 : ℝ) ^ m)⁻¹ := by positivity
  obtain ⟨hi, hi1, hi2⟩ := index_cover ha m rfl hre.1 hre.2
  obtain ⟨hj, hj1, hj2⟩ := index_cover ha m rfl him.1 him.2
  exact ⟨(⌊z.re / ((2 : ℝ) ^ m)⁻¹⌋, ⌊z.im / ((2 : ℝ) ^ m)⁻¹⌋), Finset.mem_product.2 ⟨hi, hj⟩,
    ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩⟩

theorem tile_subset_block {a : ℝ} (ha : 0 ≤ a) (ij : ℤ × ℤ) : tile a ij ⊆ block a ij := by
  rintro z ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

 
theorem block_subset_of_cleared {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 256) (ij : ℤ × ℤ)
    {w : ℂ} (hw : w ∈ block a ij) (hwc : w ∈ Exponent.InwardMap.clearedSquareAnnulus a) :
    block a ij ⊆ Exponent.PolygonalCost.openSquareAnnulus ∧ block a ij ⊆ Exponent.InwardMap.gradientBox := by
  obtain ⟨⟨w1, w2⟩, ⟨w3, w4⟩⟩ := hw
  simp only [Exponent.InwardMap.clearedSquareAnnulus, mem_sdiff, Complex.mem_reProdIm, mem_Icc, mem_Ioo,
    not_and_or, not_lt] at hwc
  obtain ⟨⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩, hout⟩ := hwc
  constructor
  · rintro z ⟨⟨z1, z2⟩, ⟨z3, z4⟩⟩
    simp only [Exponent.PolygonalCost.openSquareAnnulus, Exponent.PaidDuality.outerOpenSquare, Exponent.PaidDuality.innerSquare, mem_sdiff,
      Complex.mem_reProdIm, mem_Ioo, mem_Icc, not_and_or, not_le]
    refine ⟨⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩, ?_⟩
    rcases hout with (h | h) | (h | h)
    · left; left; nlinarith
    · left; right; nlinarith
    · right; left; nlinarith
    · right; right; nlinarith
  · rintro z ⟨⟨z1, z2⟩, ⟨z3, z4⟩⟩
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

theorem openSquareAnnulus_disjoint_inner :
    Disjoint Exponent.PolygonalCost.openSquareAnnulus Exponent.PaidDuality.innerSquare := by
  rw [Set.disjoint_left]
  rintro z ⟨-, h⟩ h'
  exact h h'

theorem openSquareAnnulus_disjoint_outer_compl :
    Disjoint Exponent.PolygonalCost.openSquareAnnulus Exponent.PaidDuality.outerOpenSquareᶜ := by
  rw [Set.disjoint_left]
  rintro z ⟨h, -⟩ h'
  exact h' h

 
theorem nonempty_of_disconnects {L : Finset (ℤ × ℤ)} {a : ℝ}
    (h : LQGMetric.Disconnects (⋃ ij ∈ L, tile a ij) Exponent.PaidDuality.innerSquare Exponent.PaidDuality.outerOpenSquareᶜ) :
    L.Nonempty := by
  obtain ⟨γ⟩ : Joined (0 : ℂ) 3 := PathConnectedSpace.joined _ _
  have h0 : (0 : ℂ) ∈ Exponent.PaidDuality.innerSquare := by
    simp [Exponent.PaidDuality.innerSquare, Complex.mem_reProdIm]
  have h3 : (3 : ℂ) ∈ Exponent.PaidDuality.outerOpenSquareᶜ := by
    simp only [Exponent.PaidDuality.outerOpenSquare, mem_compl_iff, Complex.mem_reProdIm, mem_Ioo, not_and_or]
    left; right; norm_num
  obtain ⟨z, -, hz⟩ := h 0 3 γ h0 h3
  obtain ⟨ij, hij, -⟩ := mem_iUnion₂.1 hz
  exact ⟨ij, hij⟩

 

variable (m : ℕ) (G : Exponent.PolygonalCost.RatPolygonFamily)

 
theorem longTiles_disconnects (hm : 8 ≤ m)
    (hcl : G.trace ⊆ Exponent.InwardMap.clearedSquareAnnulus (((2 : ℝ) ^ m)⁻¹))
    (hsep : LQGMetric.Disconnects G.trace Exponent.PaidDuality.innerSquare Exponent.PaidDuality.outerOpenSquareᶜ) :
    LQGMetric.Disconnects (⋃ ij ∈ longTiles m G, tile (((2 : ℝ) ^ m)⁻¹) ij)
      Exponent.PaidDuality.innerSquare Exponent.PaidDuality.outerOpenSquareᶜ := by
  classical
  set a : ℝ := ((2 : ℝ) ^ m)⁻¹ with ha_def
  have ha : 0 < a := by positivity
  have ha1 : a ≤ 1 / 256 := by
    rw [ha_def, one_div]
    exact inv_anti₀ (by norm_num) (by
      calc (256 : ℝ) = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm)
  have hdata : ∀ ij : ℤ × ℤ, ∃ c₁ c₂ d₁ d₂ : ℝ, ij ∈ tileUniv m → ij ∉ longTiles m G →
      (tile a ij ∩ G.trace).Nonempty →
      c₁ ≤ c₂ ∧ d₁ ≤ d₂ ∧ tile a ij ⊆ rectC c₁ c₂ d₁ d₂ ∧
        Disjoint (rectSides c₁ c₂ d₁ d₂) G.trace ∧
        Disjoint (rectC c₁ c₂ d₁ d₂) Exponent.PaidDuality.innerSquare ∧
        Disjoint (rectC c₁ c₂ d₁ d₂) Exponent.PaidDuality.outerOpenSquareᶜ := by
    intro ij
    by_cases hc : ij ∈ tileUniv m ∧ ij ∉ longTiles m G ∧ (tile a ij ∩ G.trace).Nonempty
    · obtain ⟨hu, hl, ⟨w, hwT, hwG⟩⟩ := hc
      have hshort : ∑ e ∈ famEdges G, segLen (block a ij) (famA G e) (famB G e) <
          ENNReal.ofReal a := by
        by_contra hge
        apply hl
        rw [longTiles, Finset.mem_filter]
        exact ⟨hu, not_lt.1 hge⟩
      obtain ⟨c₁, c₂, d₁, d₂, hc₁, hc₂, hd₁, hd₂, hdis⟩ :=
        short_block_loop ha ij (famEdges G) (famA G) (famB G) hshort
      have hBA := (block_subset_of_cleared ha ha1 ij (tile_subset_block ha.le ij hwT)
        (hcl hwG)).1
      have hRB : rectC c₁ c₂ d₁ d₂ ⊆ block a ij := by
        rintro z ⟨⟨z1, z2⟩, ⟨z3, z4⟩⟩
        exact ⟨⟨by linarith [hc₁.1], by linarith [hc₂.2]⟩,
          ⟨by linarith [hd₁.1], by linarith [hd₂.2]⟩⟩
      refine ⟨c₁, c₂, d₁, d₂, fun _ _ _ => ⟨by nlinarith [hc₁.2, hc₂.1],
        by nlinarith [hd₁.2, hd₂.1], ?_, ?_, ?_, ?_⟩⟩
      · rintro z ⟨⟨z1, z2⟩, ⟨z3, z4⟩⟩
        exact ⟨⟨by linarith [hc₁.2], by linarith [hc₂.1]⟩,
          ⟨by linarith [hd₁.2], by linarith [hd₂.1]⟩⟩
      · rw [famTrace_eq_segments]; exact hdis
      · exact Disjoint.mono_left (hRB.trans hBA) openSquareAnnulus_disjoint_inner
      · exact Disjoint.mono_left (hRB.trans hBA) openSquareAnnulus_disjoint_outer_compl
    · exact ⟨0, 0, 0, 0, fun hu hl hne => absurd ⟨hu, hl, hne⟩ hc⟩
  choose c₁ c₂ d₁ d₂ hc using hdata
  refine disconnects_of_short_loops hsep (tileUniv m) (longTiles m G) (tile a) ?_
    c₁ c₂ d₁ d₂ fun ij hu hl hne => hc ij hu hl hne
  intro z hz
  have hzc := hcl hz
  simp only [Exponent.InwardMap.clearedSquareAnnulus, mem_sdiff, Complex.mem_reProdIm, mem_Icc] at hzc
  obtain ⟨⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩, -⟩ := hzc
  obtain ⟨ij, hij, hzt⟩ := tileUniv_cover m (z := z) ⟨by linarith, by linarith⟩
    ⟨by linarith, by linarith⟩
  exact mem_iUnion₂.2 ⟨ij, hij, hzt⟩

 
theorem longTiles_block_subset (hm : 8 ≤ m)
    (hcl : G.trace ⊆ Exponent.InwardMap.clearedSquareAnnulus (((2 : ℝ) ^ m)⁻¹)) {ij : ℤ × ℤ}
    (hij : ij ∈ longTiles m G) :
    block (((2 : ℝ) ^ m)⁻¹) ij ⊆ Exponent.PolygonalCost.openSquareAnnulus ∧
      block (((2 : ℝ) ^ m)⁻¹) ij ⊆ Exponent.InwardMap.gradientBox := by
  set a : ℝ := ((2 : ℝ) ^ m)⁻¹ with ha_def
  have ha : 0 < a := by positivity
  have ha1 : a ≤ 1 / 256 := by
    rw [ha_def, one_div]
    exact inv_anti₀ (by norm_num) (by
      calc (256 : ℝ) = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm)
  rw [longTiles, Finset.mem_filter] at hij
  have hpos : segSum a G ij ≠ 0 := by
    intro h0
    have := hij.2
    rw [h0] at this
    exact (not_le.2 (ENNReal.ofReal_pos.2 ha)) this
  obtain ⟨e, he_mem, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
  obtain ⟨t, ht, hB⟩ := exists_mem_of_segLen_ne_zero he
  have hG : segPath (famA G e) (famB G e) t ∈ G.trace := by
    rw [famTrace_eq_segments]
    refine mem_iUnion₂.2 ⟨e, he_mem, ?_⟩
    rw [← Exponent.PaidDuality.segPath_trace]; exact ⟨t, ht, rfl⟩
  exact block_subset_of_cleared ha ha1 ij hB (hcl hG)

 
theorem longTiles_count {ξ : ℝ} (hξ : 0 ≤ ξ) {φ : ℂ → ℝ} (hφ : Continuous φ)
    (mlow : ℤ × ℤ → ℝ)
    (hmlow : ∀ ij ∈ longTiles m G, ∀ z ∈ block (((2 : ℝ) ^ m)⁻¹) ij, mlow ij ≤ φ z) :
    ∑ ij ∈ longTiles m G, ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) *
      ENNReal.ofReal (Real.exp (ξ * mlow ij)) ≤ 16 * G.cost ξ φ := by
  set a : ℝ := ((2 : ℝ) ^ m)⁻¹ with ha_def
  have ha : 0 < a := by positivity
  have hstep : ∀ ij ∈ longTiles m G, ENNReal.ofReal a * ENNReal.ofReal (Real.exp (ξ * mlow ij)) ≤
      ∑ e ∈ famEdges G, segCostIn ξ φ (block a ij) (famA G e) (famB G e) := by
    intro ij hij
    have hlong := (Finset.mem_filter.1 hij).2
    calc ENNReal.ofReal a * ENNReal.ofReal (Real.exp (ξ * mlow ij)) ≤
        segSum a G ij * ENNReal.ofReal (Real.exp (ξ * mlow ij)) :=
          mul_le_mul_of_nonneg_right hlong bot_le
      _ = ∑ e ∈ famEdges G, ENNReal.ofReal (Real.exp (ξ * mlow ij)) *
          segLen (block a ij) (famA G e) (famB G e) := by
          rw [segSum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun e _ => mul_comm _ _
      _ ≤ _ := Finset.sum_le_sum fun e _ =>
          segLen_le_segCostIn hξ (hmlow ij hij) _ _
  calc ∑ ij ∈ longTiles m G, ENNReal.ofReal a * ENNReal.ofReal (Real.exp (ξ * mlow ij)) ≤
      ∑ ij ∈ longTiles m G, ∑ e ∈ famEdges G,
        segCostIn ξ φ (block a ij) (famA G e) (famB G e) := Finset.sum_le_sum hstep
    _ = ∑ e ∈ famEdges G, ∑ ij ∈ longTiles m G,
        segCostIn ξ φ (block a ij) (famA G e) (famB G e) := Finset.sum_comm
    _ ≤ ∑ e ∈ famEdges G, 16 * segCost ξ φ (famA G e) (famB G e) :=
        Finset.sum_le_sum fun e _ => sum_segCostIn_block_le ha _ ξ hφ _ _
    _ = 16 * G.cost ξ φ := by rw [← Finset.mul_sum, famCost_eq_segments]



end SupercriticalLQGUniqueness.Exponent.AnnularRecursion
