/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordsAux1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan

/-!
# Records (node `R44`), auxiliary part 1: grids, polygons, local families

* square grids of side `s` (`gridIdx`, `gridPt`) and the count of grid points in a ball;
* polygons given by a vertex function `f : ℕ → ℂ` (the list `f 0, …, f m`): edges, length,
  normalized arclength average;
* membership of actual configurations in the similarity images of the normalized local
  families `smallFamily`, `largeFamily`;
* the vertex-deviation bound for polygons whose edges but the last have length `R / M`.
-/

noncomputable section

open Real
open scoped Classical ComplexConjugate

namespace LQGDimension.LFPPRecords

open Blueprint.Draft

/-! ## Square grids -/

/-- Index of the grid square of side `s` containing `z`. -/
def gridIdx (s : ℝ) (z : ℂ) : ℤ × ℤ := (⌊z.re / s⌋, ⌊z.im / s⌋)

/-- Lower-left corner of the grid square of side `s` with index `a`. -/
def gridPt (s : ℝ) (a : ℤ × ℤ) : ℂ := ⟨(a.1 : ℝ) * s, (a.2 : ℝ) * s⟩

theorem floor_mul_bounds {s : ℝ} (hs : 0 < s) (t : ℝ) :
    (⌊t / s⌋ : ℝ) * s ≤ t ∧ t < (⌊t / s⌋ : ℝ) * s + s := by
  have a1 := Int.floor_le (t / s)
  have a2 := Int.lt_floor_add_one (t / s)
  constructor
  · rwa [le_div_iff₀ hs] at a1
  · rw [div_lt_iff₀ hs] at a2; linarith

theorem abs_sub_floor_mul_le {s : ℝ} (hs : 0 < s) (t : ℝ) : |t - (⌊t / s⌋ : ℝ) * s| ≤ s := by
  obtain ⟨h1, h2⟩ := floor_mul_bounds hs t
  rw [abs_le]; constructor <;> linarith

theorem norm_sub_gridPt_le {s : ℝ} (hs : 0 < s) (z : ℂ) :
    ‖z - gridPt s (gridIdx s z)‖ ≤ 2 * s := by
  calc ‖z - gridPt s (gridIdx s z)‖
      ≤ |(z - gridPt s (gridIdx s z)).re| + |(z - gridPt s (gridIdx s z)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |z.re - (⌊z.re / s⌋ : ℝ) * s| + |z.im - (⌊z.im / s⌋ : ℝ) * s| := by
        simp [gridPt, gridIdx]
    _ ≤ s + s := add_le_add (abs_sub_floor_mul_le hs _) (abs_sub_floor_mul_le hs _)
    _ = 2 * s := by ring

theorem gridPt_injective {s : ℝ} (hs : s ≠ 0) : Function.Injective (gridPt s) := by
  intro a b h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [gridPt] at h1 h2
  have e1 : (a.1 : ℝ) = b.1 := mul_right_cancel₀ hs h1
  have e2 : (a.2 : ℝ) = b.2 := mul_right_cancel₀ hs h2
  exact Prod.ext (by exact_mod_cast e1) (by exact_mod_cast e2)

/-- Grid indices of points of norm `≤ ρ` lie in `[-B, B]` once `ρ / s + 1 ≤ B`. -/
theorem gridIdx_mem_Icc {s ρ : ℝ} (hs : 0 < s) {z : ℂ} (hz : ‖z‖ ≤ ρ) {B : ℤ}
    (hB : ρ / s + 1 ≤ B) :
    (gridIdx s z).1 ∈ Finset.Icc (-B) B ∧ (gridIdx s z).2 ∈ Finset.Icc (-B) B := by
  have key : ∀ t : ℝ, |t| ≤ ρ → ⌊t / s⌋ ∈ Finset.Icc (-B) B := by
    intro t ht
    obtain ⟨h1, h2⟩ := floor_mul_bounds hs t
    have ht' := abs_le.mp ht
    have hρs : ρ ≤ ((B : ℝ) - 1) * s := by
      have := (div_le_iff₀ hs).mp (show ρ / s ≤ (B : ℝ) - 1 by linarith)
      linarith
    rw [Finset.mem_Icc]
    constructor
    · have : ((-B : ℤ) : ℝ) < (⌊t / s⌋ : ℝ) + 1 := by
        push_cast
        have : -(B : ℝ) * s < ((⌊t / s⌋ : ℝ) + 1) * s := by nlinarith
        exact lt_of_mul_lt_mul_right this hs.le
      have : (-B : ℤ) < ⌊t / s⌋ + 1 := by exact_mod_cast this
      omega
    · have : (⌊t / s⌋ : ℝ) * s ≤ (B : ℝ) * s := by nlinarith
      have : (⌊t / s⌋ : ℝ) ≤ B := le_of_mul_le_mul_right this hs
      exact_mod_cast this
  exact ⟨key _ ((Complex.abs_re_le_norm z).trans hz), key _ ((Complex.abs_im_le_norm z).trans hz)⟩

/-- The integer box containing all grid indices whose corner lies within `ρ` of `q`. -/
def gridBox (s : ℝ) (q : ℂ) (ρ : ℝ) : Finset (ℤ × ℤ) :=
  Finset.Icc ⌈(q.re - ρ) / s⌉ ⌊(q.re + ρ) / s⌋ ×ˢ Finset.Icc ⌈(q.im - ρ) / s⌉ ⌊(q.im + ρ) / s⌋

theorem mem_gridBox {s ρ : ℝ} (hs : 0 < s) {q : ℂ} {a : ℤ × ℤ}
    (h : ‖gridPt s a - q‖ ≤ ρ) : a ∈ gridBox s q ρ := by
  have hre : |(a.1 : ℝ) * s - q.re| ≤ ρ := by
    have := (Complex.abs_re_le_norm (gridPt s a - q)).trans h
    simpa [gridPt] using this
  have him : |(a.2 : ℝ) * s - q.im| ≤ ρ := by
    have := (Complex.abs_im_le_norm (gridPt s a - q)).trans h
    simpa [gridPt] using this
  have hre' := abs_le.mp hre
  have him' := abs_le.mp him
  simp only [gridBox, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Int.ceil_le, div_le_iff₀ hs]; linarith
  · rw [Int.le_floor, le_div_iff₀ hs]; linarith
  · rw [Int.ceil_le, div_le_iff₀ hs]; linarith
  · rw [Int.le_floor, le_div_iff₀ hs]; linarith

theorem card_Icc_ceil_floor_le {x y : ℝ} (h : x ≤ y) :
    ((Finset.Icc ⌈x⌉ ⌊y⌋).card : ℝ) ≤ y - x + 1 := by
  rw [Int.card_Icc]
  rcases le_or_gt 0 (⌊y⌋ + 1 - ⌈x⌉) with hz | hz
  · have e : (((⌊y⌋ + 1 - ⌈x⌉).toNat : ℕ) : ℝ) = ((⌊y⌋ + 1 - ⌈x⌉ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]
    rw [e]
    push_cast
    linarith [Int.floor_le y, Int.le_ceil x]
  · rw [Int.toNat_of_nonpos hz.le]
    simp; linarith

theorem card_gridBox_le {s ρ : ℝ} (hs : 0 < s) (hρ : 0 ≤ ρ) (q : ℂ) :
    ((gridBox s q ρ).card : ℝ) ≤ (2 * ρ / s + 1) ^ 2 := by
  have hle : ∀ t : ℝ, (t - ρ) / s ≤ (t + ρ) / s := fun t =>
    div_le_div_of_nonneg_right (by linarith) hs.le
  have key : ∀ t : ℝ, (t + ρ) / s - (t - ρ) / s + 1 = 2 * ρ / s + 1 := by
    intro t; field_simp; ring
  rw [gridBox, Finset.card_product, Nat.cast_mul, sq]
  have h1 := card_Icc_ceil_floor_le (hle q.re)
  have h2 := card_Icc_ceil_floor_le (hle q.im)
  rw [key] at h1 h2
  exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)

/-! ## Polygons given by vertex functions -/

theorem sum_map_range_eq {β : Type*} [AddCommMonoid β] (g : ℕ → β) (m : ℕ) :
    ((List.range m).map g).sum = ∑ i ∈ Finset.range m, g i := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem edges_range_map (f : ℕ → ℂ) (m : ℕ) :
    edges ((List.range (m + 1)).map f) = (List.range m).map (fun i => (f i, f (i + 1))) := by
  unfold edges
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_zip, List.getElem_tail]

theorem polyLen_range_map (f : ℕ → ℂ) (m : ℕ) :
    polyLen ((List.range (m + 1)).map f) = ∑ i ∈ Finset.range m, ‖f (i + 1) - f i‖ := by
  rw [polyLen, edges_range_map, List.map_map, sum_map_range_eq]
  rfl

theorem polyAvg_range_map (φ : ℂ → ℝ) (f : ℕ → ℂ) (m : ℕ) :
    polyAvg φ ((List.range (m + 1)).map f) =
      ∑ i ∈ Finset.range m, ‖f (i + 1) - f i‖ / (∑ j ∈ Finset.range m, ‖f (j + 1) - f j‖) *
        segAvg φ (f i) (f (i + 1)) := by
  rw [polyAvg, polyComb, SegComb.avg, polyLen_range_map, edges_range_map, List.map_map,
    List.map_map, sum_map_range_eq]
  rfl

theorem polyLen_pair (x y : ℂ) : polyLen [x, y] = ‖y - x‖ := by
  simp [polyLen, edges]

theorem polyAvg_pair (φ : ℂ → ℝ) {x y : ℂ} (h : x ≠ y) : polyAvg φ [x, y] = segAvg φ x y := by
  have : ‖y - x‖ ≠ 0 := by rw [norm_ne_zero_iff, sub_ne_zero]; exact h.symm
  simp [polyAvg, polyComb, SegComb.avg, edges, polyLen, this]

/-! ## Normalization by similarities -/

/-- The inverse of the similarity `simMap s`. -/
def unsim (s : ℂ × ℂ) (z : ℂ) : ℂ := (z - s.2) / s.1

theorem simMap_unsim {s : ℂ × ℂ} (hα : s.1 ≠ 0) (z : ℂ) : simMap s (unsim s z) = z := by
  simp only [simMap, unsim]
  rw [mul_div_cancel₀ _ hα]; ring

theorem unsim_sub (s : ℂ × ℂ) (a b : ℂ) : unsim s a - unsim s b = (a - b) / s.1 := by
  simp only [unsim]; ring

theorem norm_unsim_sub (s : ℂ × ℂ) (a b : ℂ) : ‖unsim s a - unsim s b‖ = ‖a - b‖ / ‖s.1‖ := by
  rw [unsim_sub, norm_div]

theorem norm_unsim (s : ℂ × ℂ) (a : ℂ) : ‖unsim s a‖ = ‖a - s.2‖ / ‖s.1‖ := by
  rw [unsim, norm_div]

theorem norm_unsim_sub_one {s : ℂ × ℂ} (hα : s.1 ≠ 0) (a : ℂ) :
    ‖unsim s a - 1‖ = ‖a - (s.1 + s.2)‖ / ‖s.1‖ := by
  have : unsim s a - 1 = (a - (s.1 + s.2)) / s.1 := by
    simp only [unsim]; field_simp; ring
  rw [this, norm_div]

theorem cfgMap_unsim {s : ℂ × ℂ} (hα : s.1 ≠ 0) (c : Config) :
    cfgMap s (c.1.map (unsim s), c.2.map (unsim s)) = c := by
  simp only [cfgMap, List.map_map]
  have : simMap s ∘ unsim s = id := funext fun z => simMap_unsim hα z
  rw [this, List.map_id, List.map_id]

theorem div_norm_le {a b c : ℝ} (hc : 0 < c) (h : a ≤ b * c) : a / c ≤ b := by
  rwa [div_le_iff₀ hc]

/-- An actual large-excess configuration lies in the image of the normalized family. -/
theorem mem_image_largeFamily {M : ℕ} {δ : ℝ} {s : ℂ × ℂ} (hα : s.1 ≠ 0) {x y x' y' : ℂ}
    (hx : ‖x - s.2‖ ≤ cellRad M * δ * ‖s.1‖) (hy : ‖y - (s.1 + s.2)‖ ≤ cellRad M * δ * ‖s.1‖)
    (hx' : ‖x' - x‖ ≤ 4 * ‖y - x‖) (hy' : ‖y' - x‖ ≤ 4 * ‖y - x‖)
    (h1 : ‖y - x‖ / (2 * M) ≤ ‖y' - x'‖) (h2 : ‖y' - x'‖ ≤ 3 * ‖y - x‖ / (2 * M)) :
    ([x, y], [x', y']) ∈ cfgMap s '' largeFamily M δ := by
  have hα' : 0 < ‖s.1‖ := norm_pos_iff.mpr hα
  refine ⟨(([x, y] : List ℂ).map (unsim s), ([x', y'] : List ℂ).map (unsim s)), ?_,
    cfgMap_unsim hα (([x, y], [x', y']) : Config)⟩
  refine ⟨unsim s x, unsim s y, unsim s x', unsim s y', rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [norm_unsim]; exact div_norm_le hα' hx
  · rw [norm_unsim_sub_one hα]; exact div_norm_le hα' hy
  · rw [norm_unsim_sub, norm_unsim_sub, mul_div_assoc']
    exact div_le_div_of_nonneg_right hx' hα'.le
  · rw [norm_unsim_sub, norm_unsim_sub, mul_div_assoc']
    exact div_le_div_of_nonneg_right hy' hα'.le
  · rw [norm_unsim_sub, norm_unsim_sub, div_div, mul_comm ‖s.1‖, ← div_div]
    exact div_le_div_of_nonneg_right h1 hα'.le
  · rw [norm_unsim_sub, norm_unsim_sub, mul_div_assoc', div_div, mul_comm ‖s.1‖, ← div_div]
    exact div_le_div_of_nonneg_right h2 hα'.le

/-- An actual small-excess configuration (chord and child polygon with vertex function `f`)
lies in the image of the normalized family. -/
theorem mem_image_smallFamily {M : ℕ} {δ : ℝ} {k : ℕ} {s : ℂ × ℂ} (hα : s.1 ≠ 0)
    {f : ℕ → ℂ} {m : ℕ} (hm : 1 ≤ m) (hm3 : m ≤ 3 * M)
    (hx : ‖f 0 - s.2‖ ≤ cellRad M * δ * ‖s.1‖)
    (hy : ‖f m - (s.1 + s.2)‖ ≤ cellRad M * δ * ‖s.1‖)
    (hreg : ∀ i, i + 1 < m → ‖f (i + 1) - f i‖ = ‖f m - f 0‖ / M)
    (hl1 : ‖f m - f 0‖ / (2 * M) ≤ ‖f m - f (m - 1)‖)
    (hl2 : ‖f m - f (m - 1)‖ ≤ 3 * ‖f m - f 0‖ / (2 * M))
    (hk1 : (k : ℝ) * δ ^ 2 ≤
      Real.log ((∑ i ∈ Finset.range m, ‖f (i + 1) - f i‖) / ‖f m - f 0‖))
    (hk2 : Real.log ((∑ i ∈ Finset.range m, ‖f (i + 1) - f i‖) / ‖f m - f 0‖) <
      ((k : ℝ) + 1) * δ ^ 2)
    (hk3 : Real.log ((∑ i ∈ Finset.range m, ‖f (i + 1) - f i‖) / ‖f m - f 0‖) ≤ 1) :
    ([f 0, f m], (List.range (m + 1)).map f) ∈ cfgMap s '' smallFamily M δ k := by
  have hα' : 0 < ‖s.1‖ := norm_pos_iff.mpr hα
  have hm0 : m ≠ 0 := by omega
  refine ⟨(([f 0, f m] : List ℂ).map (unsim s), ((List.range (m + 1)).map f).map (unsim s)), ?_,
    cfgMap_unsim hα (([f 0, f m], (List.range (m + 1)).map f) : Config)⟩
  have hz : ((List.range (m + 1)).map f).map (unsim s) =
      (List.range (m + 1)).map (unsim s ∘ f) := by rw [List.map_map]
  have hE : edges (((List.range (m + 1)).map f).map (unsim s)) =
      (List.range m).map (fun i => (unsim s (f i), unsim s (f (i + 1)))) := by
    rw [hz, edges_range_map]; rfl
  have hlen : polyLen (((List.range (m + 1)).map f).map (unsim s)) =
      (∑ i ∈ Finset.range m, ‖f (i + 1) - f i‖) / ‖s.1‖ := by
    rw [hz, polyLen_range_map, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Function.comp]
    rw [norm_unsim_sub]
  have hratio : polyLen (((List.range (m + 1)).map f).map (unsim s)) /
      ‖unsim s (f m) - unsim s (f 0)‖ =
      (∑ i ∈ Finset.range m, ‖f (i + 1) - f i‖) / ‖f m - f 0‖ := by
    rw [hlen, norm_unsim_sub, div_div_div_cancel_right₀ hα'.ne']
  refine ⟨unsim s (f 0), unsim s (f m), _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [List.head?_range]
  · simp [List.getLast?_range, hm0]
  · rw [norm_unsim]; exact div_norm_le hα' hx
  · rw [norm_unsim_sub_one hα]; exact div_norm_le hα' hy
  · simp; omega
  · simp; omega
  · intro e he
    rw [hE, ← List.map_dropLast, List.dropLast_eq_take, List.length_range, List.take_range,
      List.mem_map] at he
    obtain ⟨i, hi, rfl⟩ := he
    rw [List.mem_range] at hi
    have hi' : i + 1 < m := by omega
    simp only
    rw [norm_unsim_sub, norm_unsim_sub, hreg i hi', div_div, div_div, mul_comm]
  · intro e he
    rw [hE, List.getLast?_map, List.getLast?_range] at he
    simp only [hm0, ↓reduceIte, Option.map_some, Option.mem_def, Option.some.injEq] at he
    subst he
    have hm1 : m - 1 + 1 = m := by omega
    simp only
    rw [hm1, norm_unsim_sub, norm_unsim_sub]
    constructor
    · rw [div_div, mul_comm ‖s.1‖, ← div_div]
      exact div_le_div_of_nonneg_right hl1 hα'.le
    · rw [mul_div_assoc', div_div, mul_comm ‖s.1‖, ← div_div]
      exact div_le_div_of_nonneg_right hl2 hα'.le
  · rw [hratio]; exact hk1
  · rw [hratio]; exact hk2
  · rw [hratio]; exact hk3

/-! ## Vertex deviation of polygons with small excess -/

theorem norm_sub_smul_sq (d w : ℂ) (c : ℝ) :
    ‖d - c • w‖ ^ 2 = ‖d‖ ^ 2 + c ^ 2 * ‖w‖ ^ 2 - 2 * c * (d * conj w).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.real_smul, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- **Vertex deviation.**  If all edges of the polygon `f 0, …, f m` except the last have length
`R / M` (`R = |f m - f 0|`) and every edge has length at most `R`, then the vertex `f i`
(`i < m`) is within `i √(2R(P - R))` of the straight position `f 0 + (i/M)(f m - f 0)`, where
`P` is the length of the polygon. -/
theorem vertex_dev {f : ℕ → ℂ} {m M : ℕ} (hM : 0 < M) (hR : 0 < ‖f m - f 0‖)
    (hreg : ∀ i, i + 1 < m → ‖f (i + 1) - f i‖ = ‖f m - f 0‖ / M)
    (hle : ∀ i < m, ‖f (i + 1) - f i‖ ≤ ‖f m - f 0‖) {i : ℕ} (hi : i < m) :
    ‖f i - f 0 - ((i : ℝ) / M) • (f m - f 0)‖ ≤
      i * √(2 * ‖f m - f 0‖ *
        ((∑ j ∈ Finset.range m, ‖f (j + 1) - f j‖) - ‖f m - f 0‖)) := by
  set R := ‖f m - f 0‖ with hRdef
  set w := f m - f 0 with hwdef
  set P := ∑ j ∈ Finset.range m, ‖f (j + 1) - f j‖ with hPdef
  set d : ℕ → ℂ := fun j => f (j + 1) - f j with hddef
  have hsum : ∑ j ∈ Finset.range m, d j = w := Finset.sum_range_sub f m
  have hterm : ∀ j, (d j * conj w).re ≤ ‖d j‖ * R := by
    intro j
    calc (d j * conj w).re ≤ ‖d j * conj w‖ := Complex.re_le_norm _
      _ = ‖d j‖ * R := by rw [norm_mul, Complex.norm_conj]
  have hww : (w * conj w).re = R ^ 2 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have htot : ∑ j ∈ Finset.range m, (R * ‖d j‖ - (d j * conj w).re) = R * (P - R) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul, hsum, hww]
    ring
  have hnonneg : ∀ j, 0 ≤ R * ‖d j‖ - (d j * conj w).re := by
    intro j; have := hterm j; nlinarith
  have hsingle : ∀ j < m, R * ‖d j‖ - (d j * conj w).re ≤ R * (P - R) := by
    intro j hj
    rw [← htot]
    exact Finset.single_le_sum (f := fun j => R * ‖d j‖ - (d j * conj w).re)
      (fun j _ => hnonneg j) (Finset.mem_range.mpr hj)
  have hPR : R ≤ P := by
    rw [hRdef, ← hsum]
    exact norm_sum_le _ _
  have hdj : ∀ j < m, ‖d j - (‖d j‖ / R) • w‖ ≤ √(2 * R * (P - R)) := by
    intro j hj
    apply Real.le_sqrt_of_sq_le
    rw [norm_sub_smul_sq]
    have h1 := hsingle j hj
    have h2 : ‖d j‖ ≤ R := hle j hj
    have h3 : 0 ≤ ‖d j‖ := norm_nonneg _
    have e : ‖d j‖ ^ 2 + (‖d j‖ / R) ^ 2 * R ^ 2 - 2 * (‖d j‖ / R) * (d j * conj w).re =
        2 * (‖d j‖ / R) * (R * ‖d j‖ - (d j * conj w).re) := by
      field_simp; ring
    rw [e]
    have h4 : 0 ≤ ‖d j‖ / R := div_nonneg h3 hR.le
    have h5 : ‖d j‖ / R ≤ 1 := (div_le_one hR).mpr h2
    calc 2 * (‖d j‖ / R) * (R * ‖d j‖ - (d j * conj w).re)
        ≤ 2 * (‖d j‖ / R) * (R * (P - R)) := by gcongr
      _ ≤ 2 * 1 * (R * (P - R)) := by
          gcongr
      _ = 2 * R * (P - R) := by ring
  have hsplit : f i - f 0 - ((i : ℝ) / M) • w =
      ∑ j ∈ Finset.range i, (d j - (‖d j‖ / R) • w) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub f i, ← Finset.sum_smul]
    congr 2
    have : ∀ j ∈ Finset.range i, ‖d j‖ / R = 1 / M := by
      intro j hj
      rw [Finset.mem_range] at hj
      simp only [hddef]
      rw [hreg j (by omega)]
      field_simp
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hsplit]
  calc ‖∑ j ∈ Finset.range i, (d j - (‖d j‖ / R) • w)‖
      ≤ ∑ j ∈ Finset.range i, ‖d j - (‖d j‖ / R) • w‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range i, √(2 * R * (P - R)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_range] at hj
        exact hdj j (by omega)
    _ = i * √(2 * R * (P - R)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end LQGDimension.LFPPRecords
