/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordMeanCrudeAux2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordMeanCrudeAux1

/-!
# Node `M45`, auxiliary file 2: polygons of the normalized local families

* `edges_eq`, `polyLen_eq`, `cfgComb_eq`: a configuration `([x, y], z)` has test combination
  `(range (m+1)).map (cfgG x y V L)` (chord first, then the negatively weighted edges), where
  `V i = z.getD i 0`, `m = |z| - 1` and `L` is the length of the polygon.
* `SmallGeom`: the data of a small-excess configuration in index form (`small_data`).
* Geometry of small-excess polygons (`M ≥ 16`, `0 < δ < 1`): the chord has length in `[1/2, 2]`,
  every edge has length `≥ 1/(4M)`, every vertex lies in the disc of radius `7`, and the edge
  weights are Lipschitz in the vertices.
* `small_straight`: if `4 M (k+1) δ² < 1`, the polygon has exactly `M` edges and its vertices lie
  within `7 δ √(k+1)` of the points `j / M` (projection onto the chord and Cauchy–Schwarz:
  `|z_j - x - (j/M)(y - x)| ≤ √(2 len (len - |y - x|))`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.RMCrude

open Blueprint.Draft TwoScale

/-! ## Index form of polygons -/

/-- Vertices of a list, padded by `0`. -/
def vx (z : List ℂ) (i : ℕ) : ℂ := z.getD i 0

/-- Length of the polygon `V 0, …, V m`. -/
def plen (V : ℕ → ℂ) (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, ‖V (i + 1) - V i‖

lemma vx_eq_getElem (z : List ℂ) {i : ℕ} (hi : i < z.length) : vx z i = z[i] := by
  unfold vx
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

lemma vx_eq_zero (z : List ℂ) {i : ℕ} (hi : z.length ≤ i) : vx z i = 0 := by
  unfold vx
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma edges_eq (z : List ℂ) :
    edges z = (List.range (z.length - 1)).map fun i => (vx z i, vx z (i + 1)) := by
  unfold edges
  have hlen : (z.zip z.tail).length =
      ((List.range (z.length - 1)).map fun i => (vx z i, vx z (i + 1))).length := by
    rw [List.length_zip, List.length_tail, List.length_map, List.length_range]
    omega
  refine List.ext_getElem hlen fun i h1 h2 => ?_
  have hi : i < z.length - 1 := by simpa using h2
  simp only [List.getElem_zip, List.getElem_tail, List.getElem_map, List.getElem_range]
  rw [vx_eq_getElem z (by omega), vx_eq_getElem z (by omega)]

lemma polyLen_eq (z : List ℂ) : polyLen z = plen (vx z) (z.length - 1) := by
  unfold polyLen plen
  rw [edges_eq, List.map_map, list_sum_map_range]
  rfl

lemma polyComb_eq (z : List ℂ) :
    polyComb z = (List.range (z.length - 1)).map fun i =>
      (‖vx z (i + 1) - vx z i‖ / plen (vx z) (z.length - 1), vx z i, vx z (i + 1)) := by
  unfold polyComb
  rw [polyLen_eq, edges_eq, List.map_map]
  rfl

/-- The entries of the test combination of a configuration: chord, then negated edges. -/
def cfgG (x y : ℂ) (V : ℕ → ℂ) (L : ℝ) : ℕ → ℝ × ℂ × ℂ
  | 0 => (1, x, y)
  | i + 1 => (-(‖V (i + 1) - V i‖ / L), V i, V (i + 1))

lemma cfgComb_eq {x y : ℂ} (hxy : x ≠ y) (z : List ℂ) :
    cfgComb ([x, y], z) =
      (List.range (z.length - 1 + 1)).map (cfgG x y (vx z) (plen (vx z) (z.length - 1))) := by
  have hne : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hxy.symm)
  have h1 : polyComb [x, y] = [((1 : ℝ), x, y)] := by
    unfold polyComb polyLen edges
    simp [hne]
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  unfold cfgComb SegComb.sub
  simp only
  rw [h1, polyComb_eq, List.map_map, List.singleton_append]
  rfl

/-! ## Small-excess configurations in index form -/

/-- A small-excess configuration `([x, y], z)` in index form: `V i = z.getD i 0`, `m = |z| - 1`. -/
structure SmallGeom (M : ℕ) (δ : ℝ) (k : ℕ) (x y : ℂ) (V : ℕ → ℂ) (m : ℕ) : Prop where
  v0 : V 0 = x
  vm : V m = y
  m1 : 1 ≤ m
  m3 : m ≤ 3 * M
  hx : ‖x‖ ≤ cellRad M * δ
  hy : ‖y - 1‖ ≤ cellRad M * δ
  full : ∀ i, i + 1 < m → ‖V (i + 1) - V i‖ = ‖y - x‖ / M
  last1 : ‖y - x‖ / (2 * M) ≤ ‖V m - V (m - 1)‖
  last2 : ‖V m - V (m - 1)‖ ≤ 3 * ‖y - x‖ / (2 * M)
  A1 : (k : ℝ) * δ ^ 2 ≤ Real.log (plen V m / ‖y - x‖)
  A2 : Real.log (plen V m / ‖y - x‖) < ((k : ℝ) + 1) * δ ^ 2
  A3 : Real.log (plen V m / ‖y - x‖) ≤ 1
  pad : ∀ i, m < i → V i = 0

lemma small_data {M : ℕ} {δ : ℝ} {k : ℕ} {c : Config} (hc : c ∈ smallFamily M δ k) :
    ∃ x y : ℂ, ∃ z : List ℂ, c = ([x, y], z) ∧ SmallGeom M δ k x y (vx z) (z.length - 1) := by
  obtain ⟨x, y, z, rfl, hhead, hlast, hx, hy, hl2, hl3, hdrop, hlastE, hA1, hA2, hA3⟩ := hc
  refine ⟨x, y, z, rfl, ?_⟩
  have hedge : ∀ i, i < z.length - 1 →
      ((edges z)[i]? = some (vx z i, vx z (i + 1))) := by
    intro i hi
    rw [edges_eq, List.getElem?_map, List.getElem?_range hi]
    rfl
  refine ⟨?_, ?_, by omega, by omega, hx, hy, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases z with
    | nil => simp at hhead
    | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      rw [← hhead]; rfl
  · rw [List.getLast?_eq_getElem?] at hlast
    unfold vx
    rw [List.getD_eq_getElem?_getD, hlast, Option.getD_some]
  · intro i hi
    have hlen : i < (edges z).dropLast.length := by
      rw [List.length_dropLast, edges_eq, List.length_map, List.length_range]; omega
    have hmem := List.getElem_mem hlen
    have heq : (edges z).dropLast[i] = (vx z i, vx z (i + 1)) := by
      rw [List.getElem_dropLast]
      have := hedge i (by omega)
      rw [List.getElem?_eq_getElem (by rw [edges_eq, List.length_map, List.length_range]; omega)]
        at this
      exact Option.some.inj this
    rw [heq] at hmem
    exact hdrop _ hmem
  · have hl : (edges z).getLast? = some (vx z (z.length - 1 - 1), vx z (z.length - 1)) := by
      rw [List.getLast?_eq_getElem?, edges_eq, List.length_map, List.length_range,
        List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some]
      congr 3
      omega
    exact (hlastE _ (by rw [hl]; rfl)).1
  · have hl : (edges z).getLast? = some (vx z (z.length - 1 - 1), vx z (z.length - 1)) := by
      rw [List.getLast?_eq_getElem?, edges_eq, List.length_map, List.length_range,
        List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some]
      congr 3
      omega
    exact (hlastE _ (by rw [hl]; rfl)).2
  · rw [← polyLen_eq]; exact hA1
  · rw [← polyLen_eq]; exact hA2
  · rw [← polyLen_eq]; exact hA3
  · intro i hi
    exact vx_eq_zero z (by omega)

/-! ## Elementary geometry -/

lemma cellRad_nonneg (M : ℕ) : 0 ≤ cellRad M := by unfold cellRad; positivity

lemma cellRad_mul_le {M : ℕ} (hM : 16 ≤ M) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    cellRad M * δ ≤ 1 / 64 := by
  have hM' : (16 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 : cellRad M ≤ 1 / 64 := by
    unfold cellRad
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc cellRad M * δ ≤ cellRad M * 1 := by
        gcongr; · exact cellRad_nonneg M
        · exact hδ.2.le
    _ ≤ 1 / 64 := by rw [mul_one]; exact h1

/-- The normalized chord has length in `[1/2, 2]`. -/
lemma chord_bounds {x y : ℂ} {c : ℝ} (hc : c ≤ 1 / 64) (hx : ‖x‖ ≤ c) (hy : ‖y - 1‖ ≤ c) :
    1 / 2 ≤ ‖y - x‖ ∧ ‖y - x‖ ≤ 2 ∧ ‖x‖ ≤ 1 / 64 ∧ ‖y‖ ≤ 2 := by
  have h1 : ‖y - x‖ ≤ ‖y - 1‖ + 1 + ‖x‖ := by
    have e : y - x = (y - 1) + 1 - x := by ring
    rw [e]
    calc ‖(y - 1) + 1 - x‖ ≤ ‖(y - 1) + 1‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ ‖y - 1‖ + ‖(1 : ℂ)‖ + ‖x‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by simp
  have h2 : 1 ≤ ‖y - x‖ + ‖y - 1‖ + ‖x‖ := by
    have e2 : (1 : ℂ) = (y - x) - (y - 1) + x := by ring
    calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
      _ = ‖(y - x) - (y - 1) + x‖ := by rw [← e2]
      _ ≤ ‖(y - x) - (y - 1)‖ + ‖x‖ := norm_add_le _ _
      _ ≤ ‖y - x‖ + ‖y - 1‖ + ‖x‖ := by gcongr; exact norm_sub_le _ _
  have h3 : ‖y‖ ≤ ‖y - 1‖ + 1 := by
    calc ‖y‖ = ‖(y - 1) + 1‖ := by ring_nf
      _ ≤ ‖y - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = _ := by simp
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma norm_sub_zero_le_sum (V : ℕ → ℂ) (j : ℕ) :
    ‖V j - V 0‖ ≤ ∑ i ∈ Finset.range j, ‖V (i + 1) - V i‖ := by
  rw [← Finset.sum_range_sub]; exact norm_sum_le _ _

lemma sum_le_plen (V : ℕ → ℂ) {j m : ℕ} (h : j ≤ m) :
    ∑ i ∈ Finset.range j, ‖V (i + 1) - V i‖ ≤ plen V m :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h)
    (fun _ _ _ => norm_nonneg _)

lemma exp_one_le_three : Real.exp 1 ≤ 3 := by
  have h := Real.abs_exp_sub_one_le (x := 1) (by norm_num)
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

/-- Basic geometry of a small-excess polygon. -/
lemma SmallGeom.basic {M : ℕ} {δ : ℝ} {k : ℕ} {x y : ℂ} {V : ℕ → ℂ} {m : ℕ}
    (hg : SmallGeom M δ k x y V m) (hM : 16 ≤ M) (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    1 / 2 ≤ ‖y - x‖ ∧ ‖y - x‖ ≤ 2 ∧ ‖y - x‖ ≤ plen V m ∧ plen V m ≤ 3 * ‖y - x‖ ∧
      (∀ i, ‖V i‖ ≤ 7) ∧ (∀ i < m, 1 / (4 * M) ≤ ‖V (i + 1) - V i‖) ∧ ‖x‖ ≤ 1 / 64 ∧
      ‖y‖ ≤ 2 := by
  have hc := cellRad_mul_le hM hδ
  obtain ⟨hR1, hR2, hx, hy⟩ := chord_bounds hc hg.hx hg.hy
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hRL : ‖y - x‖ ≤ plen V m := by
    have := norm_sub_zero_le_sum V m
    rw [hg.v0, hg.vm] at this
    exact this
  have hRpos : 0 < ‖y - x‖ := by linarith
  have hLpos : 0 < plen V m / ‖y - x‖ := div_pos (by linarith) hRpos
  have hL3 : plen V m ≤ 3 * ‖y - x‖ := by
    have h := (Real.log_le_iff_le_exp hLpos).1 hg.A3
    rw [div_le_iff₀ hRpos] at h
    nlinarith [exp_one_le_three]
  refine ⟨hR1, hR2, hRL, hL3, fun i => ?_, fun i hi => ?_, hx, hy⟩
  · rcases le_or_gt i m with him | him
    · have h1 := norm_sub_zero_le_sum V i
      have h2 := sum_le_plen V him
      have h3 : ‖V i‖ ≤ ‖V i - V 0‖ + ‖V 0‖ := by
        calc ‖V i‖ = ‖(V i - V 0) + V 0‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      rw [hg.v0] at h1 h3
      linarith
    · rw [hg.pad i him, norm_zero]; norm_num
  · have hq : 1 / (4 * (M : ℝ)) ≤ ‖y - x‖ / (2 * M) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    rcases lt_or_ge (i + 1) m with h | h
    · rw [hg.full i h]
      refine hq.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    · have hi' : i = m - 1 := by omega
      have hm' : i + 1 = m := by omega
      rw [hm', hi']
      exact hq.trans hg.last1

/-! ## The polygon identity `|e - |e| u|² = 2 |e| (|e| - Re(e ū))` -/

lemma norm_sub_norm_mul_sq (e u : ℂ) (hu : ‖u‖ = 1) :
    ‖e - (‖e‖ : ℂ) * u‖ ^ 2 = 2 * ‖e‖ * (‖e‖ - (e * (starRingEnd ℂ) u).re) := by
  have h1 : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu]; norm_num
  have h2 : Complex.normSq e = ‖e‖ ^ 2 := Complex.normSq_eq_norm_sq e
  rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal, h1, h2,
    map_mul, Complex.conj_ofReal]
  have e3 : e * ((‖e‖ : ℂ) * (starRingEnd ℂ) u) = (‖e‖ : ℂ) * (e * (starRingEnd ℂ) u) := by ring
  rw [e3, Complex.re_ofReal_mul]
  ring

lemma re_mul_conj_le (e u : ℂ) (hu : ‖u‖ = 1) : (e * (starRingEnd ℂ) u).re ≤ ‖e‖ := by
  calc (e * (starRingEnd ℂ) u).re ≤ ‖e * (starRingEnd ℂ) u‖ := Complex.re_le_norm _
    _ = ‖e‖ := by rw [norm_mul, Complex.norm_conj, hu, mul_one]

/-- Length of a small-excess polygon: `m - 1` full edges and the last one. -/
lemma SmallGeom.len_split {M : ℕ} {δ : ℝ} {k : ℕ} {x y : ℂ} {V : ℕ → ℂ} {m : ℕ}
    (hg : SmallGeom M δ k x y V m) :
    plen V m = ((m - 1 : ℕ) : ℝ) * (‖y - x‖ / M) + ‖V m - V (m - 1)‖ := by
  unfold plen
  have hm : m = (m - 1) + 1 := by have := hg.m1; omega
  conv_lhs => rw [hm]
  rw [Finset.sum_range_succ, ← hm]
  congr 1
  rw [Finset.sum_congr rfl fun i hi => hg.full i (by rw [Finset.mem_range] at hi; omega),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma m_eq_of_bounds {R L ℓ t : ℝ} {M m : ℕ} (hM0 : 0 < (M : ℝ)) (hR : 0 < R)
    (hsplit : L = ((m - 1 : ℕ) : ℝ) * (R / M) + ℓ) (hl1 : R / (2 * M) ≤ ℓ)
    (hl2 : ℓ ≤ 3 * R / (2 * M)) (hRL : R ≤ L) (hLt : L < R * (1 + 2 * t))
    (ht : t * (4 * M) < 1) (hm1 : 1 ≤ m) : m = M := by
  set a : ℝ := ((m - 1 : ℕ) : ℝ) with hadef
  have e1 : L * M = a * R + ℓ * M := by rw [hsplit]; field_simp
  have e2 : R ≤ ℓ * (2 * M) := by rwa [div_le_iff₀ (by positivity)] at hl1
  have e3 : ℓ * (2 * M) ≤ 3 * R := by rwa [le_div_iff₀ (by positivity)] at hl2
  have e4 : R * M ≤ L * M := mul_le_mul_of_nonneg_right hRL hM0.le
  have e5 : L * M < R * (1 + 2 * t) * M := mul_lt_mul_of_pos_right hLt hM0
  have e6 : R * (t * (4 * M)) < R * 1 := mul_lt_mul_of_pos_left ht hR
  have hA : (M : ℝ) ≤ a + 3 / 2 := by
    by_contra hc
    push_neg at hc
    have := mul_pos hR (sub_pos.2 hc)
    linarith
  have hB : a < M := by
    by_contra hc
    push_neg at hc
    have := mul_nonneg hR.le (sub_nonneg.2 hc)
    linarith
  have h1 : M < m - 1 + 2 := by
    have : (M : ℝ) < ((m - 1 + 2 : ℕ) : ℝ) := by push_cast; rw [← hadef]; linarith
    exact_mod_cast this
  have h2 : m - 1 < M := by
    have h := hB
    rw [hadef] at h
    exact_mod_cast h
  omega

/-- Vertices of a polygon whose edges before the last one have length `|y - x| / m` lie within
`√(2 len (len - |y - x|))` of the corresponding points of the chord. -/
lemma straight_core (V : ℕ → ℂ) (m : ℕ) (x y : ℂ) (hm0 : 0 < (m : ℝ)) (v0 : V 0 = x)
    (vm : V m = y) (hR : 0 < ‖y - x‖)
    (full : ∀ i, i + 1 < m → ‖V (i + 1) - V i‖ = ‖y - x‖ / m) :
    ∀ j ≤ m, ‖V j - (x + (((j : ℝ) / m : ℝ) : ℂ) * (y - x))‖ ≤
      √(2 * plen V m * (plen V m - ‖y - x‖)) := by
  intro j hj
  set R := ‖y - x‖ with hRdef
  set L := plen V m with hLdef
  set u : ℂ := (y - x) / (R : ℂ) with hudef
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, ← hRdef,
      div_self hR.ne']
  have hRu : (R : ℂ) * u = y - x := by rw [hudef]; field_simp
  set e : ℕ → ℂ := fun i => V (i + 1) - V i with hedef
  set dd : ℕ → ℝ := fun i => ‖e i‖ - (e i * (starRingEnd ℂ) u).re with hdddef
  have hdd0 : ∀ i, 0 ≤ dd i := fun i => by
    rw [hdddef]; simp only; linarith [re_mul_conj_le (e i) u hu]
  have hsumd : ∑ i ∈ Finset.range m, dd i = L - R := by
    rw [hdddef, hLdef]
    simp only
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [← Complex.re_sum, ← Finset.sum_mul, hedef]
    simp only
    rw [Finset.sum_range_sub, v0, vm, hudef, map_div₀, Complex.conj_ofReal,
      mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq, ← hRdef]
    have : ((R ^ 2 : ℝ) : ℂ) / (R : ℂ) = ((R : ℝ) : ℂ) := by
      rw [← Complex.ofReal_div]; congr 1; field_simp
    push_cast at this ⊢
    rw [this, Complex.ofReal_re]
  rcases eq_or_lt_of_le hj with hjm | hjm
  · rw [hjm, vm, div_self hm0.ne']
    simp only [Complex.ofReal_one, one_mul, add_sub_cancel, sub_self, norm_zero]
    exact Real.sqrt_nonneg _
  · have hrep : V j - (x + (((j : ℝ) / m : ℝ) : ℂ) * (y - x)) =
        ∑ i ∈ Finset.range j, (e i - (‖e i‖ : ℂ) * u) := by
      rw [Finset.sum_sub_distrib, hedef]
      simp only
      rw [Finset.sum_range_sub, v0]
      have hfull : ∀ i ∈ Finset.range j, (‖V (i + 1) - V i‖ : ℂ) * u = ((R / m : ℝ) : ℂ) * u :=
        fun i hi => by
          rw [Finset.mem_range] at hi
          rw [full i (by omega)]
      rw [Finset.sum_congr rfl hfull, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hRu]
      have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
      push_cast
      field_simp
      ring
    rw [hrep]
    calc ‖∑ i ∈ Finset.range j, (e i - (‖e i‖ : ℂ) * u)‖
        ≤ ∑ i ∈ Finset.range j, ‖e i - (‖e i‖ : ℂ) * u‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range m, ‖e i - (‖e i‖ : ℂ) * u‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hjm.le)
            (fun _ _ _ => norm_nonneg _)
      _ = ∑ i ∈ Finset.range m, √(2 * ‖e i‖) * √(dd i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Real.sqrt_mul (by positivity), hdddef]
          simp only
          rw [← norm_sub_norm_mul_sq (e i) u hu, Real.sqrt_sq (norm_nonneg _)]
      _ ≤ √(∑ i ∈ Finset.range m, 2 * ‖e i‖) * √(∑ i ∈ Finset.range m, dd i) :=
          Real.sum_sqrt_mul_sqrt_le _ (fun i => by positivity) hdd0
      _ = √(2 * L * (L - R)) := by
          rw [hsumd, ← Finset.mul_sum, ← Real.sqrt_mul (by positivity)]
          rfl

lemma cellRad_le_one {M : ℕ} (hM : 16 ≤ M) : cellRad M ≤ 1 := by
  have hM' : (16 : ℝ) ≤ M := by exact_mod_cast hM
  unfold cellRad
  rw [div_le_one (by positivity)]
  nlinarith

/-- **Near-straight polygons.**  If `4 M (k+1) δ² < 1`, a small-excess polygon has exactly `M`
edges and its vertices are within `7 δ √(k+1)` of `j / M`. -/
lemma SmallGeom.straight {M : ℕ} {δ : ℝ} {k : ℕ} {x y : ℂ} {V : ℕ → ℂ} {m : ℕ}
    (hg : SmallGeom M δ k x y V m) (hM : 16 ≤ M) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hsm : 4 * M * ((k : ℝ) + 1) * δ ^ 2 < 1) :
    m = M ∧ ∀ j ≤ M, ‖V j - (((j : ℝ) / M : ℝ) : ℂ)‖ ≤ 7 * δ * √((k : ℝ) + 1) := by
  obtain ⟨hR1, hR2, hRL, hL3, -, -, -, -⟩ := hg.basic hM hδ
  set R := ‖y - x‖ with hRdef
  set L := plen V m with hLdef
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hRpos : 0 < R := by linarith
  set t : ℝ := ((k : ℝ) + 1) * δ ^ 2 with htdef
  have ht0 : 0 < t := by have := hδ.1; positivity
  have ht1 : t * (4 * M) < 1 := by rw [htdef]; linarith
  have hM16 : (16 : ℝ) ≤ M := by exact_mod_cast hM
  have htM : t < 1 / 64 := by
    have : t * 64 ≤ t * (4 * M) := by gcongr; linarith
    linarith
  have hLt : L < R * (1 + 2 * t) := by
    have hLpos : 0 < L / R := div_pos (by linarith) hRpos
    have h := (Real.log_lt_iff_lt_exp hLpos).1 hg.A2
    have he := Real.abs_exp_sub_one_le (x := t) (by rw [abs_of_pos ht0]; linarith)
    rw [abs_le] at he
    rw [div_lt_iff₀ hRpos] at h
    have : Real.exp t * R ≤ (1 + 2 * |t|) * R := by
      gcongr; linarith [he.2]
    rw [abs_of_pos ht0] at this
    linarith
  have hmM : m = M := m_eq_of_bounds hM0 hRpos hg.len_split hg.last1 hg.last2 hRL hLt ht1 hg.m1
  refine ⟨hmM, fun j hj => ?_⟩
  have hfull : ∀ i, i + 1 < m → ‖V (i + 1) - V i‖ = ‖y - x‖ / (m : ℕ) := by
    intro i hi; rw [hg.full i hi, hmM]
  have hkey := straight_core V m x y (by rw [hmM]; exact hM0) hg.v0 hg.vm hRpos hfull j
    (by rw [hmM]; exact hj)
  have hmR : ((m : ℕ) : ℝ) = (M : ℝ) := by rw [hmM]
  rw [hmR] at hkey
  have hLR : 2 * L * (L - R) ≤ (6 * (δ * √((k : ℝ) + 1))) ^ 2 := by
    have hsq : (6 * (δ * √((k : ℝ) + 1))) ^ 2 = 36 * t := by
      rw [htdef, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    rw [hsq]
    have h1 : L - R ≤ 2 * t * R := by linarith
    have h2 : L ≤ 2 * R := by nlinarith
    have h3 : 0 ≤ L - R := by linarith
    have h4 : 2 * L * (L - R) ≤ 2 * (2 * R) * (2 * t * R) := by
      apply mul_le_mul (by linarith) h1 h3 (by linarith)
    have h5 : R * R ≤ 4 := by nlinarith
    nlinarith
  have hs1 : √(2 * L * (L - R)) ≤ 6 * (δ * √((k : ℝ) + 1)) := by
    calc √(2 * L * (L - R)) ≤ √((6 * (δ * √((k : ℝ) + 1))) ^ 2) := Real.sqrt_le_sqrt hLR
      _ = 6 * (δ * √((k : ℝ) + 1)) := Real.sqrt_sq (by have := hδ.1; positivity)
  have hsk : 1 ≤ √((k : ℝ) + 1) := by
    rw [Real.one_le_sqrt]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hstr : ‖(x + (((j : ℝ) / M : ℝ) : ℂ) * (y - x)) - (((j : ℝ) / M : ℝ) : ℂ)‖ ≤
      δ * √((k : ℝ) + 1) := by
    have hj0 : 0 ≤ (j : ℝ) / M := by positivity
    have hj1 : (j : ℝ) / M ≤ 1 := by
      rw [div_le_one hM0]; exact_mod_cast hj
    have e : (x + (((j : ℝ) / M : ℝ) : ℂ) * (y - x)) - (((j : ℝ) / M : ℝ) : ℂ) =
        ((1 - (j : ℝ) / M : ℝ) : ℂ) * x + (((j : ℝ) / M : ℝ) : ℂ) * (y - 1) := by
      push_cast; ring
    rw [e]
    have hcx := hg.hx
    have hcy := hg.hy
    have hj2 : (0 : ℝ) ≤ 1 - (j : ℝ) / M := by linarith
    have hc1 : cellRad M ≤ 1 := cellRad_le_one hM
    calc _ ≤ ‖((1 - (j : ℝ) / M : ℝ) : ℂ) * x‖ + ‖(((j : ℝ) / M : ℝ) : ℂ) * (y - 1)‖ :=
          norm_add_le _ _
      _ = (1 - (j : ℝ) / M) * ‖x‖ + (j : ℝ) / M * ‖y - 1‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg hj2, abs_of_nonneg hj0]
      _ ≤ (1 - (j : ℝ) / M) * (cellRad M * δ) + (j : ℝ) / M * (cellRad M * δ) := by
          gcongr
      _ = cellRad M * δ := by ring
      _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hc1 hδ.1.le
      _ = δ := one_mul δ
      _ ≤ δ * √((k : ℝ) + 1) := le_mul_of_one_le_right hδ.1.le hsk
  calc ‖V j - (((j : ℝ) / M : ℝ) : ℂ)‖
      ≤ ‖V j - (x + (((j : ℝ) / M : ℝ) : ℂ) * (y - x))‖ +
        ‖(x + (((j : ℝ) / M : ℝ) : ℂ) * (y - x)) - (((j : ℝ) / M : ℝ) : ℂ)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 6 * (δ * √((k : ℝ) + 1)) + δ * √((k : ℝ) + 1) := add_le_add (hkey.trans hs1) hstr
    _ = 7 * δ * √((k : ℝ) + 1) := by ring

/-! ## Lipschitz dependence of the normalized weights -/

lemma sum_abs_div_sub_div_le (m : ℕ) (a b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hLa : 0 < ∑ i ∈ Finset.range m, a i) (hLb : 0 < ∑ i ∈ Finset.range m, b i) :
    ∑ i ∈ Finset.range m, |a i / (∑ j ∈ Finset.range m, a j) - b i / (∑ j ∈ Finset.range m, b j)|
      ≤ 2 * (∑ i ∈ Finset.range m, |a i - b i|) / ∑ j ∈ Finset.range m, a j := by
  set La := ∑ j ∈ Finset.range m, a j with hLadef
  set Lb := ∑ j ∈ Finset.range m, b j with hLbdef
  set S := ∑ i ∈ Finset.range m, |a i - b i| with hSdef
  have hpt : ∀ i, |a i / La - b i / Lb| ≤ |a i - b i| / La + b i * |1 / La - 1 / Lb| := by
    intro i
    have e : a i / La - b i / Lb = (a i - b i) / La + b i * (1 / La - 1 / Lb) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos hLa, abs_mul, abs_of_nonneg (hb i)]
  have hdiff : |Lb - La| ≤ S := by
    rw [hLadef, hLbdef, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
  have hLb' : Lb * |1 / La - 1 / Lb| = |Lb - La| / La := by
    have e : Lb * (1 / La - 1 / Lb) = (Lb - La) / La := by field_simp
    rw [show Lb * |1 / La - 1 / Lb| = |Lb * (1 / La - 1 / Lb)| by rw [abs_mul, abs_of_pos hLb],
      e, abs_div, abs_of_pos hLa]
  calc ∑ i ∈ Finset.range m, |a i / La - b i / Lb|
      ≤ ∑ i ∈ Finset.range m, (|a i - b i| / La + b i * |1 / La - 1 / Lb|) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = S / La + Lb * |1 / La - 1 / Lb| := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    _ ≤ S / La + S / La := by
        rw [hLb']; gcongr
    _ = 2 * S / La := by ring

end LQGDimension.RMCrude
