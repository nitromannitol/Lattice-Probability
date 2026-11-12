/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36Graph at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36Poly
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.6, deterministic part: a left–right graph crossing of `𝕊` bounds `D^ε(K, ∂U)`

DFGPS Lemma 3.6 (arXiv:1905.00380, T:1628–1650), lower bound. A path in the 8-neighbour graph
`𝕊 ∩ εℤ²` (T:1606) from a leftmost to a rightmost vertex, made polygonal, crosses the line
`Re z = 1/2`; the piece up to the first crossing is a path from `K = [0,1/4] × [0,1]` to the boundary
of `U = (−1,1/2) × (−1,2)`. By the polygon bound (`L36Poly`, the "upper bound" half of the proof
of DG Prop 3.16, DG arXiv:1807.01072 l. 1447–1452, with vertices instead of squares) its
continuum LFPP length is at most `√2 ε e^{ξ osc} Σ_j e^{ξ φ(π(j))}`. This is the step "left–right
crossing ≥ `D^ε(K, ∂U)`" of node S11 (`blueprint/DFGPS.md` l. 141; own elementary argument, the
paper only says "the same argument as in [DG, Prop 3.16]").
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace LQGMetric.DFGPS.L36

open LQGDimension.PolygonRiemannAux Blueprint

/-- `K = [0,1/4] × [0,1]` -/
def K36 : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ 1/4 ∧ 0 ≤ z.im ∧ z.im ≤ 1}

/-- `U = (−1,1/2) × (−1,2)` -/
def U36 : Set ℂ := {z | -1 < z.re ∧ z.re < 1/2 ∧ -1 < z.im ∧ z.im < 2}

lemma isOpen_U36 : IsOpen U36 := by
  have h : U36 = Complex.re ⁻¹' Ioo (-1) (1/2) ∩ Complex.im ⁻¹' Ioo (-1) 2 := by
    ext z; simp [U36, and_assoc]
  rw [h]
  exact (isOpen_Ioo.preimage Complex.continuous_re).inter
    (isOpen_Ioo.preimage Complex.continuous_im)

lemma norm_le_of_re_im {z : ℂ} {a : ℝ} (hre : |z.re| ≤ a) (him : |z.im| ≤ a) : ‖z‖ ≤ 2 * a := by
  have := Complex.norm_le_abs_re_add_abs_im z
  linarith

lemma isBounded_U36 : Bornology.IsBounded U36 := by
  refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := 4)).subset fun z hz => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_re_im (a := 2) (abs_le.2 ⟨by linarith, by linarith⟩)
    (abs_le.2 ⟨by linarith, by linarith⟩) |>.trans (by norm_num)

lemma isCompact_K36 : IsCompact K36 := by
  have h : K36 = Complex.re ⁻¹' Icc 0 (1/4) ∩ Complex.im ⁻¹' Icc 0 1 := by
    ext z; simp [K36, and_assoc]
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · rw [h]
    exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  · refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := 2)).subset fun z hz => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_of_re_im (a := 1) (abs_le.2 ⟨by linarith, by linarith⟩)
      (abs_le.2 ⟨by linarith, by linarith⟩) |>.trans (by norm_num)

lemma K36_nonempty : K36.Nonempty := ⟨0, by simp [K36]⟩

lemma K36_subset_U36 : K36 ⊆ U36 := fun z ⟨h1, h2, h3, h4⟩ =>
  ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma mem_rS_one {x : ℂ} : x ∈ rS 1 ↔ 0 < x.re ∧ x.re < 1 ∧ 0 < x.im ∧ x.im < 1 := by
  simp [rS, scaleSet]

lemma mem_frontier_U36 {p : ℂ} (hre : p.re = 1/2) (him0 : 0 ≤ p.im) (him1 : p.im ≤ 1) :
    p ∈ frontier U36 := by
  rw [isOpen_U36.frontier_eq]
  refine ⟨Metric.mem_closure_iff.2 fun e he => ?_, fun h => by linarith [h.2.1]⟩
  set c := min (e/2) (1/4) with hc
  have hc0 : 0 < c := lt_min (by linarith) (by norm_num)
  have hc1 : c ≤ 1/4 := min_le_right _ _
  have hc2 : c < e := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨p - c, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · rw [dist_eq_norm]
    simp [abs_of_pos hc0, hc2]

/-- leftmost vertices are within `ε` of the left side -/
lemma re_le_of_mem_leftVerts {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {x : ℂ}
    (hx : x ∈ leftVerts ε 1) : x.re ≤ ε := by
  have hy : (⟨((1:ℤ):ℝ) * ε, ((1:ℤ):ℝ) * ε⟩ : ℂ) ∈ rS 1 ∩ gridPts ε :=
    ⟨mem_rS_one.2 (by simp [hε, hε1]), ⟨1, 1, rfl⟩⟩
  have := hx.2 _ hy
  simpa using this

/-- rightmost vertices have real part `≥ 1/2` -/
lemma half_le_re_of_mem_rightVerts {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1/4) {x : ℂ}
    (hx : x ∈ rightVerts ε 1) : 1/2 ≤ x.re := by
  set a : ℤ := ⌈1 / (2 * ε)⌉ with ha
  have h1 : 1 / (2 * ε) ≤ (a:ℝ) := Int.le_ceil _
  have h2 : (a:ℝ) < 1 / (2 * ε) + 1 := Int.ceil_lt_add_one _
  have hlo : 1/2 ≤ (a:ℝ) * ε := by
    have := mul_le_mul_of_nonneg_right h1 hε.le
    have e : 1 / (2 * ε) * ε = 1/2 := by field_simp
    linarith
  have hhi : (a:ℝ) * ε < 1 := by
    have := mul_lt_mul_of_pos_right h2 hε
    have e : (1 / (2 * ε) + 1) * ε = 1/2 + ε := by field_simp
    linarith
  have hy : (⟨(a:ℝ) * ε, ((1:ℤ):ℝ) * ε⟩ : ℂ) ∈ rS 1 ∩ gridPts ε :=
    ⟨mem_rS_one.2 ⟨by linarith, hhi, by simp [hε], by simp; linarith⟩, ⟨a, 1, rfl⟩⟩
  have := hx.2 _ hy
  simp only at this
  linarith

lemma list_sum_map_eq_range (f : ℂ → ℝ) (L : List ℂ) :
    (L.map f).sum = ∑ i ∈ Finset.range L.length, f (L.getD i 0) := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-- **Crossing bound.** A graph path in `𝕊 ∩ εℤ²` from a leftmost to a rightmost vertex gives
`D^ε(K, ∂U) ≤ √2 ε e^{ξ osc_{8ε} φ} Σ_j e^{ξ φ(π(j))}`. -/
theorem dgSetDist_le_graphPath {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1/4) (φ : ℂ → ℝ)
    (hφ : Continuous φ) (ξ : ℝ) (hξ : 0 ≤ ξ) (L : List ℂ) (hL : IsGraphPath ε (rS 1) L)
    (h0 : ∃ x ∈ L.head?, x ∈ leftVerts ε 1) (h1 : ∃ y ∈ L.getLast?, y ∈ rightVerts ε 1) :
    dgSetDist ξ φ K36 U36 ≤ ENNReal.ofReal (Real.sqrt 2 * ε *
      Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ (8 * ε)) *
        (L.map fun x => Real.exp (ξ * φ x)).sum) := by
  set n := L.length with hn
  set V : ℕ → ℂ := fun i => L.getD i 0 with hVdef
  have hLne : L ≠ [] := hL.1
  have hnpos : 0 < n := List.length_pos_iff.2 hLne
  have hVmem : ∀ i < n, V i ∈ rS 1 ∧ V i ∈ gridPts ε := fun i hi => by
    have : V i = L[i] := (List.getElem_eq_getD (h := hi) 0).symm
    rw [this]; exact hL.2.1 _ (List.getElem_mem hi)
  have hVsq : ∀ i < n, 0 < (V i).re ∧ (V i).re < 1 ∧ 0 < (V i).im ∧ (V i).im < 1 :=
    fun i hi => mem_rS_one.1 (hVmem i hi).1
  have hstep : ∀ i, i + 1 < n → ‖V (i+1) - V i‖ ≤ Real.sqrt 2 * ε := fun i hi => by
    have hc := hL.2.2.getElem i hi
    have e1 : V i = L[i] := (List.getElem_eq_getD (h := by omega) 0).symm
    have e2 : V (i+1) = L[i+1] := (List.getElem_eq_getD (h := hi) 0).symm
    rw [e1, e2, norm_sub_rev]
    have hs : ε ≤ Real.sqrt 2 * ε := le_mul_of_one_le_left hε.le
      (Real.one_le_sqrt.2 (by norm_num))
    rcases hc with hc | hc <;> rw [hc]
    exact hs
  -- the first and last vertices
  obtain ⟨x, hx, hxl⟩ := h0
  obtain ⟨y, hy, hyr⟩ := h1
  have hV0 : V 0 = x := by
    rw [List.head?_eq_getElem?, Option.mem_def, List.getElem?_eq_some_iff] at hx
    obtain ⟨h, rfl⟩ := hx
    exact (List.getElem_eq_getD (h := h) 0).symm
  have hVn : V (n-1) = y := by
    rw [List.getLast?_eq_getElem?, Option.mem_def, List.getElem?_eq_some_iff] at hy
    obtain ⟨h, rfl⟩ := hy
    exact (List.getElem_eq_getD (h := h) 0).symm
  have hε1 : ε < 1 := by linarith
  have hx_re : x.re ≤ ε := re_le_of_mem_leftVerts hε hε1 hxl
  have hy_re : 1/2 ≤ y.re := half_le_re_of_mem_rightVerts hε hε4 hyr
  -- first index with `Re ≥ 1/2`
  have hex : ∃ k, k < n ∧ 1/2 ≤ (V k).re := ⟨n-1, by omega, by rw [hVn]; exact hy_re⟩
  classical
  set j := Nat.find hex with hj
  have hjspec := Nat.find_spec hex
  have hjmin : ∀ k < j, k < n → (V k).re < 1/2 := fun k hk hkn => by
    have := Nat.find_min hex hk
    push Not at this
    exact this hkn
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · have := hjspec.2
      rw [← hj, h, hV0] at this
      linarith
    · exact h
  have hjn : j < n := hjspec.1
  set a := V (j-1) with ha
  set b := V j with hb
  have ha_re : a.re < 1/2 := hjmin (j-1) (by omega) (by omega)
  have hb_re : 1/2 ≤ b.re := hjspec.2
  have hden : 0 < b.re - a.re := by linarith
  set t : ℝ := (1/2 - a.re) / (b.re - a.re) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hden.le
  have ht1 : t ≤ 1 := (div_le_one hden).2 (by linarith)
  set p : ℂ := a + t • (b - a) with hp
  have hp_re : p.re = 1/2 := by
    simp only [hp, Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, sub_zero]
    rw [ht]; field_simp; ring
  have haS := hVsq (j-1) (by omega)
  have hbS := hVsq j hjn
  have hp_im : p.im = (1 - t) * a.im + t * b.im := by
    simp only [hp, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, add_zero]
    ring
  have hp_im0 : 0 ≤ p.im := by rw [hp_im]; nlinarith
  have hp_im1 : p.im ≤ 1 := by rw [hp_im]; nlinarith
  -- the truncated polygon
  set W : ℕ → ℂ := fun k => if k < j then V k else p with hW
  have hW0 : W 0 = x := by simp [hW, hjpos, hV0]
  have hWj : W j = p := by simp [hW]
  have hWK : W 0 ∈ K36 := by
    rw [hW0]
    have := hVsq 0 hnpos
    rw [hV0] at this
    exact ⟨this.1.le, by linarith, this.2.2.1.le, this.2.2.2.le⟩
  have hWU : W j ∈ frontier U36 := by rw [hWj]; exact mem_frontier_U36 hp_re hp_im0 hp_im1
  have hWball : ∀ i ≤ j, ‖W i‖ ≤ 3 := fun i hi => by
    by_cases hij : i < j
    · simp only [hW, hij, if_true]
      have := hVsq i (by omega)
      exact (norm_le_of_re_im (a := 1) (abs_le.2 ⟨by linarith, by linarith⟩)
        (abs_le.2 ⟨by linarith, by linarith⟩)).trans (by norm_num)
    · simp only [hW, hij, if_false]
      exact (norm_le_of_re_im (a := 1) (abs_le.2 ⟨by linarith, by linarith⟩)
        (abs_le.2 ⟨by linarith, by linarith⟩)).trans (by norm_num)
  have hWlen : ∀ i < j, ‖W (i+1) - W i‖ ≤ Real.sqrt 2 * ε := fun i hi => by
    have hWi : W i = V i := by simp [hW, hi]
    rw [hWi]
    by_cases hij : i + 1 < j
    · have : W (i+1) = V (i+1) := by simp [hW, hij]
      rw [this]; exact hstep i (by omega)
    · have hij' : i + 1 = j := by omega
      have : W (i+1) = p := by rw [hij']; exact hWj
      rw [this]
      have hia : V i = a := by rw [ha]; congr 1; omega
      have hib : V (i+1) = b := by rw [hb, hij']
      rw [hia, hp, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]
      calc t * ‖b - a‖ ≤ 1 * ‖b - a‖ := by gcongr
        _ = ‖V (i+1) - V i‖ := by rw [one_mul, hib, hia]
        _ ≤ _ := hstep i (by omega)
  have hlen8 : ∀ i < j, ‖W (i+1) - W i‖ ≤ 8 * ε := fun i hi =>
    (hWlen i hi).trans (by
      have : Real.sqrt 2 ≤ 8 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      nlinarith)
  have hpoly := dgLFPP_le_poly W j hjpos φ hφ ξ hξ (8 * ε) hWball hlen8
  set O := LQGDimension.Blueprint.Draft.osc φ (8 * ε)
  have hsum : ∑ i ∈ Finset.range j, ‖W (i+1) - W i‖ * Real.exp (ξ * (φ (W i) + O)) ≤
      Real.sqrt 2 * ε * Real.exp (ξ * O) *
        (L.map fun x => Real.exp (ξ * φ x)).sum := by
    rw [list_sum_map_eq_range, Finset.mul_sum]
    calc ∑ i ∈ Finset.range j, ‖W (i+1) - W i‖ * Real.exp (ξ * (φ (W i) + O))
        ≤ ∑ i ∈ Finset.range j, Real.sqrt 2 * ε * Real.exp (ξ * O) *
            Real.exp (ξ * φ (L.getD i 0)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          have hWi : W i = L.getD i 0 := by simp [hW, hi', hVdef]
          have hl := hWlen i hi'
          rw [hWi] at hl ⊢
          rw [mul_add, Real.exp_add]
          calc ‖W (i+1) - L.getD i 0‖ * (Real.exp (ξ * φ (L.getD i 0)) * Real.exp (ξ * O))
              ≤ (Real.sqrt 2 * ε) * (Real.exp (ξ * φ (L.getD i 0)) * Real.exp (ξ * O)) :=
                mul_le_mul_of_nonneg_right hl (by positivity)
            _ = _ := by ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 hjn.le) fun _ _ _ => by positivity
  calc dgSetDist ξ φ K36 U36 ≤ ENNReal.ofReal (DG.dgLFPP ξ φ univ (W 0) (W j)) :=
        (iInf₂_le (W 0) hWK).trans (iInf₂_le (W j) hWU)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hpoly.trans hsum)

end LQGMetric.DFGPS.L36
