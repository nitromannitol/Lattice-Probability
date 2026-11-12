/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordMeanLimitAux3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordsAux1

/-!
# Node `M46` (`Draft.RecordMeanLimit`), auxiliary part 3: polygon geometry

* `constrPoly_eq_range`: the constrained polygon as the vertex list of a vertex function;
  `polyLen_constrPoly_ge`: its length is at least the chord length;
* `smallFamily_vertices`: a configuration of `smallFamily` as a vertex function;
* `geom_core`: a polygon with regular edges and small excess has forward edges (positive
  component along the chord) and small transversal increments (rotated coordinates `rot`);
* `constrPoly_eq_of_nodes`: such a polygon *is* the constrained polygon of its transversal
  profile.
-/

noncomputable section

open Filter Topology Set Real

namespace LQGDimension.RML

open Blueprint.Draft LFPPRecords

/-! ## The constrained polygon as a vertex function -/

/-- The horizontal increment of the `j`-th edge of `constrPoly`. -/
def cStep (M : ℕ) (δ : ℝ) (x y : ℂ) (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  (‖y - x‖ / M) * Real.sqrt (1 - (δ * M * (f ((j : ℝ) / M) - f (((j : ℝ) - 1) / M))) ^ 2)

/-- The vertex `i < M` of `constrPoly`. -/
def cVert (M : ℕ) (δ : ℝ) (x y : ℂ) (f : ℝ → ℝ) (i : ℕ) : ℂ :=
  x + (y - x) / ((‖y - x‖ : ℝ) : ℂ) * (((∑ j ∈ Finset.Icc 1 i, cStep M δ x y f j : ℝ) : ℂ) +
    ((δ * ‖y - x‖ * f ((i : ℝ) / M) : ℝ) : ℂ) * Complex.I)

lemma constrPoly_eq (M : ℕ) (δ : ℝ) (x y : ℂ) (f : ℝ → ℝ) :
    constrPoly M δ x y f = (List.range M).map (cVert M δ x y f) ++ [y] := rfl

/-- All vertices of `constrPoly` (the last one is `y`). -/
def cVert' (M : ℕ) (δ : ℝ) (x y : ℂ) (f : ℝ → ℝ) (i : ℕ) : ℂ :=
  if i < M then cVert M δ x y f i else y

lemma constrPoly_eq_range (M : ℕ) (δ : ℝ) (x y : ℂ) (f : ℝ → ℝ) :
    constrPoly M δ x y f = (List.range (M + 1)).map (cVert' M δ x y f) := by
  rw [constrPoly_eq, List.range_succ, List.map_append]
  congr 1
  · exact List.map_congr_left fun i hi => by simp [cVert', List.mem_range.1 hi]
  · simp [cVert']

lemma cVert_zero (M : ℕ) (δ : ℝ) (x y : ℂ) {f : ℝ → ℝ} (hf : f 0 = 0) :
    cVert M δ x y f 0 = x := by
  unfold cVert
  rw [Finset.Icc_eq_empty (by norm_num)]
  simp [hf]

lemma polyLen_constrPoly_ge {M : ℕ} (hM : 0 < M) (δ : ℝ) (x y : ℂ) {f : ℝ → ℝ} (hf : f 0 = 0) :
    ‖y - x‖ ≤ polyLen (constrPoly M δ x y f) := by
  rw [constrPoly_eq_range, polyLen_range_map]
  have h0 : cVert' M δ x y f 0 = x := by simp [cVert', hM, cVert_zero M δ x y hf]
  have hM' : cVert' M δ x y f M = y := by simp [cVert']
  calc ‖y - x‖ = ‖∑ i ∈ Finset.range M, (cVert' M δ x y f (i + 1) - cVert' M δ x y f i)‖ := by
        rw [Finset.sum_range_sub, h0, hM']
    _ ≤ _ := norm_sum_le _ _

/-! ## Configurations of `smallFamily` as vertex functions -/

lemma smallFamily_vertices {M : ℕ} {δ : ℝ} {k : ℕ} {c : Config} (hc : c ∈ smallFamily M δ k) :
    ∃ (x y : ℂ) (N : ℕ) (Z : ℕ → ℂ), c = ([x, y], (List.range (N + 2)).map Z) ∧
      Z 0 = x ∧ Z (N + 1) = y ∧ ‖x‖ ≤ cellRad M * δ ∧ ‖y - 1‖ ≤ cellRad M * δ ∧
      (∀ j < N, ‖Z (j + 1) - Z j‖ = ‖y - x‖ / M) ∧
      ‖y - x‖ / (2 * M) ≤ ‖Z (N + 1) - Z N‖ ∧ ‖Z (N + 1) - Z N‖ ≤ 3 * ‖y - x‖ / (2 * M) ∧
      Real.log ((∑ j ∈ Finset.range (N + 1), ‖Z (j + 1) - Z j‖) / ‖y - x‖) <
        ((k : ℝ) + 1) * δ ^ 2 := by
  obtain ⟨x, y, z, rfl, hhead, hlast, hx, hy, hl2, -, hreg, hlastE, -, hk2, -⟩ := hc
  obtain ⟨N, hN⟩ : ∃ N, z.length = N + 2 := ⟨z.length - 2, by omega⟩
  set Z : ℕ → ℂ := fun i => z.getD i 0 with hZ
  have hz : z = (List.range (N + 2)).map Z := by
    apply List.ext_getElem
    · simp [hN]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, hZ]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]
  have hedges : edges z = (List.range (N + 1)).map (fun i => (Z i, Z (i + 1))) := by
    rw [hz]; exact edges_range_map Z (N + 1)
  have hgl : (edges z).getLast? = some (Z N, Z (N + 1)) := by
    rw [hedges, List.range_succ, List.map_append]
    simp
  refine ⟨x, y, N, Z, by rw [← hz], ?_, ?_, hx, hy, ?_, ?_, ?_, ?_⟩
  · show z.getD 0 0 = x
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, hhead, Option.getD_some]
  · show z.getD (N + 1) 0 = y
    rw [List.getD_eq_getElem?_getD, show N + 1 = z.length - 1 by omega,
      ← List.getLast?_eq_getElem?, hlast, Option.getD_some]
  · intro j hj
    refine hreg (Z j, Z (j + 1)) ?_
    rw [hedges, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.dropLast_concat]
    exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  · exact (hlastE (Z N, Z (N + 1)) (Option.mem_def.2 hgl)).1
  · exact (hlastE (Z N, Z (N + 1)) (Option.mem_def.2 hgl)).2
  · rw [hz, polyLen_range_map] at hk2
    exact hk2

/-! ## Geometry of polygons with small excess -/

/-- Rotated coordinates relative to the chord `[x, y]`: `(z - x) / e`, `e = (y - x) / |y - x|`. -/
def rot (x y z : ℂ) : ℂ := (z - x) / ((y - x) / ((‖y - x‖ : ℝ) : ℂ))

lemma norm_dir {x y : ℂ} (hR : 0 < ‖y - x‖) : ‖(y - x) / ((‖y - x‖ : ℝ) : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_self hR.ne']

lemma dir_ne_zero {x y : ℂ} (hR : 0 < ‖y - x‖) : (y - x) / ((‖y - x‖ : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := norm_dir hR
  rw [h, norm_zero] at this
  exact zero_ne_one this

lemma rot_sub (x y z w : ℂ) : rot x y z - rot x y w = (z - w) / ((y - x) / ((‖y - x‖ : ℝ) : ℂ)) := by
  unfold rot
  ring

lemma norm_rot_sub {x y : ℂ} (hR : 0 < ‖y - x‖) (z w : ℂ) : ‖rot x y z - rot x y w‖ = ‖z - w‖ := by
  rw [rot_sub, norm_div, norm_dir hR, div_one]

lemma rot_self (x y : ℂ) : rot x y x = 0 := by simp [rot]

lemma rot_end {x y : ℂ} (hR : 0 < ‖y - x‖) : rot x y y = ((‖y - x‖ : ℝ) : ℂ) := by
  have h1 : y - x ≠ 0 := fun h => by rw [h, norm_zero] at hR; exact lt_irrefl _ hR
  have h2 : ((‖y - x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold rot
  field_simp

lemma mul_rot {x y : ℂ} (hR : 0 < ‖y - x‖) (z : ℂ) :
    x + (y - x) / ((‖y - x‖ : ℝ) : ℂ) * rot x y z = z := by
  unfold rot
  rw [mul_div_cancel₀ _ (dir_ne_zero hR)]
  ring

/-- **Forward edges and transversal increments.**  For a polygon `Z 0 = x, …, Z M = y` whose
first `M - 1` edges have length `R / M` (`R = |y - x|`) and whose length exceeds `R` by at most
`η R` with `η < 1/M`, all regular edges point forwards and have squared transversal increment at
most `2 R² η` in the rotated coordinates. -/
lemma geom_core {M : ℕ} (hM : 0 < M) {Z : ℕ → ℂ} {x y : ℂ} (hZ0 : Z 0 = x) (hZM : Z M = y)
    (hR : 0 < ‖y - x‖) (hreg : ∀ j, j + 1 < M → ‖Z (j + 1) - Z j‖ = ‖y - x‖ / M) {η : ℝ}
    (hS : (∑ j ∈ Finset.range M, ‖Z (j + 1) - Z j‖) - ‖y - x‖ ≤ η * ‖y - x‖)
    (hη : η < 1 / M) :
    (∀ j, j + 1 < M → 0 < (rot x y (Z (j + 1)) - rot x y (Z j)).re) ∧
    (∀ j, j + 1 < M → (rot x y (Z (j + 1)) - rot x y (Z j)).im ^ 2 ≤ 2 * ‖y - x‖ ^ 2 * η) := by
  set R := ‖y - x‖ with hRdef
  set u : ℕ → ℂ := fun j => rot x y (Z (j + 1)) - rot x y (Z j) with hu
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hnorm : ∀ j, ‖u j‖ = ‖Z (j + 1) - Z j‖ := fun j => norm_rot_sub hR _ _
  have hsum : ∑ j ∈ Finset.range M, u j = (R : ℂ) := by
    rw [Finset.sum_range_sub (fun i => rot x y (Z i)) M, hZM, hZ0, rot_self, sub_zero,
      rot_end hR]
  have htot : ∑ j ∈ Finset.range M, (‖u j‖ - (u j).re) =
      (∑ j ∈ Finset.range M, ‖Z (j + 1) - Z j‖) - R := by
    rw [Finset.sum_sub_distrib, ← Complex.re_sum, hsum, Complex.ofReal_re]
    simp only [hnorm]
  have hnn : ∀ j, 0 ≤ ‖u j‖ - (u j).re := fun j => sub_nonneg.2 (Complex.re_le_norm _)
  have hsingle : ∀ j < M, ‖u j‖ - (u j).re ≤ η * R := by
    intro j hj
    refine le_trans ?_ (htot ▸ hS)
    exact Finset.single_le_sum (f := fun j => ‖u j‖ - (u j).re) (fun j _ => hnn j)
      (Finset.mem_range.2 hj)
  have hηR : η * R < R / M := by
    rw [lt_div_iff₀ hMr]
    have := mul_lt_mul_of_pos_right hη hR
    rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ hMr] at this
    linarith
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have h1 := hsingle j (by omega)
    have h2 : ‖u j‖ = R / M := by rw [hnorm, hreg j hj]
    change 0 < (u j).re
    linarith
  · have h1 := hsingle j (by omega)
    have h2 : ‖u j‖ = R / M := by rw [hnorm, hreg j hj]
    have hsq : ‖u j‖ ^ 2 = (u j).re ^ 2 + (u j).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hre : -‖u j‖ ≤ (u j).re := by
      have := Complex.abs_re_le_norm (u j)
      rw [abs_le] at this
      exact this.1
    have hR1 : R / M ≤ R := div_le_self hR.le (by exact_mod_cast hM)
    have hη0 : 0 ≤ η * R := (hnn j).trans h1
    change (u j).im ^ 2 ≤ 2 * R ^ 2 * η
    have e : (u j).im ^ 2 = (‖u j‖ - (u j).re) * (‖u j‖ + (u j).re) := by nlinarith
    rw [e]
    calc (‖u j‖ - (u j).re) * (‖u j‖ + (u j).re) ≤ (η * R) * (2 * R) := by
          apply mul_le_mul h1 _ (by linarith) hη0
          have := Complex.re_le_norm (u j)
          linarith
      _ = 2 * R ^ 2 * η := by ring

/-- A telescoping reindexing of sums over `Icc 1 i`. -/
lemma sum_Icc_one_eq (g : ℕ → ℝ) (i : ℕ) :
    ∑ j ∈ Finset.Icc 1 i, g (j - 1) = ∑ j ∈ Finset.range i, g j := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    simp

/-- **Identification with the constrained parametrization.**  A polygon `Z 0 = x, …, Z M = y`
with regular forward edges is `constrPoly M δ x y f` for any `f` with the node values
`f (j/M) = Im rot(Z j) / (δ R)`. -/
lemma constrPoly_eq_of_nodes {M : ℕ} (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ) {x y : ℂ} {Z : ℕ → ℂ}
    (hZ0 : Z 0 = x) (hZM : Z M = y) (hR : 0 < ‖y - x‖)
    (hreg : ∀ j, j + 1 < M → ‖Z (j + 1) - Z j‖ = ‖y - x‖ / M)
    (hfwd : ∀ j, j + 1 < M → 0 < (rot x y (Z (j + 1)) - rot x y (Z j)).re)
    {f : ℝ → ℝ} (hf : ∀ j ≤ M, f ((j : ℝ) / M) = (rot x y (Z j)).im / (δ * ‖y - x‖)) :
    constrPoly M δ x y f = (List.range (M + 1)).map Z := by
  set R := ‖y - x‖ with hRdef
  set W : ℕ → ℂ := fun i => rot x y (Z i) with hW
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hδR : δ * R ≠ 0 := (mul_pos hδ hR).ne'
  have hW0 : W 0 = 0 := by simp only [hW, hZ0, rot_self]
  -- the horizontal increments
  have hstep : ∀ j, 1 ≤ j → j < M → cStep M δ x y f j = (W j - W (j - 1)).re := by
    intro j hj1 hjM
    have hj' : j - 1 + 1 = j := Nat.sub_add_cancel hj1
    have hc : ((j : ℝ) - 1) = ((j - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hj1, Nat.cast_one]
    set u := W j - W (j - 1) with hu
    have hre : 0 < u.re := by
      have := hfwd (j - 1) (by omega)
      rw [hj'] at this
      exact this
    have hnorm : ‖u‖ = R / M := by
      have := hreg (j - 1) (by omega)
      rw [hj'] at this
      rw [hu, hW]
      simp only
      rw [norm_rot_sub hR, this]
    have hsq : u.re ^ 2 = (R / M) ^ 2 - u.im ^ 2 := by
      rw [← hnorm, Complex.sq_norm, Complex.normSq_apply]; ring
    have hdiff : δ * M * (f ((j : ℝ) / M) - f (((j : ℝ) - 1) / M)) = M * u.im / R := by
      rw [hc, hf j hjM.le, hf (j - 1) (by omega), hu, Complex.sub_im]
      simp only [hW]
      field_simp
    have hRM : R / M ≠ 0 := (div_pos hR hMr).ne'
    have key : 1 - (M * u.im / R) ^ 2 = (u.re / (R / M)) ^ 2 := by
      rw [div_pow u.re, hsq]
      field_simp
    unfold cStep
    rw [hdiff, key, Real.sqrt_sq (div_pos hre (div_pos hR hMr)).le, mul_div_cancel₀ _ hRM]
  have hhor : ∀ i < M, ∑ j ∈ Finset.Icc 1 i, cStep M δ x y f j = (W i).re := by
    intro i hi
    calc ∑ j ∈ Finset.Icc 1 i, cStep M δ x y f j
        = ∑ j ∈ Finset.Icc 1 i, (W (j - 1 + 1) - W (j - 1)).re := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.mem_Icc] at hj
          rw [hstep j hj.1 (by omega), Nat.sub_add_cancel hj.1]
      _ = ∑ j ∈ Finset.range i, (W (j + 1) - W j).re :=
          sum_Icc_one_eq (fun j => (W (j + 1) - W j).re) i
      _ = (W i).re := by
          rw [← Complex.re_sum, Finset.sum_range_sub W i, hW0, sub_zero]
  rw [constrPoly_eq_range]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  unfold cVert'
  split_ifs with h
  · unfold cVert
    rw [hhor i h, hf i h.le, mul_div_cancel₀ _ hδR]
    have e : (((W i).re : ℝ) : ℂ) + (((W i).im : ℝ) : ℂ) * Complex.I = W i := Complex.re_add_im _
    rw [e]
    exact mul_rot hR (Z i)
  · have : i = M := by omega
    rw [this, hZM]

end LQGDimension.RML
