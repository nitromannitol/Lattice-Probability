/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.ConstrainedCovPoly at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import LatticeProb.Bonanno.LQGDimension.Section2.SubadditiveAux

/-!
# The constrained polygon of Lemma 3.2 (third parametrization)

Geometry of `constrPoly M δ x y f`:

* it is the image of the *unit* constrained polygon (chord `[0,1]`) with vertices `uv M δ f i`
  under the complex-affine map `z ↦ x + (y - x) z` (`constrPoly_eq`);
* its length is `‖y - x‖ * uLen M δ f` (`polyLen_constrPoly`);
* the energy expansion (3.3): `δ⁻² log (uLen M δ f) → E(f)`, with the explicit error
  `3 (2 B M)⁴ δ²` for `|f| ≤ B` (`abs_log_uLen_sub_energy_le`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.ConstrCov

open Blueprint.Draft

/-! ## Definitions -/

/-- Scaled slope `a_j = δ M (f(j/M) - f((j-1)/M))` of the `j`-th edge. -/
def aj (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  δ * M * (f ((j : ℝ) / M) - f (((j : ℝ) - 1) / M))

/-- Horizontal increment of the `j`-th edge of the unit constrained polygon. -/
def hstep (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  (1 / (M : ℝ)) * Real.sqrt (1 - (δ * M * (f ((j : ℝ) / M) - f (((j : ℝ) - 1) / M))) ^ 2)

/-- Horizontal position of the `i`-th vertex of the unit constrained polygon. -/
def hor1 (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 i, hstep M δ f j

/-- Vertices of the unit constrained polygon (chord `[0,1]`); the last one is `1`. -/
def uv (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) : ℂ :=
  if i < M then (hor1 M δ f i : ℂ) + ((δ * f ((i : ℝ) / M) : ℝ) : ℂ) * Complex.I else 1

/-- Length of the unit constrained polygon. -/
def uLen (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, ‖uv M δ f (i + 1) - uv M δ f i‖

lemma hstep_eq (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (j : ℕ) :
    hstep M δ f j = (1 / (M : ℝ)) * Real.sqrt (1 - aj M δ f j ^ 2) := rfl

lemma aj_succ (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) :
    aj M δ f (i + 1) = δ * M * (f (((i : ℝ) + 1) / M) - f ((i : ℝ) / M)) := by
  simp only [aj, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]

lemma hor1_succ (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) :
    hor1 M δ f (i + 1) = hor1 M δ f i + hstep M δ f (i + 1) := by
  unfold hor1; rw [Finset.sum_Icc_succ_top (by omega)]

/-! ## The affine structure -/

lemma constrPoly_eq (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) {x y : ℂ} (hxy : x ≠ y) :
    constrPoly M δ x y f = (List.range (M + 1)).map (fun i => x + (y - x) * uv M δ f i) := by
  have hR0 : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  have hR : ((‖y - x‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0
  simp only [constrPoly]
  rw [List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · refine List.map_congr_left (fun i hi => ?_)
    rw [List.mem_range] at hi
    simp only [uv, hi, if_true]
    have hsum : ∑ j ∈ Finset.Icc 1 i, ‖y - x‖ / (M : ℝ) *
        Real.sqrt (1 - (δ * M * (f ((j : ℝ) / M) - f (((j : ℝ) - 1) / M))) ^ 2) =
        ‖y - x‖ * hor1 M δ f i := by
      rw [hor1, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; unfold hstep; ring
    rw [hsum]
    push_cast
    field_simp
  · simp [uv]

lemma edges_map_range' (v : ℕ → ℂ) (M : ℕ) :
    edges ((List.range (M + 1)).map v) = (List.range M).map fun i : ℕ => (v i, v (i + 1)) := by
  unfold edges
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp

lemma list_sum_map_range' (n : ℕ) (F : ℕ → ℝ) :
    ((List.range n).map F).sum = ∑ i ∈ Finset.range n, F i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma edges_constrPoly (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) {x y : ℂ} (hxy : x ≠ y) :
    edges (constrPoly M δ x y f) = (List.range M).map fun i : ℕ =>
      (x + (y - x) * uv M δ f i, x + (y - x) * uv M δ f (i + 1)) := by
  rw [constrPoly_eq M δ f hxy, edges_map_range']

lemma polyLen_constrPoly (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) {x y : ℂ} (hxy : x ≠ y) :
    polyLen (constrPoly M δ x y f) = ‖y - x‖ * uLen M δ f := by
  unfold polyLen
  rw [edges_constrPoly M δ f hxy, List.map_map, list_sum_map_range', uLen, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp]
  rw [show x + (y - x) * uv M δ f (i + 1) - (x + (y - x) * uv M δ f i) =
    (y - x) * (uv M δ f (i + 1) - uv M δ f i) by ring, norm_mul]

lemma polyComb_constrPoly (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) {x y : ℂ} (hxy : x ≠ y) :
    polyComb (constrPoly M δ x y f) = (List.range M).map fun i : ℕ =>
      (‖uv M δ f (i + 1) - uv M δ f i‖ / uLen M δ f,
        x + (y - x) * uv M δ f i, x + (y - x) * uv M δ f (i + 1)) := by
  have hR0 : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  unfold polyComb
  rw [polyLen_constrPoly M δ f hxy, edges_constrPoly M δ f hxy, List.map_map]
  refine List.map_congr_left (fun i _ => ?_)
  simp only [Function.comp]
  congr 1
  rw [show x + (y - x) * uv M δ f (i + 1) - (x + (y - x) * uv M δ f i) =
    (y - x) * (uv M δ f (i + 1) - uv M δ f i) by ring, norm_mul]
  field_simp

/-! ## Edge lengths -/

lemma norm_ofReal_add_mul_I (r s : ℝ) : ‖((r : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I‖ =
    Real.sqrt (r ^ 2 + s ^ 2) := Complex.norm_add_mul_I r s

lemma uv_succ_sub {M : ℕ} (δ : ℝ) (f : ℝ → ℝ) {i : ℕ} (hi : i + 1 < M) :
    uv M δ f (i + 1) - uv M δ f i = ((hstep M δ f (i + 1) : ℝ) : ℂ) +
      ((δ * (f (((i : ℝ) + 1) / M) - f ((i : ℝ) / M)) : ℝ) : ℂ) * Complex.I := by
  have hi' : i < M := by omega
  simp only [uv, hi, hi', if_true, hor1_succ]
  push_cast
  ring

/-- Every edge but the last has length exactly `1/M`. -/
lemma norm_uv_step {M : ℕ} (δ : ℝ) (f : ℝ → ℝ) {i : ℕ} (hi : i + 1 < M)
    (ha : aj M δ f (i + 1) ^ 2 ≤ 1) :
    ‖uv M δ f (i + 1) - uv M δ f i‖ = 1 / M := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [uv_succ_sub δ f hi, norm_ofReal_add_mul_I, hstep_eq, aj_succ]
  rw [aj_succ] at ha
  have e : (1 / (M : ℝ) * Real.sqrt (1 - (δ * M * (f (((i : ℝ) + 1) / M) - f ((i : ℝ) / M))) ^ 2))
      ^ 2 + (δ * (f (((i : ℝ) + 1) / M) - f ((i : ℝ) / M))) ^ 2 = (1 / (M : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    field_simp
    ring
  rw [e, Real.sqrt_sq (by positivity)]


/-! ## Elementary inequalities -/

/-- `0 ≤ (1 - √(1-t)) - t/2 ≤ t²/2` for `0 ≤ t ≤ 1`. -/
lemma one_sub_sqrt_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (1 - Real.sqrt (1 - t)) - t / 2 ∧ (1 - Real.sqrt (1 - t)) - t / 2 ≤ t ^ 2 / 2 := by
  set r := Real.sqrt (1 - t) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 1 - t := Real.sq_sqrt (by linarith)
  have hr1 : r ≤ 1 := by nlinarith
  have e : (1 - r) - t / 2 = (1 - r) ^ 2 / 2 := by nlinarith
  rw [e]
  refine ⟨by positivity, ?_⟩
  have h1 : 1 - r ≤ t := by nlinarith
  have h2 : 0 ≤ 1 - r := by linarith
  have : (1 - r) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ h2 h1 2
  linarith

/-- `0 ≤ u + t/2 - √(u² + t) ≤ t(u - 1) + t²` for `u ≥ 1`, `t ≥ 0`. -/
lemma sqrt_sq_add_bounds {u t : ℝ} (hu : 1 ≤ u) (ht : 0 ≤ t) :
    0 ≤ u + t / 2 - Real.sqrt (u ^ 2 + t) ∧
      u + t / 2 - Real.sqrt (u ^ 2 + t) ≤ t * (u - 1) + t ^ 2 := by
  set r := Real.sqrt (u ^ 2 + t) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = u ^ 2 + t := Real.sq_sqrt (by positivity)
  have hru : u ≤ r := by nlinarith
  have key : (u + t / 2 - r) * (u + t / 2 + r) = t * (u - 1) + t ^ 2 / 4 := by nlinarith
  have hpos : 2 ≤ u + t / 2 + r := by linarith
  have hnn : 0 ≤ t * (u - 1) + t ^ 2 / 4 := by
    have : 0 ≤ t * (u - 1) := mul_nonneg ht (by linarith)
    positivity
  have h0 : 0 ≤ u + t / 2 - r := by
    by_contra h
    rw [not_le] at h
    nlinarith
  refine ⟨h0, ?_⟩
  nlinarith

/-- The key estimate behind (3.3): with `S = Σ (1 - √(1 - t_j))`,
`L = m/(m+1) + √((1+S)² + t_M)/(m+1)` satisfies `1 ≤ L ≤ 1 + η` and
`|log L - (Σ t_j + t_M)/(2(m+1))| ≤ 3 η²` when all `t ≤ η ≤ 1/4`. -/
lemma log_len_est (m : ℕ) (t : ℕ → ℝ) {tM η : ℝ} (hη : η ≤ 1 / 4)
    (ht0 : ∀ j, 0 ≤ t j) (htη : ∀ j, t j ≤ η) (htM0 : 0 ≤ tM) (htMη : tM ≤ η) :
    1 ≤ (m : ℝ) / (m + 1) + (1 / ((m : ℝ) + 1)) *
        Real.sqrt ((1 + ∑ j ∈ Finset.Icc 1 m, (1 - Real.sqrt (1 - t j))) ^ 2 + tM) ∧
    (m : ℝ) / (m + 1) + (1 / ((m : ℝ) + 1)) *
        Real.sqrt ((1 + ∑ j ∈ Finset.Icc 1 m, (1 - Real.sqrt (1 - t j))) ^ 2 + tM) - 1 ≤ η ∧
    |Real.log ((m : ℝ) / (m + 1) + (1 / ((m : ℝ) + 1)) *
        Real.sqrt ((1 + ∑ j ∈ Finset.Icc 1 m, (1 - Real.sqrt (1 - t j))) ^ 2 + tM)) -
      (∑ j ∈ Finset.Icc 1 m, t j + tM) / (2 * ((m : ℝ) + 1))| ≤ 3 * η ^ 2 := by
  have hη0 : 0 ≤ η := (ht0 0).trans (htη 0)
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set S := ∑ j ∈ Finset.Icc 1 m, (1 - Real.sqrt (1 - t j)) with hS
  set T := ∑ j ∈ Finset.Icc 1 m, t j with hT
  have hcard : ((Finset.Icc 1 m).card : ℝ) = m := by simp
  have hb := fun j => one_sub_sqrt_bounds (ht0 j) ((htη j).trans (by linarith))
  have hsq_le : ∀ j, t j ^ 2 ≤ t j := fun j => by
    rw [sq]; exact mul_le_of_le_one_right (ht0 j) (by linarith [htη j])
  -- `0 ≤ S ≤ T ≤ m η`, `0 ≤ S - T/2 ≤ m η²/2`
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => by linarith [(hb j).1, ht0 j]
  have hST : S ≤ T := Finset.sum_le_sum fun j _ => by linarith [(hb j).2, hsq_le j]
  have hTm : T ≤ m * η := by
    calc T ≤ ∑ j ∈ Finset.Icc 1 m, η := Finset.sum_le_sum fun j _ => htη j
      _ = m * η := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hSTa : S - T / 2 = ∑ j ∈ Finset.Icc 1 m, ((1 - Real.sqrt (1 - t j)) - t j / 2) := by
    rw [hS, hT, Finset.sum_div, ← Finset.sum_sub_distrib]
  have hSTb : 0 ≤ S - T / 2 ∧ S - T / 2 ≤ m * η ^ 2 / 2 := by
    rw [hSTa]
    refine ⟨Finset.sum_nonneg fun j _ => (hb j).1, ?_⟩
    calc ∑ j ∈ Finset.Icc 1 m, ((1 - Real.sqrt (1 - t j)) - t j / 2)
        ≤ ∑ j ∈ Finset.Icc 1 m, η ^ 2 / 2 := Finset.sum_le_sum fun j _ => by
          have h1 := (hb j).2
          have h2 : t j ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (ht0 j) (htη j) 2
          linarith
      _ = m * η ^ 2 / 2 := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
  -- the square root
  set r := Real.sqrt ((1 + S) ^ 2 + tM) with hr
  have hsq := sqrt_sq_add_bounds (u := 1 + S) (t := tM) (by linarith) htM0
  rw [← hr] at hsq
  have hr1 : 1 + S ≤ r := by
    have h := Real.sqrt_le_sqrt (show (1 + S) ^ 2 ≤ (1 + S) ^ 2 + tM by linarith)
    rwa [Real.sqrt_sq (by linarith)] at h
  set L := (m : ℝ) / (m + 1) + (1 / ((m : ℝ) + 1)) * r with hL
  have hLr : ((m : ℝ) + 1) * (L - 1) = r - 1 := by rw [hL]; field_simp; ring
  have hL1 : 1 ≤ L := by nlinarith
  set E := (T + tM) / (2 * ((m : ℝ) + 1)) with hE
  have hmE : ((m : ℝ) + 1) * E = (T + tM) / 2 := by rw [hE]; field_simp
  have hEη : E ≤ η / 2 := by
    have : ((m : ℝ) + 1) * E ≤ ((m : ℝ) + 1) * (η / 2) := by rw [hmE]; linarith
    exact le_of_mul_le_mul_left this hm1
  -- `|L - 1 - E| ≤ 2 η²`
  have hdiff : |L - 1 - E| ≤ 2 * η ^ 2 := by
    have e : ((m : ℝ) + 1) * (L - 1 - E) = -(1 + S + tM / 2 - r) + (S - T / 2) := by
      rw [mul_sub, hLr, hmE]; ring
    have h1 : 1 + S + tM / 2 - r ≤ tM * S + tM ^ 2 := by
      have := hsq.2; ring_nf at this ⊢; linarith
    have h2 : tM * S ≤ η * (m * η) := mul_le_mul htMη (hST.trans hTm) hS0 hη0
    have h3 : tM ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ htM0 htMη 2
    have hb2 : |((m : ℝ) + 1) * (L - 1 - E)| ≤ ((m : ℝ) + 1) * (2 * η ^ 2) := by
      rw [e, abs_le]
      have hmη : (0 : ℝ) ≤ m * η ^ 2 := by positivity
      constructor
      · have : η * (m * η) = m * η ^ 2 := by ring
        linarith [hsq.1, hSTb.1]
      · linarith [hsq.1, hSTb.2, sq_nonneg η]
    rw [abs_mul, abs_of_pos hm1] at hb2
    exact le_of_mul_le_mul_left hb2 hm1
  have hη2 : 2 * η ^ 2 ≤ η / 2 := by nlinarith
  have hL1η : L - 1 ≤ η := by linarith [(abs_le.1 hdiff).2]
  refine ⟨hL1, hL1η, ?_⟩
  -- `|log L - (L - 1)| ≤ (L - 1)²`
  have hlog1 : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlog2 : (L - 1) - (L - 1) ^ 2 ≤ Real.log L := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < L by linarith)
    have : (L - 1) - (L - 1) ^ 2 ≤ 1 - L⁻¹ := by
      rw [show 1 - L⁻¹ = (L - 1) / L by field_simp]
      rw [le_div_iff₀ (by linarith)]
      nlinarith [sq_nonneg (L - 1)]
    linarith
  have hsqL : (L - 1) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (by linarith) hL1η 2
  rw [abs_le]
  constructor
  · linarith [(abs_le.1 hdiff).1]
  · linarith [(abs_le.1 hdiff).2]

/-! ## The length of the unit polygon and the energy -/

lemma sum_Icc_one_eq_range (g : ℕ → ℝ) (i : ℕ) :
    ∑ j ∈ Finset.Icc 1 i, g j = ∑ k ∈ Finset.range i, g (k + 1) := by
  induction i with
  | zero => simp
  | succ i ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma one_sub_hor1 (m : ℕ) (δ : ℝ) (f : ℝ → ℝ) :
    1 - hor1 (m + 1) δ f m = (1 / ((m : ℝ) + 1)) *
      (1 + ∑ j ∈ Finset.Icc 1 m, (1 - Real.sqrt (1 - aj (m + 1) δ f j ^ 2))) := by
  unfold hor1
  simp only [hstep_eq]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
  simp only [add_tsub_cancel_right, nsmul_eq_mul, mul_one]
  push_cast
  field_simp
  ring

lemma uv_last_sub (m : ℕ) (δ : ℝ) (f : ℝ → ℝ) (hf1 : f 1 = 0) :
    uv (m + 1) δ f (m + 1) - uv (m + 1) δ f m =
      ((1 - hor1 (m + 1) δ f m : ℝ) : ℂ) +
        ((aj (m + 1) δ f (m + 1) / ((m : ℝ) + 1) : ℝ) : ℂ) * Complex.I := by
  have h1 : ¬ (m + 1 < m + 1) := lt_irrefl _
  have h2 : m < m + 1 := Nat.lt_succ_self m
  simp only [uv, h1, h2, if_true, if_false]
  have ha : aj (m + 1) δ f (m + 1) / ((m : ℝ) + 1) =
      -(δ * f ((m : ℝ) / ((m + 1 : ℕ) : ℝ))) := by
    unfold aj
    have e1 : ((m + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) = 1 := div_self (by positivity)
    have e2 : (((m + 1 : ℕ) : ℝ) - 1) / ((m + 1 : ℕ) : ℝ) = (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [e1, e2, hf1]
    push_cast
    field_simp
    ring
  rw [ha]
  push_cast
  ring

/-- `S(f) = Σ_{j ≤ m} (1 - √(1 - a_j²))`, the relative horizontal shortening. -/
def shortS (m : ℕ) (δ : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 m, (1 - Real.sqrt (1 - aj (m + 1) δ f j ^ 2))

lemma norm_uv_last (m : ℕ) (δ : ℝ) (f : ℝ → ℝ) (hf1 : f 1 = 0) :
    ‖uv (m + 1) δ f (m + 1) - uv (m + 1) δ f m‖ = (1 / ((m : ℝ) + 1)) *
      Real.sqrt ((1 + shortS m δ f) ^ 2 + aj (m + 1) δ f (m + 1) ^ 2) := by
  rw [uv_last_sub m δ f hf1, norm_ofReal_add_mul_I, one_sub_hor1]
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [show (1 / ((m : ℝ) + 1) * (1 + ∑ j ∈ Finset.Icc 1 m,
      (1 - Real.sqrt (1 - aj (m + 1) δ f j ^ 2)))) ^ 2 + (aj (m + 1) δ f (m + 1) / ((m : ℝ) + 1)) ^ 2
      = (1 / ((m : ℝ) + 1)) ^ 2 * ((1 + shortS m δ f) ^ 2 + aj (m + 1) δ f (m + 1) ^ 2) by
    unfold shortS; field_simp]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

lemma uLen_eq (m : ℕ) (δ : ℝ) (f : ℝ → ℝ) (hf1 : f 1 = 0)
    (ha : ∀ j, 1 ≤ j → j ≤ m → aj (m + 1) δ f j ^ 2 ≤ 1) :
    uLen (m + 1) δ f = (m : ℝ) / (m + 1) + (1 / ((m : ℝ) + 1)) *
      Real.sqrt ((1 + shortS m δ f) ^ 2 + aj (m + 1) δ f (m + 1) ^ 2) := by
  unfold uLen
  rw [Finset.sum_range_succ, norm_uv_last m δ f hf1]
  have h : ∀ i ∈ Finset.range m, ‖uv (m + 1) δ f (i + 1) - uv (m + 1) δ f i‖ =
      1 / ((m : ℝ) + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_uv_step δ f (by omega) (ha (i + 1) (by omega) (by omega))]
    push_cast; ring
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The energy of `f ∈ V n` in terms of the scaled slopes. -/
lemma energy_eq_aj {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) (δ : ℝ) :
    δ ^ 2 * energy f =
      (∑ k ∈ Finset.range (16 ^ n), aj (16 ^ n) δ f (k + 1) ^ 2) / (2 * ((16 ^ n : ℕ) : ℝ)) := by
  rw [Subadd.V_energy hf, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [aj_succ]
  push_cast
  field_simp

lemma abs_aj_le {M : ℕ} {δ B : ℝ} {f : ℝ → ℝ} (hδ : 0 ≤ δ) (hfB : ∀ x, |f x| ≤ B) (j : ℕ) :
    |aj M δ f j| ≤ 2 * B * M * δ := by
  unfold aj
  rw [abs_mul, abs_mul, abs_of_nonneg hδ, Nat.abs_cast]
  have h := abs_sub (f ((j : ℝ) / M)) (f (((j : ℝ) - 1) / M))
  have h1 := hfB ((j : ℝ) / M)
  have h2 := hfB (((j : ℝ) - 1) / M)
  calc δ * (M : ℝ) * |f ((j : ℝ) / M) - f (((j : ℝ) - 1) / M)| ≤ δ * (M : ℝ) * (2 * B) := by
        gcongr; linarith
    _ = 2 * B * M * δ := by ring

/-- **The energy expansion (3.3)**, with an explicit error. -/
theorem uLen_energy_est (n : ℕ) {B δ : ℝ} {f : ℝ → ℝ} (hf : f ∈ V n) (hfB : ∀ x, |f x| ≤ B)
    (hδ : 0 < δ) (hsmall : (2 * B * (16 : ℝ) ^ n * δ) ^ 2 ≤ 1 / 4) :
    1 ≤ uLen (16 ^ n) δ f ∧ uLen (16 ^ n) δ f - 1 ≤ (2 * B * (16 : ℝ) ^ n * δ) ^ 2 ∧
      |δ ^ (-2 : ℤ) * Real.log (uLen (16 ^ n) δ f) - energy f| ≤
        3 * (2 * B * (16 : ℝ) ^ n) ^ 4 * δ ^ 2 := by
  obtain ⟨m, hm⟩ : ∃ m, 16 ^ n = m + 1 := ⟨16 ^ n - 1, by
    have := Nat.one_le_pow n 16 (by norm_num); omega⟩
  have hmR : (16 : ℝ) ^ n = (m : ℝ) + 1 := by exact_mod_cast hm
  have hf1 : f 1 = 0 := hf.2.1
  set η := (2 * B * (16 : ℝ) ^ n * δ) ^ 2 with hη
  have haη : ∀ j, aj (m + 1) δ f j ^ 2 ≤ η := fun j => by
    rw [hη, hmR, ← sq_abs]
    have := abs_aj_le (M := m + 1) hδ.le hfB j
    push_cast at this
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hleq := uLen_eq m δ f hf1 (fun j _ _ => (haη j).trans (by linarith))
  obtain ⟨hL1, hL1η, hlog⟩ := log_len_est m (fun j => aj (m + 1) δ f j ^ 2) hsmall
    (fun j => sq_nonneg _) haη (sq_nonneg _) (haη (m + 1))
  unfold shortS at hleq
  rw [← hleq] at hL1 hL1η hlog
  have hen := energy_eq_aj hf δ
  rw [hm, Finset.sum_range_succ, ← sum_Icc_one_eq_range (fun j => aj (m + 1) δ f j ^ 2) m] at hen
  push_cast at hen
  rw [hm]
  refine ⟨hL1, hL1η, ?_⟩
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hE' : energy f = (δ ^ 2)⁻¹ * ((∑ j ∈ Finset.Icc 1 m, aj (m + 1) δ f j ^ 2 +
      aj (m + 1) δ f (m + 1) ^ 2) / (2 * ((m : ℝ) + 1))) := by
    rw [← hen]; field_simp
  rw [show δ ^ (-2 : ℤ) = (δ ^ 2)⁻¹ by rw [zpow_neg]; norm_cast, hE', ← mul_sub, abs_mul,
    abs_of_pos (inv_pos.2 hδ2)]
  calc (δ ^ 2)⁻¹ * |Real.log (uLen (m + 1) δ f) - (∑ j ∈ Finset.Icc 1 m, aj (m + 1) δ f j ^ 2 +
        aj (m + 1) δ f (m + 1) ^ 2) / (2 * ((m : ℝ) + 1))| ≤ (δ ^ 2)⁻¹ * (3 * η ^ 2) := by
        gcongr
    _ = 3 * (2 * B * (16 : ℝ) ^ n) ^ 4 * δ ^ 2 := by rw [hη]; field_simp

/-! ## Vertex and weight estimates -/

/-- Normalized-arclength weights of the unit constrained polygon. -/
def uW (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) : ℝ := ‖uv M δ f (i + 1) - uv M δ f i‖ / uLen M δ f

/-- Graph points `i/M + i δ f(i/M)`. -/
def gpt (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) : ℂ :=
  (((i : ℝ) / M : ℝ) : ℂ) + ((δ * f ((i : ℝ) / M) : ℝ) : ℂ) * Complex.I

lemma one_sub_sqrt_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ 1 - Real.sqrt (1 - t) ∧ 1 - Real.sqrt (1 - t) ≤ t := by
  have h := one_sub_sqrt_bounds ht0 ht1
  have : t ^ 2 ≤ t := by rw [sq]; exact mul_le_of_le_one_right ht0 ht1
  constructor <;> linarith [h.1, h.2]

lemma abs_hstep_sub_le {M : ℕ} (hM : 0 < M) {δ η : ℝ} {f : ℝ → ℝ} (hη1 : η ≤ 1)
    (haη : ∀ j, aj M δ f j ^ 2 ≤ η) (j : ℕ) : |hstep M δ f j - 1 / M| ≤ η / M := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have h := one_sub_sqrt_le (sq_nonneg (aj M δ f j)) ((haη j).trans hη1)
  rw [hstep_eq, show 1 / (M : ℝ) * Real.sqrt (1 - aj M δ f j ^ 2) - 1 / M =
    -((1 - Real.sqrt (1 - aj M δ f j ^ 2)) / M) by ring, abs_neg,
    abs_of_nonneg (div_nonneg h.1 hMr.le)]
  exact div_le_div_of_nonneg_right (h.2.trans (haη j)) hMr.le

lemma abs_hor1_sub_le {M : ℕ} (hM : 0 < M) {δ η : ℝ} {f : ℝ → ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (haη : ∀ j, aj M δ f j ^ 2 ≤ η) {i : ℕ} (hi : i ≤ M) :
    |hor1 M δ f i - (i : ℝ) / M| ≤ η := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have e : hor1 M δ f i - (i : ℝ) / M = ∑ j ∈ Finset.Icc 1 i, (hstep M δ f j - 1 / M) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, hor1]
    simp only [add_tsub_cancel_right, nsmul_eq_mul]
    ring
  rw [e]
  calc _ ≤ ∑ j ∈ Finset.Icc 1 i, |hstep M δ f j - 1 / M| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 i, η / M := Finset.sum_le_sum fun j _ => abs_hstep_sub_le hM hη1 haη j
    _ = i * (η / M) := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ hMr]
        have : (i : ℝ) ≤ M := by exact_mod_cast hi
        nlinarith

lemma norm_uv_sub_gpt_le {M : ℕ} (hM : 0 < M) {δ η : ℝ} {f : ℝ → ℝ} (hf1 : f 1 = 0)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (haη : ∀ j, aj M δ f j ^ 2 ≤ η) {i : ℕ} (hi : i ≤ M) :
    ‖uv M δ f i - gpt M δ f i‖ ≤ η := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rcases lt_or_eq_of_le hi with hi' | rfl
  · simp only [uv, hi', if_true, gpt]
    rw [show ((hor1 M δ f i : ℝ) : ℂ) + ((δ * f ((i : ℝ) / M) : ℝ) : ℂ) * Complex.I -
        ((((i : ℝ) / M : ℝ) : ℂ) + ((δ * f ((i : ℝ) / M) : ℝ) : ℂ) * Complex.I) =
        ((hor1 M δ f i - (i : ℝ) / M : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_hor1_sub_le hM hη0 hη1 haη hi
  · simp only [uv, lt_irrefl, if_false, gpt, div_self hMr.ne', hf1, mul_zero]
    simp [hη0]

lemma norm_gpt_le {M : ℕ} (hM : 0 < M) {δ B : ℝ} {f : ℝ → ℝ} (hδ : 0 ≤ δ)
    (hfB : ∀ x, |f x| ≤ B) {i : ℕ} (hi : i ≤ M) : ‖gpt M δ f i‖ ≤ 1 + δ * B := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  unfold gpt
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg hδ, abs_of_nonneg (by positivity)]
  have : (i : ℝ) / M ≤ 1 := by rw [div_le_one hMr]; exact_mod_cast hi
  have := hfB ((i : ℝ) / M)
  nlinarith

lemma norm_uv_le {M : ℕ} (hM : 0 < M) {δ η B : ℝ} {f : ℝ → ℝ} (hf1 : f 1 = 0) (hδ : 0 ≤ δ)
    (hfB : ∀ x, |f x| ≤ B) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (haη : ∀ j, aj M δ f j ^ 2 ≤ η) {i : ℕ}
    (hi : i ≤ M) : ‖uv M δ f i‖ ≤ 1 + η + δ * B := by
  have h1 := norm_uv_sub_gpt_le hM hf1 hη0 hη1 haη hi
  have h2 := norm_gpt_le hM hδ hfB hi (f := f)
  calc ‖uv M δ f i‖ ≤ ‖uv M δ f i - gpt M δ f i‖ + ‖gpt M δ f i‖ := norm_le_norm_sub_add _ _
    _ ≤ 1 + η + δ * B := by linarith

lemma uW_nonneg (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (hL : 0 < uLen M δ f) (i : ℕ) : 0 ≤ uW M δ f i :=
  div_nonneg (norm_nonneg _) hL.le

lemma sum_uW (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (hL : 0 < uLen M δ f) :
    ∑ i ∈ Finset.range M, uW M δ f i = 1 := by
  unfold uW
  rw [← Finset.sum_div]
  exact div_self hL.ne'

/-- The weights are within `L - 1` of `1/M`. -/
lemma abs_uW_sub_le (m : ℕ) (δ : ℝ) (f : ℝ → ℝ) (hf1 : f 1 = 0)
    (ha : ∀ j, aj (m + 1) δ f j ^ 2 ≤ 1) (hL1 : 1 ≤ uLen (m + 1) δ f) {i : ℕ} (hi : i < m + 1) :
    |uW (m + 1) δ f i - 1 / ((m + 1 : ℕ) : ℝ)| ≤ uLen (m + 1) δ f - 1 := by
  set L := uLen (m + 1) δ f with hLdef
  have hL0 : 0 < L := by linarith
  have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hstep : ∀ k, k < m → ‖uv (m + 1) δ f (k + 1) - uv (m + 1) δ f k‖ =
      1 / ((m + 1 : ℕ) : ℝ) := fun k hk => norm_uv_step δ f (by omega) (ha (k + 1))
  have hlast : ‖uv (m + 1) δ f (m + 1) - uv (m + 1) δ f m‖ =
      L - (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    have : L = ∑ k ∈ Finset.range m, ‖uv (m + 1) δ f (k + 1) - uv (m + 1) δ f k‖ +
        ‖uv (m + 1) δ f (m + 1) - uv (m + 1) δ f m‖ := by
      rw [hLdef, uLen, Finset.sum_range_succ]
    rw [Finset.sum_congr rfl fun k hk => hstep k (Finset.mem_range.1 hk), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] at this
    rw [this]; ring
  unfold uW
  rw [← hLdef]
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hi) with hi' | rfl
  · rw [hstep i hi']
    rw [show 1 / ((m + 1 : ℕ) : ℝ) / L - 1 / ((m + 1 : ℕ) : ℝ) =
      -((1 / ((m + 1 : ℕ) : ℝ)) * ((L - 1) / L)) by field_simp; ring, abs_neg,
      abs_of_nonneg (by positivity)]
    have h1 : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hm1]; exact_mod_cast Nat.succ_pos m
    have h2 : (L - 1) / L ≤ L - 1 := by
      rw [div_le_iff₀ hL0]; nlinarith
    have h3 : 0 ≤ (L - 1) / L := by positivity
    calc _ ≤ 1 * ((L - 1) / L) := by gcongr
      _ ≤ L - 1 := by linarith
  · rw [hlast]
    have e : (L - (i : ℝ) / ((i + 1 : ℕ) : ℝ)) / L - 1 / ((i + 1 : ℕ) : ℝ) =
        ((i : ℝ) / ((i + 1 : ℕ) : ℝ)) * ((L - 1) / L) := by field_simp; push_cast; ring
    rw [e, abs_of_nonneg (by positivity)]
    have h1 : (i : ℝ) / ((i + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hm1]; push_cast; linarith
    have h2 : (L - 1) / L ≤ L - 1 := by
      rw [div_le_iff₀ hL0]; nlinarith
    have h3 : 0 ≤ (L - 1) / L := by positivity
    calc _ ≤ 1 * ((L - 1) / L) := by gcongr
      _ ≤ L - 1 := by linarith

/-! ## Dependence on the profile -/

lemma sqrt_lip {u v : ℝ} (hu : 1 / 4 ≤ u) (hv : 1 / 4 ≤ v) :
    |Real.sqrt u - Real.sqrt v| ≤ |u - v| := by
  have hsu : 1 / 2 ≤ Real.sqrt u := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hu
  have hsv : 1 / 2 ≤ Real.sqrt v := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hv
  have e : (Real.sqrt u - Real.sqrt v) * (Real.sqrt u + Real.sqrt v) = u - v := by
    rw [show (Real.sqrt u - Real.sqrt v) * (Real.sqrt u + Real.sqrt v) =
      Real.sqrt u ^ 2 - Real.sqrt v ^ 2 by ring, Real.sq_sqrt (by linarith),
      Real.sq_sqrt (by linarith)]
  have hpos : 1 ≤ Real.sqrt u + Real.sqrt v := by linarith
  rw [← e, abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt u + Real.sqrt v)]
  nlinarith [abs_nonneg (Real.sqrt u - Real.sqrt v)]

lemma abs_aj_sub_aj_le {M : ℕ} {δ d : ℝ} {f f' : ℝ → ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ i ≤ M, |f ((i : ℝ) / M) - f' ((i : ℝ) / M)| ≤ d) {j : ℕ} (hj1 : 1 ≤ j)
    (hjM : j ≤ M) : |aj M δ f j - aj M δ f' j| ≤ 2 * δ * M * d := by
  have hc : ((j : ℝ) - 1) = ((j - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hj1, Nat.cast_one]
  unfold aj
  rw [hc]
  have h1 := hd j hjM
  have h2 := hd (j - 1) (by omega)
  rw [show δ * M * (f ((j : ℝ) / M) - f (((j - 1 : ℕ) : ℝ) / M)) -
      δ * M * (f' ((j : ℝ) / M) - f' (((j - 1 : ℕ) : ℝ) / M)) =
      (δ * M) * ((f ((j : ℝ) / M) - f' ((j : ℝ) / M)) -
        (f (((j - 1 : ℕ) : ℝ) / M) - f' (((j - 1 : ℕ) : ℝ) / M))) by ring,
    abs_mul, abs_of_nonneg (by positivity)]
  have h3 := abs_sub (f ((j : ℝ) / M) - f' ((j : ℝ) / M))
    (f (((j - 1 : ℕ) : ℝ) / M) - f' (((j - 1 : ℕ) : ℝ) / M))
  have : 0 ≤ δ * M := by positivity
  calc _ ≤ (δ * M) * (d + d) := by gcongr; linarith
    _ = 2 * δ * M * d := by ring

lemma abs_hstep_sub_hstep {M : ℕ} (hM : 0 < M) {δ d : ℝ} {f f' : ℝ → ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ j, aj M δ f j ^ 2 ≤ 1 / 4) (ha' : ∀ j, aj M δ f' j ^ 2 ≤ 1 / 4)
    (hd : ∀ i ≤ M, |f ((i : ℝ) / M) - f' ((i : ℝ) / M)| ≤ d) {j : ℕ} (hj1 : 1 ≤ j)
    (hjM : j ≤ M) : |hstep M δ f j - hstep M δ f' j| ≤ 2 * δ * d := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [hstep_eq, hstep_eq, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  have h1 := sqrt_lip (u := 1 - aj M δ f j ^ 2) (v := 1 - aj M δ f' j ^ 2)
    (by linarith [ha j]) (by linarith [ha' j])
  have h2 : |aj M δ f j| ≤ 1 / 2 := by
    rw [← Real.sqrt_sq (abs_nonneg _), sq_abs, show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (ha j)
  have h3 : |aj M δ f' j| ≤ 1 / 2 := by
    rw [← Real.sqrt_sq (abs_nonneg _), sq_abs, show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (ha' j)
  have h4 : |(1 - aj M δ f j ^ 2) - (1 - aj M δ f' j ^ 2)| ≤
      |aj M δ f j - aj M δ f' j| := by
    rw [show (1 - aj M δ f j ^ 2) - (1 - aj M δ f' j ^ 2) =
      (aj M δ f' j - aj M δ f j) * (aj M δ f' j + aj M δ f j) by ring, abs_mul,
      abs_sub_comm]
    have : |aj M δ f' j + aj M δ f j| ≤ 1 := (abs_add_le _ _).trans (by linarith)
    calc _ ≤ |aj M δ f j - aj M δ f' j| * 1 := by gcongr
      _ = _ := mul_one _
  have h5 := abs_aj_sub_aj_le hδ hd hj1 hjM
  calc 1 / (M : ℝ) * |Real.sqrt (1 - aj M δ f j ^ 2) - Real.sqrt (1 - aj M δ f' j ^ 2)|
      ≤ 1 / (M : ℝ) * (2 * δ * M * d) := by gcongr; linarith
    _ = 2 * δ * d := by field_simp

lemma norm_uv_sub_uv_le {M : ℕ} (hM : 0 < M) {δ d : ℝ} {f f' : ℝ → ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ j, aj M δ f j ^ 2 ≤ 1 / 4) (ha' : ∀ j, aj M δ f' j ^ 2 ≤ 1 / 4)
    (hd : ∀ i ≤ M, |f ((i : ℝ) / M) - f' ((i : ℝ) / M)| ≤ d) {i : ℕ} (hi : i ≤ M) :
    ‖uv M δ f i - uv M δ f' i‖ ≤ 3 * M * δ * d := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hd0 : 0 ≤ d := (abs_nonneg _).trans (hd 0 (Nat.zero_le _))
  rcases lt_or_eq_of_le hi with hi' | rfl
  · simp only [uv, hi', if_true]
    rw [show ((hor1 M δ f i : ℝ) : ℂ) + ((δ * f ((i : ℝ) / M) : ℝ) : ℂ) * Complex.I -
        (((hor1 M δ f' i : ℝ) : ℂ) + ((δ * f' ((i : ℝ) / M) : ℝ) : ℂ) * Complex.I) =
        ((hor1 M δ f i - hor1 M δ f' i : ℝ) : ℂ) +
          ((δ * (f ((i : ℝ) / M) - f' ((i : ℝ) / M)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hδ]
    have h1 : |hor1 M δ f i - hor1 M δ f' i| ≤ i * (2 * δ * d) := by
      unfold hor1
      rw [← Finset.sum_sub_distrib]
      calc _ ≤ ∑ j ∈ Finset.Icc 1 i, |hstep M δ f j - hstep M δ f' j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.Icc 1 i, 2 * δ * d := Finset.sum_le_sum fun j hj => by
            rw [Finset.mem_Icc] at hj
            exact abs_hstep_sub_hstep hM hδ ha ha' hd hj.1 (by omega)
        _ = i * (2 * δ * d) := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    have h2 := hd i hi
    have hiM : (i : ℝ) ≤ M := by exact_mod_cast hi
    have : 0 ≤ δ * d := mul_nonneg hδ hd0
    have h5 : (i : ℝ) * (2 * δ * d) ≤ M * (2 * δ * d) :=
      mul_le_mul_of_nonneg_right hiM (by positivity)
    have h6 : δ * d ≤ M * (δ * d) := le_mul_of_one_le_left this hMr
    calc _ ≤ i * (2 * δ * d) + δ * d := by gcongr
      _ ≤ M * (2 * δ * d) + M * (δ * d) := by linarith
      _ = 3 * M * δ * d := by ring
  · simp only [uv, lt_irrefl, if_false, sub_self, norm_zero]
    positivity

lemma abs_uW_sub_uW_le {M : ℕ} (hM : 0 < M) {δ d : ℝ} {f f' : ℝ → ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ j, aj M δ f j ^ 2 ≤ 1 / 4) (ha' : ∀ j, aj M δ f' j ^ 2 ≤ 1 / 4)
    (hd : ∀ i ≤ M, |f ((i : ℝ) / M) - f' ((i : ℝ) / M)| ≤ d)
    (hL : 1 ≤ uLen M δ f) (hL' : 1 ≤ uLen M δ f') (hL2 : uLen M δ f ≤ 2)
    (he : ∀ i < M, ‖uv M δ f (i + 1) - uv M δ f i‖ ≤ 4) {i : ℕ} (hi : i < M) :
    |uW M δ f i - uW M δ f' i| ≤ 36 * M ^ 2 * δ * d := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hd0 : 0 ≤ d := (abs_nonneg _).trans (hd 0 (Nat.zero_le _))
  set e : ℕ → ℝ := fun k => ‖uv M δ f (k + 1) - uv M δ f k‖ with he_def
  set e' : ℕ → ℝ := fun k => ‖uv M δ f' (k + 1) - uv M δ f' k‖ with he'_def
  have hde : ∀ k < M, |e k - e' k| ≤ 6 * M * δ * d := by
    intro k hk
    have h1 := norm_uv_sub_uv_le hM hδ ha ha' hd (i := k + 1) hk
    have h2 := norm_uv_sub_uv_le hM hδ ha ha' hd (i := k) hk.le
    calc |e k - e' k| ≤ ‖(uv M δ f (k + 1) - uv M δ f k) - (uv M δ f' (k + 1) - uv M δ f' k)‖ :=
          abs_norm_sub_norm_le _ _
      _ = ‖(uv M δ f (k + 1) - uv M δ f' (k + 1)) - (uv M δ f k - uv M δ f' k)‖ := by
          congr 1; ring
      _ ≤ ‖uv M δ f (k + 1) - uv M δ f' (k + 1)‖ + ‖uv M δ f k - uv M δ f' k‖ :=
          norm_sub_le _ _
      _ ≤ 6 * M * δ * d := by linarith
  have hdL : |uLen M δ f - uLen M δ f'| ≤ 6 * M ^ 2 * δ * d := by
    unfold uLen
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ k ∈ Finset.range M, |e k - e' k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range M, 6 * M * δ * d := Finset.sum_le_sum fun k hk =>
          hde k (Finset.mem_range.1 hk)
      _ = 6 * M ^ 2 * δ * d := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  unfold uW
  set L := uLen M δ f
  set L' := uLen M δ f'
  have hLL : 0 < L * L' := by positivity
  rw [div_sub_div _ _ (by positivity : L ≠ 0) (by positivity : L' ≠ 0), abs_div,
    abs_of_pos hLL, div_le_iff₀ hLL]
  have hek := he i hi
  have hdei := hde i hi
  have hkey : e i * L' - L * e' i = e i * (L' - L) + L * (e i - e' i) := by ring
  have hb1 : |e i * (L' - L)| ≤ 4 * (6 * M ^ 2 * δ * d) := by
    rw [abs_mul, abs_of_nonneg (norm_nonneg _), abs_sub_comm]; gcongr
  have hb2 : |L * (e i - e' i)| ≤ 2 * (6 * M * δ * d) := by
    rw [abs_mul, abs_of_pos (by linarith)]; gcongr
  have hMM : (M : ℝ) ≤ M ^ 2 := by nlinarith
  have h1LL : 1 ≤ L * L' := by nlinarith
  calc |e i * L' - L * e' i| ≤ |e i * (L' - L)| + |L * (e i - e' i)| := by
        rw [hkey]; exact abs_add_le _ _
    _ ≤ 36 * M ^ 2 * δ * d := by nlinarith [mul_nonneg hδ hd0]
    _ ≤ 36 * M ^ 2 * δ * d * (L * L') := by
        have : 0 ≤ 36 * M ^ 2 * δ * d := by positivity
        nlinarith

end LQGDimension.ConstrCov
