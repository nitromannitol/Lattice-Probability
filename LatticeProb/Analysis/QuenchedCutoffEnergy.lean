import LatticeProb.Analysis.AnnealedCutoffEnergy

/-!
# Quenched critical cutoff energy

Pointwise estimates for annular cutoffs on the Euclidean integer lattice.
-/

noncomputable section

open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Shell
open LatticeProb.Analysis.CriticalCutoffEnergy
open LatticeProb.Analysis.AnnealedCutoffEnergy

namespace LatticeProb.Analysis.QuenchedCutoffEnergy

/-- The annular cutoff centered at a lattice site. -/
def cutoff {d : ℕ} (x₀ : Site d) (r₁ r₂ : ℝ) (x : Site d) : ℝ :=
  max 0 (1 - max 0 (radius (physical 1 (x - x₀)) - r₁) / r₂)

lemma cutoff_nonneg {d : ℕ} (x₀ : Site d) (r₁ r₂ : ℝ) (x : Site d) :
    0 ≤ cutoff x₀ r₁ r₂ x := le_max_left _ _

lemma cutoff_le_one {d : ℕ} (x₀ : Site d) (r₁ : ℝ) {r₂ : ℝ} (hr₂ : 0 < r₂)
    (x : Site d) : cutoff x₀ r₁ r₂ x ≤ 1 := by
  unfold cutoff
  apply max_le (by norm_num)
  have : 0 ≤ max 0 (radius (physical 1 (x - x₀)) - r₁) / r₂ :=
    div_nonneg (le_max_left _ _) hr₂.le
  linarith

/-- The increment of the cutoff is bounded by its Lipschitz constant and by one. -/
theorem cutoff_increment_le {d : ℕ} (x₀ : Site d) (r₁ : ℝ) {r₂ : ℝ} (hr₂ : 0 < r₂)
    (x y : Site d) :
    |cutoff x₀ r₁ r₂ x - cutoff x₀ r₁ r₂ y| ≤
      min 1 (radius (physical 1 (x - y)) / r₂) := by
  have hmax (a b : ℝ) : |max 0 a - max 0 b| ≤ |a - b| := by
    simpa only [max_comm] using abs_max_sub_max_le_abs a b 0
  have hdist : |radius (physical 1 (x - x₀)) - radius (physical 1 (y - x₀))| ≤
      radius (physical 1 (x - y)) := by
    convert radius_difference (physical 1 (x - x₀)) (physical 1 (y - x₀)) using 1
    congr 1
    funext i
    simp only [physical, one_mul, Pi.sub_apply, Int.cast_sub]
    ring
  have h1 : |cutoff x₀ r₁ r₂ x - cutoff x₀ r₁ r₂ y| ≤ 1 := by
    apply abs_le.mpr
    have hx := cutoff_nonneg x₀ r₁ r₂ x
    have hy := cutoff_nonneg x₀ r₁ r₂ y
    have hx' := cutoff_le_one x₀ r₁ hr₂ x
    have hy' := cutoff_le_one x₀ r₁ hr₂ y
    constructor <;> linarith
  have h2 : |cutoff x₀ r₁ r₂ x - cutoff x₀ r₁ r₂ y| ≤
      radius (physical 1 (x - y)) / r₂ := by
    unfold cutoff
    calc
      _ ≤ |(1 - max 0 (radius (physical 1 (x - x₀)) - r₁) / r₂) -
            (1 - max 0 (radius (physical 1 (y - x₀)) - r₁) / r₂)| := hmax _ _
      _ = |max 0 (radius (physical 1 (x - x₀)) - r₁) -
            max 0 (radius (physical 1 (y - x₀)) - r₁)| / r₂ := by
              have h : (1 - max 0 (radius (physical 1 (x - x₀)) - r₁) / r₂) -
                  (1 - max 0 (radius (physical 1 (y - x₀)) - r₁) / r₂) =
                  -((max 0 (radius (physical 1 (x - x₀)) - r₁) -
                    max 0 (radius (physical 1 (y - x₀)) - r₁)) / r₂) := by ring
              rw [h, abs_neg, abs_div, abs_of_pos hr₂]
      _ ≤ |radius (physical 1 (x - x₀)) - radius (physical 1 (y - x₀))| / r₂ := by
        apply div_le_div_of_nonneg_right _ hr₂.le
        simpa only [sub_sub_sub_cancel_right] using hmax
          (radius (physical 1 (x - x₀)) - r₁) (radius (physical 1 (y - x₀)) - r₁)
      _ ≤ _ := div_le_div_of_nonneg_right hdist hr₂.le
  exact le_min h1 h2

/-- The annular cutoff has finite support. -/
theorem cutoff_finiteSupport {d : ℕ} (x₀ : Site d) (r₁ : ℝ) {r₂ : ℝ} (hr₂ : 0 < r₂) :
    Function.HasFiniteSupport (cutoff x₀ r₁ r₂) := by
  classical
  let R := r₁ + r₂
  have hfinite : {z : Site d | radius (physical 1 z) ≤ R}.Finite := by
    apply (Set.Finite.pi' (fun _ : Fin d => Set.finite_Icc (-(⌈R⌉ : ℤ)) ⌈R⌉)).subset
    intro z hz i
    have h := (abs_coord_le_radius (physical 1 z) i).trans hz
    simp only [physical, one_mul] at h
    have hceil : R ≤ (⌈R⌉ : ℤ) := Int.le_ceil R
    have h' : |(z i : ℝ)| ≤ (⌈R⌉ : ℤ) := h.trans hceil
    have hi : |z i| ≤ (⌈R⌉ : ℤ) := by exact_mod_cast h'
    exact abs_le.mp hi
  apply (hfinite.image (fun z => x₀ + z)).subset
  intro x hx
  have hx' : cutoff x₀ r₁ r₂ x ≠ 0 := hx
  have hlt : radius (physical 1 (x - x₀)) < R := by
    by_contra h
    have hge : r₂ ≤ radius (physical 1 (x - x₀)) - r₁ := by dsimp [R] at h; linarith
    have hdiv : 1 ≤ max 0 (radius (physical 1 (x - x₀)) - r₁) / r₂ := by
      apply (le_div_iff₀ hr₂).2
      simpa using (hge.trans (le_max_right 0 _))
    apply hx'
    unfold cutoff
    exact max_eq_left (by linarith)
  refine ⟨x - x₀, le_of_lt hlt, ?_⟩
  simp

/-- The cutoff energy is summable and bounded by the deterministic critical sum. -/
theorem cutoff_energy_le_kernel {d : ℕ} (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, 0 ≤ a e ∧ a e ≤ lam⁻¹)
    (x₀ x : Site d) (r₁ : ℝ) {r₂ : ℝ} (hr₂ : 0 < r₂) :
    Summable (fun z : {z : Site d // z ≠ 0} =>
      a (edgeAdd x z) * (radius (physical 1 z.val) ^ (d + 2))⁻¹ *
        (cutoff x₀ r₁ r₂ x - cutoff x₀ r₁ r₂ (x + z.val)) ^ 2) ∧
    (∑' z : {z : Site d // z ≠ 0},
      a (edgeAdd x z) * (radius (physical 1 z.val) ^ (d + 2))⁻¹ *
        (cutoff x₀ r₁ r₂ x - cutoff x₀ r₁ r₂ (x + z.val)) ^ 2) ≤
      lam⁻¹ * ∑' z : {z : Site d // z ≠ 0}, weight r₂ z := by
  have hcomp (z : {z : Site d // z ≠ 0}) :
      a (edgeAdd x z) * (radius (physical 1 z.val) ^ (d + 2))⁻¹ *
        (cutoff x₀ r₁ r₂ x - cutoff x₀ r₁ r₂ (x + z.val)) ^ 2 ≤
        lam⁻¹ * weight r₂ z := by
    have hdist : radius (physical 1 (x - (x + z.val))) = radius (physical 1 z.val) := by
      have he : x - (x + z.val) = -z.val := by simp
      rw [he, radius_norm, radius_norm]
      have hp : physical 1 (-z.val) = -physical 1 z.val := by
        funext i
        simp only [physical, Pi.neg_apply, Int.cast_neg, mul_neg]
      rw [hp]
      change ‖-(WithLp.toLp 2 (physical 1 z.val) : EuclideanSpace ℝ (Fin d))‖ = _
      exact norm_neg _
    have hi := cutoff_increment_le x₀ r₁ hr₂ x (x + z.val)
    rw [hdist] at hi
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hi 2
    rw [sq_abs] at hsq
    have hmin : (min 1 (radius (physical 1 z.val) / r₂)) ^ 2 =
        min 1 (radius (physical 1 z.val) ^ 2 / r₂ ^ 2) := by
      rcases le_total 1 (radius (physical 1 z.val) / r₂) with h | h
      · rw [min_eq_left h, min_eq_left]
        · norm_num
        · have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h 2
          simpa only [one_pow, div_pow] using hh
      · rw [min_eq_right h, min_eq_right]
        · rw [div_pow]
        · have hh := pow_le_pow_left₀ (div_nonneg (radius_nonneg _) hr₂.le) h 2
          simpa only [one_pow, div_pow] using hh
    rw [hmin] at hsq
    have hk : 0 ≤ (radius (physical 1 z.val) ^ (d + 2))⁻¹ :=
      inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)
    calc
      _ ≤ lam⁻¹ * (radius (physical 1 z.val) ^ (d + 2))⁻¹ *
          min 1 (radius (physical 1 z.val) ^ 2 / r₂ ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (ha _).2 hk) hsq (sq_nonneg _)
          (mul_nonneg (inv_nonneg.mpr hlam.le) hk)
      _ = _ := by simp only [weight]; ring
  have hnonneg (z : {z : Site d // z ≠ 0}) : 0 ≤
      a (edgeAdd x z) * (radius (physical 1 z.val) ^ (d + 2))⁻¹ *
        (cutoff x₀ r₁ r₂ x - cutoff x₀ r₁ r₂ (x + z.val)) ^ 2 := by
    exact mul_nonneg (mul_nonneg (ha _).1
      (inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _))) (sq_nonneg _)
  have hmajor : Summable (fun z : {z : Site d // z ≠ 0} => lam⁻¹ * weight r₂ z) :=
    (summable_cutoff_energy d hd r₂).mul_left _
  have hs := hmajor.of_nonneg_of_le hnonneg hcomp
  exact ⟨hs, by simpa only [tsum_mul_left] using hs.tsum_le_tsum hcomp hmajor⟩

/-- A dimension-only coefficient controls the cutoff kernel at all positive radii. -/
theorem exists_cutoff_kernel_bound {d : ℕ} (hd : 1 ≤ d) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 < r →
      (∑' z : {z : Site d // z ≠ 0}, weight r z) ≤
        B * Real.log (2 + r) / r ^ 2 := by
  let A := shellConstant d * (1 + 25 / Real.log 3)
  let T := ∑' z : {z : Site d // z ≠ 0}, (radius (physical 1 z.val) ^ (d + 2))⁻¹
  have hT : 0 ≤ T := tsum_nonneg (fun z =>
    inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (shellConstant_pos hd) (by positivity)
  let B := A + T / Real.log 2 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro r hr
  have hlog : Real.log 2 ≤ Real.log (2 + r) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hfac : 0 ≤ Real.log (2 + r) / r ^ 2 :=
    div_nonneg (hlog2.le.trans hlog) (sq_nonneg r)
  by_cases hlarge : 1 ≤ r
  · have h := cutoff_energy_le_log hd hlarge
    have hAB : A ≤ B := by
      have h : 0 ≤ T / Real.log 2 := by positivity
      dsimp [B]
      linarith
    calc
      _ ≤ A * Real.log (2 + r) / r ^ 2 := h
      _ ≤ B * Real.log (2 + r) / r ^ 2 := by
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hAB hfac
  · have hr1 : r ≤ 1 := le_of_not_ge hlarge
    have hrsq : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg (r - 1)]
    have hmul : T * r ^ 2 * Real.log 2 ≤ T * Real.log (2 + r) := by
      have h1 : T * r ^ 2 ≤ T := by nlinarith
      have h2 := mul_le_mul_of_nonneg_left hlog hT
      nlinarith
    have hsmall : T ≤ (T / Real.log 2) * Real.log (2 + r) / r ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hr)).2
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hlog2).2 hmul
    have hTB : T / Real.log 2 ≤ B := by dsimp [B]; linarith
    calc
      _ ≤ T := cutoff_energy_le_total_rate d hd r
      _ ≤ (T / Real.log 2) * Real.log (2 + r) / r ^ 2 := hsmall
      _ ≤ B * Real.log (2 + r) / r ^ 2 := by
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hTB hfac

/-- The critical heat-kernel scale. -/
def scale (r : ℝ) : ℝ := r ^ 2 * Real.log 3 / Real.log (2 + r)

/-- Uniform pointwise cutoff-energy estimate for elliptic unordered-edge conductances. -/
theorem exists_cutoff_energy_bound {d : ℕ} (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Edge d → ℝ),
      (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) →
      ∀ (x₀ x : Site d) (r₁ r₂ : ℝ), r₂ ≤ r₁ → 0 < r₂ →
        Function.HasFiniteSupport (cutoff x₀ r₁ r₂) ∧
        (∀ y : Site d, |cutoff x₀ r₁ r₂ x - cutoff x₀ r₁ r₂ y| ≤
          min 1 (radius (physical 1 (x - y)) / r₂)) ∧
        (∑' z : {z : Site d // z ≠ 0},
          a (edgeAdd x z) * (radius (physical 1 z.val) ^ (d + 2))⁻¹ *
            (cutoff x₀ r₁ r₂ x - cutoff x₀ r₁ r₂ (x + z.val)) ^ 2) ≤
          C / scale r₂ := by
  obtain ⟨B, hB, hbound⟩ := exists_cutoff_kernel_bound hd
  refine ⟨lam⁻¹ * B * Real.log 3, by positivity, ?_⟩
  intro a ha x₀ x r₁ r₂ _ hr₂
  refine ⟨cutoff_finiteSupport x₀ r₁ hr₂, cutoff_increment_le x₀ r₁ hr₂ x, ?_⟩
  calc
    _ ≤ lam⁻¹ * ∑' z : {z : Site d // z ≠ 0}, weight r₂ z :=
      (cutoff_energy_le_kernel hd hlam a (fun e => ⟨hlam.le.trans (ha e).1, (ha e).2⟩)
        x₀ x r₁ hr₂).2
    _ ≤ lam⁻¹ * (B * Real.log (2 + r₂) / r₂ ^ 2) :=
      mul_le_mul_of_nonneg_left (hbound r₂ hr₂) (inv_nonneg.mpr hlam.le)
    _ = _ := by
      unfold scale
      have hl : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      have hl₂ : Real.log (2 + r₂) ≠ 0 :=
        (Real.log_pos (by linarith : 1 < 2 + r₂)).ne'
      field_simp

/-- Translation identifies nonzero displacements with sites distinct from the base site. -/
def neighborEquiv {d : ℕ} (x : Site d) :
    {z : Site d // z ≠ 0} ≃ {y : Site d // y ≠ x} where
  toFun z := ⟨x + z.val, by
    intro h
    apply z.property
    have h' : x + z.val = x + 0 := by simpa using h
    exact add_left_cancel h'⟩
  invFun y := ⟨y.val - x, sub_ne_zero.mpr y.property⟩
  left_inv z := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

/-- The unordered edge from a base site to a distinct site. -/
def neighborEdge {d : ℕ} (x : Site d) (y : {y : Site d // y ≠ x}) : Edge d :=
  ⟨s(x, y.val), by simpa only [Sym2.mk_isDiag_iff] using Ne.symm y.property⟩

/-- The Euclidean radius of a difference is symmetric. -/
lemma radius_physical_sub_comm {d : ℕ} (x y : Site d) :
    radius (physical 1 (x - y)) = radius (physical 1 (y - x)) := by
  have h : physical 1 (x - y) = -physical 1 (y - x) := by
    funext i
    simp only [physical, Pi.neg_apply, Pi.sub_apply, Int.cast_sub, one_mul]
    ring
  rw [h, radius_norm, radius_norm]
  change ‖-(WithLp.toLp 2 (physical 1 (y - x)) : EuclideanSpace ℝ (Fin d))‖ = _
  exact norm_neg _

/-- Pointwise cutoff-energy bound in the distinct-vertex indexing. -/
theorem exists_cutoff_energy_bound_sites {d : ℕ} (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) (_hlam1 : lam ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Edge d → ℝ),
      (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) →
      ∀ (x₀ x : Site d) (r₁ r₂ : ℝ), r₂ ≤ r₁ → 0 < r₂ →
        Function.HasFiniteSupport (cutoff x₀ r₁ r₂) ∧
        (∀ y : Site d, |cutoff x₀ r₁ r₂ x - cutoff x₀ r₁ r₂ y| ≤
          min 1 (radius (physical 1 (x - y)) / r₂)) ∧
        (∑' y : {y : Site d // y ≠ x},
          a (neighborEdge x y) * (radius (physical 1 (x - y.val)) ^ (d + 2))⁻¹ *
            (cutoff x₀ r₁ r₂ x - cutoff x₀ r₁ r₂ y.val) ^ 2) ≤ C / scale r₂ := by
  obtain ⟨C, hC, hbound⟩ := exists_cutoff_energy_bound hd hlam
  refine ⟨C, hC, ?_⟩
  intro a ha x₀ x r₁ r₂ hr₁ hr₂
  obtain ⟨hfinite, hinc, henergy⟩ := hbound a ha x₀ x r₁ r₂ hr₁ hr₂
  refine ⟨hfinite, hinc, ?_⟩
  rw [← (neighborEquiv x).tsum_eq]
  convert henergy using 1
  apply tsum_congr
  intro z
  have he : neighborEdge x (neighborEquiv x z) = edgeAdd x z := by
    apply Subtype.ext
    rfl
  change a (neighborEdge x (neighborEquiv x z)) *
      (radius (physical 1 (x - (x + z.val))) ^ (d + 2))⁻¹ *
        (cutoff x₀ r₁ r₂ x - cutoff x₀ r₁ r₂ (x + z.val)) ^ 2 = _
  rw [he, radius_physical_sub_comm x (x + z.val), add_sub_cancel_left]

end LatticeProb.Analysis.QuenchedCutoffEnergy
