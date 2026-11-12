/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.ConditionalGrid at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFDefs
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# GM Lemma 4.8: the ball count (deterministic part of (4.19))

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.8
(`lem-good-annulus-count`, l. 1812–1818): "each ball `B_r(z)` for `(z,r) ∈ 𝒵_k` is contained in
`B_{4λ₄ε𝕣}(∂𝓑^•_{t_k})` and the maximal number of such balls which contain any given point … is
at most a constant times `ε^{-2ν} log_8 ε^{-1}`. … each ball `B_r(z)` for `(z,r) ∈ 𝒵_k(P)` is
contained in `B_{4λ₄ε𝕣}(P)`. Therefore, the left side of (4.18) is at least a constant times
`ε^{2+2ν}(log_8 ε^{-1})^{-1} 𝕣² #𝒵_k(P)`."

Formalized (own elementary argument, a disjoint-cells form of GM's overlap count):
* `gm_card_mul_le_volume`: `#Z · σ² ≤ area(X)` for grid points `Z ⊆ δℤ²` (`σ ≤ δ`) whose cells
  `z + [0,σ)²` lie in `X` (the cells are disjoint);
* `gm_pairs_card_le`: for pairs `(z, r)` with `z ∈ δℤ²`, `r` in a finite set `Rads` of radii,
  `r ≥ 2σ` and `B_r(z) ⊆ X`: `#pairs · σ² ≤ #Rads · area(X)`. With `δ = λ₁ε^{1+ν}𝕣/4`,
  `σ = min(δ, ε^{1+ν}𝕣/2)`, `#Rads ≤ μ log_8 ε^{-1}` and `area(X) ≤ (4λ₄ε)^{2-1/M'}𝕣²` (GM.S4.8,
  `gm_S4_8`) this gives `#𝒵_k(P) ≤ C ε^{-2ν-1/M'} log_8 ε^{-1}`, i.e. (4.19) once `1/M' < ζ`.
  (GM's intermediate bound `ε^{2+2ν}(log)^{-1}` per ball is loose; counting per radius as here
  gives the stated `ε^{-2ν-ζ}`.)
* `gm_ball_subset_count`: `B_r(z) ⊆ B_a(P) ∩ B_a(∂K)` for `(z,r) ∈ 𝒵_k(P)`, `a = 4λ₄ε𝕣`,
  `λ₄ ≥ 1/2` (GM l. 1813–1815).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the half-open grid cell `z + [0,σ)²` -/
def gridCell (z : ℂ) (σ : ℝ) : Set ℂ :=
  {x | z.re ≤ x.re ∧ x.re < z.re + σ ∧ z.im ≤ x.im ∧ x.im < z.im + σ}

theorem gm_gridCell_eq (z : ℂ) (σ : ℝ) : gridCell z σ =
    Complex.measurableEquivRealProd ⁻¹' (Ico z.re (z.re + σ) ×ˢ Ico z.im (z.im + σ)) := by
  ext x
  simp [gridCell, and_assoc]

theorem gm_measurableSet_gridCell (z : ℂ) (σ : ℝ) : MeasurableSet (gridCell z σ) := by
  rw [gm_gridCell_eq]
  exact Complex.measurableEquivRealProd.measurable (measurableSet_Ico.prod measurableSet_Ico)

theorem gm_volume_gridCell (z : ℂ) {σ : ℝ} (hσ : 0 ≤ σ) :
    volume (gridCell z σ) = ENNReal.ofReal (σ ^ 2) := by
  rw [gm_gridCell_eq, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ico, Real.volume_Ico, add_sub_cancel_left,
    add_sub_cancel_left, ← ENNReal.ofReal_mul hσ, sq]

theorem gm_int_eq_of_near {a a' : ℤ} {δ σ x : ℝ} (hσδ : σ ≤ δ)
    (h1 : a * δ ≤ x) (h2 : x < a * δ + σ) (h3 : a' * δ ≤ x) (h4 : x < a' * δ + σ) : a = a' := by
  have hδ : 0 < δ := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    linarith
  have hlt : ((a - a' : ℤ) : ℝ) < 1 := by
    rw [← mul_lt_mul_iff_of_pos_right hδ]; push_cast; linarith
  have hgt : (-1 : ℝ) < ((a - a' : ℤ) : ℝ) := by
    rw [← mul_lt_mul_iff_of_pos_right hδ]; push_cast; linarith
  have h5 : a - a' < 1 := by exact_mod_cast hlt
  have h6 : -1 < a - a' := by exact_mod_cast hgt
  omega

theorem gm_disjoint_gridCell {δ σ : ℝ} (hσδ : σ ≤ δ) {z z' : ℂ} (hz : z ∈ gridPts δ)
    (hz' : z' ∈ gridPts δ) (hne : z ≠ z') : Disjoint (gridCell z σ) (gridCell z' σ) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨a', b', rfl⟩ := hz'
  rw [Set.disjoint_left]
  rintro x ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
  apply hne
  have ha := gm_int_eq_of_near hσδ h1 h2 h1' h2'
  have hb := gm_int_eq_of_near hσδ h3 h4 h3' h4'
  rw [ha, hb]

/-- `#Z · σ² ≤ area(X)` for grid points whose cells lie in `X` -/
theorem gm_card_mul_le_volume {δ σ : ℝ} (hσ : 0 ≤ σ) (hσδ : σ ≤ δ) (Zs : Finset ℂ)
    (hZ : ∀ z ∈ Zs, z ∈ gridPts δ) {X : Set ℂ} (hX : ∀ z ∈ Zs, gridCell z σ ⊆ X) :
    (Zs.card : ℝ≥0∞) * ENNReal.ofReal (σ ^ 2) ≤ volume X := by
  calc (Zs.card : ℝ≥0∞) * ENNReal.ofReal (σ ^ 2) = ∑ z ∈ Zs, volume (gridCell z σ) := by
        rw [Finset.sum_congr rfl (fun z _ => gm_volume_gridCell z hσ), Finset.sum_const,
          nsmul_eq_mul]
    _ = volume (⋃ z ∈ Zs, gridCell z σ) := by
        refine (measure_biUnion_finset ?_ (fun z _ => gm_measurableSet_gridCell z σ)).symm
        intro z hz z' hz' hne
        exact gm_disjoint_gridCell hσδ (hZ z hz) (hZ z' hz') hne
    _ ≤ volume X := measure_mono (iUnion₂_subset hX)

/-- the cell `z + [0,σ)²` lies in `B_r(z)` when `2σ ≤ r` -/
theorem gm_gridCell_subset_ball {z : ℂ} {σ r : ℝ} (hσ : 0 ≤ σ) (hr : 2 * σ ≤ r) (hr0 : 0 < r) :
    gridCell z σ ⊆ ball z r := by
  rintro x ⟨h1, h2, h3, h4⟩
  rw [mem_ball, Complex.dist_eq_re_im, Real.sqrt_lt' hr0]
  have e1 : (x.re - z.re) ^ 2 < r ^ 2 / 2 := by nlinarith
  have e2 : (x.im - z.im) ^ 2 < r ^ 2 / 2 := by nlinarith
  linarith

/-- **GM (4.18)–(4.19), ball count**: pairs `(z,r)` with `z ∈ δℤ²`, `r ∈ Rads`, `r ≥ 2σ`
(`0 < σ ≤ δ`) and `B_r(z) ⊆ X` satisfy `#pairs · σ² ≤ #Rads · area(X)`. -/
theorem gm_pairs_card_le {δ σ : ℝ} (hσ : 0 < σ) (hσδ : σ ≤ δ) (S : Finset (ℂ × ℝ))
    (Rads : Finset ℝ) (hS : ∀ p ∈ S, p.1 ∈ gridPts δ ∧ p.2 ∈ Rads ∧ 2 * σ ≤ p.2) {X : Set ℂ}
    (hX : ∀ p ∈ S, ball p.1 p.2 ⊆ X) :
    (S.card : ℝ≥0∞) * ENNReal.ofReal (σ ^ 2) ≤ Rads.card * volume X := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Rads) (fun p hp => (hS p hp).2.1)]
  push_cast
  rw [Finset.sum_mul]
  calc ∑ r ∈ Rads, ((S.filter (fun p => p.2 = r)).card : ℝ≥0∞) * ENNReal.ofReal (σ ^ 2)
      ≤ ∑ _r ∈ Rads, volume X := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        set F := S.filter (fun p => p.2 = r)
        have hinj : Set.InjOn Prod.fst (F : Set (ℂ × ℝ)) := by
          intro p hp q hq hpq
          have hp' := (Finset.mem_filter.mp hp).2
          have hq' := (Finset.mem_filter.mp hq).2
          exact Prod.ext hpq (hp'.trans hq'.symm)
        rw [← Finset.card_image_of_injOn hinj]
        refine gm_card_mul_le_volume hσ.le hσδ _ ?_ ?_
        · intro z hz
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
          exact (hS p (Finset.mem_filter.mp hp).1).1
        · intro z hz
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
          have hpS := (Finset.mem_filter.mp hp).1
          have h2 := (hS p hpS).2.2
          exact (gm_gridCell_subset_ball hσ.le h2 (by linarith)).trans (hX p hpS)
    _ = Rads.card * volume X := by rw [Finset.sum_const, nsmul_eq_mul]

/-- GM l. 1813–1815: for `(z, r) ∈ 𝒵_k(P)` (`r ≤ ε𝕣`, `dist(z, ∂K) ≤ 2λ₄ε𝕣`,
`P ∩ B_r(z) ≠ ∅`) and `λ₄ ≥ 1/2`, `B_r(z) ⊆ B_a(P) ∩ B_a(∂K)` with `a = 4λ₄ε𝕣`. -/
theorem gm_ball_subset_count {K Pset : Set ℂ} {z : ℂ} {r lam4 ε 𝕣 : ℝ} (hlam : 1 ≤ 2 * lam4)
    (hε𝕣 : 0 ≤ ε * 𝕣) (hr : r ≤ ε * 𝕣) (hK : (frontier K).Nonempty)
    (hd : infDist z (frontier K) ≤ 2 * lam4 * ε * 𝕣) (hP : (Pset ∩ ball z r).Nonempty) :
    ball z r ⊆ thickening (4 * lam4 * ε * 𝕣) Pset ∩
      thickening (4 * lam4 * ε * 𝕣) (frontier K) := by
  intro x hx
  rw [mem_ball] at hx
  obtain ⟨y, hyP, hy⟩ := hP
  rw [mem_ball] at hy
  refine ⟨mem_thickening_iff.mpr ⟨y, hyP, ?_⟩, ?_⟩
  · calc dist x y ≤ dist x z + dist z y := dist_triangle x z y
      _ < r + r := by rw [dist_comm z y]; linarith
      _ ≤ 4 * lam4 * ε * 𝕣 := by nlinarith
  · rw [mem_thickening_iff_infDist_lt hK]
    calc infDist x (frontier K) ≤ infDist z (frontier K) + dist x z :=
          infDist_le_infDist_add_dist
      _ < 2 * lam4 * ε * 𝕣 + r := by linarith
      _ ≤ 4 * lam4 * ε * 𝕣 := by nlinarith

end LQGMetric.GM
