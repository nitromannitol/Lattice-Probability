import LatticeProb.Prob.RandomCentreBallMass
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # Quantitative planar covers and random-centre ball masses -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

/-- A grid cover of the ball `B_ρ(x)` by balls of radius `r`, with at most `(3 + 2ρ/r)²` centres
(the grid `x + r(a + b i)`, `|a|, |b| ≤ ⌈ρ/r⌉`). -/
lemma exists_grid_cover (x : ℂ) {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : 0 < r) :
    ∃ Y : Finset ℂ, (Y.card : ℝ) ≤ (3 + 2 * ρ / r) ^ 2 ∧
      ∀ p ∈ ball x ρ, ∃ y ∈ Y, p ∈ ball y r := by
  classical
  have hρr : 0 ≤ ρ / r := div_nonneg hρ hr.le
  set M : ℤ := (⌈ρ / r⌉₊ : ℤ) with hM
  have hM0 : 0 ≤ M := by omega
  have hMle : ρ / r ≤ (M : ℝ) := by
    rw [hM]; exact_mod_cast Nat.le_ceil (ρ / r)
  have hMlt : (M : ℝ) < ρ / r + 1 := by
    rw [hM]; exact_mod_cast Nat.ceil_lt_add_one hρr
  set G : Finset (ℤ × ℤ) := Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M with hG
  refine ⟨G.image (fun ab : ℤ × ℤ => x + (r : ℂ) * ((ab.1 : ℂ) + (ab.2 : ℂ) * Complex.I)), ?_, ?_⟩
  · have hN : (((M + 1 - -M).toNat : ℕ) : ℝ) = 2 * (M : ℝ) + 1 := by
      have h1 : (((M + 1 - -M).toNat : ℕ) : ℤ) = M + 1 - -M := Int.toNat_of_nonneg (by omega)
      have h2 : ((((M + 1 - -M).toNat : ℕ) : ℤ) : ℝ) = ((M + 1 - -M : ℤ) : ℝ) := by rw [h1]
      rw [Int.cast_natCast] at h2
      rw [h2]; push_cast; ring
    have hcardG : (G.card : ℝ) = (2 * (M : ℝ) + 1) ^ 2 := by
      rw [hG, Finset.card_product, Int.card_Icc]
      rw [← hN]; push_cast; ring
    have h2ρ : 2 * ρ / r = 2 * (ρ / r) := by ring
    calc ((G.image (fun ab : ℤ × ℤ => x + (r : ℂ) * ((ab.1 : ℂ) + (ab.2 : ℂ) * Complex.I))).card : ℝ)
        ≤ (G.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = (2 * (M : ℝ) + 1) ^ 2 := hcardG
      _ ≤ (3 + 2 * ρ / r) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          rw [h2ρ]; linarith
  · intro p hp
    have hpρ : dist p x < ρ := hp
    rw [Complex.dist_eq_re_im] at hpρ
    have hρpos : 0 < ρ := lt_of_le_of_lt (Real.sqrt_nonneg _) hpρ
    have hS : (p.re - x.re) ^ 2 + (p.im - x.im) ^ 2 < ρ ^ 2 := (Real.sqrt_lt' hρpos).1 hpρ
    have hre : |p.re - x.re| < ρ :=
      abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (p.im - x.im)]) hρpos.le
    have him : |p.im - x.im| < ρ :=
      abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (p.re - x.re)]) hρpos.le
    set u : ℝ := (p.re - x.re) / r with hu
    set v : ℝ := (p.im - x.im) / r with hv
    have hu' : |u| < (M : ℝ) := by
      rw [hu, abs_div, abs_of_pos hr]
      have : |p.re - x.re| / r < ρ / r := by gcongr
      linarith
    have hv' : |v| < (M : ℝ) := by
      rw [hv, abs_div, abs_of_pos hr]
      have : |p.im - x.im| / r < ρ / r := by gcongr
      linarith
    obtain ⟨hu_lo, hu_hi⟩ := abs_lt.1 hu'
    obtain ⟨hv_lo, hv_hi⟩ := abs_lt.1 hv'
    set a : ℤ := ⌊u + 1 / 2⌋ with ha
    set b : ℤ := ⌊v + 1 / 2⌋ with hb
    have ha1 : (a : ℝ) ≤ u + 1 / 2 := Int.floor_le _
    have ha2 : u + 1 / 2 < (a : ℝ) + 1 := Int.lt_floor_add_one _
    have hb1 : (b : ℝ) ≤ v + 1 / 2 := Int.floor_le _
    have hb2 : v + 1 / 2 < (b : ℝ) + 1 := Int.lt_floor_add_one _
    have haM : a ∈ Finset.Icc (-M) M := by
      rw [Finset.mem_Icc]
      constructor
      · have h : (-M - 1 : ℝ) < a := by linarith
        have h' : (-M - 1 : ℤ) < a := by exact_mod_cast h
        omega
      · have h : (a : ℝ) < M + 1 := by linarith
        have h' : a < M + 1 := by exact_mod_cast h
        omega
    have hbM : b ∈ Finset.Icc (-M) M := by
      rw [Finset.mem_Icc]
      constructor
      · have h : (-M - 1 : ℝ) < b := by linarith
        have h' : (-M - 1 : ℤ) < b := by exact_mod_cast h
        omega
      · have h : (b : ℝ) < M + 1 := by linarith
        have h' : b < M + 1 := by exact_mod_cast h
        omega
    refine ⟨x + (r : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I),
      Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨haM, hbM⟩, rfl⟩, ?_⟩
    rw [mem_ball, Complex.dist_eq_re_im]
    have hyre : (x + (r : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I)).re = x.re + r * a := by simp
    have hyim : (x + (r : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I)).im = x.im + r * b := by simp
    rw [hyre, hyim]
    apply (Real.sqrt_lt' hr).2
    have e1 : p.re - (x.re + r * a) = r * (u - a) := by
      rw [hu]; field_simp; ring
    have e2 : p.im - (x.im + r * b) = r * (v - b) := by
      rw [hv]; field_simp; ring
    rw [e1, e2]
    have f1 : (u - a) ^ 2 ≤ 1 / 4 := by nlinarith
    have f2 : (v - b) ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left f1 (sq_nonneg r), mul_le_mul_of_nonneg_left f2 (sq_nonneg r),
      pow_pos hr 2]

/-- A quantitative disc cover whose centres lie in an enlarged disc. -/
theorem exists_grid_cover_local (x : ℂ) {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : 0 < r) :
    ∃ Y : Finset ℂ, (Y.card : ℝ) ≤ (3 + 2 * ρ / r) ^ 2 ∧
      (∀ y ∈ Y, y ∈ ball x (ρ + r)) ∧
      ∀ p ∈ ball x ρ, ∃ y ∈ Y, p ∈ ball y r := by
  classical
  obtain ⟨Y, hY, hcover⟩ := exists_grid_cover x hρ hr
  refine ⟨Y.filter (fun y => y ∈ ball x (ρ + r)), ?_, ?_, ?_⟩
  · exact (by exact_mod_cast Finset.card_filter_le _ _ :
      ((Y.filter (fun y => y ∈ ball x (ρ + r))).card : ℝ) ≤ Y.card).trans hY
  · intro y hy
    exact (Finset.mem_filter.mp hy).2
  · intro p hp
    obtain ⟨y, hy, hpy⟩ := hcover p hp
    refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, hpy⟩
    change dist y x < ρ + r
    have hp' : dist p x < ρ := hp
    have hpy' : dist p y < r := hpy
    calc
      dist y x ≤ dist y p + dist p x := dist_triangle y p x
      _ < r + ρ := by rw [dist_comm y p]; linarith
      _ = ρ + r := add_comm _ _

/-- A local uniform lower-tail bound controls a ball at a dependent centre,
with an explicit finite net and its quantitative size. -/
theorem exists_measure_randomCentre_planar_ball_mass_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (z : Ω → ℂ) (x : ℂ) {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : 0 < r)
    (t p : ℝ≥0∞)
    (htail : ∀ y ∈ ball x (ρ + r), P {ω | μ ω (ball y r) ≤ t} ≤ p) :
    ∃ Y : Finset ℂ, (Y.card : ℝ) ≤ (3 + 2 * ρ / r) ^ 2 ∧
      P {ω | z ω ∈ ball x ρ ∧ μ ω (ball (z ω) (2 * r)) ≤ t} ≤ Y.card * p := by
  obtain ⟨Y, hY, hlocal, hcover⟩ := exists_grid_cover_local x hρ hr
  refine ⟨Y, hY, ?_⟩
  apply measure_randomCentre_ball_mass_le_card_mul P μ z (ball x ρ) Y id r t p
  · intro a ha
    obtain ⟨y, hy, hay⟩ := hcover a ha
    exact ⟨y, hy, by simpa [dist_comm] using hay⟩
  · intro y hy
    exact htail y (hlocal y hy)

end LatticeProb
