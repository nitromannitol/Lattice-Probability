/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PolygonalCost.BandRational at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PolygonalCost.RationalRect
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PolygonCofinality
import LatticeProb.Bonanno.LQGMetric.LFPP.PathConcat




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.PolygonalCost

open LQGMetric LQGMetric.LFPP

private theorem concat_mem {S : Set ℂ} {P Q : ℝ → ℂ}
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ S)
    (hQ : ∀ t ∈ Icc (0 : ℝ) 1, Q t ∈ S) :
    ∀ t ∈ Icc (0 : ℝ) 1, concatPath P Q t ∈ S := by
  intro t ht
  unfold concatPath
  split_ifs with h
  · exact hP _ ⟨by linarith [ht.1], by linarith⟩
  · exact hQ _ ⟨by linarith [not_le.mp h], by linarith [ht.2]⟩

private theorem side₁_subset_toSet (R : DDDF.MarkedRect) (hw : 0 ≤ R.w)
    (hh : 0 ≤ R.h) : R.side₁ ⊆ R.toSet := by
  intro z hz
  cases h : R.horiz with
  | true =>
    simp only [DDDF.MarkedRect.side₁, h, ite_true, Complex.mem_reProdIm,
      mem_singleton_iff] at hz
    simp only [DDDF.MarkedRect.toSet, Complex.mem_reProdIm]
    exact ⟨⟨by rw [hz.1], by rw [hz.1]; linarith⟩, hz.2⟩
  | false =>
    simp only [DDDF.MarkedRect.side₁, h, Bool.false_eq_true, ite_false,
      Complex.mem_reProdIm, mem_singleton_iff] at hz
    simp only [DDDF.MarkedRect.toSet, Complex.mem_reProdIm]
    exact ⟨hz.1, ⟨by rw [hz.2], by rw [hz.2]; linarith⟩⟩

private theorem side₂_subset_toSet (R : DDDF.MarkedRect) (hw : 0 ≤ R.w)
    (hh : 0 ≤ R.h) : R.side₂ ⊆ R.toSet := by
  intro z hz
  cases h : R.horiz with
  | true =>
    simp only [DDDF.MarkedRect.side₂, h, ite_true, Complex.mem_reProdIm,
      mem_singleton_iff] at hz
    simp only [DDDF.MarkedRect.toSet, Complex.mem_reProdIm]
    exact ⟨⟨by rw [hz.1]; linarith, hz.1.le⟩, hz.2⟩
  | false =>
    simp only [DDDF.MarkedRect.side₂, h, Bool.false_eq_true, ite_false,
      Complex.mem_reProdIm, mem_singleton_iff] at hz
    simp only [DDDF.MarkedRect.toSet, Complex.mem_reProdIm]
    exact ⟨hz.1, ⟨by rw [hz.2]; linarith, hz.2.le⟩⟩

 
theorem rational_markedRect_sides_dense (x0 y0 w h : ℚ) (b : Bool)
    (hw : 0 < w) (hh : 0 < h) :
    let R : DDDF.MarkedRect := ⟨(x0 : ℝ), (y0 : ℝ), (w : ℝ), (h : ℝ), b⟩
    (∀ x ∈ R.side₁, ∀ ρ : ℝ, 0 < ρ →
      ∃ q ∈ gaussRat ∩ R.side₁, ‖q - x‖ < ρ) ∧
    (∀ x ∈ R.side₂, ∀ ρ : ℝ, 0 < ρ →
      ∃ q ∈ gaussRat ∩ R.side₂, ‖q - x‖ < ρ) := by
  have hhr : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hwr : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  dsimp only
  cases b with
  | true =>
    constructor
    · intro x hx ρ hρ
      exact gaussRat_vertical_side_dense x0
        (by linarith [hhr]) x
        (by simpa [DDDF.MarkedRect.side₁] using hx) ρ hρ
    · intro x hx ρ hρ
      simpa [DDDF.MarkedRect.side₂, Rat.cast_add] using
        (gaussRat_vertical_side_dense (x0 + w)
          (by linarith [hhr]) x
          (by simpa [DDDF.MarkedRect.side₂, Rat.cast_add] using hx) ρ hρ)
  | false =>
    constructor
    · intro x hx ρ hρ
      exact gaussRat_horizontal_side_dense y0
        (by linarith [hwr]) x
        (by simpa [DDDF.MarkedRect.side₁] using hx) ρ hρ
    · intro x hx ρ hρ
      simpa [DDDF.MarkedRect.side₂, Rat.cast_add] using
        (gaussRat_horizontal_side_dense (y0 + h)
          (by linarith [hwr]) x
          (by simpa [DDDF.MarkedRect.side₂, Rat.cast_add] using hx) ρ hρ)


 

theorem admPath_exists_gaussRat_polygon_le {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) (R : DDDF.MarkedRect) (hw : 0 < R.w) (hh : 0 < R.h)
    (hside₁ : ∀ x ∈ R.side₁, ∀ ρ : ℝ, 0 < ρ →
      ∃ q ∈ gaussRat ∩ R.side₁, ‖q - x‖ < ρ)
    (hside₂ : ∀ x ∈ R.side₂, ∀ ρ : ℝ, 0 < ρ →
      ∃ q ∈ gaussRat ∩ R.side₂, ‖q - x‖ < ρ)
    {P : ℝ → ℂ} (hP : DDDF.AdmPath R.toSet R.side₁ R.side₂ P)
    {η : ℝ} (hη : 0 < η) :
    ∃ (n : ℕ) (v : ℕ → ℂ),
      (∀ i ≤ n, v i ∈ gaussRat) ∧
      DDDF.AdmPath R.toSet R.side₁ R.side₂ (Exponent.PolygonCofinality.polygonPath v n) ∧
      lfppLen ξ f (Exponent.PolygonCofinality.polygonPath v n) ≤ lfppLen ξ f P + ENNReal.ofReal η := by
  obtain ⟨z, hz, w, hw', hpath, hmem⟩ := hP
  let S := R.toSet
  have hS : Convex ℝ S := Exponent.PolygonCofinality.convex_markedRect R
  have hsz : z ∈ S := side₁_subset_toSet R hw.le hh.le hz
  have hsw : w ∈ S := side₂_subset_toSet R hw.le hh.le hw'
  have hcompact : IsCompact S := R.isCompact_toSet
  obtain ⟨ρ, hρ, hshort⟩ := small_segCost_of_compact hcompact hf (show 0 < η / 4 by positivity)
  obtain ⟨qz, ⟨hqzrat, hqzside⟩, hqzclose⟩ := hside₁ z hz ρ hρ
  obtain ⟨qw, ⟨hqwrat, hqwside⟩, hqwclose⟩ := hside₂ w hw' ρ hρ
  have hqzS : qz ∈ S := side₁_subset_toSet R hw.le hh.le hqzside
  have hqwS : qw ∈ S := side₂_subset_toSet R hw.le hh.le hqwside
  let A := segPath qz z
  let B := segPath w qw
  let Q := concatPath A (concatPath P B)
  have hAz : IsPiecewiseC1Path A qz z := isPiecewiseC1Path_segPath qz z
  have hBw : IsPiecewiseC1Path B w qw := isPiecewiseC1Path_segPath w qw
  have hQ : IsPiecewiseC1Path Q qz qw :=
    isPiecewiseC1Path_concatPath hAz (isPiecewiseC1Path_concatPath hpath hBw)
  have hAS : ∀ t ∈ Icc (0 : ℝ) 1, A t ∈ S :=
    fun t ht => segPath_mem hS hqzS hsz ht
  have hBS : ∀ t ∈ Icc (0 : ℝ) 1, B t ∈ S :=
    fun t ht => segPath_mem hS hsw hqwS ht
  have hQS : ∀ t ∈ Icc (0 : ℝ) 1, Q t ∈ S :=
    concat_mem hAS (concat_mem hmem hBS)
  have hAB : A 1 = (concatPath P B) 0 := by
    simp [A, B, concatPath, segPath, hpath.source]
  have hPB : P 1 = B 0 := by simp [B, segPath, hpath.target]
  have hQlen : lfppLen ξ f Q = segCost ξ f qz z +
      (lfppLen ξ f P + segCost ξ f w qw) := by
    rw [show Q = concatPath A (concatPath P B) by rfl,
      lfppLen_concatPath hAB, lfppLen_concatPath hPB]
    rfl
  have hshortA : segCost ξ f qz z ≤ ENNReal.ofReal (η / 4) := by
    apply hshort qz hqzS z
    rw [norm_sub_rev]
    exact hqzclose
  have hshortB : segCost ξ f w qw ≤ ENNReal.ofReal (η / 4) :=
    hshort w hsw qw hqwclose
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨N, v, hv0, hvN, hvC, hcost⟩ :=
    exists_chain_le (ξ := ξ) (φ := f) (S := S) (C := gaussRat ∩ S)
      hf (fun x hx r hr => gaussRat_markedRect_dense R hw hh x hx r hr)
      hQ hQS hη2
  have hvS : ∀ i ≤ N + 1, v i ∈ S := by
    intro i hi
    by_cases h0 : i = 0
    · simpa [h0, hv0] using hqzS
    by_cases hlast : i = N + 1
    · simpa [hlast, hvN] using hqwS
    · exact (hvC i (by omega) (by omega)).2
  have hvRat : ∀ i ≤ N + 1, v i ∈ gaussRat := by
    intro i hi
    by_cases h0 : i = 0
    · simpa [h0, hv0] using hqzrat
    by_cases hlast : i = N + 1
    · simpa [hlast, hvN] using hqwrat
    · exact (hvC i (by omega) (by omega)).1
  obtain ⟨hpoly, hpolyS, hpolyLen⟩ := Exponent.PolygonCofinality.polygonPath_data hS v (N + 1) hvS
  refine ⟨N + 1, v, hvRat, ?_, ?_⟩
  · exact ⟨qz, hqzside, qw, hqwside, by simpa [hv0, hvN] using hpoly, hpolyS⟩
  · rw [hpolyLen]
    calc
      _ ≤ lfppLen ξ f Q + ENNReal.ofReal (η / 2) := hcost
      _ = segCost ξ f qz z + (lfppLen ξ f P + segCost ξ f w qw) +
          ENNReal.ofReal (η / 2) := by rw [hQlen]
      _ ≤ ENNReal.ofReal (η / 4) +
          (lfppLen ξ f P + ENNReal.ofReal (η / 4)) + ENNReal.ofReal (η / 2) := by
            exact add_le_add (add_le_add hshortA (add_le_add_right hshortB _)) le_rfl
      _ = lfppLen ξ f P + ENNReal.ofReal η := by
        have hreal : η / 4 + η / 4 + η / 2 = η := by ring
        calc
          _ = lfppLen ξ f P +
              (ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) +
                ENNReal.ofReal (η / 2)) := by ac_rfl
          _ = lfppLen ξ f P + ENNReal.ofReal (η / 4 + η / 4 + η / 2) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
          _ = _ := by rw [hreal]



end SupercriticalLQGUniqueness.Exponent.PolygonalCost
