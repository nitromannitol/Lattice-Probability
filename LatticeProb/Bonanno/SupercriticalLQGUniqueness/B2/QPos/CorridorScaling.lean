/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.CorridorScaling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.AnnulusGeometry
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRect
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DNum

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.QPos

def eastShift : ℂ := ⟨2 / 5, -1 / 16⟩

def eastInverse (z : ℂ) : ℂ :=
  ⟨8 * (z.re - 2 / 5), 8 * (z.im + 1 / 16)⟩

private theorem eastMot_re (z : ℂ) :
    (T20B.mot 3 1 eastShift z).re = 2 / 5 + z.re / 8 := by
  norm_num [T20B.mot, eastShift, Complex.mul_re, Complex.mul_im]
  ring

private theorem eastMot_im (z : ℂ) :
    (T20B.mot 3 1 eastShift z).im = -1 / 16 + z.im / 8 := by
  norm_num [T20B.mot, eastShift, Complex.mul_re, Complex.mul_im]
  ring

private theorem eastInverse_left (z : ℂ) :
    eastInverse (T20B.mot 3 1 eastShift z) = z := by
  apply Complex.ext
  · simp [eastInverse, eastMot_re]
    ring
  · simp [eastInverse, eastMot_im]
    ring

private theorem eastInverse_right (z : ℂ) :
    T20B.mot 3 1 eastShift (eastInverse z) = z := by
  apply Complex.ext
  · simp [eastInverse, eastMot_re]
  · simp [eastInverse, eastMot_im]
    ring

private theorem mem_eastMot_image_iff (S : Set ℂ) (z : ℂ) :
    z ∈ T20B.mot 3 1 eastShift '' S ↔ eastInverse z ∈ S := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [eastInverse_left] using hw
  · intro hz
    exact ⟨eastInverse z, hz, eastInverse_right z⟩

private theorem east_set_image :
    T20B.mot 3 1 eastShift '' (rectAB 3 1).toSet = eastCorridor.toSet := by
  ext z
  rw [mem_eastMot_image_iff]
  simp only [rectAB, MarkedRect.toSet, eastCorridor, Complex.mem_reProdIm,
    mem_Icc, eastInverse]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

private theorem east_side₁_image :
    T20B.mot 3 1 eastShift '' (rectAB 3 1).side₁ = eastCorridor.side₁ := by
  ext z
  rw [mem_eastMot_image_iff]
  simp only [rectAB, MarkedRect.side₁, eastCorridor,
    ↓reduceIte, Complex.mem_reProdIm, mem_singleton_iff, mem_Icc,
    eastInverse]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by linarith⟩

private theorem east_side₂_image :
    T20B.mot 3 1 eastShift '' (rectAB 3 1).side₂ = eastCorridor.side₂ := by
  ext z
  rw [mem_eastMot_image_iff]
  simp only [rectAB, MarkedRect.side₂, eastCorridor,
    ↓reduceIte, Complex.mem_reProdIm, mem_singleton_iff, mem_Icc,
    eastInverse]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by linarith⟩

 
theorem eastCorridor_rectLen_eq_mrectLen (ξ : ℝ) (f : ℂ → ℝ) :
    (rectLen ξ f eastCorridor).toReal = T20B.mrectLen ξ f 3 1 eastShift 3 1 := by
  unfold rectLen T20B.mrectLen
  rw [east_set_image, east_side₁_image, east_side₂_image]

 

theorem upperAnnulus_crossReal_le_mrectLen (ξ : ℝ) {f : ℂ → ℝ}
    (hf : Continuous f) :
    (crossLenIn ξ f upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal ≤
      T20B.mrectLen ξ f 3 1 eastShift 3 1 := by
  have hfin : rectLen ξ f eastCorridor ≠ ∞ :=
    rectLen_ne_top eastCorridor (by norm_num [eastCorridor])
      (by norm_num [eastCorridor]) hf
  have hle := upperAnnulus_crossLen_le_eastCorridor ξ f
  exact (ENNReal.toReal_mono hfin hle).trans_eq
    (eastCorridor_rectLen_eq_mrectLen ξ f)

 

theorem upperAnnulus_crossReal_le_of_field_cmp
    (ξ : ℝ) {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a : ℝ} (h : ∀ x ∈ eastCorridor.toSet, ξ * f x ≤ ξ * g x + a) :
    (crossLenIn ξ f upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal ≤
      Real.exp a * T20B.mrectLen ξ g 3 1 eastShift 3 1 := by
  calc
    _ ≤ T20B.mrectLen ξ f 3 1 eastShift 3 1 :=
      upperAnnulus_crossReal_le_mrectLen ξ hf
    _ ≤ Real.exp a * T20B.mrectLen ξ g 3 1 eastShift 3 1 := by
      apply T20D.mrectLen_le_of (K := 3) (j := (1, eastShift)) hg
      intro x hx
      exact h x (east_set_image ▸ hx)

end SupercriticalLQGUniqueness.B2.QPos
