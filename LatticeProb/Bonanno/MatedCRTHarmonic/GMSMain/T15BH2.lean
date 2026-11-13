/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T15BH2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Cells

/-!
Boundary-value bounds for [18], equation (1.6),
used in the Hölder boundary estimate (3.32).
-/

set_option autoImplicit false

namespace MatedCRTHarmonic.GMSMain.T15BH2

open Set Metric MatedCRTHarmonic.GMS3

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- (1.6) values are bounded by any bound of `|f|` on `∂D`. -/
theorem abs_sSup_image_le {D : Set ℂ} {f : ℂ → ℝ} {M : ℝ}
    (hM : ∀ z ∈ frontier D, |f z| ≤ M) {x : V} (hx : (H.cell x ∩ frontier D).Nonempty) :
    |sSup (f '' (H.cell x ∩ frontier D))| ≤ M := by
  obtain ⟨z₀, hz₀⟩ := hx
  have hne : (f '' (H.cell x ∩ frontier D)).Nonempty := ⟨f z₀, z₀, hz₀, rfl⟩
  have hbdd : BddAbove (f '' (H.cell x ∩ frontier D)) := by
    refine ⟨M, ?_⟩
    rintro a ⟨z, hz, rfl⟩
    exact (le_abs_self _).trans (hM z hz.2)
  apply abs_le.mpr
  constructor
  · have hlow := (abs_le.mp (hM z₀ hz₀.2)).1
    exact hlow.trans (le_csSup hbdd ⟨z₀, hz₀, rfl⟩)
  · apply csSup_le hne
    rintro a ⟨z, hz, rfl⟩
    exact (le_abs_self _).trans (hM z hz.2)

/-- (1.6) values inherit a Hölder bound of `f` on `∂D`: for cells meeting `∂D` and any points `p ∈ H_x`, `q ∈ H_y`. -/
theorem abs_sSup_image_sub_le {D : Set ℂ} {f : ℂ → ℝ} {Cf χ : ℝ} (hCf : 0 ≤ Cf) (hχ : 0 < χ)
    (hf : ∀ z ∈ frontier D, ∀ w ∈ frontier D, |f z - f w| ≤ Cf * dist z w ^ χ)
    {x y : V} (hx : (H.cell x ∩ frontier D).Nonempty) (hy : (H.cell y ∩ frontier D).Nonempty)
    {p q : ℂ} (hp : p ∈ H.cell x) (hq : q ∈ H.cell y) :
    |sSup (f '' (H.cell x ∩ frontier D)) - sSup (f '' (H.cell y ∩ frontier D))| ≤
      Cf * (diam (H.cell x) + dist p q + diam (H.cell y)) ^ χ := by
  have hbdd (u : V) (hu : (H.cell u ∩ frontier D).Nonempty) :
      BddAbove (f '' (H.cell u ∩ frontier D)) := by
    obtain ⟨z₀, hz₀⟩ := hu
    refine ⟨f z₀ + Cf * (diam (H.cell u)) ^ χ, ?_⟩
    rintro a ⟨z, hz, rfl⟩
    have hd : dist z z₀ ≤ diam (H.cell u) := dist_le_cellDiam H hz.1 hz₀.1
    have hpow := Real.rpow_le_rpow (dist_nonneg) hd (le_of_lt hχ)
    have hmul := mul_le_mul_of_nonneg_left hpow hCf
    have habs := (abs_le.mp (hf z hz.2 z₀ hz₀.2)).2
    linarith only [habs, hmul]
  have hne (u : V) (hu : (H.cell u ∩ frontier D).Nonempty) :
      (f '' (H.cell u ∩ frontier D)).Nonempty := by
    obtain ⟨z, hz⟩ := hu
    exact ⟨f z, z, hz, rfl⟩
  have hdist {z w : ℂ} (hz : z ∈ H.cell x) (hw : w ∈ H.cell y) :
      dist z w ≤ diam (H.cell x) + dist p q + diam (H.cell y) := by
    calc
      dist z w ≤ dist z p + dist p q + dist q w := by
        have h₁ := dist_triangle z p w
        have h₂ := dist_triangle p q w
        linarith only [h₁, h₂]
      _ ≤ diam (H.cell x) + dist p q + diam (H.cell y) := by
        have h₁ : dist z p ≤ diam (H.cell x) := dist_le_cellDiam H hz hp
        have h₂ : dist q w ≤ diam (H.cell y) := dist_le_cellDiam H hq hw
        linarith only [h₁, h₂]
  have hcross {z w : ℂ} (hz : z ∈ H.cell x ∩ frontier D)
      (hw : w ∈ H.cell y ∩ frontier D) :
      |f z - f w| ≤ Cf * (diam (H.cell x) + dist p q + diam (H.cell y)) ^ χ := by
    have hpow := Real.rpow_le_rpow (dist_nonneg) (hdist hz.1 hw.1) (le_of_lt hχ)
    exact (hf z hz.2 w hw.2).trans (mul_le_mul_of_nonneg_left hpow hCf)
  have hxy : sSup (f '' (H.cell x ∩ frontier D)) ≤
      sSup (f '' (H.cell y ∩ frontier D)) +
        Cf * (diam (H.cell x) + dist p q + diam (H.cell y)) ^ χ := by
    obtain ⟨w, hw⟩ := hy
    apply csSup_le (hne x hx)
    rintro a ⟨z, hz, rfl⟩
    have h := (abs_le.mp (hcross hz hw)).2
    have hfw : f w ≤ sSup (f '' (H.cell y ∩ frontier D)) :=
      le_csSup (hbdd y ⟨w, hw⟩) ⟨w, hw, rfl⟩
    linarith only [h, hfw]
  have hyx : sSup (f '' (H.cell y ∩ frontier D)) ≤
      sSup (f '' (H.cell x ∩ frontier D)) +
        Cf * (diam (H.cell x) + dist p q + diam (H.cell y)) ^ χ := by
    obtain ⟨z, hz⟩ := hx
    apply csSup_le (hne y hy)
    rintro a ⟨w, hw, rfl⟩
    have h := (abs_le.mp (hcross hz hw)).1
    have hfz : f z ≤ sSup (f '' (H.cell x ∩ frontier D)) :=
      le_csSup (hbdd x ⟨z, hz⟩) ⟨z, hz, rfl⟩
    linarith only [h, hfz]
  exact abs_le.mpr ⟨by linarith only [hyx], by linarith only [hxy]⟩

end MatedCRTHarmonic.GMSMain.T15BH2
