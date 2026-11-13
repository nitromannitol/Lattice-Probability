/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PolygonalCost.FourBand at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PolygonalCost.BandRational
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.RingSeparation




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.PolygonalCost

open LQGMetric LQGMetric.LFPP

private theorem sB_sides_dense :
    (∀ x ∈ (DDDF.sB (0, 0)).side₁, ∀ ρ : ℝ, 0 < ρ →
      ∃ q ∈ gaussRat ∩ (DDDF.sB (0, 0)).side₁, ‖q - x‖ < ρ) ∧
    (∀ x ∈ (DDDF.sB (0, 0)).side₂, ∀ ρ : ℝ, 0 < ρ →
      ∃ q ∈ gaussRat ∩ (DDDF.sB (0, 0)).side₂, ‖q - x‖ < ρ) := by
  simpa [DDDF.sB] using rational_markedRect_sides_dense (-1) (-1) 3 1 true
    (by norm_num) (by norm_num)

private theorem sT_sides_dense :
    (∀ x ∈ (DDDF.sT (0, 0)).side₁, ∀ ρ : ℝ, 0 < ρ →
      ∃ q ∈ gaussRat ∩ (DDDF.sT (0, 0)).side₁, ‖q - x‖ < ρ) ∧
    (∀ x ∈ (DDDF.sT (0, 0)).side₂, ∀ ρ : ℝ, 0 < ρ →
      ∃ q ∈ gaussRat ∩ (DDDF.sT (0, 0)).side₂, ‖q - x‖ < ρ) := by
  simpa [DDDF.sT] using rational_markedRect_sides_dense (-1) 1 3 1 true
    (by norm_num) (by norm_num)

private theorem sL_sides_dense :
    (∀ x ∈ (DDDF.sL (0, 0)).side₁, ∀ ρ : ℝ, 0 < ρ →
      ∃ q ∈ gaussRat ∩ (DDDF.sL (0, 0)).side₁, ‖q - x‖ < ρ) ∧
    (∀ x ∈ (DDDF.sL (0, 0)).side₂, ∀ ρ : ℝ, 0 < ρ →
      ∃ q ∈ gaussRat ∩ (DDDF.sL (0, 0)).side₂, ‖q - x‖ < ρ) := by
  simpa [DDDF.sL] using rational_markedRect_sides_dense (-1) (-1) 1 3 false
    (by norm_num) (by norm_num)

private theorem sR_sides_dense :
    (∀ x ∈ (DDDF.sR (0, 0)).side₁, ∀ ρ : ℝ, 0 < ρ →
      ∃ q ∈ gaussRat ∩ (DDDF.sR (0, 0)).side₁, ‖q - x‖ < ρ) ∧
    (∀ x ∈ (DDDF.sR (0, 0)).side₂, ∀ ρ : ℝ, 0 < ρ →
      ∃ q ∈ gaussRat ∩ (DDDF.sR (0, 0)).side₂, ‖q - x‖ < ρ) := by
  simpa [DDDF.sR] using rational_markedRect_sides_dense 1 (-1) 1 3 false
    (by norm_num) (by norm_num)

 
def closedSquareAnnulus : Set ℂ :=
  (Icc (-1 : ℝ) 2 ×ℂ Icc (-1 : ℝ) 2) \
    (Ioo (0 : ℝ) 1 ×ℂ Ioo (0 : ℝ) 1)

private theorem sB_subset_closedSquareAnnulus :
    (DDDF.sB (0, 0)).toSet ⊆ closedSquareAnnulus := by
  intro z hz
  simp only [DDDF.sB, DDDF.MarkedRect.toSet, Complex.mem_reProdIm] at hz
  norm_num at hz
  simp only [closedSquareAnnulus, mem_sdiff, Complex.mem_reProdIm]
  refine ⟨⟨hz.1, ⟨hz.2.1, hz.2.2.trans (by norm_num)⟩⟩, ?_⟩
  rintro ⟨_, hi⟩
  linarith [hi.1, hz.2.2]

private theorem sT_subset_closedSquareAnnulus :
    (DDDF.sT (0, 0)).toSet ⊆ closedSquareAnnulus := by
  intro z hz
  simp only [DDDF.sT, DDDF.MarkedRect.toSet, Complex.mem_reProdIm] at hz
  norm_num at hz
  simp only [closedSquareAnnulus, mem_sdiff, Complex.mem_reProdIm]
  refine ⟨⟨hz.1, ⟨by linarith [hz.2.1], hz.2.2⟩⟩, ?_⟩
  rintro ⟨_, hi⟩
  linarith [hi.2, hz.2.1]

private theorem sL_subset_closedSquareAnnulus :
    (DDDF.sL (0, 0)).toSet ⊆ closedSquareAnnulus := by
  intro z hz
  simp only [DDDF.sL, DDDF.MarkedRect.toSet, Complex.mem_reProdIm] at hz
  norm_num at hz
  simp only [closedSquareAnnulus, mem_sdiff, Complex.mem_reProdIm]
  refine ⟨⟨⟨hz.1.1, hz.1.2.trans (by norm_num)⟩, hz.2⟩, ?_⟩
  rintro ⟨hr, _⟩
  linarith [hr.1, hz.1.2]

private theorem sR_subset_closedSquareAnnulus :
    (DDDF.sR (0, 0)).toSet ⊆ closedSquareAnnulus := by
  intro z hz
  simp only [DDDF.sR, DDDF.MarkedRect.toSet, Complex.mem_reProdIm] at hz
  norm_num at hz
  simp only [closedSquareAnnulus, mem_sdiff, Complex.mem_reProdIm]
  refine ⟨⟨⟨by linarith [hz.1.1], hz.1.2⟩, hz.2⟩, ?_⟩
  rintro ⟨hr, _⟩
  linarith [hr.2, hz.1.1]

 
structure RationalFourBand (ξ : ℝ) (f : ℂ → ℝ) where
  nB : ℕ
  vB : ℕ → ℂ
  nT : ℕ
  vT : ℕ → ℂ
  nL : ℕ
  vL : ℕ → ℂ
  nR : ℕ
  vR : ℕ → ℂ
  ratB : ∀ i ≤ nB, vB i ∈ gaussRat
  ratT : ∀ i ≤ nT, vT i ∈ gaussRat
  ratL : ∀ i ≤ nL, vL i ∈ gaussRat
  ratR : ∀ i ≤ nR, vR i ∈ gaussRat
  crossB : DDDF.AdmPath (DDDF.sB (0, 0)).toSet
    (DDDF.sB (0, 0)).side₁ (DDDF.sB (0, 0)).side₂ (Exponent.PolygonCofinality.polygonPath vB nB)
  crossT : DDDF.AdmPath (DDDF.sT (0, 0)).toSet
    (DDDF.sT (0, 0)).side₁ (DDDF.sT (0, 0)).side₂ (Exponent.PolygonCofinality.polygonPath vT nT)
  crossL : DDDF.AdmPath (DDDF.sL (0, 0)).toSet
    (DDDF.sL (0, 0)).side₁ (DDDF.sL (0, 0)).side₂ (Exponent.PolygonCofinality.polygonPath vL nL)
  crossR : DDDF.AdmPath (DDDF.sR (0, 0)).toSet
    (DDDF.sR (0, 0)).side₁ (DDDF.sR (0, 0)).side₂ (Exponent.PolygonCofinality.polygonPath vR nR)

namespace RationalFourBand

variable {ξ : ℝ} {f : ℂ → ℝ}

def cost (F : RationalFourBand ξ f) : ℝ≥0∞ :=
  lfppLen ξ f (Exponent.PolygonCofinality.polygonPath F.vB F.nB) +
    lfppLen ξ f (Exponent.PolygonCofinality.polygonPath F.vT F.nT) +
    lfppLen ξ f (Exponent.PolygonCofinality.polygonPath F.vL F.nL) +
    lfppLen ξ f (Exponent.PolygonCofinality.polygonPath F.vR F.nR)

def trace (F : RationalFourBand ξ f) : Set ℂ :=
  Exponent.PolygonCofinality.polygonPath F.vB F.nB '' Icc (0 : ℝ) 1 ∪
    Exponent.PolygonCofinality.polygonPath F.vT F.nT '' Icc (0 : ℝ) 1 ∪
    Exponent.PolygonCofinality.polygonPath F.vL F.nL '' Icc (0 : ℝ) 1 ∪
    Exponent.PolygonCofinality.polygonPath F.vR F.nR '' Icc (0 : ℝ) 1

 
theorem trace_subset_closedSquareAnnulus (F : RationalFourBand ξ f) :
    F.trace ⊆ closedSquareAnnulus := by
  intro z hz
  obtain ⟨_, _, _, _, _, hmB⟩ := F.crossB
  obtain ⟨_, _, _, _, _, hmT⟩ := F.crossT
  obtain ⟨_, _, _, _, _, hmL⟩ := F.crossL
  obtain ⟨_, _, _, _, _, hmR⟩ := F.crossR
  change z ∈ _ ∪ _ ∪ _ ∪ _ at hz
  rcases hz with (((hB | hT) | hL) | hR)
  · obtain ⟨t, ht, rfl⟩ := hB
    exact sB_subset_closedSquareAnnulus (hmB t ht)
  · obtain ⟨t, ht, rfl⟩ := hT
    exact sT_subset_closedSquareAnnulus (hmT t ht)
  · obtain ⟨t, ht, rfl⟩ := hL
    exact sL_subset_closedSquareAnnulus (hmL t ht)
  · obtain ⟨t, ht, rfl⟩ := hR
    exact sR_subset_closedSquareAnnulus (hmR t ht)

 
theorem disconnects (F : RationalFourBand ξ f) :
    LQGMetric.Disconnects F.trace
      (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1)
      (Ioo (-1 : ℝ) 2 ×ℂ Ioo (-1 : ℝ) 2)ᶜ := by
  let C : DDDF.SiteCirc ξ f (0, 0) F.cost := {
    B := Exponent.PolygonCofinality.polygonPath F.vB F.nB
    T := Exponent.PolygonCofinality.polygonPath F.vT F.nT
    L := Exponent.PolygonCofinality.polygonPath F.vL F.nL
    R := Exponent.PolygonCofinality.polygonPath F.vR F.nR
    hB := F.crossB
    hT := F.crossT
    hL := F.crossL
    hR := F.crossR
    hc := le_rfl
  }
  exact RingSeparation.siteCirc_union_pathHit C

end RationalFourBand

 

theorem exists_rational_four_band_le {ξ : ℝ} {f : ℂ → ℝ} (hf : Continuous f)
    {B T L R : ℝ → ℂ}
    (hB : DDDF.AdmPath (DDDF.sB (0, 0)).toSet
      (DDDF.sB (0, 0)).side₁ (DDDF.sB (0, 0)).side₂ B)
    (hT : DDDF.AdmPath (DDDF.sT (0, 0)).toSet
      (DDDF.sT (0, 0)).side₁ (DDDF.sT (0, 0)).side₂ T)
    (hL : DDDF.AdmPath (DDDF.sL (0, 0)).toSet
      (DDDF.sL (0, 0)).side₁ (DDDF.sL (0, 0)).side₂ L)
    (hR : DDDF.AdmPath (DDDF.sR (0, 0)).toSet
      (DDDF.sR (0, 0)).side₁ (DDDF.sR (0, 0)).side₂ R)
    {η : ℝ} (hη : 0 < η) :
    ∃ F : RationalFourBand ξ f,
      LQGMetric.Disconnects F.trace
        (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1)
        (Ioo (-1 : ℝ) 2 ×ℂ Ioo (-1 : ℝ) 2)ᶜ ∧
      F.cost ≤ lfppLen ξ f B + lfppLen ξ f T +
        lfppLen ξ f L + lfppLen ξ f R + ENNReal.ofReal η := by
  have hη4 : 0 < η / 4 := by positivity
  obtain ⟨nB, vB, hrB, hpB, hcB⟩ :=
    admPath_exists_gaussRat_polygon_le (ξ := ξ) hf (DDDF.sB (0, 0))
      (by norm_num [DDDF.sB]) (by norm_num [DDDF.sB])
      sB_sides_dense.1 sB_sides_dense.2 hB hη4
  obtain ⟨nT, vT, hrT, hpT, hcT⟩ :=
    admPath_exists_gaussRat_polygon_le (ξ := ξ) hf (DDDF.sT (0, 0))
      (by norm_num [DDDF.sT]) (by norm_num [DDDF.sT])
      sT_sides_dense.1 sT_sides_dense.2 hT hη4
  obtain ⟨nL, vL, hrL, hpL, hcL⟩ :=
    admPath_exists_gaussRat_polygon_le (ξ := ξ) hf (DDDF.sL (0, 0))
      (by norm_num [DDDF.sL]) (by norm_num [DDDF.sL])
      sL_sides_dense.1 sL_sides_dense.2 hL hη4
  obtain ⟨nR, vR, hrR, hpR, hcR⟩ :=
    admPath_exists_gaussRat_polygon_le (ξ := ξ) hf (DDDF.sR (0, 0))
      (by norm_num [DDDF.sR]) (by norm_num [DDDF.sR])
      sR_sides_dense.1 sR_sides_dense.2 hR hη4
  let F : RationalFourBand ξ f := {
    nB := nB
    vB := vB
    nT := nT
    vT := vT
    nL := nL
    vL := vL
    nR := nR
    vR := vR
    ratB := hrB
    ratT := hrT
    ratL := hrL
    ratR := hrR
    crossB := hpB
    crossT := hpT
    crossL := hpL
    crossR := hpR
  }
  refine ⟨F, F.disconnects, ?_⟩
  have hsum := add_le_add (add_le_add (add_le_add hcB hcT) hcL) hcR
  have hreal : η / 4 + η / 4 + η / 4 + η / 4 = η := by ring
  calc
    F.cost ≤ (lfppLen ξ f B + ENNReal.ofReal (η / 4)) +
        (lfppLen ξ f T + ENNReal.ofReal (η / 4)) +
        (lfppLen ξ f L + ENNReal.ofReal (η / 4)) +
        (lfppLen ξ f R + ENNReal.ofReal (η / 4)) := hsum
    _ = lfppLen ξ f B + lfppLen ξ f T + lfppLen ξ f L +
        lfppLen ξ f R +
        (ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) +
          ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4)) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), hreal]



end SupercriticalLQGUniqueness.Exponent.PolygonalCost
