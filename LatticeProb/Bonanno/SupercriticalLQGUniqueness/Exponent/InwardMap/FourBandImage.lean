/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.FourBandImage at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.FourBandCarrier




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

variable {ξ : ℝ} {f : ℂ → ℝ}

def mappedFourBandFamily (a : ℚ) (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    Exponent.PolygonalCost.RatPolygonFamily :=
  let S := fourBandRatFamily F
  appendFamilies
    (appendFamilies
      (appendFamilies
        (canonicalImagePolygonFamily a (S.paths 0))
        (canonicalImagePolygonFamily a (S.paths 1)))
      (canonicalImagePolygonFamily a (S.paths 2)))
    (canonicalImagePolygonFamily a (S.paths 3))

private theorem fourBand_path_subset_closed (F : Exponent.PolygonalCost.RationalFourBand ξ f)
    (i : Fin 4) :
    ((fourBandRatFamily F).paths i).path '' Icc (0:ℝ) 1 ⊆
      Exponent.PolygonalCost.closedSquareAnnulus := by
  intro z hz
  apply F.trace_subset_closedSquareAnnulus
  rw [← fourBandRatFamily_trace F, ratFamily_trace_iUnion]
  exact Set.mem_iUnion_of_mem i hz

private theorem fourBand_source_trace_union (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    let S := fourBandRatFamily F
    S.trace =
      (((S.paths 0).path '' Icc (0:ℝ) 1 ∪
        (S.paths 1).path '' Icc (0:ℝ) 1) ∪
        (S.paths 2).path '' Icc (0:ℝ) 1) ∪
        (S.paths 3).path '' Icc (0:ℝ) 1 := by
  let S := fourBandRatFamily F
  dsimp only
  rw [ratFamily_trace_iUnion]
  ext z
  change z ∈ (⋃ i : Fin 4, (S.paths i).path '' Icc (0:ℝ) 1) ↔ _
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    fin_cases i
    · exact Or.inl (Or.inl (Or.inl (by simpa [S, fourBandRatFamily,
        bandPolygon_path] using hi)))
    · exact Or.inl (Or.inl (Or.inr (by simpa [S, fourBandRatFamily,
        bandPolygon_path] using hi)))
    · exact Or.inl (Or.inr (by simpa [S, fourBandRatFamily,
        bandPolygon_path] using hi))
    · exact Or.inr (by simpa [S, fourBandRatFamily,
        bandPolygon_path] using hi)
  · rintro (((h0 | h1) | h2) | h3)
    · exact Set.mem_iUnion.mpr ⟨0, h0⟩
    · exact Set.mem_iUnion.mpr ⟨1, h1⟩
    · exact Set.mem_iUnion.mpr ⟨2, h2⟩
    · exact Set.mem_iUnion.mpr ⟨3, h3⟩

private theorem fourBand_source_cost_sum (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    let S := fourBandRatFamily F
    S.cost ξ f =
      lfppLen ξ f (S.paths 0).path + lfppLen ξ f (S.paths 1).path +
        lfppLen ξ f (S.paths 2).path + lfppLen ξ f (S.paths 3).path := by
  let S := fourBandRatFamily F
  dsimp only
  change (∑ i : Fin 4, lfppLen ξ f (S.paths i).path) = _
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp [S, fourBandRatFamily, bandPolygon_path]
  ac_rfl

theorem mappedFourBandFamily_trace (a : ℚ) (ha : 0 ≤ a)
    (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    (mappedFourBandFamily a F).trace = inwardMap (a:ℝ) '' F.trace := by
  let S := fourBandRatFamily F
  let K : Set ℂ :=
    (((S.paths 0).path '' Icc (0:ℝ) 1 ∪
      (S.paths 1).path '' Icc (0:ℝ) 1) ∪
      (S.paths 2).path '' Icc (0:ℝ) 1) ∪
      (S.paths 3).path '' Icc (0:ℝ) 1
  have hs : S.trace = K := by
    simpa only [S, K] using fourBand_source_trace_union F
  calc
    (mappedFourBandFamily a F).trace = inwardMap (a:ℝ) '' K := by
      dsimp only [K]
      rw [mappedFourBandFamily, appendFamilies_trace,
        appendFamilies_trace, appendFamilies_trace]
      rw [canonicalImagePolygonFamily_trace a ha,
        canonicalImagePolygonFamily_trace a ha,
        canonicalImagePolygonFamily_trace a ha,
        canonicalImagePolygonFamily_trace a ha]
      rw [Set.image_union, Set.image_union, Set.image_union]
    _ = inwardMap (a:ℝ) '' S.trace := congrArg _ hs.symm
    _ = inwardMap (a:ℝ) '' F.trace := by rw [fourBandRatFamily_trace]

theorem mappedFourBandFamily_cost_le (a : ℚ) (ha0 : 0 ≤ a)
    (ha : (a:ℝ) ≤ 1/256) (ξ G : ℝ) (hξ : 0 ≤ ξ) (hG0 : 0 ≤ G)
    (f : ℂ → ℝ)
    (hfd : ∀ z ∈ gradientBox, DifferentiableAt ℝ f z)
    (hG : ∀ z ∈ gradientBox, ‖fderiv ℝ f z‖ ≤ G)
    (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    (mappedFourBandFamily a F).cost ξ f ≤
      ENNReal.ofReal ((5/4:ℝ)*Real.exp
        (32*Real.sqrt 2*ξ*((a:ℝ)*G))) * F.cost := by
  let S := fourBandRatFamily F
  let C := ENNReal.ofReal ((5/4:ℝ)*Real.exp
    (32*Real.sqrt 2*ξ*((a:ℝ)*G)))
  have hi (i : Fin 4) :
      (canonicalImagePolygonFamily a (S.paths i)).cost ξ f ≤
        C * lfppLen ξ f (S.paths i).path :=
    canonicalImagePolygonFamily_cost_le a ha0 ha ξ G hξ hG0 f hfd hG
      (S.paths i) (fourBand_path_subset_closed F i)
  have hs : S.cost ξ f =
      lfppLen ξ f (S.paths 0).path + lfppLen ξ f (S.paths 1).path +
        lfppLen ξ f (S.paths 2).path + lfppLen ξ f (S.paths 3).path := by
    simpa only [S] using fourBand_source_cost_sum F
  change (appendFamilies (appendFamilies (appendFamilies
      (canonicalImagePolygonFamily a (S.paths 0))
      (canonicalImagePolygonFamily a (S.paths 1)))
      (canonicalImagePolygonFamily a (S.paths 2)))
      (canonicalImagePolygonFamily a (S.paths 3))).cost ξ f ≤ C * F.cost
  rw [appendFamilies_cost, appendFamilies_cost, appendFamilies_cost]
  calc
    _ ≤ C * lfppLen ξ f (S.paths 0).path +
        C * lfppLen ξ f (S.paths 1).path +
        C * lfppLen ξ f (S.paths 2).path +
        C * lfppLen ξ f (S.paths 3).path := by
      exact add_le_add (add_le_add (add_le_add (hi 0) (hi 1)) (hi 2)) (hi 3)
    _ = C * S.cost ξ f := by rw [hs]; ring
    _ = C * F.cost := by rw [fourBandRatFamily_cost]

theorem mappedFourBandFamily_admitted (a : ℚ) (ha0 : 0 < a)
    (ha : (a:ℝ) ≤ 1/256) (ξ : ℝ) (f : ℂ → ℝ)
    (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    (mappedFourBandFamily a F).Admitted := by
  rw [Exponent.PolygonalCost.RatPolygonFamily.Admitted,
    mappedFourBandFamily_trace a ha0.le F]
  constructor
  · rintro z ⟨w, hw, rfl⟩
    exact inwardMap_closed_to_open (a:ℝ) (by exact_mod_cast ha0)
      ha (F.trace_subset_closedSquareAnnulus hw)
  · exact inwardMap_preserves_disconnects (a:ℝ)
      (by exact_mod_cast ha0) ha _ F.disconnects


end SupercriticalLQGUniqueness.Exponent.InwardMap
