/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.CanonicalCuts at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.MappedSegmentTrace




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

private theorem ratSegmentCuts_card_ge_two (p q : ℚ × ℚ) :
    2 ≤ (ratSegmentCuts p q).card := by
  have hs : ({0, 1} : Finset ℚ) ⊆ ratSegmentCuts p q := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ratSegmentCuts_zero p q
    · exact ratSegmentCuts_one p q
  have h := Finset.card_le_card hs
  rwa [Finset.card_pair (by norm_num : (0:ℚ) ≠ 1)] at h

def canonicalCutCount (p q : ℚ × ℚ) : ℕ := (ratSegmentCuts p q).card - 1

private theorem canonicalCutCount_card (p q : ℚ × ℚ) :
    (ratSegmentCuts p q).card = canonicalCutCount p q + 1 := by
  unfold canonicalCutCount
  have h := ratSegmentCuts_card_ge_two p q
  omega

def canonicalCuts (p q : ℚ × ℚ) : Fin (canonicalCutCount p q + 1) → ℚ :=
  (ratSegmentCuts p q).orderEmbOfFin (canonicalCutCount_card p q)

theorem canonicalCuts_strictMono (p q : ℚ × ℚ) :
    StrictMono (canonicalCuts p q) :=
  (ratSegmentCuts p q).orderEmbOfFin (canonicalCutCount_card p q) |>.strictMono

theorem canonicalCuts_range (p q : ℚ × ℚ) :
    Finset.univ.image (canonicalCuts p q) = ratSegmentCuts p q := by
  apply Finset.coe_injective
  simpa only [canonicalCuts, Finset.coe_image, Finset.coe_univ,
    Set.image_univ] using
    (Finset.range_orderEmbOfFin (ratSegmentCuts p q) (canonicalCutCount_card p q))

theorem canonicalCuts_zero (p q : ℚ × ℚ) : canonicalCuts p q 0 = 0 := by
  unfold canonicalCuts
  let G := ratSegmentCuts p q
  have hmin := Finset.orderEmbOfFin_zero (canonicalCutCount_card p q)
    (Nat.succ_pos (canonicalCutCount p q))
  rw [show (0 : Fin (canonicalCutCount p q+1)) =
    ⟨0, Nat.succ_pos (canonicalCutCount p q)⟩ from rfl, hmin]
  exact le_antisymm (G.min'_le 0 (ratSegmentCuts_zero p q))
    (ratSegmentCuts_mem_Icc p q (G.min'_mem _)).1

theorem canonicalCuts_last (p q : ℚ × ℚ) :
    canonicalCuts p q (Fin.last (canonicalCutCount p q)) = 1 := by
  unfold canonicalCuts
  let G := ratSegmentCuts p q
  have hmax := Finset.orderEmbOfFin_last (canonicalCutCount_card p q)
    (Nat.succ_pos (canonicalCutCount p q))
  rw [show (Fin.last (canonicalCutCount p q)) =
    ⟨canonicalCutCount p q+1-1,
      Nat.sub_lt (Nat.succ_pos _) (Nat.succ_pos 0)⟩ from
        Fin.ext (by simp), hmax]
  exact le_antisymm (ratSegmentCuts_mem_Icc p q (G.max'_mem _)).2
    (G.le_max' 1 (ratSegmentCuts_one p q))

def canonicalMappedSegmentPolygon (a : ℚ) (p q : ℚ × ℚ) : Exponent.PolygonalCost.RatPolygon :=
  mappedSegmentPolygon a p q (canonicalCutCount p q) (canonicalCuts p q)

theorem canonicalMappedSegment_trace (a : ℚ) (ha : 0 ≤ a) (p q : ℚ × ℚ) :
    (canonicalMappedSegmentPolygon a p q).path '' Set.Icc (0:ℝ) 1 =
      inwardMap (a:ℝ) ''
        (LQGMetric.LFPP.segPath (ratComplex p) (ratComplex q) '' Set.Icc (0:ℝ) 1) :=
  mapped_segment_trace a ha p q (canonicalCuts_strictMono p q)
    (canonicalCuts_zero p q) (canonicalCuts_last p q) (canonicalCuts_range p q)

theorem canonicalMappedSegment_cost_le (a : ℚ) (ha0 : 0 ≤ a)
    (ha : (a:ℝ) ≤ 1/256) (ξ G : ℝ) (hξ : 0 ≤ ξ) (hG0 : 0 ≤ G)
    (f : ℂ → ℝ)
    (hfd : ∀ z ∈ gradientBox, DifferentiableAt ℝ f z)
    (hG : ∀ z ∈ gradientBox, ‖fderiv ℝ f z‖ ≤ G)
    (p q : ℚ × ℚ) (hpath : ∀ u ∈ Set.Icc (0:ℝ) 1,
      LQGMetric.LFPP.segPath (ratComplex p) (ratComplex q) u ∈
        Exponent.PolygonalCost.closedSquareAnnulus) :
    LQGMetric.lfppLen ξ f (canonicalMappedSegmentPolygon a p q).path ≤
      ENNReal.ofReal ((5/4:ℝ)*Real.exp
        (32*Real.sqrt 2*ξ*((a:ℝ)*G))) *
      LQGMetric.LFPP.segCost ξ f (ratComplex p) (ratComplex q) :=
  mapped_segment_cost_le a ha0 ha ξ G hξ hG0 f hfd hG p q hpath
    (canonicalCuts_strictMono p q) (canonicalCuts_zero p q)
    (canonicalCuts_last p q) (canonicalCuts_range p q)


end SupercriticalLQGUniqueness.Exponent.InwardMap
