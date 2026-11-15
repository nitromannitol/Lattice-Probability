import LatticeProb.Analysis.MovingIntervalInfimum
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Strict comparisons of moving interval minima -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Strictness of weak cell-to-middle comparisons for a shifted grid. -/
def cellWindowStrict (ε : ℝ) (f : C(ℝ, ℝ)) (θ : ℝ) : Prop :=
  ∀ i j : ℤ, i + 1 < j →
    let a := ε * ((i : ℝ) - 1 + θ)
    let b := ε * ((i : ℝ) + θ)
    let c := ε * ((j : ℝ) - 1 + θ)
    let d := ε * ((j : ℝ) + θ)
    let l := sInf (f '' uIcc a b)
    let m := sInf (f '' uIcc b c)
    let r := sInf (f '' uIcc c d)
    max l r ≤ m → max l r < m

/-- The strict comparison event is Borel in the path and phase. -/
theorem measurableSet_cellWindowStrict (ε : ℝ) :
    MeasurableSet {p : C(ℝ, ℝ) × ℝ | cellWindowStrict ε p.1 p.2} := by
  have hm (x y : ℝ) : Continuous (fun p : C(ℝ, ℝ) × ℝ =>
      sInf (p.1 '' uIcc (ε * (x + p.2)) (ε * (y + p.2)))) := by
    have hx : Continuous (fun p : C(ℝ, ℝ) × ℝ => ε * (x + p.2)) := by fun_prop
    have hy : Continuous (fun p : C(ℝ, ℝ) × ℝ => ε * (y + p.2)) := by fun_prop
    exact continuous_sInf_image_uIcc.comp (continuous_fst.prodMk (hx.prodMk hy))
  have hp (i j : ℤ) : MeasurableSet {p : C(ℝ, ℝ) × ℝ |
      i + 1 < j →
      max (sInf (p.1 '' uIcc (ε * ((i : ℝ) - 1 + p.2)) (ε * ((i : ℝ) + p.2))))
          (sInf (p.1 '' uIcc (ε * ((j : ℝ) - 1 + p.2)) (ε * ((j : ℝ) + p.2)))) ≤
          sInf (p.1 '' uIcc (ε * ((i : ℝ) + p.2)) (ε * ((j : ℝ) - 1 + p.2))) →
      max (sInf (p.1 '' uIcc (ε * ((i : ℝ) - 1 + p.2)) (ε * ((i : ℝ) + p.2))))
          (sInf (p.1 '' uIcc (ε * ((j : ℝ) - 1 + p.2)) (ε * ((j : ℝ) + p.2)))) <
          sInf (p.1 '' uIcc (ε * ((i : ℝ) + p.2)) (ε * ((j : ℝ) - 1 + p.2)))} := by
    by_cases hij : i + 1 < j
    · simp only [hij, true_implies]
      have hl := (hm ((i : ℝ) - 1) i).max (hm ((j : ℝ) - 1) j)
      have hm' := hm (i : ℝ) ((j : ℝ) - 1)
      have h := (measurableSet_le hl.measurable hm'.measurable).compl.union
        (measurableSet_lt hl.measurable hm'.measurable)
      convert h using 1
      ext p
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    · simp [hij]
  simpa only [cellWindowStrict, ofPred_forall] using
    MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => hp i j))

/-- Countable exceptional phase sections yield an almost-sure product event. -/
theorem ae_prod_cellWindowStrict_of_countable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (G : Ω → C(ℝ, ℝ)) (hG : Measurable G) (ε : ℝ)
    (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume)
    (hc : ∀ᵐ ω ∂P, {θ : ℝ | ¬ cellWindowStrict ε (G ω) θ}.Countable) :
    ∀ᵐ p ∂P.prod Q, cellWindowStrict ε (G p.1) p.2 := by
  have hs := (measurableSet_cellWindowStrict ε).preimage
    ((hG.comp measurable_fst).prodMk measurable_snd)
  apply (Measure.ae_prod_iff_ae_ae hs).2
  filter_upwards [hc] with ω hω
  apply hQ.ae_le
  change ∀ᵐ θ ∂volume, cellWindowStrict ε (G ω) θ
  simpa only [mem_ofPred_eq, not_not] using hω.ae_notMem volume

end LatticeProb
