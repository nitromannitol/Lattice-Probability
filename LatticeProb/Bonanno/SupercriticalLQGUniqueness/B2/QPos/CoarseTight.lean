/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.CoarseTight at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.CoarseSplit
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldOscExp

 





set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

private instance : CompactSpace (eastCorridor.toSet) :=
  isCompact_iff_compactSpace.mp eastCorridor.isCompact_toSet

private instance : Nonempty (eastCorridor.toSet) := by
  refine ⟨⟨⟨2 / 5, -1 / 16⟩, ?_⟩⟩
  norm_num [eastCorridor, MarkedRect.toSet, Complex.mem_reProdIm]

 
def coarseCorridorSup {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (ω : Ω) : ℝ :=
  ⨆ x : eastCorridor.toSet, |phiMN W P 0 3 x ω|

theorem measurable_coarseCorridorSup
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) :
    Measurable (coarseCorridorSup P W) := by
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le 3)
  exact measurable_iSup_of_continuous
    (X := fun (x : eastCorridor.toSet) ω => |phiMN W P 0 3 x ω|)
    (fun ω => continuous_abs.comp ((hφ.cont ω).comp continuous_subtype_val))
    (fun x => continuous_abs.measurable.comp (hφ.meas x))

theorem coarseCorridorSup_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (ω : Ω)
    (x : ℂ) (hx : x ∈ eastCorridor.toSet) :
    |phiMN W P 0 3 x ω| ≤ coarseCorridorSup P W ω := by
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le 3)
  have hc : Continuous (fun y : eastCorridor.toSet => |phiMN W P 0 3 y ω|) :=
    continuous_abs.comp ((hφ.cont ω).comp continuous_subtype_val)
  have hb : BddAbove (range fun y : eastCorridor.toSet => |phiMN W P 0 3 y ω|) := by
    simpa only [image_univ] using (isCompact_univ.image hc).bddAbove
  exact le_ciSup hb ⟨x, hx⟩

 

theorem coarseCorridorSup_linear_tail_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ =>
      P {ω | κ * (n : ℝ) < coarseCorridorSup P W ω}) atTop (𝓝 0) := by
  have hm := measurable_coarseCorridorSup hW
  let μ : Measure ℝ := P.map (coarseCorridorSup P W)
  have hμ : μ Set.univ = 1 := by
    dsimp [μ]
    rw [Measure.map_apply hm (by simp)]
    simp
  have hfinite : ∃ M : ℝ, μ (Ioi M) ≠ ∞ := by
    refine ⟨0, ne_top_of_le_ne_top (by rw [hμ]; exact ENNReal.one_ne_top)
      (measure_mono (subset_univ _))⟩
  have hinter : (⋂ M : ℝ, Ioi M) = (∅ : Set ℝ) := by
    ext x
    simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false]
    intro h
    have hx := h (x + 1)
    linarith
  have ht : Tendsto (fun M : ℝ => μ (Ioi M)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun M : ℝ => Ioi M)
      (fun M => measurableSet_Ioi.nullMeasurableSet)
      (fun M N hMN x hx => lt_of_le_of_lt hMN hx)
      hfinite
    simpa only [Function.comp_def, hinter, measure_empty] using h
  have hs : Tendsto (fun n : ℕ => κ * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hκ
  convert ht.comp hs using 1
  funext n
  change P {ω | κ * (n : ℝ) < coarseCorridorSup P W ω} = μ (Ioi (κ * (n : ℝ)))
  dsimp [μ]
  rw [Measure.map_apply hm measurableSet_Ioi]
  rfl

end SupercriticalLQGUniqueness.B2.QPos
