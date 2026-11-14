/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointOpenSmallUpper at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatLocalEdgeUpper
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatLocalChainEvent

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_point_open_small_upper_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Qexp : ℝ) (hQ : IsLFPPExponent ξ Qexp)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U)
    (η : ℝ) (hη : 0 < η) :
    ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
      ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
        P {ω | ENNReal.ofReal T <
          ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
            crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {z} {w}} ≤
          ENNReal.ofReal η := by
  obtain ⟨ρ, N, p, hρ, hρsmall, hp0, hpN, hball, hpstep⟩ :=
    dg20_heat_local_chain_geometry hU hUc hz hw
  let δ : ℝ := η / (N + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hedge (j : Fin (N + 1)) :
      ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
        ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
          P {ω | ENNReal.ofReal T <
            ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
              crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U
                {p j} {p (j + 1)}} ≤ ENNReal.ofReal δ :=
    dg20_heat_local_edge_small_upper
      hPerc hExp hPos ξ Qexp hQ m hm P h hh X hX U
      (p j) (p (j + 1)) ρ hρ hρsmall
      (hpstep (j : ℕ) (Nat.lt_succ_iff.mp j.isLt))
      (hball (j : ℕ) (by omega)) δ hδ
  choose Tj εj hTj hεj htail using hedge
  let A : ℝ := (∑ j : Fin (N + 1), Tj j) + 1
  have hA : 0 < A := by
    dsimp [A]
    have hs : 0 ≤ ∑ j : Fin (N + 1), Tj j :=
      Finset.sum_nonneg fun j _ => (hTj j).le
    linarith
  have hnonempty : (Finset.univ : Finset (Fin (N + 1))).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  let ε₀ : ℝ := Finset.univ.inf' hnonempty εj
  have hε₀ : 0 < ε₀ :=
    (Finset.lt_inf'_iff hnonempty).2 (fun j _ => hεj j)
  let T : ℝ := (N + 1) * A
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T, ε₀, hT, hε₀, ?_⟩
  intro ε hε
  let b : ℝ≥0∞ := ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹
  let φ : Ω → ℂ → ℝ := fun ω => X ⟨ε, ε.property.1⟩ ω
  have hAj (j : Fin (N + 1)) : Tj j ≤ A := by
    have hsingle : Tj j ≤ ∑ i : Fin (N + 1), Tj i :=
      Finset.single_le_sum (fun i _ => (hTj i).le) (Finset.mem_univ j)
    dsimp [A]
    linarith
  have hprob (j : ℕ) (hj : j ≤ N) :
      P {ω | ENNReal.ofReal A < b *
        crossLenIn ξ (φ ω) U {p j} {p (j + 1)}} ≤ ENNReal.ofReal δ := by
    let i : Fin (N + 1) := ⟨j, by omega⟩
    have hεi : (ε : ℝ) < εj i :=
      lt_of_lt_of_le hε (Finset.inf'_le εj (Finset.mem_univ i))
    have hi := htail i ε hεi
    calc
      P {ω | ENNReal.ofReal A < b *
          crossLenIn ξ (φ ω) U {p j} {p (j + 1)}} ≤
        P {ω | ENNReal.ofReal (Tj i) < b *
          crossLenIn ξ (φ ω) U {p j} {p (j + 1)}} := by
          apply measure_mono
          intro ω hω
          exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (hAj i)) hω
      _ ≤ ENNReal.ofReal δ := by simpa only [i, b, φ] using hi
  have hsub : {ω | ENNReal.ofReal T < b *
      crossLenIn ξ (φ ω) U {z} {w}} ⊆
      ⋃ j ∈ Finset.range (N + 1),
        {ω | ENNReal.ofReal A < b *
          crossLenIn ξ (φ ω) U {p j} {p (j + 1)}} := by
    have hs := dg20_normalized_chain_upper_bad_subset
      (ξ : ℝ) φ U p N b (ENNReal.ofReal A)
    simp only [LQGMetric.DFGPS.crossLenIn_singleton]
    have hTreal : ENNReal.ofReal T = (N + 1 : ℝ≥0∞) * ENNReal.ofReal A := by
      dsimp [T]
      have hc : ENNReal.ofReal ((N : ℝ) + 1) = (N + 1 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add (Nat.cast_nonneg N) (by norm_num),
          ENNReal.ofReal_natCast, ENNReal.ofReal_one]
      rw [← hc, ← ENNReal.ofReal_mul (by positivity)]
    simpa only [hp0, hpN, hTreal] using hs
  calc
    P {ω | ENNReal.ofReal T < b * crossLenIn ξ (φ ω) U {z} {w}} ≤
      P (⋃ j ∈ Finset.range (N + 1),
        {ω | ENNReal.ofReal A < b *
          crossLenIn ξ (φ ω) U {p j} {p (j + 1)}}) := measure_mono hsub
    _ ≤ ∑ j ∈ Finset.range (N + 1),
      P {ω | ENNReal.ofReal A < b *
        crossLenIn ξ (φ ω) U {p j} {p (j + 1)}} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (N + 1), ENNReal.ofReal δ := by
      apply Finset.sum_le_sum
      intro j hj
      exact hprob j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = ENNReal.ofReal η := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hc : ((N + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((N + 1 : ℕ) : ℝ) := by
        norm_cast
      rw [hc, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [δ]
      field_simp
      push_cast
      rfl

end SupercriticalLQGUniqueness.B2.DG20Pt
