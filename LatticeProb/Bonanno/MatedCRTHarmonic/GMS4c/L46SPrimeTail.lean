/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.L46SPrimeTail at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SCount
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46STail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SWindow
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveAdapters
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SCoverageTail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SPolylog
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.Segments
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.AreaDominates
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.L46SAllVisits

/-! The polynomial gamma-cone tail applies to the maximum over all visits. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4c

open MatedCRTHarmonic.GMS4b
open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.MoTInput
open MatedCRTHarmonic.GMSLemma27

/-- The primed analogue of the L46S polylogarithmic tail. -/
def InnerDegreeBoundPolylogPrime {γ : ℝ} (M : CellModel γ) (k : ℕ) : Prop :=
  ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ ζ ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
    M.P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
          ((degreeInPrime ε (M.curve ω) z : ℕ∞) : ℝ≥0∞)} ≤
      ENNReal.ofReal (C * ε ^ s)

/-- L46S's Brownian-chain proof works uniformly over all point visits. -/
theorem innerDegreeBoundPolylog_prime_coupled
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ k : ℕ, InnerDegreeBoundPolylogPrime (cellModelOfCoupling D hγ) (2 * k) := by
  let M := cellModelOfCoupling D hγ
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hSLE : SegmentsContainBalls M := segmentsContainBalls_of_coupling D hγ
  have hGMC : GMCLowerTail γ := GMCFacts.gmcLowerTail_holds hγ.1 hγ.2
  have hcone : GMCFacts.ConeAreaExists γ P X B B' :=
    GMCFacts.coneAreaExists_holds hγ.1 hγ.2 D.gff D.bm_B D.bm_B' D.indep_cone
  have hdom : AreaDominatesWholePlaneGFF M :=
    areaDominatesWholePlaneGFF_of_coupling D hγ hcone
  obtain ⟨k, hdet⟩ := l46s_coupled_bound_all_visits D hγ
  refine ⟨k, ?_⟩
  intro ρ hρ ζ hζ s
  obtain ⟨p, hp, C₁, hcover⟩ := l46s_coverage_superpoly D s
  obtain ⟨C₂, hwindow⟩ := l46s_window_in_unit_ball_superpoly M hγ.1 hSLE hGMC hdom hρ s
  obtain ⟨C₃, hdegree⟩ := l46s_coupling_degree_tail_superpoly D hp hζ.1 s
  let C : ℝ := max C₁ 0 + max C₂ 0 + max C₃ 0
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (Real.log ε⁻¹ ^ ((2 * k : ℝ) * (1 + ζ) + 1)) <
          ((degreeInPrime ε (η ω) z : ℕ∞) : ℝ≥0∞)} ≤
        ENNReal.ofReal (C * ε ^ s) := by
    filter_upwards [l46s_graphball_le_polylog_eventually k hζ.1,
      self_mem_nhdsWithin, eventually_lt_nhdsGT_zero one_pos]
      with ε hlog hε0 hε1
    have hε : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε0, hε1⟩
    let T : ℝ := ε ^ (-p)
    let n : ℕ := ⌈(Real.log ε⁻¹) ^ (1 + ζ / 2)⌉₊
    let S : Finset ℤ := Finset.Icc ⌈-T / ε⌉ (⌈T / ε⌉ + 1)
    let Ecover : Set Ω := {ω | ¬ ball (0 : ℂ) 1 ⊆ η ω '' Icc (-T) T}
    let Ewindow : Set Ω := {ω | ∃ t : ℝ, η ω t ∈ ball (0 : ℂ) ρ ∧
      ¬ locWindow ε (η ω) t ⊆ ball (0 : ℂ) 1}
    let Edegree : Set Ω := {ω | ∃ x ∈ S, (n : ℕ∞) < lemma25Degree ε (bm ω) x}
    have hD := hdet hε.1 T (by dsimp [T]; exact Real.rpow_nonneg hε.1.le _) n ρ
    have hsub : {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (Real.log ε⁻¹ ^ ((2 * k : ℝ) * (1 + ζ) + 1)) <
          ((degreeInPrime ε (η ω) z : ℕ∞) : ℝ≥0∞)} ≤ᵐ[P]
        Ecover ∪ Ewindow ∪ Edegree := by
      filter_upwards [hD] with ω hω
      rintro ⟨z, hz, hbad⟩
      by_contra hnot
      simp only [mem_union, not_or] at hnot
      obtain ⟨⟨hncover, hnwindow⟩, hndegree⟩ := hnot
      have hc : ball (0 : ℂ) 1 ⊆ η ω '' Icc (-T) T := by
        by_contra hh
        exact hncover hh
      have hw : ∀ t : ℝ, η ω t ∈ ball (0 : ℂ) ρ →
          locWindow ε (η ω) t ⊆ ball (0 : ℂ) 1 := by
        intro t ht
        by_contra hh
        exact hnwindow ⟨t, ht, hh⟩
      have hr : ∀ x ∈ Icc ⌈-T / ε⌉ (⌈T / ε⌉ + 1),
          lemma25Degree ε (bm ω) x ≤ (n : ℕ∞) := by
        intro x hx
        by_contra hh
        exact hndegree ⟨x, Finset.mem_Icc.mpr hx, not_le.mp hh⟩
      have hin := l46s_prime_le_on_good_event (hω hc hw hr) z hz
      have hlog' : ((9 * ((n + 1) ^ (2 * k) : ℕ∞) : ℕ∞) : ℝ≥0∞) ≤
          ENNReal.ofReal (Real.log ε⁻¹ ^ ((2 * k : ℝ) * (1 + ζ) + 1)) := by
        convert l46s_graphball_ENNReal_le_polylog hlog using 1 <;> simp [n]
      exact (not_lt_of_ge (le_trans (by exact_mod_cast hin) hlog')) hbad
    have hPcover : P Ecover ≤ ENNReal.ofReal (C₁ * ε ^ s) := hcover ε hε
    have hPwindow : P Ewindow ≤ ENNReal.ofReal (C₂ * ε ^ s) := hwindow ε hε
    have hPdegree : P Edegree ≤ ENNReal.ofReal (C₃ * ε ^ s) := hdegree ε hε
    have hεs : 0 ≤ ε ^ s := Real.rpow_nonneg hε.1.le _
    calc
      P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (Real.log ε⁻¹ ^ ((2 * k : ℝ) * (1 + ζ) + 1)) <
          ((degreeInPrime ε (η ω) z : ℕ∞) : ℝ≥0∞)} ≤
          P (Ecover ∪ Ewindow ∪ Edegree) := measure_mono_ae hsub
      _ ≤ P Ecover + P Ewindow + P Edegree := by
          calc
            P (Ecover ∪ Ewindow ∪ Edegree) ≤ P (Ecover ∪ Ewindow) + P Edegree :=
              measure_union_le _ _
            _ ≤ P Ecover + P Ewindow + P Edegree := by
              gcongr
              exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (C₁ * ε ^ s) + ENNReal.ofReal (C₂ * ε ^ s) +
          ENNReal.ofReal (C₃ * ε ^ s) := by gcongr
      _ ≤ ENNReal.ofReal (max C₁ 0 * ε ^ s) + ENNReal.ofReal (max C₂ 0 * ε ^ s) +
          ENNReal.ofReal (max C₃ 0 * ε ^ s) := by
          gcongr <;> exact le_max_left _ _
      _ = ENNReal.ofReal (C * ε ^ s) := by
          have h₁ : 0 ≤ max C₁ 0 * ε ^ s := mul_nonneg (le_max_right _ _) hεs
          have h₂ : 0 ≤ max C₂ 0 * ε ^ s := mul_nonneg (le_max_right _ _) hεs
          rw [← ENNReal.ofReal_add h₁ h₂,
            ← ENNReal.ofReal_add (add_nonneg h₁ h₂)
              (mul_nonneg (le_max_right _ _) hεs)]
          congr 1
          dsimp [C]
          ring
  convert (exists_bound_of_eventually (fun _ => prob_le_one) hev) using 1 <;>
    simp only [Nat.cast_mul, Nat.cast_ofNat, cellModelOfCoupling]
  funext C
  rfl

end MatedCRTHarmonic.GMS4c

