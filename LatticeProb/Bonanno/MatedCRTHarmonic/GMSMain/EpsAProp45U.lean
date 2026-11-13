/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsAProp45U at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsACase0

/-!
# [18] Proposition 4.5 with an exponent uniform in the radius `ρ`

Source: [18] Proposition 4.5. G4b's `GMS4b.prop45_holds_of_polylog`
states `∀ ρ, ∃ α, ∃ C`, but its proof chooses `α = min(α(q′, γ)/2, α_{4.7}, (q − 4ζ)β_h, (q − 4ζ)β_IG)` BEFORE
using `ρ`: L27's `lemma27_segments` takes `α` as input, Lemma 4.7 (`GMS4b.lemma47_holds`) and the circle-average sup
bound (`GMS4b.CircleAverageSupBound`) give `∃ α, ∀ ρ`, and the polylog Lemma 4.6 input
(`GMS4b.InnerDegreeBoundPolylog`) takes the target exponent as input. This file re-runs that proof with the
quantifiers `∃ α, ∀ ρ, ∃ C` (only the order of the `obtain`s changes), which is what [18]'s Propositions 2.10/4.10
need for their exponent `α = α(γ)` to be independent of `ρ`.

* `epsA_prop45_uniform_of_polylog` — on any cell model, from the inputs of `prop45_holds_of_polylog`;
* **`epsA_zeroCone_prop45_uniform`** — on the frozen zero-cone model of every coupling, unconditionally.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Asymptotics
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic MatedCRTHarmonic.GMSLemma27 MatedCRTHarmonic.GMS4b

variable {γ : ℝ}

/-- **[18] Proposition 4.5 from the polylog Lemma 4.6 input, exponent uniform in `ρ`** (the proof of
`GMS4b.prop45_holds_of_polylog` with `∃ α` moved before `∀ ρ`). -/
theorem epsA_prop45_uniform_of_polylog (k : ℕ) (M : CellModel γ) (hγ : 0 < γ)
    (hSLE : SegmentsContainBalls M) (hGMC : GMCLowerTail γ) (hdom : AreaDominatesWholePlaneGFF M)
    (hmass : UpperMassBound M) (hgeom : SpaceFillingGeometry M) (hin : InnerDegreeBoundPolylog M k)
    {H HIG : ℝ → ℂ → M.Ω → ℝ}
    (hH : CircleAverageSupBound M.P H) (hHIG : CircleAverageSupBound M.P HIG)
    {q ζ : ℝ} (hq : q ∈ Ioo (0 : ℝ) (2 / (2 + γ) ^ 2)) (hζ : ζ ∈ Ioo (0 : ℝ) (q / 4)) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      M.P (prop45Event M H HIG ε ρ q ζ)ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hζ0, hζq⟩ := hζ
  -- Lemma 2.7 with a slightly larger `q′`
  set q' : ℝ := (q + 2 / (2 + γ) ^ 2) / 2 with hq'
  have hqq' : q < q' := by rw [hq']; linarith
  have hq'1 : q' < 2 / (2 + γ) ^ 2 := by rw [hq']; linarith
  have hq'0 : 0 < q' := hq0.trans hqq'
  have hexp := lemma27Exponent_pos hγ hq'0 hq'1
  set α₁ : ℝ := lemma27Exponent q' γ / 2
  have hα₁ : 0 < α₁ := by positivity
  -- Lemma 4.7 (exponent before `ρ`)
  obtain ⟨α₂, hα₂, h47⟩ := lemma47_holds M hγ hSLE hGMC hdom hmass hgeom
  -- circle averages at `r = ε^{q − 4ζ}`, `δ′ = 8ζ/(q − 4ζ)` (exponents before `ρ`)
  have hqζ : 0 < q - 4 * ζ := by linarith
  set δ' : ℝ := 8 * ζ / (q - 4 * ζ) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  obtain ⟨βh, hβh, hHρ⟩ := hH δ' hδ'0
  obtain ⟨βg, hβg, hHIGρ⟩ := hHIG δ' hδ'0
  set α : ℝ := min (min α₁ α₂) (min ((q - 4 * ζ) * βh) ((q - 4 * ζ) * βg)) with hα
  have hα0 : 0 < α := lt_min (lt_min hα₁ hα₂) (lt_min (by positivity) (by positivity))
  refine ⟨α, hα0, fun ρ hρ => ?_⟩
  obtain ⟨C₁, hC₁⟩ := lemma27_segments M hSLE hGMC hdom hγ hq'0 hq'1 hρ.1 hρ.2
    (show α₁ < lemma27Exponent q' γ from half_lt_self hexp)
  have hq_half : q < 1 / 2 := by
    have h4 : (4 : ℝ) ≤ (2 + γ) ^ 2 := by nlinarith
    have : 2 / (2 + γ) ^ 2 ≤ 2 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h4
    linarith
  obtain ⟨C₂, hC₂⟩ := h47 ρ hρ (ζ / 2) ⟨by linarith, by linarith⟩
  obtain ⟨C₄, hC₄⟩ := hHρ ρ hρ
  obtain ⟨C₅, hC₅⟩ := hHIGρ ρ hρ
  -- the polylog input with exponent `k(1+1/2)+1` and failure `O(ε^α)`
  obtain ⟨C₃, hC₃⟩ := hin ρ hρ (1 / 2) ⟨by norm_num, by norm_num⟩ α
  set N : Set M.Ω := {ω | Continuous (M.curve ω) ∧ Function.Surjective (M.curve ω) ∧
    Tendsto (M.curve ω) (cocompact ℝ) (cocompact ℂ)} with hN
  have hNc : M.P Nᶜ = 0 := by
    have hae : ∀ᵐ ω ∂M.P, ω ∈ N := by
      filter_upwards [M.ae_continuous_curve, hgeom] with ω h1 h3
      exact ⟨h1, h3.1, h3.2.1⟩
    exact ae_iff.mp hae
  set C₀ : ℝ := max C₁ 0 + max C₂ 0 + max C₃ 0 + max C₄ 0 + max C₅ 0 with hC₀
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      M.P (prop45Event M H HIG ε ρ q ζ)ᶜ ≤ ENNReal.ofReal (C₀ * ε ^ α) := by
    filter_upwards [self_mem_nhdsWithin, eventually_lt_nhdsGT_zero one_pos,
      eventually_rpow_lt (show (0 : ℝ) < q' - q by linarith) (show (0 : ℝ) < 1 / 2 by norm_num),
      eventually_rpow_lt (show (0 : ℝ) < ζ / 2 by linarith) (show (0 : ℝ) < 1 / 2 by norm_num),
      eventually_log_rpow_le ((k : ℝ) * (1 + 1 / 2) + 1) hζ0] with ε hε0 hε1 hεq hεζ hlog
    have hε0' : (0 : ℝ) < ε := hε0
    set E1 : Set M.Ω := segmentDiamGood M ε q' ρ
    set Eout : Set M.Ω := {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      ENNReal.ofReal (ε ^ (-(ζ / 2))) < ((degreeOut ε (M.curve ω) z : ℕ∞) : ℝ≥0∞)}
    set Ein : Set M.Ω := {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + (1 : ℝ) / 2) + 1)) < ((degreeIn ε (M.curve ω) z : ℕ∞) : ℝ≥0∞)}
    set r : ℝ := ε ^ (q - 4 * ζ)
    have hr0 : 0 < r := Real.rpow_pos_of_pos hε0' _
    have hr1 : r < 1 := Real.rpow_lt_one hε0'.le hε1 hqζ
    set Eh : Set M.Ω := {ω | ∃ z ∈ ball (0 : ℂ) ρ, (2 + δ') * Real.log r⁻¹ < |H r z ω|}
    set Eg : Set M.Ω := {ω | ∃ z ∈ ball (0 : ℂ) ρ, (2 + δ') * Real.log r⁻¹ < |HIG r z ω|}
    have hlogr : (2 + δ') * Real.log r⁻¹ = 2 * q * Real.log ε⁻¹ := by
      have hne : q - 4 * ζ ≠ 0 := hqζ.ne'
      have hδ'mul : δ' * (q - 4 * ζ) = 8 * ζ := by rw [hδ']; exact div_mul_cancel₀ _ hne
      have hkey : (2 + δ') * (q - 4 * ζ) = 2 * q := by linear_combination hδ'mul
      rw [Real.log_inv, Real.log_rpow hε0', Real.log_inv]
      calc (2 + δ') * -((q - 4 * ζ) * Real.log ε) = -((2 + δ') * (q - 4 * ζ)) * Real.log ε := by ring
        _ = 2 * q * -Real.log ε := by rw [hkey]; ring
    have hsub : (prop45Event M H HIG ε ρ q ζ)ᶜ ⊆ E1ᶜ ∪ Eout ∪ Ein ∪ Eh ∪ Eg ∪ Nᶜ := by
      intro ω hω
      by_contra hcon
      simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
      obtain ⟨⟨⟨⟨⟨h1, hout⟩, hinω⟩, hh⟩, hg⟩, hNω⟩ := hcon
      obtain ⟨hcont, hsurj, htrans⟩ := hNω
      apply hω
      refine ⟨fun z hz => ⟨?_, ?_⟩, fun z hz => ⟨?_, ?_⟩⟩
      · -- window diameter
        have hτ : M.curve ω (hitTime (M.curve ω) z) = z := hitTime_spec hcont htrans (hsurj z)
        have hd := diam_locWindow_le_two_mul hε0'.le (fun a b hab hmeet => h1 a b hab hmeet)
          (show M.curve ω (hitTime (M.curve ω) z) ∈ ball (0 : ℂ) ρ by rw [hτ]; exact hz)
        have hsplit : ε ^ q' = ε ^ (q' - q) * ε ^ q := by
          rw [← Real.rpow_add hε0']; ring_nf
        have hεq0 : 0 < ε ^ q := Real.rpow_pos_of_pos hε0' q
        change diam (locWindow ε (M.curve ω) (hitTime (M.curve ω) z)) ≤ ε ^ q
        nlinarith
      · -- degrees
        have hin' : ((degreeIn ε (M.curve ω) z : ℕ∞) : ℝ≥0∞) ≤
            ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + (1 : ℝ) / 2) + 1)) := by
          by_contra hlt; exact hinω ⟨z, hz, not_le.mp hlt⟩
        have hout' : ((degreeOut ε (M.curve ω) z : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (ε ^ (-(ζ / 2))) := by
          by_contra hlt; exact hout ⟨z, hz, not_le.mp hlt⟩
        have h2 : ε ^ (-(ζ / 2)) ≤ ε ^ (-ζ) / 2 := by
          have hpos : 0 < ε ^ (ζ / 2) := Real.rpow_pos_of_pos hε0' _
          have hsplit : ε ^ (-ζ) = ε ^ (-(ζ / 2)) * ε ^ (-(ζ / 2)) := by
            rw [← Real.rpow_add hε0']; ring_nf
          have hinv : ε ^ (-(ζ / 2)) = (ε ^ (ζ / 2))⁻¹ := Real.rpow_neg hε0'.le _
          have h2' : 2 ≤ ε ^ (-(ζ / 2)) := by
            rw [hinv, le_inv_comm₀ (by norm_num) hpos]; linarith
          rw [hsplit]
          nlinarith [Real.rpow_pos_of_pos hε0' (-(ζ / 2))]
        rw [ENat.toENNReal_add]
        calc ((degreeIn ε (M.curve ω) z : ℕ∞) : ℝ≥0∞) + ((degreeOut ε (M.curve ω) z : ℕ∞) : ℝ≥0∞)
            ≤ ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + (1 : ℝ) / 2) + 1)) + ENNReal.ofReal (ε ^ (-(ζ / 2))) :=
              add_le_add hin' hout'
          _ ≤ ENNReal.ofReal (ε ^ (-ζ) / 2) + ENNReal.ofReal (ε ^ (-ζ) / 2) :=
              add_le_add (ENNReal.ofReal_le_ofReal hlog) (ENNReal.ofReal_le_ofReal h2)
          _ = ENNReal.ofReal (ε ^ (-ζ)) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
      · by_contra hlt
        exact hh ⟨z, hz, by rw [hlogr]; exact not_le.mp hlt⟩
      · by_contra hlt
        exact hg ⟨z, hz, by rw [hlogr]; exact not_le.mp hlt⟩
    have hεα : 0 ≤ ε ^ α := Real.rpow_nonneg hε0'.le _
    have hmono : ∀ {e : ℝ}, α ≤ e → ε ^ e ≤ ε ^ α := fun he =>
      Real.rpow_le_rpow_of_exponent_ge hε0' hε1.le he
    have hb : ∀ {C e : ℝ}, α ≤ e → ENNReal.ofReal (C * ε ^ e) ≤ ENNReal.ofReal (max C 0 * ε ^ α) := by
      intro C e he
      refine ENNReal.ofReal_le_ofReal ?_
      calc C * ε ^ e ≤ max C 0 * ε ^ e :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε0'.le _)
        _ ≤ max C 0 * ε ^ α := mul_le_mul_of_nonneg_left (hmono he) (le_max_right _ _)
    have hP1 : M.P E1ᶜ ≤ ENNReal.ofReal (max C₁ 0 * ε ^ α) :=
      (hC₁ ε ⟨hε0', hε1⟩).trans (hb ((min_le_left _ _).trans (min_le_left _ _)))
    have hP2 : M.P Eout ≤ ENNReal.ofReal (max C₂ 0 * ε ^ α) :=
      (hC₂ ε ⟨hε0', hε1⟩).trans (hb ((min_le_left _ _).trans (min_le_right _ _)))
    have hP3 : M.P Ein ≤ ENNReal.ofReal (max C₃ 0 * ε ^ α) :=
      (hC₃ ε ⟨hε0', hε1⟩).trans (hb le_rfl)
    have hrpow : ∀ β : ℝ, r ^ β = ε ^ ((q - 4 * ζ) * β) := fun β => by
      rw [← Real.rpow_mul hε0'.le]
    have hP4 : M.P Eh ≤ ENNReal.ofReal (max C₄ 0 * ε ^ α) := by
      refine (hC₄ r ⟨hr0, hr1⟩).trans ?_
      rw [hrpow]
      exact hb ((min_le_right _ _).trans (min_le_left _ _))
    have hP5 : M.P Eg ≤ ENNReal.ofReal (max C₅ 0 * ε ^ α) := by
      refine (hC₅ r ⟨hr0, hr1⟩).trans ?_
      rw [hrpow]
      exact hb ((min_le_right _ _).trans (min_le_right _ _))
    calc M.P (prop45Event M H HIG ε ρ q ζ)ᶜ ≤ M.P (E1ᶜ ∪ Eout ∪ Ein ∪ Eh ∪ Eg ∪ Nᶜ) := measure_mono hsub
      _ ≤ M.P E1ᶜ + M.P Eout + M.P Ein + M.P Eh + M.P Eg + M.P Nᶜ := by
          refine (measure_union_le _ _).trans ?_; gcongr
          refine (measure_union_le _ _).trans ?_; gcongr
          refine (measure_union_le _ _).trans ?_; gcongr
          refine (measure_union_le _ _).trans ?_; gcongr
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (max C₁ 0 * ε ^ α) + ENNReal.ofReal (max C₂ 0 * ε ^ α) +
            ENNReal.ofReal (max C₃ 0 * ε ^ α) + ENNReal.ofReal (max C₄ 0 * ε ^ α) +
            ENNReal.ofReal (max C₅ 0 * ε ^ α) + 0 := by
          rw [hNc]; gcongr
      _ = ENNReal.ofReal (C₀ * ε ^ α) := by
          have n : ∀ C : ℝ, 0 ≤ max C 0 * ε ^ α := fun C => mul_nonneg (le_max_right C 0) hεα
          rw [add_zero, ← ENNReal.ofReal_add (n C₁) (n C₂),
            ← ENNReal.ofReal_add (add_nonneg (n C₁) (n C₂)) (n C₃),
            ← ENNReal.ofReal_add (add_nonneg (add_nonneg (n C₁) (n C₂)) (n C₃)) (n C₄),
            ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg (n C₁) (n C₂)) (n C₃)) (n C₄)) (n C₅)]
          congr 1
          rw [hC₀]; ring
  exact exists_bound_of_eventually (fun _ => prob_le_one) hev

section Bundle

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] Proposition 4.5 on the frozen zero-cone model, exponent uniform in `ρ`, unconditionally**: there are
circle-average processes `H` (zero-cone field) and `HIG` (IG field with the phase `U`, as in
`BundleSec4.zeroCone_prop45_holds`) such that for every admissible `q, ζ` there is `α > 0` with, for every
`ρ ∈ (0, 1)`, `P[prop45Event(H, HIG)ᶜ] ≤ C ε^α` for all `ε ∈ (0, 1)`. -/
theorem epsA_zeroCone_prop45_uniform
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ H HIG : ℝ → ℂ → Ω → ℝ,
      ∀ q ∈ Ioo (0 : ℝ) (2 / (2 + γ) ^ 2), ∀ ζ ∈ Ioo (0 : ℝ) (q / 4),
        ∃ α : ℝ, 0 < α ∧ ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
          P (prop45Event (l46tZeroConeCellModel D hγ) H HIG ε ρ q ζ)ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨H, -, -, hsup⟩ := BundleSec4.exists_zeroCone_circleAvgVersion D hγ
  obtain ⟨HIG, -, -, hHIGsup⟩ := BundleSec4.exists_igCircleAvgVersion_withPhase D
  obtain ⟨k, hin⟩ := BundleSec4.l46t_zeroCone_innerDegreeBoundPolylog_holds D hγ
  let M := l46tZeroConeCellModel D hγ
  have hmass : UpperMassBound M :=
    GMCUpper.upperMassBoundZeroCone_toCellModel M hγ D (Filter.Eventually.of_forall fun _ => rfl)
  refine ⟨H, fun r z ω => HIG r z ω + U ω, fun q hq ζ hζ => ?_⟩
  exact epsA_prop45_uniform_of_polylog (2 * k) M hγ.1 (l46t_zeroCone_segmentsContainBalls D hγ)
    (GMCFacts.gmcLowerTail_holds hγ.1 hγ.2) (l46t_zeroCone_areaDominates D hγ) hmass
    (l46t_zeroCone_spaceFillingGeometry D hγ) hin hsup hHIGsup hq hζ

end Bundle

end MatedCRTHarmonic.GMSMain
