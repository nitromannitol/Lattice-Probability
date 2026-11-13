/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsBUniform at commit fdb5cad. The proofs are copied; in the statements
   the exponent `β` is an explicit parameter instead of an existential witness chosen after the radius. -/
import LatticeProb.LQG.ScaledGridExplicitExponent
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBUniform

/-!
# Lemma 3.11 at every real mesh with a scale exponent independent of the radius

`EpsBUniform.lemma311RealUniform_of_coupling` gives, for a mating-of-trees coupling, a rate `α` independent of the
radius `ρ`, but its scale exponent `β` is still chosen after `ρ`. In the chain of explicit rates
(`Lemma38ExplicitScale`, `ItineraryExplicitExponent`, `ScaledGridExplicitExponent`) the scale exponents are functions
of `γ` and of the exponents of Proposition 4.10 only; the radius enters the probability exponent `p` and the constant.

* `lemma311Exponent a27 α410 q β` — the exponent of the final statement;
* `lemma311_bandSeqAt_rate` — Lemma 3.11 along a band sequence with that exponent;
* `lemma311RealUniformExponent_of_coupling` — `∃ α β > 0, ∀ ρ ∈ (0, 1), ∃ p > 0, ∃ C, ∀ ε ∈ (0, 1),
  P (Lemma311GoodReal bm η ε ρ β p)ᶜ ≤ C ε^α`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LatticeProb.LQG.ExplicitScale

open MatedCRTHarmonic MatedCRTHarmonic.GMSMain MatedCRTHarmonic.GMSMain.EpsB

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **The Lemma 3.11 exponent**, a function of the rate `a27` of Lemma 2.7, the rate `α410` of Proposition 4.10,
`q` and the scale exponent `β` of Lemma 3.8 only. The itinerary exponent is `βᵢ = min β q / 2`, the grid exponent is
`χ = min a27 aᵢ / 6` with `aᵢ = min a27 (min a27 (α410 / 2) / 2)`, the exponent of the grid control is
`min χ (min q βᵢ) / 2`, and the exponent at the real mesh is half of it. -/
def lemma311Exponent (a27 α410 q β : ℝ) : ℝ :=
  min (min a27 (min a27 (min a27 (α410 / 2) / 2)) / 6) (min q (min β q / 2)) / 2 / 2

theorem lemma311Exponent_pos {a27 α410 q β : ℝ} (ha27 : 0 < a27) (hα410 : 0 < α410) (hq : 0 < q)
    (hβ : 0 < β) : 0 < lemma311Exponent a27 α410 q β := by
  unfold lemma311Exponent
  have hα : 0 < α410 / 2 := half_pos hα410
  positivity

/-- **[18] Lemma 3.11 along a band sequence at the actual meshes `θₖ`, with the explicit rate
`chainRate a27 (α410/2)` and the explicit exponent `lemma311Exponent a27 α410 q β`**, from [18] Lemma 2.7 at real
meshes at `ρ'` (rate `a27`) and Proposition 4.10 at real meshes at `(ρ', 100)` (rate `α410`, exponent `β410`),
`ρ < ρ' < 1`, `q = 1/(2+γ)²`, and scale exponents `β, β'` for `(q, β410, α410/2)`. The exponent depends on
`a27, α410, q, β` only; the radii enter only the probability exponent `p` and the constant. -/
theorem lemma311_bandSeqAt_rate (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo 0 2) {θ : ℕ → ℝ} (hθb : IsBandSeq θ) {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (hρ' : ρ' < 1) {a27 C27 α410 β410 A Cfail : ℝ} (ha27 : 0 < a27) (hC27 : 0 ≤ C27)
    (hL : ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | ¬ SegDiamGood (η ω) ε (1 / (2 + γ) ^ 2) ρ'} ≤ ENNReal.ofReal (C27 * ε ^ a27))
    (hα410 : 0 < α410) (hβ410 : 0 < β410) (hA : 0 ≤ A) (hCfail : 0 ≤ Cfail)
    (h410 : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible ε ρ' 100 β410 V f →
      P (BundleSec4.Prop410Bad η ε V f A (ε ^ α410)) ≤ ENNReal.ofReal (Cfail * ε ^ α410))
    {β β' : ℝ} (hexp : ScaleExponentsAt (1 / (2 + γ) ^ 2) β410 (α410 / 2) β β') :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
      ∀ k, P (Lemma311GoodReal bm η (θ k) ρ (lemma311Exponent a27 α410 (1 / (2 + γ) ^ 2) β) p)ᶜ ≤
        ENNReal.ofReal (C * θ k ^ chainRate a27 (α410 / 2)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  set q : ℝ := 1 / (2 + γ) ^ 2
  have hden : 0 < (2 + γ) ^ 2 := by
    have : 0 < 2 + γ := by linarith [hγ.1]
    positivity
  have hq0 : 0 < q := by positivity
  set ρ₂ : ℝ := (ρ + ρ') / 2 with hρ₂def
  have hρ₂ : 0 < ρ₂ := by linarith
  have hρρ₂ : ρ < ρ₂ := by linarith
  have hρ₂ρ' : ρ₂ < ρ' := by linarith
  have ha210 : 0 < α410 / 2 := half_pos hα410
  set F := bandFamily D θ hθb.pos with hFdef
  have hconn := bandFamily_graphConnected D θ hθb.pos
  have hloop := bandFamily_graphLoopless D θ hθb.pos
  have hpeano := bandFamily_peanosphereG0 D θ hθb.pos
  have h27G3 := bandFamily_cellDiamBound_bad D θ hθb.pos hθb hq0.le ha27 hC27 hL
  have hDiam := bandFamily_diameterGood_bad D hθb hq0.le ha27 hC27 hρ₂ρ' hL
  have h210 : ∀ k (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible (CellFamily.mesh k) ρ' 100 β410 V f →
      F.P (GMS4.Prop210Bad F k V f (2 * A) (CellFamily.mesh k ^ (α410 / 2))) ≤
        ENNReal.ofReal ((Cfail + 2) * CellFamily.mesh k ^ (α410 / 2)) := fun k V f hadm =>
    bandFamily_prop210Bad_le D θ hθb.pos hθb hadm.2.2.2.2.2.2.1.measurableSet hα410 hCfail
      (h410 (θ k) ⟨hθb.pos k, (hθb k).2.2⟩ V f (prop210Admissible_mono (hθb.pos k) (hθb k).2.1 hadm))
  have hβ8 : 0 < β := hexp.1
  have hW : Annulus38RateAt F ρ₂ (min a27 (α410 / 2)) β :=
    annulus38RateAt_of_L27_G4 F hρ₂ hρ₂ρ' hρ' hq0 hexp hβ410 ha210 ha27 hA hC27 (by linarith) hpeano
      h27G3 h210
  have hmin : 0 < min a27 (α410 / 2) := lt_min ha27 ha210
  have h38 : L38RateAt F ρ₂ (min a27 (α410 / 2) / 2) β :=
    l38RateAt_of_annulus38RateAt F ρ₂ hmin hβ8 hexp.2.1 hW
  have hmin8 : 0 < min β q := lt_min hβ8 hq0
  have hβi : 0 < min β q / 2 := half_pos hmin8
  have hβi8 : min β q / 2 < β := by linarith [min_le_left β q]
  have hβiq : min β q / 2 < q := by linarith [min_le_right β q]
  have hItin : ItinRateAt F ρ₂ (min a27 (min a27 (α410 / 2) / 2)) (min β q / 2) :=
    itinRateAt_of_l38RateAt F q ρ₂ ha27 hDiam (half_pos hmin) h38 hβi hβi8 hβiq hconn hloop
      (CellFamily.waypointStrongMarkovInputFixed2_holds F q ρ₂)
  have hai : 0 < min a27 (min a27 (α410 / 2) / 2) := lt_min ha27 (half_pos hmin)
  have hχ : 0 < min a27 (min a27 (min a27 (α410 / 2) / 2)) / 6 := by
    have := lt_min ha27 hai
    positivity
  have hmins : 0 < min (min a27 (min a27 (min a27 (α410 / 2) / 2)) / 6) (min q (min β q / 2)) :=
    lt_min hχ (lt_min hq0 hβi)
  have hβs : 0 < min (min a27 (min a27 (min a27 (α410 / 2) / 2)) / 6) (min q (min β q / 2)) / 2 :=
    half_pos hmins
  have hβsχ : min (min a27 (min a27 (min a27 (α410 / 2) / 2)) / 6) (min q (min β q / 2)) / 2 <
      min a27 (min a27 (min a27 (α410 / 2) / 2)) / 6 := by
    linarith [min_le_left (min a27 (min a27 (min a27 (α410 / 2) / 2)) / 6) (min q (min β q / 2))]
  have hβsq : min (min a27 (min a27 (min a27 (α410 / 2) / 2)) / 6) (min q (min β q / 2)) / 2 < q := by
    linarith [min_le_right (min a27 (min a27 (min a27 (α410 / 2) / 2)) / 6) (min q (min β q / 2)),
      min_le_left q (min β q / 2)]
  have hβsi : min (min a27 (min a27 (min a27 (α410 / 2) / 2)) / 6) (min q (min β q / 2)) / 2 <
      min β q / 2 := by
    linarith [min_le_right (min a27 (min a27 (min a27 (α410 / 2) / 2)) / 6) (min q (min β q / 2)),
      min_le_right q (min β q / 2)]
  obtain ⟨p, C, hp, h26⟩ :=
    sgcRateAt_of_itinRateAt F ρ₂ q ha27 hDiam hai hItin hβs hβsχ hβsq hβsi
      (CellFamily.finiteGridCount_holds ρ₂) hconn
      (CellFamily.templateSeparation_of_peanosphereG0 F hpeano)
  have hrate := chainRate_pos ha27 ha210
  obtain ⟨C', hC'⟩ := lemma311Rate_of_sgc F hconn hβs hβsχ hβsq hrate hp hρρ₂ h26
  refine ⟨p, hp, max C' 0 * 2 ^ chainRate a27 (α410 / 2) + 2 ^ chainRate a27 (α410 / 2),
    fun k => ?_⟩
  refine ofReal_mesh_le_band hθb hrate.le k prob_le_one fun hk => ?_
  refine (measure_le_of_bandFamily D hθb.pos
    (Lemma311GoodReal bm η (θ k) ρ (lemma311Exponent a27 α410 (1 / (2 + γ) ^ 2) β) p)ᶜ
    (T15A.Lemma311Good F k ρ (min (min a27 (min a27 (min a27 (α410 / 2) / 2)) / 6) (min q (min β q / 2)) / 2) p)ᶜ
    (fun ω hω hgood => hω ?_)).trans (hC' k)
  exact ⟨(bandSpace_good D θ hθb.pos ω).locFin k, bandEmbedding D θ hθb.pos ω k,
    fun x => bandEmbedding_cell D θ hθb.pos ω k x,
    lemma311Holds_of_floor_le hgood (mesh_rpow_le_band_rpow_half hθb hk hβs.le)⟩

/-- **[18] Lemma 3.11 at every real mesh with a rate and a scale exponent independent of the radius**, for the
embedded mated-CRT map of every mating-of-trees coupling (standard Borel, `γ ∈ (0, 2)`): there are `α, β > 0`
(depending only on `γ` and the coupling) such that for every `ρ ∈ (0, 1)` there are `p > 0` and `C` with
`P[(3.35) fails at mesh ε] ≤ C ε^α` for every `ε ∈ (0, 1)`. -/
theorem lemma311RealUniformExponent_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → P (Lemma311GoodReal bm η ε ρ β p)ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  set q : ℝ := 1 / (2 + γ) ^ 2 with hqdef
  have hden : 0 < (2 + γ) ^ 2 := by
    have : 0 < 2 + γ := by linarith [hγ.1]
    positivity
  have hq0 : 0 < q := by positivity
  have hq2 : q < 2 / (2 + γ) ^ 2 := by
    rw [hqdef]
    exact div_lt_div_of_pos_right (by norm_num) hden
  have hq1 : q < 1 := by
    have hfrac : 2 / (2 + γ) ^ 2 < 1 := (div_lt_iff₀ hden).mpr (by nlinarith [sq_nonneg γ, hγ.1])
    linarith
  have hexp : 0 < GMSLemma27.lemma27Exponent q γ := GMSLemma27.lemma27Exponent_pos hγ.1 hq0 hq2
  set a27 : ℝ := GMSLemma27.lemma27Exponent q γ / 2 with ha27def
  have ha27 : 0 < a27 := by positivity
  have ha27lt : a27 < GMSLemma27.lemma27Exponent q γ := by linarith
  obtain ⟨α410, hα410, β410, hβ410, hsrc⟩ := GMSMain.epsA_prop410Source D hstd hγ
  obtain ⟨β, β', hβexp⟩ := exists_scaleExponentsAt hq0 hq1 hβ410 (half_pos hα410)
  refine ⟨chainRate a27 (α410 / 2), chainRate_pos ha27 (half_pos hα410),
    lemma311Exponent a27 α410 q β, lemma311Exponent_pos ha27 hα410 hq0 hβexp.1, fun ρ hρ hρ1 => ?_⟩
  set ρ' : ℝ := (1 + ρ) / 2 with hρ'def
  have hρρ' : ρ < ρ' := by linarith
  have hρ' : ρ' < 1 := by linarith
  obtain ⟨A, hA, hCh⟩ := hsrc ρ' (by linarith) hρ'
  obtain ⟨Cfail, hCfail, h410⟩ := hCh 100 (by norm_num)
  obtain ⟨C27, hC27, hL⟩ := lemma27_real D hstd hγ hq0 hq2 (by linarith : 0 < ρ') hρ' ha27lt
  obtain ⟨_, _, p, hp, C, hC⟩ := uniform_fixedRate_of_bandSeq
    (fun ε _ p => P (Lemma311GoodReal bm η ε ρ (lemma311Exponent a27 α410 q β) p)ᶜ)
    (fun _ _ _ => prob_le_one)
    (fun ε _ p _ p' h0 h1 _ hp =>
      measure_mono (compl_subset_compl.mpr (lemma311GoodReal_mono h0 h1.le le_rfl hp)))
    (chainRate_pos ha27 (half_pos hα410)).le
    (fun θ hθb => by
      obtain ⟨p, hp, C, hC⟩ := lemma311_bandSeqAt_rate D hγ hθb hρ hρρ' hρ' ha27 hC27 hL hα410 hβ410
        hA.le hCfail h410 hβexp
      exact ⟨1, one_pos, p, hp, C, hC⟩)
  exact ⟨p, hp, C, hC⟩

end Coupling

end LatticeProb.LQG.ExplicitScale
