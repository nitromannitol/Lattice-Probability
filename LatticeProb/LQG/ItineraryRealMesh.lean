/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsBUniform at commit fdb5cad. The chain of estimates is the one of the
   source; here it is applied to the itinerary events at the real meshes. -/
import LatticeProb.LQG.Lemma311ExplicitExponent

/-!
# The itinerary events of Lemma 3.11 at every real mesh

For the embedded mated-CRT map of a mating-of-trees coupling, the itinerary event at the circle `∂B_r(z)` of mesh
`ε` (`ItinGoodReal`) is the event that the cells `η([ε(x-1), εx])` form a cellular embedding of the map and that the
random walk started at every vertex whose cell meets the circle follows a polar template itinerary around it with
quenched probability at least `p₀`.

* `itin_bandSeqAt_rate` — the itinerary estimate along a band sequence, with the exponent `itinExponent q β`;
* `pairEventsReal_of_coupling` — the itinerary events at the circles with `ε^β ≤ r`, `B_{2r}(z) ⊆ B_ρ(0)`, and the
  disconnection event of Lemma 3.11, fail with probability at most `C ε^α`, with `α, β` independent of `ρ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LatticeProb.LQG.ExplicitScale

open MatedCRTHarmonic MatedCRTHarmonic.GMSMain MatedCRTHarmonic.GMSMain.EpsB

/-- **The itinerary event at the circle `∂B_r(z)` at the real mesh `ε`**: the mesh-`ε` mated-CRT map of `bm ω` is
locally finite, its cells `η([ε(x-1), εx])` form a cellular embedding `H`, and from every vertex whose cell meets
`∂B_r(z)` the walk performs a polar template itinerary around `∂B_r(z)` with quenched probability at least `p₀`. -/
def ItinGoodReal {Ω : Type*} (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ)) (ε : ℝ) (z : ℂ) (r p₀ : ℝ) :
    Set Ω :=
  {ω | ∃ h : MatedCRT.IsLocallyFinite ε (bm ω), ∃ H : CellularEmbedding (MatedCRT.graph ε (bm ω) h) 0,
    (∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
    ∀ y ∈ verticesMeeting H.cell (sphere z r),
      ENNReal.ofReal p₀ ≤ (MatedCRT.graph ε (bm ω) h).walkLaw y
        {ξ | CellFamily.PolarTemplateItinerary H z r ((MatedCRT.graph ε (bm ω) h).vertexPath ξ)}}

theorem itinGoodReal_mono {Ω : Type*} {bm : Ω → MatedCRT.Path2} {η : Ω → C(ℝ, ℂ)} {ε : ℝ} {z : ℂ} {r p₀ p₀' : ℝ}
    (hp : p₀' ≤ p₀) : ItinGoodReal bm η ε z r p₀ ⊆ ItinGoodReal bm η ε z r p₀' := by
  rintro ω ⟨h, H, hcell, hgood⟩
  exact ⟨h, H, hcell, fun y hy => (ENNReal.ofReal_le_ofReal hp).trans (hgood y hy)⟩

/-- The exponent of the lower scale in the itinerary estimate at the real mesh: half of the itinerary exponent
`min β q / 2`. -/
def itinExponent (q β : ℝ) : ℝ := min β q / 2 / 2

theorem lemma311Exponent_le_itinExponent {a27 α410 q β : ℝ} (hq : 0 < q) (hβ : 0 < β) :
    lemma311Exponent a27 α410 q β ≤ itinExponent q β := by
  unfold lemma311Exponent itinExponent
  have h1 : min (min a27 (min a27 (min a27 (α410 / 2) / 2)) / 6) (min q (min β q / 2)) ≤ min β q / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have h2 : 0 < min β q := lt_min hβ hq
  linarith

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **The itinerary estimate along a band sequence at the actual meshes `θₖ`**, with the rate
`chainRate a27 (α410/2)` and the lower scale `θₖ ^ itinExponent q β`, `q = 1/(2+γ)²`; the inputs are those of
`lemma311_bandSeqAt_rate`, and the itinerary radius `ρ` is smaller than the radius `ρ'` of the inputs. -/
theorem itin_bandSeqAt_rate (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo 0 2) {θ : ℕ → ℝ} (hθb : IsBandSeq θ) {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (hρ' : ρ' < 1) {a27 C27 α410 β410 A Cfail : ℝ} (ha27 : 0 < a27) (hC27 : 0 ≤ C27)
    (hL : ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | ¬ SegDiamGood (η ω) ε (1 / (2 + γ) ^ 2) ρ'} ≤ ENNReal.ofReal (C27 * ε ^ a27))
    (hα410 : 0 < α410) (hβ410 : 0 < β410) (hA : 0 ≤ A) (hCfail : 0 ≤ Cfail)
    (h410 : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible ε ρ' 100 β410 V f →
      P (BundleSec4.Prop410Bad η ε V f A (ε ^ α410)) ≤ ENNReal.ofReal (Cfail * ε ^ α410))
    {β β' : ℝ} (hexp : ScaleExponentsAt (1 / (2 + γ) ^ 2) β410 (α410 / 2) β β') :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∃ C : ℝ, ∀ (k : ℕ) (z : ℂ) (r : ℝ),
      θ k ^ itinExponent (1 / (2 + γ) ^ 2) β ≤ r → ball z (2 * r) ⊆ ball (0 : ℂ) ρ →
      P (ItinGoodReal bm η (θ k) z r p₀)ᶜ ≤ ENNReal.ofReal (C * θ k ^ chainRate a27 (α410 / 2)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  set q : ℝ := 1 / (2 + γ) ^ 2
  have hden : 0 < (2 + γ) ^ 2 := by
    have : 0 < 2 + γ := by linarith [hγ.1]
    positivity
  have hq0 : 0 < q := by positivity
  have ha210 : 0 < α410 / 2 := half_pos hα410
  set F := bandFamily D θ hθb.pos with hFdef
  have hconn := bandFamily_graphConnected D θ hθb.pos
  have hloop := bandFamily_graphLoopless D θ hθb.pos
  have hpeano := bandFamily_peanosphereG0 D θ hθb.pos
  have h27G3 := bandFamily_cellDiamBound_bad D θ hθb.pos hθb hq0.le ha27 hC27 hL
  have hDiam := bandFamily_diameterGood_bad D hθb hq0.le ha27 hC27 hρρ' hL
  have h210 : ∀ k (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible (CellFamily.mesh k) ρ' 100 β410 V f →
      F.P (GMS4.Prop210Bad F k V f (2 * A) (CellFamily.mesh k ^ (α410 / 2))) ≤
        ENNReal.ofReal ((Cfail + 2) * CellFamily.mesh k ^ (α410 / 2)) := fun k V f hadm =>
    bandFamily_prop210Bad_le D θ hθb.pos hθb hadm.2.2.2.2.2.2.1.measurableSet hα410 hCfail
      (h410 (θ k) ⟨hθb.pos k, (hθb k).2.2⟩ V f (prop210Admissible_mono (hθb.pos k) (hθb k).2.1 hadm))
  have hβ8 : 0 < β := hexp.1
  have hW : Annulus38RateAt F ρ (min a27 (α410 / 2)) β :=
    annulus38RateAt_of_L27_G4 F hρ hρρ' hρ' hq0 hexp hβ410 ha210 ha27 hA hC27 (by linarith) hpeano
      h27G3 h210
  have hmin : 0 < min a27 (α410 / 2) := lt_min ha27 ha210
  have h38 : L38RateAt F ρ (min a27 (α410 / 2) / 2) β :=
    l38RateAt_of_annulus38RateAt F ρ hmin hβ8 hexp.2.1 hW
  have hmin8 : 0 < min β q := lt_min hβ8 hq0
  have hβi : 0 < min β q / 2 := half_pos hmin8
  have hβi8 : min β q / 2 < β := by linarith [min_le_left β q]
  have hβiq : min β q / 2 < q := by linarith [min_le_right β q]
  have hItin : ItinRateAt F ρ (min a27 (min a27 (α410 / 2) / 2)) (min β q / 2) :=
    itinRateAt_of_l38RateAt F q ρ ha27 hDiam (half_pos hmin) h38 hβi hβi8 hβiq hconn hloop
      (CellFamily.waypointStrongMarkovInputFixed2_holds F q ρ)
  obtain ⟨s₀, Ci, hs₀, -, hI⟩ := hItin
  have hai : 0 < min a27 (min a27 (α410 / 2) / 2) := lt_min ha27 (half_pos hmin)
  have hrate := chainRate_pos ha27 ha210
  have hrate_le : chainRate a27 (α410 / 2) ≤ min a27 (min a27 (α410 / 2) / 2) := by
    unfold chainRate
    have h1 : min a27 (min a27 (min a27 (α410 / 2) / 2)) ≤ min a27 (min a27 (α410 / 2) / 2) := min_le_right _ _
    linarith [lt_min ha27 hai]
  refine ⟨(2 : ℝ) ^ (-(⌈11600 / s₀⌉ : ℤ)), by positivity,
    max Ci 0 * 2 ^ (min a27 (min a27 (α410 / 2) / 2)) + 2 ^ (min a27 (min a27 (α410 / 2) / 2)),
    fun k z r hr hball => ?_⟩
  have hθk0 : 0 < θ k := hθb.pos k
  have hθk1 : θ k ≤ 1 := ((hθb k).2.1).trans (EpsB.mesh_le_one k)
  have hrpos : 0 < r := lt_of_lt_of_le (Real.rpow_pos_of_pos hθk0 _) hr
  have hr' : r ≤ ρ := by
    have := T15A.norm_add_le_of_ball_subset (by linarith : (0 : ℝ) < 2 * r) hball
    nlinarith [norm_nonneg z]
  refine (ofReal_mesh_le_band (C := Ci) hθb hai.le k prob_le_one fun hk => ?_).trans ?_
  · refine (measure_le_of_bandFamily D hθb.pos (ItinGoodReal bm η (θ k) z r ((2 : ℝ) ^ (-(⌈11600 / s₀⌉ : ℤ))))ᶜ
      (CellFamily.PolarItineraryGood F k z r s₀)ᶜ (fun ω hω hgood => hω ?_)).trans
      (hI k z r ((mesh_rpow_le_band_rpow_half hθb hk hβi.le).trans hr) hr' hball)
    exact ⟨(bandSpace_good D θ hθb.pos ω).locFin k, bandEmbedding D θ hθb.pos ω k,
      fun x => bandEmbedding_cell D θ hθb.pos ω k x, hgood⟩
  · apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hθk0 hθk1 hrate_le)
    positivity

/-- **The itinerary events and the disconnection event of Lemma 3.11 at every real mesh, with exponents independent
of the radius**, for the embedded mated-CRT map of every mating-of-trees coupling (standard Borel, `γ ∈ (0, 2)`):
there are `α, β > 0` such that for every `ρ ∈ (0, 1)` there are `p₀, p₁ > 0` and `C` such that for every
`ε ∈ (0, 1)` the itinerary event at every circle `∂B_r(z)` with `ε^β ≤ r` and `B_{2r}(z) ⊆ B_ρ(0)` fails with
probability at most `C ε^α`, and so does the disconnection event of Lemma 3.11 with floor `ε^β`. -/
theorem pairEventsReal_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ p₀ : ℝ, 0 < p₀ ∧ ∃ p₁ : ℝ, 0 < p₁ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        (∀ (z : ℂ) (r : ℝ), ε ^ β ≤ r → ball z (2 * r) ⊆ ball (0 : ℂ) ρ →
          P (ItinGoodReal bm η ε z r p₀)ᶜ ≤ ENNReal.ofReal (C * ε ^ α)) ∧
        P (Lemma311GoodReal bm η ε ρ β p₁)ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
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
  obtain ⟨_, _, pB, hpB, CB, hCB⟩ := uniform_fixedRate_of_bandSeq
    (fun ε _ p => P (Lemma311GoodReal bm η ε ρ (lemma311Exponent a27 α410 q β) p)ᶜ)
    (fun _ _ _ => prob_le_one)
    (fun ε _ p _ p' h0 h1 _ hp =>
      measure_mono (compl_subset_compl.mpr (lemma311GoodReal_mono h0 h1.le le_rfl hp)))
    (chainRate_pos ha27 (half_pos hα410)).le
    (fun θ hθb => by
      obtain ⟨p, hp, C, hC⟩ := lemma311_bandSeqAt_rate D hγ hθb hρ hρρ' hρ' ha27 hC27 hL hα410 hβ410
        hA.le hCfail h410 hβexp
      exact ⟨1, one_pos, p, hp, C, hC⟩)
  obtain ⟨_, _, pA, hpA, CA, hCA⟩ := uniform_fixedRate_of_bandSeq
    (fun ε _ p => ⨆ (z : ℂ) (r : ℝ)
      (_ : ε ^ lemma311Exponent a27 α410 q β ≤ r ∧ ball z (2 * r) ⊆ ball (0 : ℂ) ρ),
      P (ItinGoodReal bm η ε z r p)ᶜ)
    (fun _ _ _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => prob_le_one)
    (fun ε _ p _ p' _ _ _ hp => iSup_mono fun z => iSup_mono fun r => iSup_mono fun _ =>
      measure_mono (compl_subset_compl.mpr (itinGoodReal_mono hp)))
    (chainRate_pos ha27 (half_pos hα410)).le
    (fun θ hθb => by
      obtain ⟨p, hp, C, hC⟩ := itin_bandSeqAt_rate D hγ hθb hρ hρρ' hρ' ha27 hC27 hL hα410 hβ410
        hA.le hCfail h410 hβexp
      refine ⟨1, one_pos, p, hp, C, fun k => iSup_le fun z => iSup_le fun r => iSup_le fun hh => ?_⟩
      refine hC k z r ?_ hh.2
      exact (Real.rpow_le_rpow_of_exponent_ge (hθb.pos k) ((hθb k).2.1.trans (EpsB.mesh_le_one k))
        (lemma311Exponent_le_itinExponent hq0 hβexp.1)).trans hh.1)
  refine ⟨pA, hpA, pB, hpB, max CA CB, fun ε h0 h1 => ⟨fun z r hr hb => ?_, ?_⟩⟩
  · have hmem : ε ^ lemma311Exponent a27 α410 q β ≤ r ∧ ball z (2 * r) ⊆ ball (0 : ℂ) ρ := ⟨hr, hb⟩
    refine (le_iSup₂_of_le z r (le_of_eq (iSup_pos (f := fun _ => P (ItinGoodReal bm η ε z r pA)ᶜ) hmem).symm)).trans
      ((hCA ε h0 h1).trans (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg h0.le _)
  · refine (hCB ε h0 h1).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg h0.le _)

end Coupling

end LatticeProb.LQG.ExplicitScale
