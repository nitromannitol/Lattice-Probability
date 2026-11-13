/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.BundleSec4.L46TPrime at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.L46TAdapter
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.L46SPrimeTail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TTransfer
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TModel
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TZeroInputs
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.AreaRecord

/-!
# The all-visit form of the transfer in [18] Lemma 4.6

The transfer's `GMS4b.L46TLocalReconstruction` asks the measurable [18] Lemma 4.3 to reconstruct the FIRST-VISIT inner-degree
event `GMS4b.l46tInnerBad` (degrees at `τ_z = inf {t : c t = z}`) from the local observation
`(h|_V, hIG|_V, U)`. Which visit of `z` comes first is a global property of the curve, so that event is not a function
of local data in general. the reconstruction therefore works with ALL-VISIT observables (`GMS4c.degreeInPrime` etc., the sup over
every visit; finite on bundle samples by the v4 `visitBound`). This file restates the transfer for the all-visit observables:

* `l46tInnerBadPrime` — the all-visit inner-degree failure; the escape event `GMS4b.l46tEscapeBad` is already an
  all-visit event (`∃ t, c t ∈ S ∧ ¬ locBall ε c t ⊆ U`);
* **`L46TLocalReconstructionPrime`** — the transfer's reconstruction structure with the all-visit inner event: the target
  for the measurable reconstruction;
* `l46t_innerBadPrime_le_holder`, `l46t_innerDegreeBoundPrime_disk`, `l46t_innerDegreeBoundPolylogPrime_of_localComparison`
  — the transfer's Hölder step, per-disk transfer and finite cover with the all-visit events; the source bound is the
  `GMS4c.innerDegreeBoundPolylog_prime_coupled` (γ-cone, all visits) translated, with the localization from
  `l46t_localization_shifted_disk`;
* `l46t_zeroCone_innerDegreeBoundPolylogPrime_of_primeReconstruction` — with `BundleSec4.l46tZeroConeComparison_of_CMRN`
  (the (4.16)), the all-visit polylog bound on the frozen zero-cone model from the primed reconstruction alone;
* `l46t_zeroCone_innerDegreeBoundPolylog_of_primeReconstruction` — the first-visit `GMS4b.InnerDegreeBoundPolylog`
  (first visit ≤ all visits on curves hitting every point at `τ_z`: `GMS4c.firstHit_innerBad_subset_prime`, with the
  zero-cone geometry `GMS4b.l46t_zeroCone_spaceFillingGeometry`);
* `l46t_zeroCone_prop45_of_primeReconstruction` — [18] Proposition 4.5 on the zero-cone model
  (`GMS4b.prop45_holds_of_polylog` with the transfer's zero-cone inputs).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic
open MatedCRTHarmonic.GMS4b

/-! ### All-visit events and the primed reconstruction interface -/

/-- **The all-visit localized inner-degree failure** on a spatial test region `S`: some `z ∈ S` has a visit whose local
inner degree exceeds `(log ε⁻¹)^{k(1+ζ)+1}`. -/
def l46tInnerBadPrime {Ω : Type*} (c : Ω → ℝ → ℂ) (S : Set ℂ) (ε : ℝ) (k : ℕ) (ζ : ℝ) : Set Ω :=
  {ω | ∃ z ∈ S,
    ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
      ((GMS4c.degreeInPrime ε (c ω) z : ℕ∞) : ℝ≥0∞)}

/-- **The primed measurable [18] Lemma 4.3 input** (the repair of `GMS4b.L46TLocalReconstruction`): one
Borel map from the local observation `(h|_V, hIG|_V, u)` to the local configuration on `U`, and Borel sets
reconstructing, under both laws, the escape event and the ALL-VISIT inner-degree failure on its complement. -/
structure L46TLocalReconstructionPrime {Ωγ Ω₀ : Type*}
    [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    (V U : TopologicalSpace.Opens ℂ)
    (Pγ : Measure Ωγ) (P₀ : Measure Ω₀)
    (hγ hIGγ : Ωγ → LQGMetric.DistC) (uγ : Ωγ → ℝ)
    (h₀ hIG₀ : Ω₀ → LQGMetric.DistC) (u₀ : Ω₀ → ℝ)
    (cγ : Ωγ → ℝ → ℂ) (c₀ : Ω₀ → ℝ → ℂ)
    (S : Set ℂ) (ε : ℝ) (k : ℕ) (ζ : ℝ) : Type where
  reconstruct : L46TLocalFieldPhase V → GMS4c.LocalConfiguration U
  reconstruct_measurable : Measurable reconstruct
  escapeBad : Set (GMS4c.LocalConfiguration U)
  escapeBad_measurable : MeasurableSet escapeBad
  innerBad : Set (GMS4c.LocalConfiguration U)
  innerBad_measurable : MeasurableSet innerBad
  gamma_escape : l46tEscapeBad cγ S U ε =ᵐ[Pγ]
    {ω | reconstruct (l46tLocalFieldPhase V hγ hIGγ uγ ω) ∈ escapeBad}
  target_escape : l46tEscapeBad c₀ S U ε =ᵐ[P₀]
    {ω | reconstruct (l46tLocalFieldPhase V h₀ hIG₀ u₀ ω) ∈ escapeBad}
  gamma_inner : (l46tInnerBadPrime cγ S ε k ζ ∩ (l46tEscapeBad cγ S U ε)ᶜ) =ᵐ[Pγ]
    {ω | reconstruct (l46tLocalFieldPhase V hγ hIGγ uγ ω) ∈ innerBad}
  target_inner : (l46tInnerBadPrime c₀ S ε k ζ ∩ (l46tEscapeBad c₀ S U ε)ᶜ) =ᵐ[P₀]
    {ω | reconstruct (l46tLocalFieldPhase V h₀ hIG₀ u₀ ω) ∈ innerBad}

/-- The primed reconstruction is unchanged by a.e.-equal observations. -/
def l46tPrimeReconstruction_congr
    {Ωγ Ω₀ : Type*} [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V U : TopologicalSpace.Opens ℂ}
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → LQGMetric.DistC} {uγ : Ωγ → ℝ}
    {h₀ hIG₀ : Ω₀ → LQGMetric.DistC} {u₀ : Ω₀ → ℝ}
    {hγ' hIGγ' : Ωγ → LQGMetric.DistC} {uγ' : Ωγ → ℝ}
    {h₀' hIG₀' : Ω₀ → LQGMetric.DistC} {u₀' : Ω₀ → ℝ}
    {cγ : Ωγ → ℝ → ℂ} {c₀ : Ω₀ → ℝ → ℂ}
    {S : Set ℂ} {ε : ℝ} {k : ℕ} {ζ : ℝ}
    (hlocal : L46TLocalReconstructionPrime V U Pγ P₀ hγ hIGγ uγ h₀ hIG₀ u₀ cγ c₀ S ε k ζ)
    (hs : l46tLocalFieldPhase V hγ' hIGγ' uγ' =ᵐ[Pγ] l46tLocalFieldPhase V hγ hIGγ uγ)
    (ht : l46tLocalFieldPhase V h₀' hIG₀' u₀' =ᵐ[P₀] l46tLocalFieldPhase V h₀ hIG₀ u₀) :
    L46TLocalReconstructionPrime V U Pγ P₀ hγ' hIGγ' uγ' h₀' hIG₀' u₀' cγ c₀ S ε k ζ := by
  refine ⟨hlocal.reconstruct, hlocal.reconstruct_measurable,
    hlocal.escapeBad, hlocal.escapeBad_measurable,
    hlocal.innerBad, hlocal.innerBad_measurable, ?_, ?_, ?_, ?_⟩
  · refine hlocal.gamma_escape.trans ?_
    filter_upwards [hs] with ω hω
    simp only [hω]
  · refine hlocal.target_escape.trans ?_
    filter_upwards [ht] with ω hω
    simp only [hω]
  · refine hlocal.gamma_inner.trans ?_
    filter_upwards [hs] with ω hω
    simp only [hω]
  · refine hlocal.target_inner.trans ?_
    filter_upwards [ht] with ω hω
    simp only [hω]

/-! ### The Hölder step for the all-visit events -/

/-- The two applications of (4.16) with the all-visit inner event (the transfer's `l46t_innerBad_le_holder`, primed). -/
theorem l46t_innerBadPrime_le_holder {Ωγ Ω₀ : Type*}
    [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V U : TopologicalSpace.Opens ℂ}
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → LQGMetric.DistC} {uγ : Ωγ → ℝ}
    {h₀ hIG₀ : Ω₀ → LQGMetric.DistC} {u₀ : Ω₀ → ℝ}
    {cγ : Ωγ → ℝ → ℂ} {c₀ : Ω₀ → ℝ → ℂ}
    {S : Set ℂ} {ε : ℝ} {k : ℕ} {ζ : ℝ} {p q : ℝ}
    (hcmp : L46TPhaseLawComparison V Pγ P₀ hγ hIGγ uγ h₀ hIG₀ u₀ p q)
    (hlocal : L46TLocalReconstructionPrime V U Pγ P₀ hγ hIGγ uγ h₀ hIG₀ u₀ cγ c₀ S ε k ζ) :
    P₀ (l46tInnerBadPrime c₀ S ε k ζ) ≤
      (∫⁻ x, hcmp.density x ^ p
        ∂(Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ))) ^ (1 / p) *
        (Pγ (l46tEscapeBad cγ S U ε)) ^ (1 / q) +
      (∫⁻ x, hcmp.density x ^ p
        ∂(Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ))) ^ (1 / p) *
        (Pγ (l46tInnerBadPrime cγ S ε k ζ)) ^ (1 / q) := by
  let K : ℝ≥0∞ :=
    (∫⁻ x, hcmp.density x ^ p
      ∂(Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ))) ^ (1 / p)
  have hesc := l46t_phase_badEvent_le_holder hcmp
    (hlocal.reconstruct_measurable hlocal.escapeBad_measurable)
  have hinn := l46t_phase_badEvent_le_holder hcmp
    (hlocal.reconstruct_measurable hlocal.innerBad_measurable)
  have hesc' : P₀ (l46tEscapeBad c₀ S U ε) ≤
      K * (Pγ (l46tEscapeBad cγ S U ε)) ^ (1 / q) := by
    rw [measure_congr hlocal.target_escape, measure_congr hlocal.gamma_escape]
    exact hesc
  have hinn' : P₀ (l46tInnerBadPrime c₀ S ε k ζ ∩ (l46tEscapeBad c₀ S U ε)ᶜ) ≤
      K * (Pγ (l46tInnerBadPrime cγ S ε k ζ)) ^ (1 / q) := by
    rw [measure_congr hlocal.target_inner]
    exact hinn.trans (by
      change K * (Pγ {ω | hlocal.reconstruct
        (l46tLocalFieldPhase V hγ hIGγ uγ ω) ∈ hlocal.innerBad}) ^ (1 / q) ≤
        K * (Pγ (l46tInnerBadPrime cγ S ε k ζ)) ^ (1 / q)
      rw [← measure_congr hlocal.gamma_inner]
      gcongr
      · exact one_div_nonneg.mpr hcmp.conjugate.symm.pos.le
      · exact inter_subset_left)
  calc
    P₀ (l46tInnerBadPrime c₀ S ε k ζ) ≤
        P₀ (l46tEscapeBad c₀ S U ε ∪
          (l46tInnerBadPrime c₀ S ε k ζ ∩ (l46tEscapeBad c₀ S U ε)ᶜ)) :=
      measure_mono (by intro ω hω; by_cases he : ω ∈ l46tEscapeBad c₀ S U ε <;> simp [he, hω])
    _ ≤ P₀ (l46tEscapeBad c₀ S U ε) +
        P₀ (l46tInnerBadPrime c₀ S ε k ζ ∩ (l46tEscapeBad c₀ S U ε)ᶜ) :=
      measure_union_le _ _
    _ ≤ K * (Pγ (l46tEscapeBad cγ S U ε)) ^ (1 / q) +
        K * (Pγ (l46tInnerBadPrime cγ S ε k ζ)) ^ (1 / q) :=
      add_le_add hesc' hinn'

/-! ### Translation of the all-visit degree -/

/-- Spatial translation preserves the all-visit inner degree at the translated point. -/
theorem l46t_degreeInPrime_translate (z₀ : ℂ) (c : ℝ → ℂ) (ε : ℝ) (z : ℂ) :
    GMS4c.degreeInPrime ε (l46tTranslateCurve z₀ c) (z + z₀) = GMS4c.degreeInPrime ε c z := by
  have hcurve : l46tTranslateCurve z₀ c = simC 1 z₀ one_ne_zero ∘ c := by
    funext t
    simp [l46tTranslateCurve, simC_apply]
  have hloc : ∀ t, locDegIn ε (l46tTranslateCurve z₀ c) t = locDegIn ε c t := by
    intro t
    rw [hcurve]
    exact locDegIn_simC 1 z₀ one_ne_zero c ε t
  unfold GMS4c.degreeInPrime
  refine iSup_congr fun t => ?_
  have hiff : l46tTranslateCurve z₀ c t = z + z₀ ↔ c t = z := by
    simp only [l46tTranslateCurve]
    exact add_left_inj z₀
  rw [hloc t]
  exact iSup_congr_Prop hiff (fun _ => rfl)

/-- the all-visit γ-cone bound remains valid after moving the root to a fixed point `z₀`
(the transfer's `l46t_innerDegreeBoundPolylog_translate`, primed). -/
theorem l46t_innerDegreeBoundPolylogPrime_translate {γ : ℝ}
    (M : GMSLemma27.CellModel γ) (k : ℕ)
    (hin : GMS4c.InnerDegreeBoundPolylogPrime M k) (z₀ : ℂ)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    {ζ : ℝ} (hζ : ζ ∈ Ioo (0 : ℝ) 1) (s : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      M.P {ω | ∃ z ∈ ball z₀ ρ,
        ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
          ((GMS4c.degreeInPrime ε (l46tTranslateCurve z₀ (M.curve ω)) z : ℕ∞) : ℝ≥0∞)} ≤
        ENNReal.ofReal (C * ε ^ s) := by
  obtain ⟨C, hC⟩ := hin ρ hρ ζ hζ s
  refine ⟨C, fun ε hε => (measure_mono ?_).trans (hC ε hε)⟩
  rintro ω ⟨z, hz, hbad⟩
  refine ⟨z - z₀, ?_, ?_⟩
  · simpa [Metric.mem_ball, dist_eq_norm] using hz
  · have heq : z - z₀ + z₀ = z := sub_add_cancel z z₀
    rw [← heq, l46t_degreeInPrime_translate] at hbad
    exact hbad

/-! ### The per-disk transfer and the finite cover, all visits -/

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **The all-visit transfer on one disk** (the transfer's `l46t_innerDegreeBound_disk_of_coupled_bound`, primed): the γ-cone
all-visit bound (translated to `z₀`), L27 localization of the translated curve, and Hölder through the joint local
density give the all-visit bound for the target model on `ball w r`. -/
theorem l46t_innerDegreeBoundPrime_disk
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hS : Ω → LQGMetric.DistC) (uS : Ω → ℝ) (k : ℕ)
    (hpoly : GMS4c.InnerDegreeBoundPolylogPrime (MoTInput.cellModelOfCoupling D hγ) (2 * k))
    (M₀ : GMSLemma27.CellModel γ) (hIGtarget : M₀.Ω → LQGMetric.DistC) (u₀ : M₀.Ω → ℝ)
    (z₀ w : ℂ) {ρ r R : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hsub : ball w r ⊆ ball z₀ ρ) (hrR : r < R)
    (V : TopologicalSpace.Opens ℂ) {p q : ℝ}
    (hcmp : L46TPhaseLawComparison V P M₀.P
      (l46tTranslatedField z₀ hS) (l46tTranslatedField z₀ hIG₀) uS
      M₀.field hIGtarget u₀ p q)
    (hlocal : ∀ (k : ℕ) (ζ ε : ℝ), ε ∈ Ioo (0 : ℝ) 1 →
      L46TLocalReconstructionPrime V ⟨ball w R, isOpen_ball⟩ P M₀.P
        (l46tTranslatedField z₀ hS) (l46tTranslatedField z₀ hIG₀) uS
        M₀.field hIGtarget u₀
        (fun ω => l46tTranslateCurve z₀ (η ω)) M₀.curve
        (ball w r) ε k ζ) :
    ∀ ζ ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
      ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
        M₀.P (l46tInnerBadPrime M₀.curve (ball w r) ε (2 * k) ζ) ≤
          ENNReal.ofReal (C * ε ^ s) := by
  let Mγ := MoTInput.cellModelOfCoupling D hγ
  let _ : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hSLE : GMSLemma27.SegmentsContainBalls Mγ :=
    MoTInput.segmentsContainBalls_of_coupling D hγ
  have hGMC : GMSLemma27.GMCLowerTail γ :=
    GMCFacts.gmcLowerTail_holds hγ.1 hγ.2
  have hcone : GMCFacts.ConeAreaExists γ P X B B' :=
    GMCFacts.coneAreaExists_holds hγ.1 hγ.2 D.gff D.bm_B D.bm_B' D.indep_cone
  have hdom : GMSLemma27.AreaDominatesWholePlaneGFF Mγ :=
    MoTInput.areaDominatesWholePlaneGFF_of_coupling D hγ hcone
  intro ζ hζ s
  obtain ⟨Cdeg, hdeg⟩ := l46t_innerDegreeBoundPolylogPrime_translate Mγ (2 * k)
    hpoly z₀ hρ hζ (q * s)
  obtain ⟨Cloc, hloc⟩ := l46t_localization_shifted_disk Mγ hγ.1
    hSLE hGMC hdom z₀ w hρ hsub hrR (q * s)
  let K : ℝ≥0∞ :=
    (∫⁻ x, hcmp.density x ^ p
      ∂(P.map (l46tLocalFieldPhase V (l46tTranslatedField z₀ hS)
        (l46tTranslatedField z₀ hIG₀) uS))) ^ (1 / p)
  have hK : K < ⊤ := l46t_phase_holder_constant_finite hcmp
  have hq : 0 < q := hcmp.conjugate.symm.pos
  let C : ℝ := K.toReal * (max Cloc 0) ^ (1 / q) +
    K.toReal * (max Cdeg 0) ^ (1 / q)
  refine ⟨C, fun ε hε => ?_⟩
  have hlocγ : P (l46tEscapeBad
      (fun ω => l46tTranslateCurve z₀ (η ω)) (ball w r) (ball w R) ε) ≤
      ENNReal.ofReal (Cloc * ε ^ (q * s)) := hloc ε hε
  have hdegγ : P (l46tInnerBadPrime
      (fun ω => l46tTranslateCurve z₀ (η ω)) (ball w r) ε (2 * k) ζ) ≤
      ENNReal.ofReal (Cdeg * ε ^ (q * s)) := by
    refine (measure_mono ?_).trans (hdeg ε hε)
    rintro ω ⟨z, hz, hbad⟩
    exact ⟨z, hsub hz, hbad⟩
  have hholder := l46t_innerBadPrime_le_holder hcmp (hlocal (2 * k) ζ ε hε)
  change M₀.P (l46tInnerBadPrime M₀.curve (ball w r) ε (2 * k) ζ) ≤
    K * (P (l46tEscapeBad
      (fun ω => l46tTranslateCurve z₀ (η ω)) (ball w r) (ball w R) ε)) ^ (1 / q) +
    K * (P (l46tInnerBadPrime
      (fun ω => l46tTranslateCurve z₀ (η ω)) (ball w r) ε (2 * k) ζ)) ^ (1 / q)
    at hholder
  calc
    M₀.P (l46tInnerBadPrime M₀.curve (ball w r) ε (2 * k) ζ) ≤
        K * (P (l46tEscapeBad
          (fun ω => l46tTranslateCurve z₀ (η ω)) (ball w r) (ball w R) ε)) ^ (1 / q) +
        K * (P (l46tInnerBadPrime
          (fun ω => l46tTranslateCurve z₀ (η ω)) (ball w r) ε (2 * k) ζ)) ^ (1 / q) := hholder
    _ ≤ K * (ENNReal.ofReal (Cloc * ε ^ (q * s))) ^ (1 / q) +
        K * (ENNReal.ofReal (Cdeg * ε ^ (q * s))) ^ (1 / q) := by
          gcongr
    _ ≤ ENNReal.ofReal (K.toReal * (max Cloc 0) ^ (1 / q) * ε ^ s) +
        ENNReal.ofReal (K.toReal * (max Cdeg 0) ^ (1 / q) * ε ^ s) :=
      add_le_add (l46t_holder_power_bound K hK q Cloc ε s hq hε.1)
        (l46t_holder_power_bound K hK q Cdeg ε s hq hε.1)
    _ = ENNReal.ofReal (C * ε ^ s) := by
      have h₁ : 0 ≤ K.toReal * (max Cloc 0) ^ (1 / q) * ε ^ s :=
        mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
          (Real.rpow_nonneg (le_max_right _ _) _)) (Real.rpow_nonneg hε.1.le _)
      have h₂ : 0 ≤ K.toReal * (max Cdeg 0) ^ (1 / q) * ε ^ s :=
        mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
          (Real.rpow_nonneg (le_max_right _ _) _)) (Real.rpow_nonneg hε.1.le _)
      rw [← ENNReal.ofReal_add h₁ h₂]
      congr 1
      dsimp [C]
      ring

/-- Each test disk lies inside the disk where the translated γ-cone bound is used (the transfer's private
`l46t_testDisk_subset_sourceDisk`). -/
theorem bundle_testDisk_subset_sourceDisk {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (w : ℂ) :
    ball w ((1 - ρ) / 16) ⊆ ball (w + ((1 - ρ) / 2 : ℝ)) (3 / 4 : ℝ) := by
  intro z hz
  have hzw : dist z w < (1 - ρ) / 16 := hz
  have hone : 0 ≤ 1 - ρ := by linarith [hρ.2]
  have hw : dist w (w + ((1 - ρ) / 2 : ℝ)) = (1 - ρ) / 2 := by
    simp [dist_eq_norm]
    change ‖((1 : ℝ) : ℂ) - (ρ : ℂ)‖ = 1 - ρ
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hone]
  have htri := dist_triangle z w (w + ((1 - ρ) / 2 : ℝ))
  rw [Metric.mem_ball, hw] at *
  linarith [hρ.1]

/-- **The all-visit polylog bound for a target model on the whole unit disk** (the transfer's
`l46t_innerDegreeBoundPolylog_of_localComparison`, primed): from the joint local density on every observation disk
and the primed reconstruction. -/
theorem l46t_innerDegreeBoundPolylogPrime_of_localComparison
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hS : Ω → LQGMetric.DistC) (uS : Ω → ℝ)
    (M₀ : GMSLemma27.CellModel γ) (hIGtarget : M₀.Ω → LQGMetric.DistC) (u₀ : M₀.Ω → ℝ)
    (hcmp : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      Σ p q : ℝ, L46TPhaseLawComparison (l46tObservation ρ w) P M₀.P
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hS)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) uS
        M₀.field hIGtarget u₀ p q)
    (hlocal : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      ∀ (k : ℕ) (ζ ε : ℝ), ε ∈ Ioo (0 : ℝ) 1 →
      L46TLocalReconstructionPrime (l46tObservation ρ w) (l46tLocalRegion ρ w)
        P M₀.P
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hS)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) uS
        M₀.field hIGtarget u₀
        (fun ω => l46tTranslateCurve (w + ((1 - ρ) / 2 : ℝ)) (η ω)) M₀.curve
        (ball w ((1 - ρ) / 16)) ε k ζ) :
    ∃ k : ℕ, GMS4c.InnerDegreeBoundPolylogPrime M₀ (2 * k) := by
  obtain ⟨k, hk⟩ := GMS4c.innerDegreeBoundPolylog_prime_coupled D hγ
  refine ⟨k, ?_⟩
  intro ρ hρ ζ hζ s
  let W : Type := {w : ℂ // w ∈ closedBall (0 : ℂ) ρ}
  have hrpos : 0 < (1 - ρ) / 16 := by linarith [hρ.2]
  obtain ⟨F, hF⟩ := (isCompact_closedBall (0 : ℂ) ρ).elim_finite_subcover
    (fun w : W => ball (w : ℂ) ((1 - ρ) / 16)) (fun _ => isOpen_ball) (by
      intro z hz
      exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, by simpa [Metric.mem_ball] using hrpos⟩)
  have hcover : ball (0 : ℂ) ρ ⊆ ⋃ w ∈ F, ball (w : ℂ) ((1 - ρ) / 16) := by
    intro z hz
    exact hF (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hz)))
  have hdisk : ∀ w ∈ F, ∃ Cw : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      M₀.P (l46tInnerBadPrime M₀.curve (ball (w : ℂ) ((1 - ρ) / 16)) ε (2 * k) ζ) ≤
        ENNReal.ofReal (Cw * ε ^ s) := by
    intro w _
    obtain ⟨p, q, hcmpw⟩ := hcmp ρ hρ w w.2
    have hw := l46t_innerDegreeBoundPrime_disk D hγ hS uS k hk M₀ hIGtarget u₀
      ((w : ℂ) + ((1 - ρ) / 2 : ℝ)) w
      (show (3 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num)
      (bundle_testDisk_subset_sourceDisk hρ w)
      (show (1 - ρ) / 16 < (1 - ρ) / 8 by linarith [hρ.2])
      (l46tObservation ρ w) hcmpw
      (by intro k' ζ' ε hε;
          simpa [l46tLocalRegion] using hlocal ρ hρ w w.2 k' ζ' ε hε)
    exact hw ζ hζ s
  let Cw (w : W) : ℝ := if hw : w ∈ F then Classical.choose (hdisk w hw) else 0
  have hCw : ∀ w ∈ F, ∀ ε ∈ Ioo (0 : ℝ) 1,
      M₀.P (l46tInnerBadPrime M₀.curve (ball (w : ℂ) ((1 - ρ) / 16)) ε (2 * k) ζ) ≤
        ENNReal.ofReal (Cw w * ε ^ s) := by
    intro w hw ε hε
    simp only [Cw, dite_eq_left hw]
    exact (Classical.choose_spec (hdisk w hw)) ε hε
  let C : ℝ := ∑ w ∈ F, max (Cw w) 0
  refine ⟨C, fun ε hε => ?_⟩
  have hsub : {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (Real.log ε⁻¹ ^ (((2 * k : ℕ) : ℝ) * (1 + ζ) + 1)) <
          ((GMS4c.degreeInPrime ε (M₀.curve ω) z : ℕ∞) : ℝ≥0∞)} ⊆
      ⋃ w ∈ F, l46tInnerBadPrime M₀.curve (ball (w : ℂ) ((1 - ρ) / 16)) ε (2 * k) ζ := by
    rintro ω ⟨z, hz, hbad⟩
    have hzF := hcover hz
    simp only [Set.mem_iUnion] at hzF
    obtain ⟨w, hwF, hzw⟩ := hzF
    exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hwF, ⟨z, hzw, hbad⟩⟩⟩
  calc
    M₀.P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (Real.log ε⁻¹ ^ (((2 * k : ℕ) : ℝ) * (1 + ζ) + 1)) <
          ((GMS4c.degreeInPrime ε (M₀.curve ω) z : ℕ∞) : ℝ≥0∞)} ≤
        M₀.P (⋃ w ∈ F, l46tInnerBadPrime M₀.curve
          (ball (w : ℂ) ((1 - ρ) / 16)) ε (2 * k) ζ) :=
      measure_mono hsub
    _ ≤ ∑ w ∈ F, M₀.P (l46tInnerBadPrime M₀.curve
        (ball (w : ℂ) ((1 - ρ) / 16)) ε (2 * k) ζ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ w ∈ F, ENNReal.ofReal (max (Cw w) 0 * ε ^ s) := by
      apply Finset.sum_le_sum
      intro w hw
      exact (hCw w hw ε hε).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.1.le _)))
    _ = ENNReal.ofReal (C * ε ^ s) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun w hw =>
        mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hε.1.le _))]
      congr 1
      simp only [C, Finset.sum_mul]

/-! ### The zero-cone model -/

/-- **The all-visit transferred Lemma 4.6 on the frozen zero-cone model from the primed reconstruction alone**
(the comparison via `BundleSec4.l46tZeroConeComparison_of_CMRN`; sources `coneFieldVersion D`, target
`l46tZeroConeFieldVersion D`, phase `U` on both sides). -/
theorem l46t_zeroCone_innerDegreeBoundPolylogPrime_of_primeReconstruction
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hlocal : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      ∀ (k : ℕ) (ζ ε : ℝ), ε ∈ Ioo (0 : ℝ) 1 →
      L46TLocalReconstructionPrime (l46tObservation ρ w) (l46tLocalRegion ρ w) P P
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) (coneFieldVersion D))
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) T
        (l46tZeroConeFieldVersion D) hIG₀ T
        (fun ω => l46tTranslateCurve (w + ((1 - ρ) / 2 : ℝ)) (η ω))
        (l46tZeroConeCellModel D hγ).curve
        (ball w ((1 - ρ) / 16)) ε k ζ) :
    ∃ k : ℕ, GMS4c.InnerDegreeBoundPolylogPrime (l46tZeroConeCellModel D hγ) (2 * k) := by
  -- the target model with the measurable version of the 0-cone field (same law, curve and area)
  let M₀' : GMSLemma27.CellModel γ :=
    { (l46tZeroConeCellModel D hγ) with field := l46tZeroConeFieldVersion D }
  obtain ⟨k, hk⟩ := l46t_innerDegreeBoundPolylogPrime_of_localComparison D hγ (coneFieldVersion D) T
    M₀' hIG₀ T (l46tZeroConeComparison_of_CMRN D hγ) hlocal
  exact ⟨k, hk⟩

/-- On the zero-cone model, the first-visit degree failure is a.s. inside the all-visit failure (η₀ hits every point at
`τ_z`: `GMS4b.hitTime_spec` with the zero-cone geometry). -/
theorem l46t_zeroCone_innerDegreeBoundPolylog_of_prime
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {k : ℕ}
    (h : GMS4c.InnerDegreeBoundPolylogPrime (l46tZeroConeCellModel D hγ) k) :
    InnerDegreeBoundPolylog (l46tZeroConeCellModel D hγ) k := by
  intro ρ hρ ζ hζ s
  obtain ⟨C, hC⟩ := h ρ hρ ζ hζ s
  refine ⟨C, fun ε hε => ?_⟩
  have hgeom := l46t_zeroCone_spaceFillingGeometry D hγ
  have hhit : ∀ᵐ ω ∂(l46tZeroConeCellModel D hγ).P, ∀ z : ℂ,
      (l46tZeroConeCellModel D hγ).curve ω (hitTime ((l46tZeroConeCellModel D hγ).curve ω) z) = z := by
    filter_upwards [hgeom, (l46tZeroConeCellModel D hγ).ae_continuous_curve] with ω hω hc z
    exact hitTime_spec hc hω.2.1 (hω.1 z)
  have hnull : (l46tZeroConeCellModel D hγ).P {ω | ¬ ∀ z : ℂ,
      (l46tZeroConeCellModel D hγ).curve ω (hitTime ((l46tZeroConeCellModel D hγ).curve ω) z) = z} = 0 :=
    ae_iff.mp hhit
  have hsub : {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
          ((degreeIn ε ((l46tZeroConeCellModel D hγ).curve ω) z : ℕ∞) : ℝ≥0∞)} ⊆
      {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
          ((GMS4c.degreeInPrime ε ((l46tZeroConeCellModel D hγ).curve ω) z : ℕ∞) : ℝ≥0∞)} ∪
        {ω | ¬ ∀ z : ℂ,
          (l46tZeroConeCellModel D hγ).curve ω (hitTime ((l46tZeroConeCellModel D hγ).curve ω) z) = z} := by
    rintro ω ⟨z, hz, hbad⟩
    by_cases hω : ∀ z : ℂ,
        (l46tZeroConeCellModel D hγ).curve ω (hitTime ((l46tZeroConeCellModel D hγ).curve ω) z) = z
    · left
      have hmem := GMS4c.firstHit_innerBad_subset_prime (ε := ε) (ζ := ζ) (k := k)
        (c := (l46tZeroConeCellModel D hγ).curve ω) (S := ball (0 : ℂ) ρ)
        (fun z _ => hω z) ⟨hz, hbad⟩
      exact ⟨z, hmem.1, hmem.2⟩
    · exact Or.inr hω
  calc
    (l46tZeroConeCellModel D hγ).P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
          ((degreeIn ε ((l46tZeroConeCellModel D hγ).curve ω) z : ℕ∞) : ℝ≥0∞)} ≤
        (l46tZeroConeCellModel D hγ).P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
          ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
            ((GMS4c.degreeInPrime ε ((l46tZeroConeCellModel D hγ).curve ω) z : ℕ∞) : ℝ≥0∞)} +
        (l46tZeroConeCellModel D hγ).P {ω | ¬ ∀ z : ℂ,
          (l46tZeroConeCellModel D hγ).curve ω (hitTime ((l46tZeroConeCellModel D hγ).curve ω) z) = z} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ = (l46tZeroConeCellModel D hγ).P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
          ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
            ((GMS4c.degreeInPrime ε ((l46tZeroConeCellModel D hγ).curve ω) z : ℕ∞) : ℝ≥0∞)} := by
      rw [hnull, add_zero]
    _ ≤ ENNReal.ofReal (C * ε ^ s) := hC ε hε

/-- **The repaired Lemma 4.6 (first visit) on the frozen zero-cone model from the primed reconstruction alone.** -/
theorem l46t_zeroCone_innerDegreeBoundPolylog_of_primeReconstruction
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hlocal : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      ∀ (k : ℕ) (ζ ε : ℝ), ε ∈ Ioo (0 : ℝ) 1 →
      L46TLocalReconstructionPrime (l46tObservation ρ w) (l46tLocalRegion ρ w) P P
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) (coneFieldVersion D))
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) T
        (l46tZeroConeFieldVersion D) hIG₀ T
        (fun ω => l46tTranslateCurve (w + ((1 - ρ) / 2 : ℝ)) (η ω))
        (l46tZeroConeCellModel D hγ).curve
        (ball w ((1 - ρ) / 16)) ε k ζ) :
    ∃ k : ℕ, InnerDegreeBoundPolylog (l46tZeroConeCellModel D hγ) (2 * k) := by
  obtain ⟨k, hk⟩ := l46t_zeroCone_innerDegreeBoundPolylogPrime_of_primeReconstruction D hγ hlocal
  exact ⟨k, l46t_zeroCone_innerDegreeBoundPolylog_of_prime D hγ hk⟩

/-- **[18] Proposition 4.5 on the frozen zero-cone model from the primed reconstruction** (and the two circle-average
bounds of its event), through L46S's `prop45_holds_of_polylog` and the transfer's zero-cone inputs. -/
theorem l46t_zeroCone_prop45_of_primeReconstruction
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hlocal : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      ∀ (k : ℕ) (ζ ε : ℝ), ε ∈ Ioo (0 : ℝ) 1 →
      L46TLocalReconstructionPrime (l46tObservation ρ w) (l46tLocalRegion ρ w) P P
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) (coneFieldVersion D))
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) T
        (l46tZeroConeFieldVersion D) hIG₀ T
        (fun ω => l46tTranslateCurve (w + ((1 - ρ) / 2 : ℝ)) (η ω))
        (l46tZeroConeCellModel D hγ).curve
        (ball w ((1 - ρ) / 16)) ε k ζ)
    {H HIG : ℝ → ℂ → Ω → ℝ}
    (hH : CircleAverageSupBound P H) (hHIG : CircleAverageSupBound P HIG)
    {ρ q ζ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ Ioo (0 : ℝ) (2 / (2 + γ) ^ 2))
    (hζ : ζ ∈ Ioo (0 : ℝ) (q / 4)) :
    ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      P (prop45Event (l46tZeroConeCellModel D hγ) H HIG ε ρ q ζ)ᶜ ≤
        ENNReal.ofReal (C * ε ^ α) := by
  let M := l46tZeroConeCellModel D hγ
  have hmass : UpperMassBound M :=
    GMCUpper.upperMassBoundZeroCone_toCellModel M hγ D
      (Filter.Eventually.of_forall fun _ => rfl)
  obtain ⟨k, hin⟩ := l46t_zeroCone_innerDegreeBoundPolylog_of_primeReconstruction D hγ hlocal
  exact prop45_holds_of_polylog (2 * k) M hγ.1
    (l46t_zeroCone_segmentsContainBalls D hγ)
    (GMCFacts.gmcLowerTail_holds hγ.1 hγ.2)
    (l46t_zeroCone_areaDominates D hγ) hmass
    (l46t_zeroCone_spaceFillingGeometry D hγ) hin hH hHIG hρ hq hζ

end Bundle

end MatedCRTHarmonic.BundleSec4
