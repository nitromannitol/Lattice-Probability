/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Field.LawTransfer at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Field.BandFacts
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.LfppDistance
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseLaw
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Law transfer for the white-noise band fields (packet P-X2, target T3)

Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1)–(1.2) (the field `H_{ε,1}` and the
LFPP distance are defined from one white-noise realization); planning audits HA5 Details D14
("the law of a Borel functional of the version of `H_{a',b'}` is the same for all white noises")
and D12 Claim 5, HA2 Details D2 (Corollary (ii)).

The law of a white-noise family `(W (F t))_{t ∈ T}` is determined by its finite-dimensional laws,
which are centered Gaussian with covariance `⟪F s, F t⟫` (`IsWhiteNoise.cov_eq`). Hence:

* `IsWhiteNoise.map_restrict_eq`, `IsWhiteNoise.map_eq`: for every family `F : T → WN d` (any
  index type), `(W (F t))_t` has the same law on `T → ℝ` (product σ-algebra) for any two white
  noises `W`, `W'` on any two probability spaces;
* `IsWhiteNoise.map_eq_of_ae_eq`, `IsWhiteNoise.map_comp_eq_of_ae_eq`: the same for measurable
  modifications, and for every measurable functional of them;
* `IsBandVersion.map_eq`, `IsBandVersion.map_comp_eq` (target T3, product σ-algebra on
  `Rd d → ℝ`), and `map_bandVersion_family_eq` (joint law of versions of several bands);
* the Borel σ-algebra of `C(Rd d, ℝ)` (compact-open topology) is the pullback of the product
  σ-algebra (`measurableSpace_continuousMap_eq_comap`); with `contField` (a continuous field as a
  random element of `C(Rd d, ℝ)`): `IsBandVersion.map_contField_eq`,
  `IsBandVersion.map_comp_contField_eq` (Borel functionals on `C(Rd d, ℝ)`),
  `IsBandVersion.map_comp_restrict_eq` (Borel functionals on `C(K, ℝ)`, e.g. `K` compact);
* `IsBandVersion.map_comp_eq_of_measurable` and `IsBandVersion.identDistrib_comp`: for every
  `G : (Rd d → ℝ) → β` whose restriction to continuous functions is Borel measurable on
  `C(Rd d, ℝ)` (`Measurable fun f : C(Rd d, ℝ) => G f`), the laws of `G(H)` and `G(H')` agree;
  in particular `IsBandVersion.map_lfppDistance_eq` for `G = lfppDistance d ζ`.

Templates: `LQGMetric.WhiteNoise.map_phi_eq_of_cov`, `map_eq_of_forall_finset'`
(`LQGMetric/Field/WhiteNoiseLaw.lean`), QuantumZipper's `WedgeRes.map_eq_of_gaussian_vec`,
`LQGMetric.DDDF.measurableSpace_continuousMap_eq_comap` (`LQGMetric/Papers/DDDF/P10Law.lean`)
and `GaussianLQG.FieldCmp.map_contPhiMN_eq`, `map_comp_contPhiMN_eq`
(`GaussianLQG/Uniform/FieldComparison/Shift.lean`), from `ℂ` to `ℝ^d`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP

variable {d : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ}

namespace IsWhiteNoise

/-- **Finite-dimensional laws do not depend on the white noise**: for a finite family of vectors,
`(W (F i))_{i ∈ I}` has the same law for any two white noises (on any two probability spaces):
both are centered Gaussian vectors with covariance `⟪F i, F j⟫`. -/
theorem map_restrict_eq (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {T : Type*}
    (F : T → WN d) (I : Finset T) :
    P.map (fun ω => I.restrict fun t => W (F t) ω) =
      P'.map (fun ω => I.restrict fun t => W' (F t) ω) := by
  have := hW.isProbabilityMeasure
  have := hW'.isProbabilityMeasure
  exact QuantumZipper.WedgeRes.map_eq_of_gaussian_vec (ι := I) (U := fun i => W (F i))
    (V := fun i => W' (F i)) (hW.hasGaussianLaw_fintype fun i : I => F i)
    (hW'.hasGaussianLaw_fintype fun i : I => F i) (fun i => hW.measurable _)
    (fun i => hW'.measurable _) (fun i => hW.memLp _ 2 ENNReal.ofNat_ne_top)
    (fun i => hW'.memLp _ 2 ENNReal.ofNat_ne_top) (fun i => hW.integral_eq_zero _)
    (fun i => hW'.integral_eq_zero _) fun i j => by rw [hW.cov_eq, hW'.cov_eq]

/-- **Law transfer** (product σ-algebra on `T → ℝ`): for every family `F : T → WN d` (any index
type), the process `(W (F t))_t` has the same law for any two white noises. -/
theorem map_eq (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {T : Type*} (F : T → WN d) :
    P.map (fun ω t => W (F t) ω) = P'.map (fun ω t => W' (F t) ω) := by
  have := hW.isProbabilityMeasure
  have := hW'.isProbabilityMeasure
  exact LQGMetric.WhiteNoise.map_eq_of_forall_finset'
    (measurable_pi_iff.2 fun t => hW.measurable (F t)).aemeasurable
    (measurable_pi_iff.2 fun t => hW'.measurable (F t)).aemeasurable (hW.map_restrict_eq hW' F)

/-- **Law transfer for modifications**: measurable modifications `X` of `(W (F t))_t` and `X'`
of `(W' (F t))_t` have the same law on `T → ℝ` (product σ-algebra). -/
theorem map_eq_of_ae_eq (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {T : Type*}
    (F : T → WN d) {X : T → Ω → ℝ} {X' : T → Ω' → ℝ} (hXm : ∀ t, Measurable (X t))
    (hX'm : ∀ t, Measurable (X' t)) (hX : ∀ t, X t =ᵐ[P] W (F t))
    (hX' : ∀ t, X' t =ᵐ[P'] W' (F t)) :
    P.map (fun ω t => X t ω) = P'.map (fun ω t => X' t ω) := by
  have := hW.isProbabilityMeasure
  have := hW'.isProbabilityMeasure
  rw [map_eq_of_forall_ae_eq (measurable_pi_iff.2 hXm).aemeasurable
      (measurable_pi_iff.2 fun t => hW.measurable (F t)).aemeasurable hX,
    map_eq_of_forall_ae_eq (measurable_pi_iff.2 hX'm).aemeasurable
      (measurable_pi_iff.2 fun t => hW'.measurable (F t)).aemeasurable hX']
  exact hW.map_eq hW' F

end IsWhiteNoise

/-! ### Band versions: the product σ-algebra -/

variable {κ : Rd d → ℝ} {a b : ℝ} {H : Rd d → Ω → ℝ} {H' : Rd d → Ω' → ℝ}

namespace IsBandVersion

/-- **Law transfer for band versions** (target T3, product σ-algebra on `Rd d → ℝ`): versions of
the same band field `H_{a,b}` over two white noises (possibly on different probability spaces)
have the same law. No continuity and no condition on `a`, `b` are needed. -/
theorem map_eq (hH : IsBandVersion P W κ a b H) (hH' : IsBandVersion P' W' κ a b H')
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') :
    P.map (fun ω z => H z ω) = P'.map (fun ω z => H' z ω) :=
  hW.map_eq_of_ae_eq hW' (fun z => bandVec κ a b z) hH.measurable hH'.measurable hH.ae_eq
    hH'.ae_eq

end IsBandVersion

/-! ### Continuous fields as random elements of `C(Rd d, ℝ)` -/

/-- The Borel σ-algebra of `C(Rd d, ℝ)` (compact-open topology) is the pullback of the product
σ-algebra of `Rd d → ℝ`. -/
theorem measurableSpace_continuousMap_eq_comap :
    (ContinuousMap.measurableSpace : MeasurableSpace C(Rd d, ℝ)) =
      MeasurableSpace.comap (fun f : C(Rd d, ℝ) => (f : Rd d → ℝ)) MeasurableSpace.pi := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, MeasurableSpace.pi,
    MeasurableSpace.comap_iSup]
  simp_rw [MeasurableSpace.comap_comp]
  rfl

/-- A continuous field `z ↦ H z ω` as a random element of `C(Rd d, ℝ)`. -/
def contField {α : Type*} (H : Rd d → α → ℝ) (hc : ∀ ω, Continuous fun z => H z ω) (ω : α) :
    C(Rd d, ℝ) :=
  ⟨fun z => H z ω, hc ω⟩

@[simp]
theorem contField_apply {α : Type*} (H : Rd d → α → ℝ) (hc : ∀ ω, Continuous fun z => H z ω)
    (ω : α) (z : Rd d) : contField H hc ω z = H z ω :=
  rfl

theorem measurable_contField {H : Rd d → Ω → ℝ} (hc : ∀ ω, Continuous fun z => H z ω)
    (hm : ∀ z, Measurable (H z)) : Measurable (contField H hc) :=
  ContinuousMap.measurable_iff_eval.2 hm

/-- Continuous measurable fields with the same law on `Rd d → ℝ` have the same law on
`C(Rd d, ℝ)`. -/
theorem map_contField_eq_of_map_eq (hc : ∀ ω, Continuous fun z => H z ω)
    (hm : ∀ z, Measurable (H z)) (hc' : ∀ ω, Continuous fun z => H' z ω)
    (hm' : ∀ z, Measurable (H' z))
    (h : P.map (fun ω z => H z ω) = P'.map (fun ω z => H' z ω)) :
    P.map (contField H hc) = P'.map (contField H' hc') := by
  ext S hS
  rw [Measure.map_apply (measurable_contField hc hm) hS,
    Measure.map_apply (measurable_contField hc' hm') hS]
  have hS' := hS
  rw [measurableSpace_continuousMap_eq_comap] at hS'
  obtain ⟨T, hT, rfl⟩ := hS'
  have e1 : contField H hc ⁻¹' ((fun f : C(Rd d, ℝ) => (f : Rd d → ℝ)) ⁻¹' T) =
      (fun ω z => H z ω) ⁻¹' T := rfl
  have e2 : contField H' hc' ⁻¹' ((fun f : C(Rd d, ℝ) => (f : Rd d → ℝ)) ⁻¹' T) =
      (fun ω z => H' z ω) ⁻¹' T := rfl
  rw [e1, e2, ← Measure.map_apply (measurable_pi_iff.2 hm) hT,
    ← Measure.map_apply (measurable_pi_iff.2 hm') hT, h]

namespace IsBandVersion

/-- **Law transfer on `C(Rd d, ℝ)`** (target T3, Borel σ-algebra of the compact-open topology):
the continuous versions of the same band field over two white noises have the same law as random
elements of `C(Rd d, ℝ)`. -/
theorem map_contField_eq (hH : IsBandVersion P W κ a b H) (hH' : IsBandVersion P' W' κ a b H')
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') :
    P.map (contField H hH.continuous) = P'.map (contField H' hH'.continuous) :=
  map_contField_eq_of_map_eq hH.continuous hH.measurable hH'.continuous hH'.measurable
    (hH.map_eq hH' hW hW')

/-- **Law transfer of Borel functionals on `C(Rd d, ℝ)`** (target T3). -/
theorem map_comp_contField_eq (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ a b H') (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    {β : Type*} [MeasurableSpace β] {G : C(Rd d, ℝ) → β} (hG : Measurable G) :
    P.map (fun ω => G (contField H hH.continuous ω)) =
      P'.map (fun ω => G (contField H' hH'.continuous ω)) := by
  have e1 : (fun ω => G (contField H hH.continuous ω)) = G ∘ contField H hH.continuous := rfl
  have e2 : (fun ω => G (contField H' hH'.continuous ω)) = G ∘ contField H' hH'.continuous := rfl
  rw [e1, e2, ← Measure.map_map hG (measurable_contField hH.continuous hH.measurable),
    ← Measure.map_map hG (measurable_contField hH'.continuous hH'.measurable),
    hH.map_contField_eq hH' hW hW']

/-- **Law transfer of functionals of the continuous field** (target T3, the form that applies to
`lfppDistance d ζ`): for every `G : (Rd d → ℝ) → β` such that `f ↦ G f` is Borel measurable on
`C(Rd d, ℝ)`, `G(H)` and `G(H')` have the same law. -/
theorem map_comp_eq_of_measurable (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ a b H') (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    {β : Type*} [MeasurableSpace β] {G : (Rd d → ℝ) → β}
    (hG : Measurable fun f : C(Rd d, ℝ) => G f) :
    P.map (fun ω => G fun z => H z ω) = P'.map (fun ω => G fun z => H' z ω) :=
  hH.map_comp_contField_eq hH' hW hW' hG

/-- The field functional `G(H)` is measurable (same hypothesis on `G`). -/
theorem measurable_comp (hH : IsBandVersion P W κ a b H) {β : Type*} [MeasurableSpace β]
    {G : (Rd d → ℝ) → β} (hG : Measurable fun f : C(Rd d, ℝ) => G f) :
    Measurable fun ω => G fun z => H z ω :=
  hG.comp (measurable_contField hH.continuous hH.measurable)

/-- Probabilities of events `{G(H) ∈ S}` do not depend on the white noise. -/
theorem measure_comp_mem_eq (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ a b H') (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    {β : Type*} [MeasurableSpace β] {G : (Rd d → ℝ) → β}
    (hG : Measurable fun f : C(Rd d, ℝ) => G f) {S : Set β} (hS : MeasurableSet S) :
    P {ω | (G fun z => H z ω) ∈ S} = P' {ω | (G fun z => H' z ω) ∈ S} := by
  have h : P.map (fun ω => G fun z => H z ω) S = P'.map (fun ω => G fun z => H' z ω) S := by
    rw [hH.map_comp_eq_of_measurable hH' hW hW' hG]
  rwa [Measure.map_apply (hH.measurable_comp hG) hS,
    Measure.map_apply (hH'.measurable_comp hG) hS] at h

/-- **Law transfer of the LFPP distance** (target T3): once `f ↦ D^ζ(f)` is known to be Borel
measurable on `C(Rd d, ℝ)` (packet P-X1), the laws of `D^ζ(H)` and `D^ζ(H')` agree. -/
theorem map_lfppDistance_eq (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P' W' κ a b H') (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    (ζ : ℝ) (hmeas : Measurable fun f : C(Rd d, ℝ) => lfppDistance d ζ f) :
    P.map (fun ω => lfppDistance d ζ fun z => H z ω) =
      P'.map (fun ω => lfppDistance d ζ fun z => H' z ω) :=
  hH.map_comp_eq_of_measurable hH' hW hW' hmeas

end IsBandVersion

end HigherDimLFPP
