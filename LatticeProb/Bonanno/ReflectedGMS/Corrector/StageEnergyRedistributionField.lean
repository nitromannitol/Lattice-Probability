/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.StageEnergyRedistributionField at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StagePairingBlockOwnership
import LatticeProb.Bonanno.ReflectedGMS.Corrector.OwnedFieldLabelTransport
import LatticeProb.Bonanno.ReflectedGMS.Corrector.TransportAeGating
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PairingTransportWeld
import LatticeProb.Bonanno.ReflectedGMS.Spatial.GoodMarkedSpace

/-!
# The owned energy coefficient field, and the endpoint density of an energy coefficient

`Corrector/StagePairingVanishing` reduces `hproj` to two block-local inputs, the first of
which (`MarkedStageBlockEnergy`, the long-standing `hmE`) has blocked the lane because every
naive route bounds the wrong side of the minimality inequality.  The route that does close it
runs the checked redistribution `s:lem:redistribution` for the **nonnegative energy coefficient**
`q_e = c_e |∇_e Ψ|²` of a field `Ψ`, restricted to the edges owned by a selected square.  This
module supplies the field-level objects of that route, all on an arbitrary marked re-rooting:

* `energyEndpointDensity e Ψ` — the manuscript endpoint density `(2 a_{H_0})⁻¹ ∑_{e ∋ H_0} q_e`
  of the energy coefficient of `Ψ`, read on raw labels.  Off the cell boundary mask it **is** the
  rooted specific-energy density `ρ_{∇Ψ}(ω, 0)` of `Environment/RootDensities`
  (`energyEndpointDensity_eq_rootedSpecificEnergyDensity`): the two normalisations agree.
* `posField_rootEndpointDensity` — for a `PairingOwnership` of the pair `(Ψ, Ψ)` the positive
  part of the signed pairing coefficient is exactly the energy coefficient, definitionally.
* `ownedEnergyField R m Ψ` — the `OwnedEdgeField` carrying `q_e` **only on the owned edges**
  (owner `labelOwner R m`, weight `0` on unowned edges).  Unlike a `PairingOwnership`, it needs
  no vanishing of `Ψ` on the skeleton, so it is available for the centroid embedding itself.
  Its endpoint density is dominated by `energyEndpointDensity`
  (`rootEndpointDensity_ownedEnergyField_le`), and on the actual marked space it is
  `MarkedMassTransportProducer.SimilarityCovariantField` as soon as the increments of `Ψ`
  transport (`similarityCovariantField_ownedEnergyField`), so the redistribution identity holds
  for it from `s:eq:MTP` alone (`lintegral_rootEndpointDensity_eq_ownerBlockDensity_ownedEnergyField`).
* `endpointDensity_le_of_le_abs` — the endpoint density of any real coefficient dominated by
  `|c_e ⟪∇_e Ψ, ∇_e H⟫|` is at most `ρ_{∇Ψ} + ρ_{∇H}`; this is the input of
  `MarkedStagePairingEndpointFinite`.
* `aemeasurable_ownerBlockDensity` — the owner-block density of any owned edge field on the
  actual marked space is almost surely measurable: on the event where the selected origin block
  is unique it is a countable sum over the candidate levels of measurable block densities.

Nothing here is a transport identity for the stage fields; those are assembled in
`Corrector/StageBlockEnergy`.  **This file proves no main theorem.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.StageEnergyRedistributionField

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging
open SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField
open EnvironmentLaws RootDensities OwnedFieldPairingTransport PairingOwnershipInstance
open MarkedMassTransportProducer OwnedFieldLabelTransport StagePairingBlockOwnership

/-! ### A real inequality: the signed coefficient against the two energy coefficients -/

/-- `x ≤ |c ⟪a, b⟫|` with `c ≥ 0` gives `x⁺ ≤ c ⟪a, a⟫ + c ⟪b, b⟫` in `ℝ≥0∞`. -/
theorem ofReal_le_of_le_abs_inner {x c : ℝ} (hc : 0 ≤ c) (a b : Plane)
    (hx : x ≤ |c * inner ℝ a b|) :
    ENNReal.ofReal x ≤ ENNReal.ofReal (c * inner ℝ a a) + ENNReal.ofReal (c * inner ℝ b b) := by
  have h1 : |inner ℝ a b| ≤ ‖a‖ * ‖b‖ := abs_real_inner_le_norm a b
  have h2 : ‖a‖ * ‖b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]
  have h3 : x ≤ c * inner ℝ a a + c * inner ℝ b b := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    calc x ≤ |c * inner ℝ a b| := hx
      _ = c * |inner ℝ a b| := by rw [abs_mul, abs_of_nonneg hc]
      _ ≤ c * (‖a‖ ^ 2 + ‖b‖ ^ 2) := mul_le_mul_of_nonneg_left (h1.trans h2) hc
      _ = c * ‖a‖ ^ 2 + c * ‖b‖ ^ 2 := by ring
  have hnn1 : 0 ≤ c * inner ℝ a a := mul_nonneg hc real_inner_self_nonneg
  have hnn2 : 0 ≤ c * inner ℝ b b := mul_nonneg hc real_inner_self_nonneg
  calc ENNReal.ofReal x ≤ ENNReal.ofReal (c * inner ℝ a a + c * inner ℝ b b) :=
        ENNReal.ofReal_le_ofReal h3
    _ = ENNReal.ofReal (c * inner ℝ a a) + ENNReal.ofReal (c * inner ℝ b b) :=
        ENNReal.ofReal_add hnn1 hnn2

/-! ### The endpoint density of the energy coefficient -/

/-- The manuscript endpoint density `(2 a_{H_0})⁻¹ ∑_{e ∋ H_0} c_e |∇_e Ψ|²` of the energy
coefficient of `Ψ`, read on raw labels with the boundary convention of
`SpecificEnergyRedistribution.originLabel`. -/
noncomputable def energyEndpointDensity (e : Env) (Ψ : Vertex e.val → Plane) : ℝ≥0∞ :=
  (originLabel e).elim 0 fun a =>
    (∑' k : ℕ, ENNReal.ofReal (pairCoeff e Ψ Ψ (a, k))) / (2 * volume (labelCell e a))

/-- The cell area of the root label, as an `ℝ≥0∞` volume. -/
theorem ofReal_cellArea_eq_volume_labelCell (e : Env) (v : Vertex e.val) :
    ENNReal.ofReal (cellArea (decode e) v) = volume (labelCell e v.1) := by
  rw [← toReal_volume_labelCell e v, ENNReal.ofReal_toReal (volume_labelCell_lt_top e v.1).ne]

/-- The neighbour sum of the energy coefficient at a root vertex, over raw labels, is the
neighbour sum of `RootDensities.specificEnergyDensity` over vertices. -/
theorem tsum_ofReal_pairCoeff_self (e : Env) (Ψ : Vertex e.val → Plane) (v : Vertex e.val) :
    (∑' k : ℕ, ENNReal.ofReal (pairCoeff e Ψ Ψ (v.1, k)))
      = ∑' w : Vertex e.val,
          ENNReal.ofReal ((decode e).graph.c v w) * ENNReal.ofReal (‖Ψ w - Ψ v‖ ^ 2) := by
  rw [← tsum_vertex_eq_tsum_nat e (fun k : ℕ => ENNReal.ofReal (pairCoeff e Ψ Ψ (v.1, k)))
    (fun n hn => by rw [pairCoeff_eq_zero_of_snd_absent e Ψ Ψ v.1 hn, ENNReal.ofReal_zero])]
  refine tsum_congr fun w => ?_
  rw [pairCoeff_vertex e Ψ Ψ v w, real_inner_self_eq_norm_sq,
    ENNReal.ofReal_mul ((decode e).graph.c_nonneg v w)]

/-- **The endpoint density of the energy coefficient is the rooted specific-energy density**,
off the cell boundary mask.  The two normalisations `2 · volume (labelCell …)` and
`2 · cellArea` agree. -/
theorem energyEndpointDensity_eq_rootedSpecificEnergyDensity (e : Env)
    (Ψ : Vertex e.val → Plane) (h0 : (0 : Plane) ∉ boundaryMask (decode e)) :
    energyEndpointDensity e Ψ = rootedSpecificEnergyDensity (decode e) Ψ 0 := by
  have hF : Geometry (decode e) := decode_geometry e
  obtain ⟨v, hv, -⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode e) hF h0
  have horigin : originLabel e = some v.1 := by
    rw [originLabel_eq_map_rootAt e h0, hv]
    rfl
  have hL : energyEndpointDensity e Ψ
      = (∑' k : ℕ, ENNReal.ofReal (pairCoeff e Ψ Ψ (v.1, k))) / (2 * volume (labelCell e v.1)) := by
    unfold energyEndpointDensity
    rw [horigin]
    rfl
  have hR : rootedSpecificEnergyDensity (decode e) Ψ 0 = specificEnergyDensity (decode e) Ψ v := by
    unfold rootedSpecificEnergyDensity
    rw [hv]
    rfl
  rw [hL, hR, tsum_ofReal_pairCoeff_self e Ψ v, ← ofReal_cellArea_eq_volume_labelCell e v]
  rfl

/-- **The endpoint density of a coefficient dominated by the absolute signed coefficient is at
most the sum of the two rooted specific-energy densities**, off the boundary mask.  This is
the pointwise input of `MarkedStagePairingEndpointFinite`: it is applied to the positive and to
the negative part of the signed pairing coefficient. -/
theorem endpointDensity_le_of_le_abs (e : Env) (Ψ H : Vertex e.val → Plane)
    (h0 : (0 : Plane) ∉ boundaryMask (decode e)) (g : ℕ → ℕ → ℝ)
    (hg : ∀ a k : ℕ, g a k ≤ |pairCoeff e Ψ H (a, k)|) :
    ((originLabel e).elim 0 fun a =>
        (∑' k : ℕ, ENNReal.ofReal (g a k)) / (2 * volume (labelCell e a)))
      ≤ rootedSpecificEnergyDensity (decode e) Ψ 0 + rootedSpecificEnergyDensity (decode e) H 0 := by
  have hF : Geometry (decode e) := decode_geometry e
  obtain ⟨v, hv, -⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode e) hF h0
  have horigin : originLabel e = some v.1 := by
    rw [originLabel_eq_map_rootAt e h0, hv]
    rfl
  rw [← energyEndpointDensity_eq_rootedSpecificEnergyDensity e Ψ h0,
    ← energyEndpointDensity_eq_rootedSpecificEnergyDensity e H h0]
  have hΨ : energyEndpointDensity e Ψ
      = (∑' k : ℕ, ENNReal.ofReal (pairCoeff e Ψ Ψ (v.1, k))) / (2 * volume (labelCell e v.1)) := by
    unfold energyEndpointDensity
    rw [horigin]
    rfl
  have hH : energyEndpointDensity e H
      = (∑' k : ℕ, ENNReal.ofReal (pairCoeff e H H (v.1, k))) / (2 * volume (labelCell e v.1)) := by
    unfold energyEndpointDensity
    rw [horigin]
    rfl
  have hL : ((originLabel e).elim 0 fun a =>
        (∑' k : ℕ, ENNReal.ofReal (g a k)) / (2 * volume (labelCell e a)))
      = (∑' k : ℕ, ENNReal.ofReal (g v.1 k)) / (2 * volume (labelCell e v.1)) := by
    rw [horigin]
    rfl
  rw [hL, hΨ, hH, ← ENNReal.add_div]
  refine ENNReal.div_le_div_right ?_ _
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : (e.val.1 k).isSome
  · have hΨH : pairCoeff e Ψ H (v.1, k)
        = (decode e).graph.c v ⟨k, hk⟩ * inner ℝ (Ψ ⟨k, hk⟩ - Ψ v) (H ⟨k, hk⟩ - H v) :=
      pairCoeffAt_of_isSome e Ψ H v.2 hk
    have hΨΨ : pairCoeff e Ψ Ψ (v.1, k)
        = (decode e).graph.c v ⟨k, hk⟩ * inner ℝ (Ψ ⟨k, hk⟩ - Ψ v) (Ψ ⟨k, hk⟩ - Ψ v) :=
      pairCoeffAt_of_isSome e Ψ Ψ v.2 hk
    have hHH : pairCoeff e H H (v.1, k)
        = (decode e).graph.c v ⟨k, hk⟩ * inner ℝ (H ⟨k, hk⟩ - H v) (H ⟨k, hk⟩ - H v) :=
      pairCoeffAt_of_isSome e H H v.2 hk
    rw [hΨΨ, hHH]
    refine ofReal_le_of_le_abs_inner ((decode e).graph.c_nonneg v ⟨k, hk⟩) _ _ ?_
    rw [← hΨH]
    exact hg v.1 k
  · have hz : pairCoeff e Ψ H (v.1, k) = 0 := pairCoeff_eq_zero_of_snd_absent e Ψ H v.1 hk
    have hle : g v.1 k ≤ 0 := by
      have := hg v.1 k
      rwa [hz, abs_zero] at this
    rw [ENNReal.ofReal_of_nonpos hle]
    exact zero_le

/-! ### The positive part of the pairing coefficient of `(Ψ, Ψ)` -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {R : MarkedReRooting Ω} {m : ℝ}

/-- For the pair `(Ψ, Ψ)` the positive part of the signed pairing coefficient is the energy
coefficient, so the endpoint density of `posField` is `energyEndpointDensity`.  Definitional. -/
theorem posField_rootEndpointDensity {Ψ : ∀ ω : Ω, Vertex (R.env ω).val → Plane}
    (O : PairingOwnership R m Ψ Ψ) (ω : Ω) :
    (posField O).rootEndpointDensity ω = energyEndpointDensity (R.env ω) (Ψ ω) := rfl

/-! ### The owned energy coefficient field -/

/-- **The owned energy coefficient field** of a marked vertex field `Ψ`: the weight is the
energy coefficient `c_e |∇_e Ψ|²` on the edges owned by a selected square (the canonical
`labelOwner`) and `0` elsewhere.  No vanishing of `Ψ` on the skeleton is required, so this is
available for the centroid embedding itself. -/
noncomputable def ownedEnergyField (R : MarkedReRooting Ω) (m : ℝ)
    (Ψ : ∀ ω : Ω, Vertex (R.env ω).val → Plane) : OwnedEdgeField R m where
  weight ω p := (labelOwner R m ω p).elim 0 fun _ =>
    ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) p)
  owner := labelOwner R m
  weight_symm ω p := by
    show (labelOwner R m ω (p.2, p.1)).elim 0 (fun _ =>
        ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) (p.2, p.1)))
      = (labelOwner R m ω p).elim 0 (fun _ => ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) p))
    rw [labelOwner_symm R m ω p, pairCoeff_symm (R.env ω) (Ψ ω) (Ψ ω) p]
  owner_symm := labelOwner_symm R m
  weight_eq_zero_of_owner_eq_none ω p h := by
    show (labelOwner R m ω p).elim 0 (fun _ =>
      ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) p)) = 0
    rw [h]
    rfl
  weight_eq_zero_of_absent ω p h := by
    obtain ⟨a, b⟩ := p
    show (labelOwner R m ω (a, b)).elim 0 (fun _ =>
      ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) (a, b))) = 0
    rw [labelOwner_eq_none_of_fst R m ω h b]
    rfl
  owner_selected := by
    intro ω p s h
    obtain ⟨a, b⟩ := p
    by_cases ha : ((R.env ω).val.1 a).isSome
    · by_cases hb : ((R.env ω).val.1 b).isSome
      · rw [labelOwner_pair R m ω a b ha hb] at h
        exact (activeEdge_of_activeOwner_eq_some (decode (R.env ω)) (R.grid ω) m h).1
      · rw [labelOwner_eq_none_of_snd R m ω a hb] at h
        exact absurd h (by simp)
    · rw [labelOwner_eq_none_of_fst R m ω ha b] at h
      exact absurd h (by simp)

variable (R) (m)

theorem ownedEnergyField_owner (Ψ : ∀ ω : Ω, Vertex (R.env ω).val → Plane) (ω : Ω)
    (q : ℕ × ℕ) : (ownedEnergyField R m Ψ).owner ω q = labelOwner R m ω q := rfl

theorem ownedEnergyField_weight_of_eq_some (Ψ : ∀ ω : Ω, Vertex (R.env ω).val → Plane)
    (ω : Ω) {p : ℕ × ℕ} {s : SquareIndex} (h : labelOwner R m ω p = some s) :
    (ownedEnergyField R m Ψ).weight ω p = ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) p) := by
  show (labelOwner R m ω p).elim 0 (fun _ =>
    ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) p)) = _
  rw [h]
  rfl

/-- The owned weight never exceeds the energy coefficient. -/
theorem ownedEnergyField_weight_le (Ψ : ∀ ω : Ω, Vertex (R.env ω).val → Plane) (ω : Ω)
    (p : ℕ × ℕ) :
    (ownedEnergyField R m Ψ).weight ω p ≤ ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) p) := by
  by_cases h : labelOwner R m ω p = none
  · rw [(ownedEnergyField R m Ψ).weight_eq_zero_of_owner_eq_none ω p h]
    exact zero_le
  · obtain ⟨s, hs⟩ := exists_eq_some_of_ne_none h
    rw [ownedEnergyField_weight_of_eq_some R m Ψ ω hs]

/-- The owned weight as an indicator, for measurability. -/
theorem ownedEnergyField_weight_eq_indicator (Ψ : ∀ ω : Ω, Vertex (R.env ω).val → Plane)
    (p : ℕ × ℕ) (ω : Ω) :
    (ownedEnergyField R m Ψ).weight ω p
      = {ω : Ω | labelOwner R m ω p ≠ none}.indicator
          (fun ω : Ω => ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) p)) ω := by
  by_cases h : labelOwner R m ω p = none
  · rw [(ownedEnergyField R m Ψ).weight_eq_zero_of_owner_eq_none ω p h,
      Set.indicator_of_notMem (fun hmem => (show labelOwner R m ω p ≠ none from hmem) h)]
  · obtain ⟨s, hs⟩ := exists_eq_some_of_ne_none h
    rw [ownedEnergyField_weight_of_eq_some R m Ψ ω hs, Set.indicator_of_mem h]

/-- **The endpoint density of the owned energy field is dominated by the endpoint density of
the energy coefficient.** -/
theorem rootEndpointDensity_ownedEnergyField_le (Ψ : ∀ ω : Ω, Vertex (R.env ω).val → Plane)
    (ω : Ω) :
    (ownedEnergyField R m Ψ).rootEndpointDensity ω ≤ energyEndpointDensity (R.env ω) (Ψ ω) := by
  unfold OwnedEdgeField.rootEndpointDensity energyEndpointDensity
  cases originLabel (R.env ω) with
  | none => exact le_rfl
  | some a =>
    show (∑' k : ℕ, (ownedEnergyField R m Ψ).weight ω (a, k)) / (2 * volume (labelCell (R.env ω) a))
      ≤ (∑' k : ℕ, ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) (a, k)))
          / (2 * volume (labelCell (R.env ω) a))
    exact ENNReal.div_le_div_right
      (ENNReal.tsum_le_tsum fun k => ownedEnergyField_weight_le R m Ψ ω (a, k)) _

/-- The `none`-fibre of the owner label is measurable as soon as every `some c`-fibre is. -/
theorem measurableSet_labelOwner_ne_none
    (howner : ∀ (q : ℕ × ℕ) (c : SquareIndex),
      MeasurableSet {ω : Ω | labelOwner R m ω q = some c}) (q : ℕ × ℕ) :
    MeasurableSet {ω : Ω | labelOwner R m ω q ≠ none} := by
  have hEq : {ω : Ω | labelOwner R m ω q ≠ none}
      = ⋃ c : SquareIndex, {ω : Ω | labelOwner R m ω q = some c} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact Option.ne_none_iff_exists'
  rw [hEq]
  exact MeasurableSet.iUnion fun c => howner q c

/-- **The owned weight is measurable** as soon as the energy coefficient and the owner fibres
are. -/
theorem measurable_ownedEnergyField_weight (Ψ : ∀ ω : Ω, Vertex (R.env ω).val → Plane)
    (hcoeff : ∀ q : ℕ × ℕ, Measurable fun ω : Ω => pairCoeff (R.env ω) (Ψ ω) (Ψ ω) q)
    (howner : ∀ (q : ℕ × ℕ) (c : SquareIndex),
      MeasurableSet {ω : Ω | labelOwner R m ω q = some c}) (q : ℕ × ℕ) :
    Measurable fun ω : Ω => (ownedEnergyField R m Ψ).weight ω q := by
  have hEq : (fun ω : Ω => (ownedEnergyField R m Ψ).weight ω q)
      = {ω : Ω | labelOwner R m ω q ≠ none}.indicator
          (fun ω : Ω => ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) q)) :=
    funext fun ω => ownedEnergyField_weight_eq_indicator R m Ψ q ω
  rw [hEq]
  exact (hcoeff q).ennreal_ofReal.indicator (measurableSet_labelOwner_ne_none R m howner q)

end Generic

/-! ### The actual marked configuration space -/

section Marked

open ActualMarkedBlockTransport DyadicGridLaw HarmonicMainStatement HarmonicCoordinateAssembly
open HarmonicLawIngredients DyadicGridTranslation UniformGridDilationInvariance

variable {m : ℝ}

/-- **`SimilarityCovariantField` for the owned energy field of a transported field.**  The
cells by `LabelBijectionProducer.preimage_labelCell_labelEquiv`, the owner set and area by the
two lemmas of `Corrector/OwnedFieldLabelTransport` (the owner is `labelOwner`), and the weight
because the owner label is equivariant (`labelOwner_labelEquiv`) and the energy coefficient
scales by `s²` (`pairCoeff_labelEquiv`). -/
theorem similarityCovariantField_ownedEnergyField
    {Ψ : ∀ p : Env × Grid, Vertex p.1.val → Plane} (hΨ : SimilarityTransportedField Ψ) :
    SimilarityCovariantField (ownedEnergyField actualReRooting m Ψ) := by
  intro s u hs p
  have h := LabelBijectionProducer.isSimilarityRelabel_similarityRelabel s u hs p.1
  have hgrid : (markedSimilarity s u hs p).2 = dilate s hs (translate u p.2) := rfl
  refine ⟨LabelBijectionProducer.labelEquiv (LabelBijectionProducer.similarityRelabel s u hs p.1),
    LabelBijectionProducer.preimage_labelCell_labelEquiv h, fun q => ?_, fun q => ?_, fun q => ?_⟩
  · have hown := labelOwner_labelEquiv (hs := hs) m p (markedSimilarity s u hs p) h hgrid q
    have hco := pairCoeff_labelEquiv h (hΨ s u hs p _ h) (hΨ s u hs p _ h) q
    have key : ∀ (o o' : Option SquareIndex) (τ : SquareIndex → SquareIndex), o' = o.map τ →
        ∀ {x y : ℝ}, x = s ^ 2 * y →
          o'.elim 0 (fun _ => ENNReal.ofReal x)
            = ENNReal.ofReal (s ^ 2) * o.elim 0 (fun _ => ENNReal.ofReal y) := by
      intro o o' τ ho x y hxy
      subst ho
      cases o with
      | none => simp
      | some a =>
        show ENNReal.ofReal x = ENNReal.ofReal (s ^ 2) * ENNReal.ofReal y
        rw [hxy, ENNReal.ofReal_mul (sq_nonneg s)]
    exact key _ _ _ hown hco
  · exact preimage_ownerSet_labelEquiv (hs := hs) (ownedEnergyField actualReRooting m Ψ)
      (fun _ _ => rfl) p (markedSimilarity s u hs p) h hgrid q
  · exact ownerArea_labelEquiv (hs := hs) (ownedEnergyField actualReRooting m Ψ)
      (fun _ _ => rfl) p (markedSimilarity s u hs p) h hgrid q

/-- **Redistribution for the owned energy field on `Env × Grid` from `s:eq:MTP`**, with an
almost-sure selected origin block. -/
theorem lintegral_rootEndpointDensity_eq_ownerBlockDensity_ownedEnergyField
    {Ψ : ∀ p : Env × Grid, Vertex p.1.val → Plane} (hΨ : SimilarityTransportedField Ψ)
    (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (hcoeff : ∀ q : ℕ × ℕ, Measurable fun ω : Env × Grid => pairCoeff ω.1 (Ψ ω) (Ψ ω) q)
    (hsel : ∀ᵐ ω ∂(ν.prod gridMeasure), ∃ k : ℤ, OriginSelected (decode ω.1) ω.2 m k) :
    (∫⁻ ω, (ownedEnergyField actualReRooting m Ψ).rootEndpointDensity ω ∂(ν.prod gridMeasure))
      = ∫⁻ ω, (ownedEnergyField actualReRooting m Ψ).ownerBlockDensity ω ∂(ν.prod gridMeasure) :=
  TransportAeGating.lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_of_massTransport_ae
    (ownedEnergyField actualReRooting m Ψ) ν hν
    (measurable_ownedEnergyField_weight actualReRooting m Ψ hcoeff
      (fun q c => measurableSet_labelOwner_eq_some m q c))
    (fun q c => measurableSet_labelOwner_eq_some m q c)
    (similarityCovariantField_ownedEnergyField hΨ) hsel

/-- **Redistribution for the positive part of the pairing coefficient of `(Ψ, Ψ)` on
`Env × Grid` from `s:eq:MTP`**, for any ownership datum with the canonical owner. -/
theorem lintegral_rootEndpointDensity_eq_ownerBlockDensity_posField
    {Ψ : ∀ p : Env × Grid, Vertex p.1.val → Plane} (hΨ : SimilarityTransportedField Ψ)
    (O : PairingOwnership actualReRooting m Ψ Ψ)
    (hO : ∀ (ω : Env × Grid) (q : ℕ × ℕ), O.owner ω q = labelOwner actualReRooting m ω q)
    (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (hcoeff : ∀ q : ℕ × ℕ, Measurable fun ω : Env × Grid => pairCoeff ω.1 (Ψ ω) (Ψ ω) q)
    (hsel : ∀ᵐ ω ∂(ν.prod gridMeasure), ∃ k : ℤ, OriginSelected (decode ω.1) ω.2 m k) :
    (∫⁻ ω, (posField O).rootEndpointDensity ω ∂(ν.prod gridMeasure))
      = ∫⁻ ω, (posField O).ownerBlockDensity ω ∂(ν.prod gridMeasure) := by
  have hwp : ∀ q : ℕ × ℕ, Measurable fun ω : Env × Grid => (posField O).weight ω q :=
    fun q => (hcoeff q).ennreal_ofReal
  have how : ∀ (q : ℕ × ℕ) (c : SquareIndex),
      MeasurableSet {ω : Env × Grid | (posField O).owner ω q = some c} := by
    intro q c
    have hEq : {ω : Env × Grid | (posField O).owner ω q = some c}
        = {ω : Env × Grid | labelOwner actualReRooting m ω q = some c} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [show (posField O).owner ω q = O.owner ω q from rfl, hO]
    rw [hEq]
    exact measurableSet_labelOwner_eq_some m q c
  exact TransportAeGating.lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_ae
    (posField O)
    (PairingTransportWeld.markedMassTransport_endpointSpreadTransport (posField O) ν hν hwp how
      (similarityCovariantField_posField O hO hΨ hΨ)) hsel

/-! ### Almost-sure measurability of the owner-block density

`OwnedEdgeField.ownerBlockDensity` is indexed by the selected origin block, a
`Classical.epsilon` over the origin chain.  On the event where exactly one origin square is
selected — which has full measure under `s:eq:MTP` and (FE) — the density is the unique
nonvanishing term of a countable sum over the candidate levels, each of which is measurable. -/

/-- The block density read at a fixed candidate origin level `k`. -/
noncomputable def blockDensityAt (Q : OwnedEdgeField actualReRooting m) (k : ℤ)
    (ω : Env × Grid) : ℝ≥0∞ :=
  (∑' p : ℕ × ℕ, {p : ℕ × ℕ | Q.owner ω p = some (originIndex k)}.indicator (Q.weight ω) p) /
    (2 * ENNReal.ofReal (side ω.2 k ^ 2))

theorem measurable_blockDensityAt (Q : OwnedEdgeField actualReRooting m)
    (hweight : ∀ q : ℕ × ℕ, Measurable fun ω : Env × Grid => Q.weight ω q)
    (howner : ∀ (q : ℕ × ℕ) (c : SquareIndex),
      MeasurableSet {ω : Env × Grid | Q.owner ω q = some c}) (k : ℤ) :
    Measurable (blockDensityAt Q k) := by
  have hnum : Measurable fun ω : Env × Grid =>
      ∑' p : ℕ × ℕ, {p : ℕ × ℕ | Q.owner ω p = some (originIndex k)}.indicator (Q.weight ω) p := by
    refine Measurable.ennreal_tsum fun p => ?_
    have hEq : (fun ω : Env × Grid =>
          {p : ℕ × ℕ | Q.owner ω p = some (originIndex k)}.indicator (Q.weight ω) p)
        = {ω : Env × Grid | Q.owner ω p = some (originIndex k)}.indicator
            (fun ω : Env × Grid => Q.weight ω p) := by
      funext ω
      by_cases h : Q.owner ω p = some (originIndex k)
      · rw [Set.indicator_of_mem (show p ∈ {p : ℕ × ℕ | Q.owner ω p = some (originIndex k)} from h),
          Set.indicator_of_mem (show ω ∈ {ω : Env × Grid | Q.owner ω p = some (originIndex k)} from h)]
      · rw [Set.indicator_of_notMem
          (show p ∉ {p : ℕ × ℕ | Q.owner ω p = some (originIndex k)} from h),
          Set.indicator_of_notMem
          (show ω ∉ {ω : Env × Grid | Q.owner ω p = some (originIndex k)} from h)]
    rw [hEq]
    exact (hweight p).indicator (howner p (originIndex k))
  have hden : Measurable fun ω : Env × Grid => (2 * ENNReal.ofReal (side ω.2 k ^ 2))⁻¹ := by
    have h1 : Measurable fun ω : Env × Grid => side ω.2 k :=
      (MeasurableEndpointTransport.measurable_gridSide k).comp measurable_snd
    exact ((ENNReal.measurable_ofReal.comp (h1.pow_const 2)).const_mul 2).inv
  have hEq : blockDensityAt Q k = fun ω : Env × Grid =>
      (∑' p : ℕ × ℕ, {p : ℕ × ℕ | Q.owner ω p = some (originIndex k)}.indicator (Q.weight ω) p) *
        (2 * ENNReal.ofReal (side ω.2 k ^ 2))⁻¹ := by
    funext ω
    unfold blockDensityAt
    rw [div_eq_mul_inv]
  rw [hEq]
  exact hnum.mul hden

/-- At a configuration whose selected origin level is `k`, the owner-block density is the block
density at `k`. -/
theorem ownerBlockDensity_eq_blockDensityAt (Q : OwnedEdgeField actualReRooting m)
    (ω : Env × Grid) {k : ℤ} (hk : blockLevel (decode ω.1) ω.2 m = k) :
    Q.ownerBlockDensity ω = blockDensityAt Q k ω := by
  unfold OwnedEdgeField.ownerBlockDensity OwnedEdgeField.ownedByOriginBlock blockDensityAt
  rw [actualReRooting_blockSideAt]
  show (∑' p : ℕ × ℕ,
      {p : ℕ × ℕ | Q.owner ω p = some (originIndex (blockLevel (decode ω.1) ω.2 m))}.indicator
        (Q.weight ω) p) / (2 * ENNReal.ofReal (side ω.2 (blockLevel (decode ω.1) ω.2 m) ^ 2)) = _
  rw [hk]

/-- Where exactly one origin square is selected, the owner-block density is the countable sum
over the candidate levels of the indicator of that level's selection event times the block
density at that level. -/
theorem ownerBlockDensity_eq_tsum_indicator (Q : OwnedEdgeField actualReRooting m)
    (ω : Env × Grid) (huniq : ∃! k : ℤ, OriginSelected (decode ω.1) ω.2 m k) :
    Q.ownerBlockDensity ω
      = ∑' k : ℤ, {ω : Env × Grid | OriginSelected (decode ω.1) ω.2 m k}.indicator
          (blockDensityAt Q k) ω := by
  obtain ⟨k₀, hk₀, huniq'⟩ := huniq
  have hlevel : blockLevel (decode ω.1) ω.2 m = k₀ :=
    huniq' _ (originSelected_blockLevel ⟨k₀, hk₀⟩)
  have hsingle : (∑' k : ℤ, {ω : Env × Grid | OriginSelected (decode ω.1) ω.2 m k}.indicator
        (blockDensityAt Q k) ω)
      = {ω : Env × Grid | OriginSelected (decode ω.1) ω.2 m k₀}.indicator
          (blockDensityAt Q k₀) ω := by
    refine tsum_eq_single (f := fun k : ℤ =>
      {ω : Env × Grid | OriginSelected (decode ω.1) ω.2 m k}.indicator (blockDensityAt Q k) ω)
      k₀ fun k hk => ?_
    show {ω : Env × Grid | OriginSelected (decode ω.1) ω.2 m k}.indicator (blockDensityAt Q k) ω
      = 0
    exact Set.indicator_of_notMem
      (show ω ∉ {ω : Env × Grid | OriginSelected (decode ω.1) ω.2 m k} from
        fun h => hk (huniq' k h)) (blockDensityAt Q k)
  rw [hsingle, Set.indicator_of_mem
    (show ω ∈ {ω : Env × Grid | OriginSelected (decode ω.1) ω.2 m k₀} from hk₀)]
  exact ownerBlockDensity_eq_blockDensityAt Q ω hlevel

/-- **The owner-block density is almost surely measurable**, on any law under which the
selected origin block is almost surely unique. -/
theorem aemeasurable_ownerBlockDensity (Q : OwnedEdgeField actualReRooting m)
    (hweight : ∀ q : ℕ × ℕ, Measurable fun ω : Env × Grid => Q.weight ω q)
    (howner : ∀ (q : ℕ × ℕ) (c : SquareIndex),
      MeasurableSet {ω : Env × Grid | Q.owner ω q = some c})
    {μ : Measure (Env × Grid)}
    (huniq : ∀ᵐ ω ∂μ, ∃! k : ℤ, OriginSelected (decode ω.1) ω.2 m k) :
    AEMeasurable Q.ownerBlockDensity μ := by
  have hmeas : Measurable fun ω : Env × Grid =>
      ∑' k : ℤ, {ω : Env × Grid | OriginSelected (decode ω.1) ω.2 m k}.indicator
        (blockDensityAt Q k) ω :=
    Measurable.ennreal_tsum fun k => (measurable_blockDensityAt Q hweight howner k).indicator
      (MeasurableSelectedAtIndex.measurableSet_originSelected_of_index m k)
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [huniq] with ω hω
  exact (ownerBlockDensity_eq_tsum_indicator Q ω hω).symm

/-- **The selected origin block is almost surely unique** at every positive parameter, on the
marked law: existence and strict monotonicity of `κ` along the origin chain both hold on the
good set of `Spatial/GoodMarkedSpace`. -/
theorem ae_existsUnique_originSelected (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω : Env × Grid ∂(ν.prod gridMeasure),
      ∃! k : ℤ, OriginSelected (decode ω.1) ω.2 r k := by
  have hgood : ∀ᵐ e ∂ν, e ∈ GoodMarkedSpace.goodSet :=
    GoodMarkedSpace.ae_mem_goodSet ν hν hFE.ne
  have hcov : ∀ᵐ e ∂ν, (0 : Plane) ∉ uncoveredSet (decode e) :=
    ReflectedGMS.ae_zero_notMem_uncoveredSet ν hν
  filter_upwards [ae_marked_of_ae_env ν hgood, ae_marked_of_ae_env ν hcov] with ω hω hωcov
  have hreg := GoodMarkedSpace.originChainRegularOn_goodMarked
  have hmono : StrictMono fun k : ℤ => blockIndex (decode ω.1) ω.2 (originIndex k) :=
    hreg.strictMono ((⟨ω.1, hω⟩ : GoodMarkedSpace.goodSet), ω.2)
  obtain ⟨k, hk⟩ := hreg.exists_originSelected'
    (ω := ((⟨ω.1, hω⟩ : GoodMarkedSpace.goodSet), ω.2)) hωcov hr
  exact ⟨k, hk, fun l hl => originSelected_unique hmono hl hk⟩

end Marked

end ReflectedGMS.StageEnergyRedistributionField
