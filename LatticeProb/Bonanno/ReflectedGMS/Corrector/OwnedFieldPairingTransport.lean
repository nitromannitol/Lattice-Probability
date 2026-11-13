/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.OwnedFieldPairingTransport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SpecificEnergyPolarization
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MeasurableEndpointTransport
import LatticeProb.Bonanno.ReflectedGMS.Corrector.OwnedBlockDensityEquality

/-!
# Signed owner-field transport for the rooted pairing density

`Corrector/SpecificEnergyPolarization` reduces the manuscript's expected Pythagoras identity
(clause 4, `lintegral_rootedSpecificEnergyDensity_eq_add_of_integral_pairing_eq_zero`) to the
single probabilistic input

`∫ ω, rootedPairingDensity (decode (R.env ω)) (Ψ ω) (Θ ω - Ψ ω) 0 ∂μ = 0`.

`Corrector/SpecificEnergyRedistribution` proves the manuscript's redistribution lemma
`s:lem:redistribution` for an arbitrary `OwnedEdgeField`, and
`Corrector/MeasurableEndpointTransport` discharges its joint measurability and reduces its
covariance to label-level equivariance.  This module supplies the **bridge** between the two:

* `pairCoeffAt` / `pairCoeff` — the signed manuscript edge coefficient
  `c(H,H') ⟪Ψ(H') − Ψ(H), η(H') − η(H)⟫`, read on *ordered raw label pairs* (the index type of
  an `OwnedEdgeField`), extended by zero to absent labels;
* `posField` / `negField` — the two `OwnedEdgeField`s whose weights are `ofReal (±q_e)`, i.e.
  literally the positive and negative parts of the signed coefficient.  The only extra datum
  they need is the ownership assignment, packaged as `PairingOwnership`: a symmetric,
  selected-square-valued owner label whose absence forces the coefficient to vanish;
* `toReal_rootEndpointDensity_sub_eq_rootedPairingDensity` — the **adapter**: off the cell
  boundary mask the signed endpoint density of the pair `(posField, negField)` is exactly the
  rooted pairing density of `SpecificEnergyPolarization`.  The two normalizations agree: the
  endpoint density divides by `2 · volume (labelCell …)` and `pairingDensity` divides by
  `2 · cellArea`, and these are the same number;
* `integral_rootedPairingDensity_eq_zero` — the resulting transport statement, and
  `integral_rootedPairingDensity_sub_eq_zero` its instance in the exact shape of the
  hypothesis `horth` of the polarization clause.

Its inputs are exactly the inputs of the checked redistribution: the mass-transport identity
for the two single kernels `(posField O).endpointSpreadTransport` and
`(negField O).endpointSpreadTransport` (the one genuinely probabilistic producer, *not* proved
here; on the actual marked space `Env × Grid` it follows from the manuscript's own `s:eq:MTP`
through `MarkedMassTransportProducer.markedMassTransport_of_massTransport`, and it replaces the
whole-class predicate `SpecificEnergyRedistribution.MarkedMassTransport`, which is strictly
stronger than `s:eq:MTP` and is not derivable from it), the structural measurability of the
environment/grid/coefficient/ownership observables, the label-level re-rooting equivariance
`PairingReRooting`, the pathwise origin-selection hypothesis, finiteness of the two expected
endpoint densities, the deterministic blockwise orthogonality (this is the manuscript's
separate deterministic half, proved blockwise in `Corrector/NestedEnergyProjections` and
delivered as the signed edge sum `NestedProjectionProducers.tsum_vectorGradProd_nested_eq_zero`
together with its summability `NestedProjectionProducers.summable_vectorGradProd`), and the
almost-sure absence of the origin from the cell boundary mask (produced by
`Spatial/NullBoundaryRoots`).  No finite total energy of the environment is used: the specific
energy stays an expected root density throughout.

The blockwise orthogonality enters here in its **real-valued** form — the signed coefficient is
summable on the owner block of the origin and sums to zero there — and
`Corrector/OwnedBlockDensityEquality` performs the `ENNReal`/real transfer to the equality of
the two owner-block densities that the redistribution actually consumes.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.OwnedFieldPairingTransport

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging
open SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField
open MeasurableEndpointTransport OwnedBlockDensityEquality

/-! ### Summing a label-indexed family over the actual vertices

The index type of an `OwnedEdgeField` is the raw label type `ℕ`, while every density of
`Corrector/SpecificEnergyPolarization` sums over the vertex type `Vertex e.val`, which is the
subtype of *present* labels.  A family supported on present labels has the same sum either
way. -/

/-- A label-indexed family vanishing at absent labels has the same sum over the raw labels and
over the actual vertices. -/
theorem tsum_vertex_eq_tsum_nat {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [T2Space M]
    (e : Env) (g : ℕ → M) (hg : ∀ n : ℕ, ¬ (e.val.1 n).isSome → g n = 0) :
    ∑' w : Vertex e.val, g w.1 = ∑' n : ℕ, g n := by
  classical
  have hsupp : Function.support g ⊆ {n : ℕ | (e.val.1 n).isSome} := by
    intro n hn
    by_contra hc
    exact hn (hg n hc)
  exact tsum_subtype_eq_of_support_subset hsupp

/-! ### The signed pairing coefficient on ordered raw label pairs -/

/-- The manuscript's signed edge coefficient `c(H,H') ⟪Ψ(H') − Ψ(H), η(H') − η(H)⟫`, read on an
ordered pair of raw labels and extended by zero to absent labels. -/
noncomputable def pairCoeffAt (e : Env) (Ψ H : Vertex e.val → Plane) (a b : ℕ) : ℝ :=
  if ha : (e.val.1 a).isSome then
    if hb : (e.val.1 b).isSome then
      (decode e).graph.c ⟨a, ha⟩ ⟨b, hb⟩ *
        inner ℝ (Ψ ⟨b, hb⟩ - Ψ ⟨a, ha⟩) (H ⟨b, hb⟩ - H ⟨a, ha⟩)
    else 0
  else 0

/-- The same coefficient as a function of an ordered pair, the index type of an
`OwnedEdgeField`. -/
noncomputable def pairCoeff (e : Env) (Ψ H : Vertex e.val → Plane) (p : ℕ × ℕ) : ℝ :=
  pairCoeffAt e Ψ H p.1 p.2

theorem pairCoeffAt_of_isSome (e : Env) (Ψ H : Vertex e.val → Plane) {a b : ℕ}
    (ha : (e.val.1 a).isSome) (hb : (e.val.1 b).isSome) :
    pairCoeffAt e Ψ H a b
      = (decode e).graph.c ⟨a, ha⟩ ⟨b, hb⟩ *
        inner ℝ (Ψ ⟨b, hb⟩ - Ψ ⟨a, ha⟩) (H ⟨b, hb⟩ - H ⟨a, ha⟩) := by
  unfold pairCoeffAt
  rw [dif_pos ha, dif_pos hb]

theorem pairCoeffAt_of_not_isSome_left (e : Env) (Ψ H : Vertex e.val → Plane) {a : ℕ}
    (ha : ¬ (e.val.1 a).isSome) (b : ℕ) : pairCoeffAt e Ψ H a b = 0 := by
  unfold pairCoeffAt
  rw [dif_neg ha]

theorem pairCoeffAt_of_not_isSome_right (e : Env) (Ψ H : Vertex e.val → Plane) (a : ℕ) {b : ℕ}
    (hb : ¬ (e.val.1 b).isSome) : pairCoeffAt e Ψ H a b = 0 := by
  unfold pairCoeffAt
  by_cases ha : (e.val.1 a).isSome
  · rw [dif_pos ha, dif_neg hb]
  · rw [dif_neg ha]

/-- At a pair of actual vertices the coefficient is the manuscript expression. -/
theorem pairCoeffAt_vertex (e : Env) (Ψ H : Vertex e.val → Plane) (v w : Vertex e.val) :
    pairCoeffAt e Ψ H v.1 w.1
      = (decode e).graph.c v w * inner ℝ (Ψ w - Ψ v) (H w - H v) :=
  pairCoeffAt_of_isSome e Ψ H v.2 w.2

/-- **The coefficient lives on unoriented edges.** -/
theorem pairCoeffAt_symm (e : Env) (Ψ H : Vertex e.val → Plane) (a b : ℕ) :
    pairCoeffAt e Ψ H b a = pairCoeffAt e Ψ H a b := by
  by_cases ha : (e.val.1 a).isSome
  · by_cases hb : (e.val.1 b).isSome
    · rw [pairCoeffAt_of_isSome e Ψ H hb ha, pairCoeffAt_of_isSome e Ψ H ha hb,
        (decode e).graph.c_symm ⟨b, hb⟩ ⟨a, ha⟩]
      congr 1
      have h1 : Ψ ⟨a, ha⟩ - Ψ ⟨b, hb⟩ = -(Ψ ⟨b, hb⟩ - Ψ ⟨a, ha⟩) := by abel
      have h2 : H ⟨a, ha⟩ - H ⟨b, hb⟩ = -(H ⟨b, hb⟩ - H ⟨a, ha⟩) := by abel
      rw [h1, h2, inner_neg_neg]
    · rw [pairCoeffAt_of_not_isSome_left e Ψ H hb a,
        pairCoeffAt_of_not_isSome_right e Ψ H a hb]
  · rw [pairCoeffAt_of_not_isSome_right e Ψ H b ha,
      pairCoeffAt_of_not_isSome_left e Ψ H ha b]

theorem pairCoeff_symm (e : Env) (Ψ H : Vertex e.val → Plane) (p : ℕ × ℕ) :
    pairCoeff e Ψ H (p.2, p.1) = pairCoeff e Ψ H p :=
  pairCoeffAt_symm e Ψ H p.1 p.2

theorem pairCoeff_eq_zero_of_absent (e : Env) (Ψ H : Vertex e.val → Plane) {p : ℕ × ℕ}
    (h : ¬ (e.val.1 p.1).isSome) : pairCoeff e Ψ H p = 0 :=
  pairCoeffAt_of_not_isSome_left e Ψ H h p.2

theorem pairCoeff_vertex (e : Env) (Ψ H : Vertex e.val → Plane) (v w : Vertex e.val) :
    pairCoeff e Ψ H (v.1, w.1)
      = (decode e).graph.c v w * inner ℝ (Ψ w - Ψ v) (H w - H v) :=
  pairCoeffAt_vertex e Ψ H v w

theorem pairCoeff_eq_zero_of_snd_absent (e : Env) (Ψ H : Vertex e.val → Plane) (a : ℕ) {b : ℕ}
    (hb : ¬ (e.val.1 b).isSome) : pairCoeff e Ψ H (a, b) = 0 :=
  pairCoeffAt_of_not_isSome_right e Ψ H a hb

/-! ### The two owned edge fields -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The ownership datum of the signed pairing coefficient.**  An owner label for every
ordered pair of raw labels, symmetric, taking values in *selected* squares, and absent only
where the coefficient itself vanishes.  Nothing about any transport identity is assumed. -/
structure PairingOwnership (R : MarkedReRooting Ω) (m : ℝ)
    (Ψ H : ∀ ω : Ω, Vertex (R.env ω).val → Plane) where
  /-- The owner block `S_e` of an edge, as a selected dyadic square. -/
  owner : Ω → ℕ × ℕ → Option SquareIndex
  owner_symm : ∀ (ω : Ω) (p : ℕ × ℕ), owner ω (p.2, p.1) = owner ω p
  owner_selected : ∀ (ω : Ω) (p : ℕ × ℕ) (s : SquareIndex), owner ω p = some s →
    Selected (decode (R.env ω)) (R.grid ω) m s
  pairCoeff_eq_zero_of_owner_eq_none : ∀ (ω : Ω) (p : ℕ × ℕ), owner ω p = none →
    pairCoeff (R.env ω) (Ψ ω) (H ω) p = 0

variable {R : MarkedReRooting Ω} {m : ℝ} {Ψ H : ∀ ω : Ω, Vertex (R.env ω).val → Plane}

/-- The owned edge field carrying the **positive part** of the signed pairing coefficient:
`ENNReal.ofReal` truncates at zero, so `ofReal q_e` is exactly `q_e⁺`. -/
noncomputable def posField (O : PairingOwnership R m Ψ H) : OwnedEdgeField R m where
  weight ω p := ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (H ω) p)
  owner := O.owner
  weight_symm ω p := by rw [pairCoeff_symm]
  owner_symm := O.owner_symm
  weight_eq_zero_of_owner_eq_none ω p h := by
    rw [O.pairCoeff_eq_zero_of_owner_eq_none ω p h, ENNReal.ofReal_zero]
  weight_eq_zero_of_absent ω p h := by
    rw [pairCoeff_eq_zero_of_absent (R.env ω) (Ψ ω) (H ω) h, ENNReal.ofReal_zero]
  owner_selected := O.owner_selected

/-- The owned edge field carrying the **negative part** of the signed pairing coefficient. -/
noncomputable def negField (O : PairingOwnership R m Ψ H) : OwnedEdgeField R m where
  weight ω p := ENNReal.ofReal (-(pairCoeff (R.env ω) (Ψ ω) (H ω) p))
  owner := O.owner
  weight_symm ω p := by rw [pairCoeff_symm]
  owner_symm := O.owner_symm
  weight_eq_zero_of_owner_eq_none ω p h := by
    rw [O.pairCoeff_eq_zero_of_owner_eq_none ω p h, neg_zero, ENNReal.ofReal_zero]
  weight_eq_zero_of_absent ω p h := by
    rw [pairCoeff_eq_zero_of_absent (R.env ω) (Ψ ω) (H ω) h, neg_zero, ENNReal.ofReal_zero]
  owner_selected := O.owner_selected

theorem posField_weight (O : PairingOwnership R m Ψ H) (ω : Ω) (p : ℕ × ℕ) :
    (posField O).weight ω p = ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (H ω) p) := rfl

theorem negField_weight (O : PairingOwnership R m Ψ H) (ω : Ω) (p : ℕ × ℕ) :
    (negField O).weight ω p = ENNReal.ofReal (-(pairCoeff (R.env ω) (Ψ ω) (H ω) p)) := rfl

/-! ### The endpoint density of a real coefficient at the root -/

/-- The label cell of a vertex carries the vertex's cell area. -/
theorem toReal_volume_labelCell (e : Env) (v : Vertex e.val) :
    (volume (labelCell e v.1)).toReal = StatementIngredients.cellArea (decode e) v := by
  rw [labelCell_of_isSome e v.2]
  rfl

/-- **The endpoint density of a nonnegative-part weight.**  For an owned edge field whose
weight is `ofReal f` for a real coefficient `f`, the manuscript endpoint density at a root
label `v` is the positive part of the neighbour sum of `f`, normalized by `2 a_H`. -/
theorem toReal_rootEndpointDensity_of_originLabel (Q : OwnedEdgeField R m) (ω : Ω)
    (f : ℕ × ℕ → ℝ) (hQ : ∀ p : ℕ × ℕ, Q.weight ω p = ENNReal.ofReal (f p))
    (v : Vertex (R.env ω).val) (horigin : originLabel (R.env ω) = some v.1)
    (g : Vertex (R.env ω).val → ℝ)
    (hg : ∀ w : Vertex (R.env ω).val, f (v.1, w.1) = g w)
    (hg0 : ∀ n : ℕ, ¬ ((R.env ω).val.1 n).isSome → f (v.1, n) = 0)
    (hsum : Summable fun w : Vertex (R.env ω).val => max (g w) 0) :
    (Q.rootEndpointDensity ω).toReal
      = (∑' w : Vertex (R.env ω).val, max (g w) 0) /
        (2 * StatementIngredients.cellArea (decode (R.env ω)) v) := by
  have hden : Q.rootEndpointDensity ω
      = (∑' k : ℕ, Q.weight ω (v.1, k)) / (2 * volume (labelCell (R.env ω) v.1)) := by
    unfold OwnedEdgeField.rootEndpointDensity
    rw [horigin]
    rfl
  have hnum : (∑' k : ℕ, Q.weight ω (v.1, k))
      = ENNReal.ofReal (∑' w : Vertex (R.env ω).val, max (g w) 0) := by
    have h1 : (fun k : ℕ => Q.weight ω (v.1, k))
        = fun k : ℕ => ENNReal.ofReal (f (v.1, k)) := funext fun k => hQ (v.1, k)
    have h2 : ∀ n : ℕ, ¬ ((R.env ω).val.1 n).isSome →
        ENNReal.ofReal (f (v.1, n)) = 0 := by
      intro n hn
      rw [hg0 n hn, ENNReal.ofReal_zero]
    rw [h1, ← tsum_vertex_eq_tsum_nat (R.env ω) (fun k : ℕ => ENNReal.ofReal (f (v.1, k))) h2,
      ENNReal.ofReal_tsum_of_nonneg (fun w => le_max_right (g w) 0) hsum]
    exact tsum_congr fun w => by rw [hg w, ofReal_eq_ofReal_max]
  rw [hden, hnum, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (tsum_nonneg fun w => le_max_right (g w) 0),
    ENNReal.toReal_mul, toReal_volume_labelCell]
  norm_num

/-! ### The adapter: signed endpoint density is the rooted pairing density -/

/-- **The transport adapter.**  Off the cell boundary mask, the signed endpoint density of the
positive and negative parts of the pairing coefficient is exactly the rooted pairing density of
`Corrector/SpecificEnergyPolarization`.  The normalizations match: both divide by twice the
area of the root cell. -/
theorem toReal_rootEndpointDensity_sub_eq_rootedPairingDensity
    (O : PairingOwnership R m Ψ H) (ω : Ω)
    (h0 : (0 : Plane) ∉ RootDensities.boundaryMask (decode (R.env ω))) :
    ((posField O).rootEndpointDensity ω).toReal
        - ((negField O).rootEndpointDensity ω).toReal
      = SpecificEnergyPolarization.rootedPairingDensity
          (decode (R.env ω)) (Ψ ω) (H ω) 0 := by
  have hF : Geometry (decode (R.env ω)) := decode_geometry (R.env ω)
  obtain ⟨v, hv, -⟩ :=
    RootDensities.rootAt_eq_some_of_not_mem_boundaryMask (decode (R.env ω)) hF h0
  have horigin : originLabel (R.env ω) = some v.1 := by
    rw [originLabel_eq_map_rootAt (R.env ω) h0, hv]
    rfl
  have hpsum : Summable fun w : Vertex (R.env ω).val =>
      max ((decode (R.env ω)).graph.c v w * inner ℝ (Ψ ω w - Ψ ω v) (H ω w - H ω v)) 0 :=
    SpecificEnergyPolarization.summable_of_conductance_support (decode (R.env ω)) hF v
      (fun w hw => by rw [hw, zero_mul, max_self])
  have hmsum : Summable fun w : Vertex (R.env ω).val =>
      max (-((decode (R.env ω)).graph.c v w * inner ℝ (Ψ ω w - Ψ ω v) (H ω w - H ω v))) 0 :=
    SpecificEnergyPolarization.summable_of_conductance_support (decode (R.env ω)) hF v
      (fun w hw => by rw [hw, zero_mul, neg_zero, max_self])
  have hpos := toReal_rootEndpointDensity_of_originLabel (posField O) ω
    (pairCoeff (R.env ω) (Ψ ω) (H ω)) (posField_weight O ω) v horigin
    (fun w => (decode (R.env ω)).graph.c v w * inner ℝ (Ψ ω w - Ψ ω v) (H ω w - H ω v))
    (fun w => pairCoeff_vertex (R.env ω) (Ψ ω) (H ω) v w)
    (fun n hn => pairCoeff_eq_zero_of_snd_absent (R.env ω) (Ψ ω) (H ω) v.1 hn) hpsum
  have hneg := toReal_rootEndpointDensity_of_originLabel (negField O) ω
    (fun p => -(pairCoeff (R.env ω) (Ψ ω) (H ω) p)) (negField_weight O ω) v horigin
    (fun w => -((decode (R.env ω)).graph.c v w * inner ℝ (Ψ ω w - Ψ ω v) (H ω w - H ω v)))
    (fun w => by rw [pairCoeff_vertex (R.env ω) (Ψ ω) (H ω) v w])
    (fun n hn => by
      rw [pairCoeff_eq_zero_of_snd_absent (R.env ω) (Ψ ω) (H ω) v.1 hn, neg_zero]) hmsum
  have hroot : SpecificEnergyPolarization.rootedPairingDensity
      (decode (R.env ω)) (Ψ ω) (H ω) 0
      = SpecificEnergyPolarization.pairingDensity (decode (R.env ω)) (Ψ ω) (H ω) v := by
    unfold SpecificEnergyPolarization.rootedPairingDensity
    rw [hv]
    rfl
  rw [hpos, hneg, div_sub_div_same, ← Summable.tsum_sub hpsum hmsum, hroot,
    SpecificEnergyPolarization.pairingDensity, div_eq_inv_mul]
  exact congrArg _ (tsum_congr fun w => max_zero_sub_max_neg_zero_eq_self _)

/-! ### The label-level re-rooting equivariance of the pairing coefficient -/

/-! ### The transported identity -/

end ReflectedGMS.OwnedFieldPairingTransport
