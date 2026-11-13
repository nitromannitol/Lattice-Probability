/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.GridCrossOrthogonalityPolarization at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.OwnedFieldPairingTransport
import LatticeProb.Bonanno.ReflectedGMS.Corrector.LabelBijectionProducer
import LatticeProb.Bonanno.ReflectedGMS.Corrector.HarmonicGridIndependence
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedRootedSpecificEnergyMeasurability

/-!
# Polarization toolkit for the cross orthogonality

Small analytic facts about the signed pairing density
`SpecificEnergyPolarization.rootedPairingDensity` that the passage from the stagewise cross
identities `⟪Φ¹, φ_m² − b⟫_* = 0` to the manuscript's `⟪g¹, g² − g₀⟫ = 0` needs, none of which
existed in the tree:

* `rootedSpecificPairingDensity_eq_rootedPairingDensity` — the two signed densities of the
  project (`HarmonicGridIndependence`, coordinatewise; `SpecificEnergyPolarization`, inner
  product) coincide.  Both routes to `hcopies` are therefore about one quantity.
* `rootedPairingDensity_sub_right`, `rootedPairingDensity_smul_left` — bilinearity in the second
  slot and homogeneity in the first; `rootedQuadDensity_smul` the quadratic scaling.
* `abs_rootedPairingDensity_le_scaled` — the weighted arithmetic–geometric bound
  `2|⟨θ, η⟩| ≤ t ρ_θ + t⁻¹ ρ_η`, `t > 0`, which is the Cauchy–Schwarz surrogate used to send the
  stage to infinity.
* `measurable_rootedPairingDensity_of_labels` — measurability of the rooted pairing density of
  two label-indexed fields, by polarization from
  `MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity`.
* `rootEndpointDensity_posField_le` / `negField_le` — off the boundary mask the endpoint density
  of either part of the signed coefficient is at most `ρ_Ψ(0) + ρ_H(0)`.  This is what makes the
  finiteness inputs `hpfin`/`hmfin` of the pairing transport follow from finite expected specific
  energies.
* `tendsto_integral_rootedPairingDensity_of_tendsto_zero` — **the limit lemma**: if
  `E ρ_θ < ∞` and `E ρ_{η_n} → 0` then `E⟨θ, η_n⟩ → 0`.

**This file proves no main theorem.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.GridCrossOrthogonalityPolarization

open Code StatementIngredients RootDensities SpecificEnergyPolarization
open MarkedBlockAveraging SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField
open OwnedFieldPairingTransport LabelBijectionProducer

/-! ### The two signed densities coincide -/

section Bridge

variable {V : Type*} [Countable V]

/-- The inner product on the plane in coordinates, in the shape of `pairingSum`. -/
theorem inner_eq_sum_coord (x y : Plane) :
    (inner ℝ x y : ℝ) = ∑ i : Fin 2, x i * y i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **The coordinatewise signed density is the inner-product signed density.** -/
theorem rootedSpecificPairingDensity_eq_rootedPairingDensity (F : IndexedCells V)
    (Φ Ψ : V → Plane) (z : Plane) :
    HarmonicGridIndependence.rootedSpecificPairingDensity F Φ Ψ z
      = rootedPairingDensity F Φ Ψ z := by
  cases hroot : rootAt F z with
  | none =>
      rw [HarmonicGridIndependence.rootedSpecificPairingDensity_of_eq_none F Φ Ψ hroot]
      simp [rootedPairingDensity, hroot]
  | some v =>
      rw [HarmonicGridIndependence.rootedSpecificPairingDensity_of_eq_some F Φ Ψ hroot]
      simp only [rootedPairingDensity, hroot, Option.elim]
      show HarmonicGridIndependence.pairingSum F Φ Ψ v / (2 * cellArea F v)
        = (2 * cellArea F v)⁻¹ * ∑' w : V, F.graph.c v w * inner ℝ (Φ w - Φ v) (Ψ w - Ψ v)
      rw [div_eq_inv_mul]
      congr 1
      refine tsum_congr fun w => ?_
      rw [inner_eq_sum_coord, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [PiLp.sub_apply]

end Bridge

/-! ### Bilinearity and scaling of the signed density -/

section Bilinear

variable {V : Type*} [Countable V] (F : IndexedCells V)

theorem pairingDensity_sub_right (hF : Geometry F) (Θ H₁ H₂ : V → Plane) (v : V) :
    pairingDensity F Θ (fun u => H₁ u - H₂ u) v
      = pairingDensity F Θ H₁ v - pairingDensity F Θ H₂ v := by
  unfold pairingDensity
  rw [← mul_sub, ← (summable_conductance_mul_inner F hF Θ H₁ v).tsum_sub
    (summable_conductance_mul_inner F hF Θ H₂ v)]
  congr 1
  refine tsum_congr fun w => ?_
  have h : (H₁ w - H₂ w) - (H₁ v - H₂ v) = (H₁ w - H₁ v) - (H₂ w - H₂ v) := by abel
  show F.graph.c v w * inner ℝ (Θ w - Θ v) ((H₁ w - H₂ w) - (H₁ v - H₂ v))
    = F.graph.c v w * inner ℝ (Θ w - Θ v) (H₁ w - H₁ v)
      - F.graph.c v w * inner ℝ (Θ w - Θ v) (H₂ w - H₂ v)
  rw [h, inner_sub_right, mul_sub]

theorem rootedPairingDensity_sub_right (hF : Geometry F) (Θ H₁ H₂ : V → Plane) (z : Plane) :
    rootedPairingDensity F Θ (fun u => H₁ u - H₂ u) z
      = rootedPairingDensity F Θ H₁ z - rootedPairingDensity F Θ H₂ z := by
  cases hroot : rootAt F z with
  | none => simp [rootedPairingDensity, hroot]
  | some v =>
      simp only [rootedPairingDensity, hroot, Option.elim]
      exact pairingDensity_sub_right F hF Θ H₁ H₂ v

theorem pairingDensity_smul_left (t : ℝ) (Θ H : V → Plane) (v : V) :
    pairingDensity F (fun u => t • Θ u) H v = t * pairingDensity F Θ H v := by
  have hterm : ∀ w : V, F.graph.c v w * inner ℝ (t • Θ w - t • Θ v) (H w - H v)
      = t * (F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v)) := by
    intro w
    rw [← smul_sub, real_inner_smul_left]
    ring
  show (2 * cellArea F v)⁻¹ * ∑' w : V, F.graph.c v w * inner ℝ (t • Θ w - t • Θ v) (H w - H v)
    = t * ((2 * cellArea F v)⁻¹ * ∑' w : V, F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v))
  rw [tsum_congr hterm, tsum_mul_left]
  ring

theorem rootedPairingDensity_smul_left (t : ℝ) (Θ H : V → Plane) (z : Plane) :
    rootedPairingDensity F (fun u => t • Θ u) H z = t * rootedPairingDensity F Θ H z := by
  cases hroot : rootAt F z with
  | none => simp [rootedPairingDensity, hroot]
  | some v =>
      simp only [rootedPairingDensity, hroot, Option.elim]
      exact pairingDensity_smul_left F t Θ H v

theorem quadDensity_smul (t : ℝ) (Θ : V → Plane) (v : V) :
    quadDensity F (fun u => t • Θ u) v = t ^ 2 * quadDensity F Θ v := by
  have hterm : ∀ w : V, F.graph.c v w * ‖t • Θ w - t • Θ v‖ ^ 2
      = t ^ 2 * (F.graph.c v w * ‖Θ w - Θ v‖ ^ 2) := by
    intro w
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  show (2 * cellArea F v)⁻¹ * ∑' w : V, F.graph.c v w * ‖t • Θ w - t • Θ v‖ ^ 2
    = t ^ 2 * ((2 * cellArea F v)⁻¹ * ∑' w : V, F.graph.c v w * ‖Θ w - Θ v‖ ^ 2)
  rw [tsum_congr hterm, tsum_mul_left]
  ring

theorem rootedQuadDensity_smul (t : ℝ) (Θ : V → Plane) (z : Plane) :
    rootedQuadDensity F (fun u => t • Θ u) z = t ^ 2 * rootedQuadDensity F Θ z := by
  cases hroot : rootAt F z with
  | none => simp [rootedQuadDensity, hroot]
  | some v =>
      simp only [rootedQuadDensity, hroot, Option.elim]
      exact quadDensity_smul F t Θ v

/-- **The weighted arithmetic–geometric bound** `2|⟨θ,η⟩| ≤ t ρ_θ + t⁻¹ ρ_η` for `t > 0`. -/
theorem abs_rootedPairingDensity_le_scaled (hF : Geometry F) {t : ℝ} (ht : 0 < t)
    (Θ H : V → Plane) (z : Plane) :
    |rootedPairingDensity F Θ H z|
      ≤ (t * rootedQuadDensity F Θ z + t⁻¹ * rootedQuadDensity F H z) / 2 := by
  have h := abs_rootedPairingDensity_le F hF (fun u => t • Θ u) H z
  rw [rootedPairingDensity_smul_left F t Θ H z, rootedQuadDensity_smul F t Θ z, abs_mul,
    abs_of_pos ht] at h
  have hkey : t * |rootedPairingDensity F Θ H z|
      ≤ t * ((t * rootedQuadDensity F Θ z + t⁻¹ * rootedQuadDensity F H z) / 2) := by
    have h1 : t * (t⁻¹ * rootedQuadDensity F H z) = rootedQuadDensity F H z := by
      rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
    have hrw : t * ((t * rootedQuadDensity F Θ z + t⁻¹ * rootedQuadDensity F H z) / 2)
        = (t ^ 2 * rootedQuadDensity F Θ z + rootedQuadDensity F H z) / 2 := by
      calc t * ((t * rootedQuadDensity F Θ z + t⁻¹ * rootedQuadDensity F H z) / 2)
          = (t * (t * rootedQuadDensity F Θ z) + t * (t⁻¹ * rootedQuadDensity F H z)) / 2 := by
            ring
        _ = (t ^ 2 * rootedQuadDensity F Θ z + rootedQuadDensity F H z) / 2 := by
            rw [h1]
            ring
    rw [hrw]
    exact h
  exact le_of_mul_le_mul_left hkey ht

end Bilinear

/-! ### Measurability of the rooted pairing density of label fields -/

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The rooted pairing density by polarization of the rooted specific-energy densities. -/
theorem rootedPairingDensity_eq_polarization {V : Type*} [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (Θ H : V → Plane) (z : Plane) :
    rootedPairingDensity F Θ H z
      = ((rootedSpecificEnergyDensity F (fun u => Θ u + H u) z).toReal
          - (rootedSpecificEnergyDensity F Θ z).toReal
          - (rootedSpecificEnergyDensity F H z).toReal) / 2 := by
  rw [toReal_rootedSpecificEnergyDensity_add F hF Θ H z]
  ring

/-- **The rooted pairing density of two label-indexed fields is measurable.** -/
theorem measurable_rootedPairingDensity_of_labels {E : Ω → Env} (hE : Measurable E)
    {LΘ LH : Ω → ℕ → Plane} (hΘ : ∀ n : ℕ, Measurable fun ω => LΘ ω n)
    (hH : ∀ n : ℕ, Measurable fun ω => LH ω n) :
    Measurable fun ω : Ω =>
      rootedPairingDensity (decode (E ω)) (fun v : Vertex (E ω).val => LΘ ω v.val)
        (fun v : Vertex (E ω).val => LH ω v.val) 0 := by
  have hEq : (fun ω : Ω =>
      rootedPairingDensity (decode (E ω)) (fun v : Vertex (E ω).val => LΘ ω v.val)
        (fun v : Vertex (E ω).val => LH ω v.val) 0)
      = fun ω : Ω =>
        ((rootedSpecificEnergyDensity (decode (E ω))
            (fun v : Vertex (E ω).val => LΘ ω v.val + LH ω v.val) 0).toReal
          - (rootedSpecificEnergyDensity (decode (E ω))
            (fun v : Vertex (E ω).val => LΘ ω v.val) 0).toReal
          - (rootedSpecificEnergyDensity (decode (E ω))
            (fun v : Vertex (E ω).val => LH ω v.val) 0).toReal) / 2 :=
    funext fun ω => rootedPairingDensity_eq_polarization (decode (E ω)) (decode_geometry (E ω))
      _ _ 0
  rw [hEq]
  have h1 := (MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity hE
    (Ψ := fun ω n => LΘ ω n + LH ω n) fun n => (hΘ n).add (hH n)).ennreal_toReal
  have h2 := (MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity hE
    (Ψ := LΘ) hΘ).ennreal_toReal
  have h3 := (MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity hE
    (Ψ := LH) hH).ennreal_toReal
  exact ((h1.sub h2).sub h3).div_const 2

end Measurability

/-! ### The endpoint density of either part of the signed coefficient -/

section Endpoint

variable {Ω : Type*} [MeasurableSpace Ω] {R : MarkedReRooting Ω} {m : ℝ}
  {Ψ H : ∀ ω : Ω, Vertex (R.env ω).val → Plane}

/-- Termwise: either sign of the pairing coefficient is dominated by the two energy terms. -/
theorem ofReal_pairCoeff_le (e : Env) (Φ Θ : Vertex e.val → Plane) (v w : Vertex e.val)
    (hsign : ∀ x : ℝ, (x = pairCoeff e Φ Θ (v.1, w.1)) ∨ (x = -pairCoeff e Φ Θ (v.1, w.1)) →
      x ≤ (decode e).graph.c v w * (‖Φ w - Φ v‖ ^ 2 + ‖Θ w - Θ v‖ ^ 2)) (x : ℝ)
    (hx : (x = pairCoeff e Φ Θ (v.1, w.1)) ∨ (x = -pairCoeff e Φ Θ (v.1, w.1))) :
    ENNReal.ofReal x
      ≤ ENNReal.ofReal ((decode e).graph.c v w) * ENNReal.ofReal (‖Φ w - Φ v‖ ^ 2)
        + ENNReal.ofReal ((decode e).graph.c v w) * ENNReal.ofReal (‖Θ w - Θ v‖ ^ 2) := by
  have hc := (decode e).graph.c_nonneg v w
  rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hc,
    ← ENNReal.ofReal_add (mul_nonneg hc (sq_nonneg _)) (mul_nonneg hc (sq_nonneg _))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← mul_add]
  exact hsign x hx

/-- The coefficient itself, or its negative, is at most `c (‖ΔΦ‖² + ‖ΔΘ‖²)`. -/
theorem pairCoeff_sign_le (e : Env) (Φ Θ : Vertex e.val → Plane) (v w : Vertex e.val) (x : ℝ)
    (hx : (x = pairCoeff e Φ Θ (v.1, w.1)) ∨ (x = -pairCoeff e Φ Θ (v.1, w.1))) :
    x ≤ (decode e).graph.c v w * (‖Φ w - Φ v‖ ^ 2 + ‖Θ w - Θ v‖ ^ 2) := by
  have hc := (decode e).graph.c_nonneg v w
  have hcs := abs_real_inner_le_norm (Φ w - Φ v) (Θ w - Θ v)
  have hamgm : ‖Φ w - Φ v‖ * ‖Θ w - Θ v‖ ≤ ‖Φ w - Φ v‖ ^ 2 + ‖Θ w - Θ v‖ ^ 2 := by
    nlinarith [sq_nonneg (‖Φ w - Φ v‖ - ‖Θ w - Θ v‖), norm_nonneg (Φ w - Φ v),
      norm_nonneg (Θ w - Θ v), mul_nonneg (norm_nonneg (Φ w - Φ v)) (norm_nonneg (Θ w - Θ v))]
  have habs : |inner ℝ (Φ w - Φ v) (Θ w - Θ v)| ≤ ‖Φ w - Φ v‖ ^ 2 + ‖Θ w - Θ v‖ ^ 2 :=
    hcs.trans hamgm
  have hval : pairCoeff e Φ Θ (v.1, w.1)
      = (decode e).graph.c v w * inner ℝ (Φ w - Φ v) (Θ w - Θ v) := pairCoeff_vertex e Φ Θ v w
  rcases hx with rfl | rfl
  · rw [hval]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans habs) hc
  · rw [hval, ← mul_neg]
    exact mul_le_mul_of_nonneg_left ((neg_le_abs _).trans habs) hc

/-- The endpoint density of an owned edge field whose weight is `ofReal` of a signed coefficient
of either sign, off the boundary mask, is at most `ρ_Ψ(0) + ρ_H(0)`. -/
theorem rootEndpointDensity_le_of_sign (Q : OwnedEdgeField R m) (ω : Ω)
    (hQ : ∀ p : ℕ × ℕ, (Q.weight ω p = ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (H ω) p))
      ∨ (Q.weight ω p = ENNReal.ofReal (-pairCoeff (R.env ω) (Ψ ω) (H ω) p)))
    (h0 : (0 : Plane) ∉ boundaryMask (decode (R.env ω))) :
    Q.rootEndpointDensity ω
      ≤ rootedSpecificEnergyDensity (decode (R.env ω)) (Ψ ω) 0
        + rootedSpecificEnergyDensity (decode (R.env ω)) (H ω) 0 := by
  have hF : Geometry (decode (R.env ω)) := decode_geometry (R.env ω)
  obtain ⟨v, hv, -⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode (R.env ω)) hF h0
  have horigin : originLabel (R.env ω) = some v.1 := by
    rw [originLabel_eq_map_rootAt (R.env ω) h0, hv]
    rfl
  have hden : Q.rootEndpointDensity ω
      = (∑' k : ℕ, Q.weight ω (v.1, k)) / (2 * volume (labelCell (R.env ω) v.1)) := by
    unfold OwnedEdgeField.rootEndpointDensity
    rw [horigin]
    rfl
  have hvol : volume (labelCell (R.env ω) v.1)
      = ENNReal.ofReal (cellArea (decode (R.env ω)) v) := by
    rw [labelCell_val]
    show volume ((decode (R.env ω)).cell v : Set Plane)
      = ENNReal.ofReal ((volume ((decode (R.env ω)).cell v : Set Plane)).toReal)
    rw [ENNReal.ofReal_toReal (cellVolume_pos_lt_top _ hF v).2.ne]
  have hΨ : rootedSpecificEnergyDensity (decode (R.env ω)) (Ψ ω) 0
      = specificEnergyDensity (decode (R.env ω)) (Ψ ω) v := by
    show (rootAt (decode (R.env ω)) 0).elim 0 _ = _
    rw [hv]
    rfl
  have hH : rootedSpecificEnergyDensity (decode (R.env ω)) (H ω) 0
      = specificEnergyDensity (decode (R.env ω)) (H ω) v := by
    show (rootAt (decode (R.env ω)) 0).elim 0 _ = _
    rw [hv]
    rfl
  have hzero : ∀ n : ℕ, ¬ ((R.env ω).val.1 n).isSome → Q.weight ω (v.1, n) = 0 := by
    intro n hn
    rcases hQ (v.1, n) with h | h
    · rw [h, pairCoeff_eq_zero_of_snd_absent (R.env ω) (Ψ ω) (H ω) v.1 hn, ENNReal.ofReal_zero]
    · rw [h, pairCoeff_eq_zero_of_snd_absent (R.env ω) (Ψ ω) (H ω) v.1 hn, neg_zero,
        ENNReal.ofReal_zero]
  have hnum : (∑' k : ℕ, Q.weight ω (v.1, k))
      = ∑' w : Vertex (R.env ω).val, Q.weight ω (v.1, w.1) :=
    (tsum_vertex_eq_tsum_nat (R.env ω) (fun k : ℕ => Q.weight ω (v.1, k)) hzero).symm
  have hterm : ∀ w : Vertex (R.env ω).val,
      Q.weight ω (v.1, w.1)
        ≤ ENNReal.ofReal ((decode (R.env ω)).graph.c v w) * ENNReal.ofReal (‖Ψ ω w - Ψ ω v‖ ^ 2)
          + ENNReal.ofReal ((decode (R.env ω)).graph.c v w)
            * ENNReal.ofReal (‖H ω w - H ω v‖ ^ 2) := by
    intro w
    rcases hQ (v.1, w.1) with h | h
    · rw [h]
      exact ofReal_pairCoeff_le (R.env ω) (Ψ ω) (H ω) v w
        (fun x hx => pairCoeff_sign_le (R.env ω) (Ψ ω) (H ω) v w x hx) _ (Or.inl rfl)
    · rw [h]
      exact ofReal_pairCoeff_le (R.env ω) (Ψ ω) (H ω) v w
        (fun x hx => pairCoeff_sign_le (R.env ω) (Ψ ω) (H ω) v w x hx) _ (Or.inr rfl)
  rw [hden, hnum, hvol, hΨ, hH]
  show (∑' w : Vertex (R.env ω).val, Q.weight ω (v.1, w.1))
      / (2 * ENNReal.ofReal (cellArea (decode (R.env ω)) v))
    ≤ (∑' w : Vertex (R.env ω).val, ENNReal.ofReal ((decode (R.env ω)).graph.c v w)
        * ENNReal.ofReal (‖Ψ ω w - Ψ ω v‖ ^ 2))
        / (2 * ENNReal.ofReal (cellArea (decode (R.env ω)) v))
      + (∑' w : Vertex (R.env ω).val, ENNReal.ofReal ((decode (R.env ω)).graph.c v w)
        * ENNReal.ofReal (‖H ω w - H ω v‖ ^ 2))
        / (2 * ENNReal.ofReal (cellArea (decode (R.env ω)) v))
  rw [← ENNReal.add_div, ← ENNReal.tsum_add]
  exact ENNReal.div_le_div_right (ENNReal.tsum_le_tsum hterm) _

/-- **Finiteness of the expected endpoint density of either part**, from the two finite
expected specific energies, the null boundary mask and the measurability of the two
densities. -/
theorem lintegral_rootEndpointDensity_ne_top_of_sign (Q : OwnedEdgeField R m) {μ : Measure Ω}
    (hQ : ∀ (ω : Ω) (p : ℕ × ℕ),
      (Q.weight ω p = ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (H ω) p))
        ∨ (Q.weight ω p = ENNReal.ofReal (-pairCoeff (R.env ω) (Ψ ω) (H ω) p)))
    (hbdry : ∀ᵐ ω ∂μ, (0 : Plane) ∉ boundaryMask (decode (R.env ω)))
    (hΨmeas : AEMeasurable (fun ω => rootedSpecificEnergyDensity (decode (R.env ω)) (Ψ ω) 0) μ)
    (hΨ : (∫⁻ ω, rootedSpecificEnergyDensity (decode (R.env ω)) (Ψ ω) 0 ∂μ) ≠ ∞)
    (hH : (∫⁻ ω, rootedSpecificEnergyDensity (decode (R.env ω)) (H ω) 0 ∂μ) ≠ ∞) :
    (∫⁻ ω, Q.rootEndpointDensity ω ∂μ) ≠ ∞ := by
  have hle : (∫⁻ ω, Q.rootEndpointDensity ω ∂μ)
      ≤ ∫⁻ ω, (rootedSpecificEnergyDensity (decode (R.env ω)) (Ψ ω) 0
          + rootedSpecificEnergyDensity (decode (R.env ω)) (H ω) 0) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hbdry] with ω h0
    exact rootEndpointDensity_le_of_sign Q ω (hQ ω) h0
  rw [lintegral_add_left' hΨmeas] at hle
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hΨ, hH⟩) hle

end Endpoint

/-! ### The limit lemma -/

section Limit

variable {Ω : Type*} [MeasurableSpace Ω] {Vtx : Ω → Type*} [∀ ω, Countable (Vtx ω)]

/-- **`E⟨θ, η_n⟩ → 0` when `E ρ_θ < ∞` and `E ρ_{η_n} → 0`.**  By the weighted bound
`2|⟨θ,η⟩| ≤ t ρ_θ + t⁻¹ ρ_η`: given `ε`, take `t` with `t · E ρ_θ ≤ ε`, then `n` large. -/
theorem tendsto_integral_rootedPairingDensity_of_tendsto_zero (μ : Measure Ω)
    (cells : ∀ ω, IndexedCells (Vtx ω)) (Θ : ∀ ω, Vtx ω → Plane)
    (Hs : ℕ → ∀ ω, Vtx ω → Plane) (root : Ω → Plane)
    (hcells : ∀ ω, Geometry (cells ω))
    (hΘmeas : AEMeasurable
      (fun ω => rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)) μ)
    (hHmeas : ∀ n : ℕ, AEMeasurable
      (fun ω => rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω)) μ)
    (hPmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => rootedPairingDensity (cells ω) (Θ ω) (Hs n ω) (root ω)) μ)
    (hΘ : (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω) ∂μ) ≠ ∞)
    (hH : Tendsto (fun n => ∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω) ∂μ)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, rootedPairingDensity (cells ω) (Θ ω) (Hs n ω) (root ω) ∂μ)
      atTop (𝓝 0) := by
  set A : ℝ := (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω) ∂μ).toReal with hA
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hintΘ : Integrable
      (fun ω => (rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hΘmeas hΘ
  have hintegralΘ : (∫ ω, (rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)).toReal ∂μ)
      = A :=
    integral_toReal hΘmeas (ae_lt_top' hΘmeas hΘ)
  have hBto : Tendsto (fun n =>
      (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω) ∂μ).toReal) atTop
      (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hH
    rw [ENNReal.toReal_zero] at this
    exact this
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  set t : ℝ := ε / 2 / (A + 1) with ht
  have htpos : 0 < t := div_pos hε2 (by linarith)
  have htA : t * A ≤ ε / 2 := by
    rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < A + 1)]
    nlinarith
  have hfin : ∀ᶠ n in atTop,
      (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω) ∂μ) < 1 :=
    hH.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1))
  have hsmall : ∀ᶠ n in atTop,
      (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω) ∂μ).toReal
        < t * (ε / 2) := by
    have := hBto.eventually (gt_mem_nhds (mul_pos htpos hε2))
    exact this
  filter_upwards [hfin, hsmall] with n hn hnsmall
  have hHn : (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω) ∂μ) ≠ ∞ :=
    hn.ne_top
  have hintH : Integrable
      (fun ω => (rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω)).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top (hHmeas n) hHn
  have hintegralH : (∫ ω, (rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω)).toReal ∂μ)
      = (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω) ∂μ).toReal :=
    integral_toReal (hHmeas n) (ae_lt_top' (hHmeas n) hHn)
  have hintP : Integrable (fun ω => rootedPairingDensity (cells ω) (Θ ω) (Hs n ω) (root ω)) μ :=
    integrable_rootedPairingDensity μ cells Θ (Hs n) root hcells hΘmeas (hHmeas n) (hPmeas n) hΘ
      hHn
  have hbound : Integrable (fun ω =>
      (t * (rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)).toReal
        + t⁻¹ * (rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω)).toReal) / 2) μ :=
    ((hintΘ.const_mul t).add (hintH.const_mul t⁻¹)).div_const 2
  have hpt : ∀ ω, ‖rootedPairingDensity (cells ω) (Θ ω) (Hs n ω) (root ω)‖
      ≤ (t * (rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)).toReal
        + t⁻¹ * (rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω)).toReal) / 2 := by
    intro ω
    rw [Real.norm_eq_abs, toReal_rootedSpecificEnergyDensity (cells ω) (hcells ω) (Θ ω) (root ω),
      toReal_rootedSpecificEnergyDensity (cells ω) (hcells ω) (Hs n ω) (root ω)]
    exact abs_rootedPairingDensity_le_scaled (cells ω) (hcells ω) htpos (Θ ω) (Hs n ω) (root ω)
  have h1 : ‖∫ ω, rootedPairingDensity (cells ω) (Θ ω) (Hs n ω) (root ω) ∂μ‖
      ≤ ∫ ω, (t * (rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)).toReal
        + t⁻¹ * (rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω)).toReal) / 2 ∂μ :=
    (norm_integral_le_integral_norm _).trans (integral_mono hintP.norm hbound hpt)
  have h2 : (∫ ω, (t * (rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)).toReal
        + t⁻¹ * (rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω)).toReal) / 2 ∂μ)
      = (t * A + t⁻¹ *
        (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω) ∂μ).toReal) / 2 := by
    rw [integral_div, integral_add (hintΘ.const_mul t) (hintH.const_mul t⁻¹), integral_const_mul,
      integral_const_mul, hintegralΘ, hintegralH]
  have h3 : t⁻¹ * (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω) ∂μ).toReal
      ≤ ε / 2 := by
    have hinv : 0 < t⁻¹ := inv_pos.2 htpos
    calc t⁻¹ * (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω) ∂μ).toReal
        ≤ t⁻¹ * (t * (ε / 2)) := mul_le_mul_of_nonneg_left hnsmall.le hinv.le
      _ = ε / 2 := by field_simp
  rw [Real.dist_eq, sub_zero]
  have hnorm : |∫ ω, rootedPairingDensity (cells ω) (Θ ω) (Hs n ω) (root ω) ∂μ|
      ≤ (ε / 2 + ε / 2) / 2 := by
    rw [← Real.norm_eq_abs]
    refine h1.trans ?_
    rw [h2]
    have : t * A + t⁻¹ *
        (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Hs n ω) (root ω) ∂μ).toReal
        ≤ ε / 2 + ε / 2 := add_le_add htA h3
    linarith
  linarith

end Limit

end ReflectedGMS.GridCrossOrthogonalityPolarization
