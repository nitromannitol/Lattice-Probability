import Mathlib
import LatticeProb.Prob.PairingSymmetricSwap
import LatticeProb.Prob.LawFieldPairingContinuous

/-!
# A symmetric reversibility pairing at rational times makes the space-time measure swap invariant

For a law field `P : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))` and a locally finite measure `μ` on `ℂ`, the
space-time measure at time `s` is `m_s = μ ⊗ₘ evalLawKernel P s`, `m_s(dz, dw) = μ(dz) P_z(X_s ∈ dw)`.
For Lipschitz compactly supported `f, g` the difference of the two sides of the pairing,
`s ↦ ∫ f(z) E_{P_z}[g(X_s)] dμ(z) - ∫ g(z) E_{P_z}[f(X_s)] dμ(z)`, is continuous in `s`: it is the
reversibility pairing of `LawFieldPairingContinuous` at the finite measure `ψ μ` for a continuous
compactly supported cutoff `ψ` equal to `1` on `tsupport f ∪ tsupport g`. So the symmetry of the pairing
at the times `q ∈ ℚ≥0`, which are dense in `ℝ≥0`, gives it at every time, and then the countable form of
`PairingSymmetricSwap` gives the swap invariance of `m_s` for every `s`.

* `reversibilityPairing_cutoffWeightedMeasure`: the reversibility pairing at the finite measure
  `c ψ μ` (density `c ψ` against `μ`), for a cutoff `0 ≤ ψ` equal to `1` on `tsupport f ∪ tsupport g` and
  `c ≥ 0`, is `c (∫ f(z) E_{P_z}[g(X_s)] dμ(z) - ∫ g(z) E_{P_z}[f(X_s)] dμ(z))`.
* `exists_countable_compProd_evalLawKernel_swap_of_pairing_symm_rat`: a countable family of Lipschitz
  compactly supported `f, g` and the rational times suffice, uniformly in `μ` and `P`, for the swap
  invariance of `m_s` at every time `s`.
* `ae_compProd_evalLawKernel_swap_of_pairing_symm_rat`: the almost sure form for random `μ` and `P`.
-/

open MeasureTheory Filter Topology Set Metric ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-! ### The reversibility pairing at a cutoff-weighted measure -/

/-- For a continuous compactly supported `ψ`, the measure with density `c ψ` against a locally finite
`μ` is finite. -/
theorem isFiniteMeasure_withDensity_cutoff (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {ψ : ℂ → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (c : ℝ) :
    IsFiniteMeasure (μ.withDensity fun z => ENNReal.ofReal (c * ψ z)) := by
  have hcψ : HasCompactSupport fun z => c * ψ z := hψc.mul_left (f := fun _ => c)
  exact isFiniteMeasure_withDensity_ofReal
    ((continuous_const.mul hψ).integrable_of_hasCompactSupport hcψ).hasFiniteIntegral

/-- The finite measure `c ψ μ` with density `c ψ` against a locally finite `μ`, for a continuous compactly
supported cutoff `ψ`. -/
noncomputable def cutoffWeightedMeasure (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {ψ : ℂ → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (c : ℝ) : FiniteMeasure ℂ :=
  ⟨μ.withDensity fun z => ENNReal.ofReal (c * ψ z), isFiniteMeasure_withDensity_cutoff μ hψ hψc c⟩

theorem coe_cutoffWeightedMeasure (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {ψ : ℂ → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (c : ℝ) :
    ((cutoffWeightedMeasure μ hψ hψc c : FiniteMeasure ℂ) : Measure ℂ) =
      μ.withDensity fun z => ENNReal.ofReal (c * ψ z) :=
  rfl

/-- If `0 ≤ ψ`, `ψ = 1` on `tsupport a` and `c ≥ 0`, then
`∫ a(z) u(z) ψ(z) d(c ψ μ)(z) = c ∫ a(z) u(z) dμ(z)`. -/
theorem integral_mul_cutoff_withDensity (μ : Measure ℂ) {a ψ : ℂ → ℝ} (u : ℂ → ℝ)
    (hψm : Measurable ψ) (hψ0 : ∀ z, 0 ≤ ψ z) (hψ1 : EqOn ψ 1 (tsupport a)) {c : ℝ} (hc : 0 ≤ c) :
    ∫ z, a z * u z * ψ z ∂(μ.withDensity fun z => ENNReal.ofReal (c * ψ z)) =
      c * ∫ z, a z * u z ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul (hψm.const_mul c).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg hc (hψ0 z))]
  by_cases hz : z ∈ tsupport a
  · rw [hψ1 hz, Pi.one_apply]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hz]
    ring

/-- **The reversibility pairing at a cutoff-weighted measure.** For a continuous compactly supported
cutoff `0 ≤ ψ` with `ψ = 1` on `tsupport f ∪ tsupport g` and `c ≥ 0`, the reversibility pairing
`∫ f(z) E_{P_z}[g(X_s)] ψ(z) dν(z) - ∫ g(z) E_{P_z}[f(X_s)] ψ(z) dν(z)` of
`continuous_reversibilityPairing` at `ν = c ψ μ` equals
`c (∫ f(z) E_{P_z}[g(X_s)] dμ(z) - ∫ g(z) E_{P_z}[f(X_s)] dμ(z))`. -/
theorem reversibilityPairing_cutoffWeightedMeasure (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (P : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))) (s : ℝ≥0) {f g ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z) (hψ1 : EqOn ψ 1 (tsupport f ∪ tsupport g))
    {c : ℝ} (hc : 0 ≤ c) :
    (∫ z, f z * (∫ X, g (X s) ∂(P z : Measure C(ℝ≥0, ℂ))) * ψ z
        ∂((cutoffWeightedMeasure μ hψ hψc c : FiniteMeasure ℂ) : Measure ℂ))
      - ∫ z, g z * (∫ X, f (X s) ∂(P z : Measure C(ℝ≥0, ℂ))) * ψ z
          ∂((cutoffWeightedMeasure μ hψ hψc c : FiniteMeasure ℂ) : Measure ℂ) =
      c * ((∫ z, f z * (∫ X, g (X s) ∂(P z : Measure C(ℝ≥0, ℂ))) ∂μ)
        - ∫ z, g z * (∫ X, f (X s) ∂(P z : Measure C(ℝ≥0, ℂ))) ∂μ) := by
  rw [coe_cutoffWeightedMeasure,
    integral_mul_cutoff_withDensity μ _ hψ.measurable hψ0 (hψ1.mono subset_union_left) hc,
    integral_mul_cutoff_withDensity μ _ hψ.measurable hψ0 (hψ1.mono subset_union_right) hc, mul_sub]

/-! ### Continuity of the pairing in time -/

/-- For Lipschitz compactly supported `f, g`, the time map
`s ↦ ∫ f(z) E_{P_z}[g(X_s)] dμ(z) - ∫ g(z) E_{P_z}[f(X_s)] dμ(z)` is continuous. -/
theorem continuous_integral_lawField_pairing_sub {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (P : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))) {f g : ℂ → ℝ} {Kf Kg : ℝ≥0}
    (hfl : LipschitzWith Kf f) (hfc : HasCompactSupport f) (hgl : LipschitzWith Kg g)
    (hgc : HasCompactSupport g) :
    Continuous fun s : ℝ≥0 =>
      (∫ z, f z * (∫ X, g (X s) ∂(P z : Measure C(ℝ≥0, ℂ))) ∂μ)
        - ∫ z, g z * (∫ X, f (X s) ∂(P z : Measure C(ℝ≥0, ℂ))) ∂μ := by
  obtain ⟨ψ, hψ1, -, hψc, hψI⟩ := exists_continuous_one_zero_of_isCompact
    (hfc.isCompact.union hgc.isCompact) isClosed_empty (disjoint_empty _)
  have hfb : ∃ C, ∀ z, |f z| ≤ C := by
    obtain ⟨C, hC⟩ := hfl.continuous.bounded_above_of_compact_support hfc
    exact ⟨C, fun z => by simpa [Real.norm_eq_abs] using hC z⟩
  have hgb : ∃ C, ∀ z, |g z| ≤ C := by
    obtain ⟨C, hC⟩ := hgl.continuous.bounded_above_of_compact_support hgc
    exact ⟨C, fun z => by simpa [Real.norm_eq_abs] using hC z⟩
  have hq : Continuous fun s : ℝ≥0 =>
      ((cutoffWeightedMeasure μ ψ.continuous hψc 1, P, s) :
        FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  refine ((continuous_reversibilityPairing hfb hfl hgb hgl ψ.continuous hψc).comp hq).congr
    fun s => ?_
  exact (reversibilityPairing_cutoffWeightedMeasure μ P s ψ.continuous hψc (fun z => (hψI z).1)
    hψ1 zero_le_one).trans (one_mul _)

/-! ### Rational times -/

private theorem toNNRat_cast_coe_real (q : ℚ) (hq : 0 ≤ q) :
    (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = (q : ℝ) := by
  have hn : (0 : ℝ) ≤ (q.num : ℝ) := by exact_mod_cast Rat.num_nonneg.2 hq
  rw [NNRat.cast_def]
  simp [Rat.toNNRat, hq]
  rw [Rat.cast_def, abs_of_nonneg hn]

/-- The nonnegative rationals are dense in `ℝ≥0`. -/
theorem dense_range_nnratCast_nnreal : Dense (range ((↑) : ℚ≥0 → ℝ≥0)) := by
  refine dense_of_exists_between fun s t h => ?_
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show (s : ℝ) < (t : ℝ) from NNReal.coe_lt_coe.2 h)
  have hq : (0 : ℚ) ≤ q := by
    have : (0 : ℝ) ≤ (s : ℝ) := s.2
    exact_mod_cast (le_trans this h1.le)
  refine ⟨(q.toNNRat : ℝ≥0), ⟨q.toNNRat, rfl⟩, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, toNNRat_cast_coe_real q hq]
    exact h1
  · rw [← NNReal.coe_lt_coe, toNNRat_cast_coe_real q hq]
    exact h2

/-- **The symmetric pairing at rational times gives swap invariance at all times.** There is a countable
family `𝓕` of Lipschitz compactly supported functions such that, for every locally finite `μ` and law
field `P`, if `∫ f(z) E_{P_z}[g(X_q)] dμ(z) = ∫ g(z) E_{P_z}[f(X_q)] dμ(z)` for `f, g ∈ 𝓕` and
`q ∈ ℚ≥0`, then `m_s = μ ⊗ₘ evalLawKernel P s` equals its image under `(z, w) ↦ (w, z)` for every
`s ∈ ℝ≥0`. -/
theorem exists_countable_compProd_evalLawKernel_swap_of_pairing_symm_rat :
    ∃ 𝓕 : Set (ℂ → ℝ), 𝓕.Countable ∧
      (∀ f ∈ 𝓕, (∃ K, LipschitzWith K f) ∧ HasCompactSupport f) ∧
      ∀ (μ : Measure ℂ), IsLocallyFiniteMeasure μ → ∀ P : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)),
        (∀ f ∈ 𝓕, ∀ g ∈ 𝓕, ∀ q : ℚ≥0,
          ∫ z, f z * (∫ X, g (X (q : ℝ≥0)) ∂(P z : Measure C(ℝ≥0, ℂ))) ∂μ =
            ∫ z, g z * (∫ X, f (X (q : ℝ≥0)) ∂(P z : Measure C(ℝ≥0, ℂ))) ∂μ) →
        ∀ s : ℝ≥0, (μ ⊗ₘ evalLawKernel P s).map Prod.swap = μ ⊗ₘ evalLawKernel P s := by
  obtain ⟨𝓕, hcount, h𝓕, hswap⟩ := exists_countable_compProd_evalLawKernel_swap_of_pairing_symm
  refine ⟨𝓕, hcount, h𝓕, fun μ hμ P h s => hswap μ hμ P s fun f hf g hg => ?_⟩
  obtain ⟨⟨Kf, hKf⟩, hfc⟩ := h𝓕 f hf
  obtain ⟨⟨Kg, hKg⟩, hgc⟩ := h𝓕 g hg
  have hext := Continuous.ext_on dense_range_nnratCast_nnreal
    (continuous_integral_lawField_pairing_sub (μ := μ) P hKf hfc hKg hgc)
    (continuous_const : Continuous fun _ : ℝ≥0 => (0 : ℝ)) (by
      rintro _ ⟨q, rfl⟩
      exact sub_eq_zero.2 (h f hf g hg q))
  exact sub_eq_zero.1 (congrFun hext s)

/-- A countable family of Lipschitz compactly supported test functions for which the symmetry of the
pairing at rational times gives the swap invariance of every space-time measure at every time. -/
noncomputable def pairingTestFamily : Set (ℂ → ℝ) :=
  exists_countable_compProd_evalLawKernel_swap_of_pairing_symm_rat.choose

theorem pairingTestFamily_countable : pairingTestFamily.Countable :=
  exists_countable_compProd_evalLawKernel_swap_of_pairing_symm_rat.choose_spec.1

theorem lipschitz_hasCompactSupport_of_mem_pairingTestFamily {f : ℂ → ℝ}
    (hf : f ∈ pairingTestFamily) : (∃ K, LipschitzWith K f) ∧ HasCompactSupport f :=
  exists_countable_compProd_evalLawKernel_swap_of_pairing_symm_rat.choose_spec.2.1 f hf

/-- The symmetry of the pairing for `f, g ∈ pairingTestFamily` at rational times makes
`m_s = μ ⊗ₘ evalLawKernel P s` swap invariant for every `s`. -/
theorem compProd_evalLawKernel_swap_of_pairingTestFamily (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (P : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)))
    (h : ∀ f ∈ pairingTestFamily, ∀ g ∈ pairingTestFamily, ∀ q : ℚ≥0,
      ∫ z, f z * (∫ X, g (X (q : ℝ≥0)) ∂(P z : Measure C(ℝ≥0, ℂ))) ∂μ =
        ∫ z, g z * (∫ X, f (X (q : ℝ≥0)) ∂(P z : Measure C(ℝ≥0, ℂ))) ∂μ) (s : ℝ≥0) :
    (μ ⊗ₘ evalLawKernel P s).map Prod.swap = μ ⊗ₘ evalLawKernel P s :=
  exists_countable_compProd_evalLawKernel_swap_of_pairing_symm_rat.choose_spec.2.2 μ inferInstance
    P h s

/-- **The almost sure form.** Let `μ ω` be locally finite measures and `P ω` law fields indexed by a
measure space `(Ω, P₀)`. If for all `f, g ∈ pairingTestFamily` and `q ∈ ℚ≥0` the pairing is
symmetric for `P₀`-almost every `ω`, then for `P₀`-almost every `ω` the space-time measure
`μ ω ⊗ₘ evalLawKernel (P ω) s` is swap invariant for every `s ∈ ℝ≥0`. No measurability in `ω` is
needed: the family of conditions is countable. -/
theorem ae_compProd_evalLawKernel_swap_of_pairing_symm_rat {Ω : Type*} [MeasurableSpace Ω]
    {P₀ : Measure Ω} (μ : Ω → Measure ℂ) (hμ : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    (P : Ω → C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)))
    (h : ∀ f ∈ pairingTestFamily, ∀ g ∈ pairingTestFamily, ∀ q : ℚ≥0, ∀ᵐ ω ∂P₀,
      ∫ z, f z * (∫ X, g (X (q : ℝ≥0)) ∂(P ω z : Measure C(ℝ≥0, ℂ))) ∂(μ ω) =
        ∫ z, g z * (∫ X, f (X (q : ℝ≥0)) ∂(P ω z : Measure C(ℝ≥0, ℂ))) ∂(μ ω)) :
    ∀ᵐ ω ∂P₀, ∀ s : ℝ≥0,
      (μ ω ⊗ₘ evalLawKernel (P ω) s).map Prod.swap = μ ω ⊗ₘ evalLawKernel (P ω) s := by
  have : Countable pairingTestFamily := pairingTestFamily_countable.to_subtype
  have hall : ∀ᵐ ω ∂P₀, ∀ f : pairingTestFamily, ∀ g : pairingTestFamily, ∀ q : ℚ≥0,
      ∫ z, f.1 z * (∫ X, g.1 (X (q : ℝ≥0)) ∂(P ω z : Measure C(ℝ≥0, ℂ))) ∂(μ ω) =
        ∫ z, g.1 z * (∫ X, f.1 (X (q : ℝ≥0)) ∂(P ω z : Measure C(ℝ≥0, ℂ))) ∂(μ ω) :=
    ae_all_iff.2 fun f => ae_all_iff.2 fun g => ae_all_iff.2 fun q => h f.1 f.2 g.1 g.2 q
  filter_upwards [hall] with ω hω
  have := hμ ω
  exact compProd_evalLawKernel_swap_of_pairingTestFamily (μ ω) (P ω)
    (fun f hf g hg q => hω ⟨f, hf⟩ ⟨g, hg⟩ q)

end LatticeProb
