/-
# The Liggett–Schonmann–Stacey theorem on the planar carrier

Theorem 0.0 of Liggett, Schonmann and Stacey, *Domination by product measures*, Ann. Probab.
25 (1997), read at dimension `2`, dependence range `2` and product density `7/8` on the planar
carrier `ℤ × ℤ`. This proves the dense domination hypothesis `DenseSevenEighths p` at some
density `p < 1`, so the thin domination statements that assume it hold with no remaining
hypothesis.

The transfer runs along the coordinate identification `fieldEquivPlanar` between fields on
`ℤ × ℤ` and fields on `Site 2`. The dependence range and the one-site bound pass forward; an
increasing planar event pulls back to an increasing lattice event; and the planar product field
of density `ρ` is the image of Bernoulli site percolation of density `ρ`.

## Main results

* `LatticeProb.Percolation.LSS.bernoulliFieldPlanar_eq_map`: the planar product field is the
  image of site percolation on `Site 2`.
* `LatticeProb.Percolation.LSS.exists_denseSevenEighths`: `DenseSevenEighths p` for some `p < 1`.
* `LatticeProb.Percolation.LSS.exists_consumerThin`: the thin domination bound by the product
  field of density `1/8`, in the consumer vocabulary, with no remaining hypothesis.
-/

import LatticeProb.Prob.Percolation.LSS
import LatticeProb.Prob.Percolation.LSSThinRotorMatch

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb.Percolation.LSS

open LatticeProb

/-- The Bernoulli law of density `p` on `Bool` is the bit law `bitLaw p`. -/
theorem bernoulli_eq_bitLaw (p : ℝ≥0) (hp : p ≤ 1) :
    LatticeProb.Percolation.bernoulli p hp = bitLaw (p : ℝ) := by
  refine Measure.ext_iff_singleton.mpr fun b => ?_
  rw [LatticeProb.Percolation.bernoulli,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
  cases b
  · change ((1 - p : ℝ≥0) : ℝ≥0∞) = bitLaw (p : ℝ) {false}
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_sub hp, NNReal.coe_one]
    simp [bitLaw]
  · change ((p : ℝ≥0) : ℝ≥0∞) = bitLaw (p : ℝ) {true}
    simp [bitLaw]

/-- The planar product field of density `p` is the image of Bernoulli site percolation of
density `p` on `Site 2` under the coordinate identification. -/
theorem bernoulliFieldPlanar_eq_map (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliFieldPlanar p hp = (sitePercolation 2 (p : ℝ)).map fieldEquivPlanar.invFun := by
  have hfun : (fieldEquivPlanar.invFun : (Site 2 → Bool) → PlanarCarrier → Bool) =
      MeasurableEquiv.piCongrLeft (fun _ : PlanarCarrier => Bool) planarSiteEquiv.symm := by
    funext η q
    conv_rhs => rw [← planarSiteEquiv.symm_apply_apply q]
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  rw [hfun, sitePercolation, ← bernoulli_eq_bitLaw p hp, bernoulliFieldPlanar, bitProduct]
  exact (Measure.infinitePi_map_piCongrLeft
    (fun _ : PlanarCarrier => LatticeProb.Percolation.bernoulli p hp) planarSiteEquiv.symm).symm

/-- **The dense domination hypothesis holds.** Theorem 0.0 of Liggett, Schonmann and Stacey at
`d = 2`, `k = 2` and `ρ = 7/8` gives a density `p < 1` such that every probability `2`-dependent
planar field whose one-site probabilities are at least `p` dominates the planar product field of
density `7/8` on measurable increasing events. -/
theorem exists_denseSevenEighths : ∃ p : ℝ, p < 1 ∧ DenseSevenEighths p := by
  obtain ⟨p, hp1, hdom⟩ :=
    xlse_lss_general 2 2 (by norm_num) (7 / 8) (by norm_num) (by norm_num)
  refine ⟨p, hp1, fun ν hν hKD hsite C hC hinc => ?_⟩
  have hKD2 : KDependent 2 (ν.map fieldEquivPlanar.toFun) :=
    kDependentPlanar_map_fieldEquivPlanar 2 hKD
  have hsite2 : ∀ s : Site 2,
      ENNReal.ofReal p ≤ (ν.map fieldEquivPlanar.toFun) {ω | ω s = true} := by
    intro s
    rw [fieldEquivPlanar_oneSite]
    exact hsite (ofSite2 s)
  have hA : MeasurableSet (fieldEquivPlanar.invFun ⁻¹' C) := measurable_ofSite2Field hC
  have hincA : IsIncreasingEvent (fieldEquivPlanar.invFun ⁻¹' C) := by
    intro η η' hη hle
    exact hinc (fieldEquivPlanar.invFun η) (fieldEquivPlanar.invFun η') hη
      fun q hq => hle (toSite2 q) hq
  have hpre : fieldEquivPlanar.toFun ⁻¹' (fieldEquivPlanar.invFun ⁻¹' C) = C := by
    ext ω
    simp only [Set.mem_preimage]
    rw [fieldEquivPlanar.left_inv ω]
  have h78 : ((7 / 8 : ℝ≥0) : ℝ) = 7 / 8 := by norm_num
  calc bernoulliFieldPlanar (7 / 8) seven_eighths_le_one C
      = (sitePercolation 2 (7 / 8)).map fieldEquivPlanar.invFun C := by
        rw [bernoulliFieldPlanar_eq_map, h78]
    _ = sitePercolation 2 (7 / 8) (fieldEquivPlanar.invFun ⁻¹' C) :=
        Measure.map_apply measurable_ofSite2Field hC
    _ ≤ (ν.map fieldEquivPlanar.toFun) (fieldEquivPlanar.invFun ⁻¹' C) :=
        hdom _ inferInstance hKD2 hsite2 _ hA hincA
    _ = ν C := by rw [Measure.map_apply measurable_toSite2Field hA, hpre]

/-- **The thin domination bound on the planar carrier.** There is `ε > 0` such that every
probability `2`-dependent planar field whose one-site probabilities are at most `2ε` is dominated
on measurable increasing events by the planar product field of density `1/8`. -/
theorem exists_thinPlanar :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → KDependentPlanar 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A →
          μ A ≤ bernoulliFieldPlanar (1 / 8) one_eighth_le_one A :=
  let ⟨_, hp, hdense⟩ := exists_denseSevenEighths
  thinLSS_bridge hp hdense

/-- **The thin domination bound in the consumer vocabulary.** The statement of
`exists_thinPlanar` with the dependence predicate, the increasing events and the product field
of density `1/8` read in the vocabulary of the consumer statement. -/
theorem exists_consumerThin :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → consumerKDependent 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → consumerIsIncreasing A →
          μ A ≤ consumerBernoulliField (1 / 8) one_eighth_le_one A :=
  let ⟨_, hp, hdense⟩ := exists_denseSevenEighths
  exists_consumerThin_of_dense hp hdense

end LatticeProb.Percolation.LSS
