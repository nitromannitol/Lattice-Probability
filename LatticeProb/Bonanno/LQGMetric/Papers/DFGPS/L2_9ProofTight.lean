/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_9ProofTight at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_9ProofCont
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofF

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.9, second conjunct: tightness on `W̄` (T:909–925)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`), proof of Lemma 2.9, T:909–925:
by Lemma 2.8 and the tightness criterion (2.8) the restrictions to each square `S ∈ 𝒮` are
tight, which gives (2.9): with probability `≥ 1 − ζ`, `D(z,w;W̄) ≤ ζ` for `|z − w| ≤ δ` with
`z, w` in a common square (we use the internal metrics `D(·,·;S) ≥ D(·,·;W̄)`); for `z, w` in
different squares the point `u ∈ S ∩ S'` (`exists_mem_inter_closedSq_near`) and the triangle
inequality give `D(z,w;W̄) ≤ 2ζ`; the tightness criterion (`LFPP.isTightMeasureSet_of_modulus`)
concludes. The converse direction of (2.8) for one square (tight ⇒ uniform modulus with high
probability) is `exists_modulus_of_isCompact` (L2_8ProofTight).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

/-- **(2.8) for one square, from Lemma 2.8**: with probability `≥ 1 − η` (uniformly in
`ε ∈ (0,1)`), `𝔞_ε⁻¹ D_h^ε(z,w;S) ≤ ζ` for all `z, w ∈ S` with `|z − w| ≤ δ`. -/
theorem sq_modulus (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {a : ℂ} {s : ℝ}
    (hs : 0 < s) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusBddCont h P) {ζ η : ℝ} (hζ : 0 < ζ) (hη : 0 < η) :
    ∃ δ > (0 : ℝ), ∀ ε ∈ Ioo (0 : ℝ) 1, P {ω | ¬ ∀ z ∈ closedSq a s, ∀ w ∈ closedSq a s,
      ‖w - z‖ ≤ δ → (aEpsDF (xiGamma γ) ε)⁻¹ *
        (lfppDOn (xiGamma γ) (heatMollify ε (h ω)) (closedSq a s) z w).toReal ≤ ζ} ≤
      ENNReal.ofReal η := by
  obtain ⟨-, hT, -⟩ := h28 γ hγ hγ2 a s hs P h hh
  haveI : CompactSpace (closedSq a s) := isCompact_iff_compactSpace.1 (isCompact_closedSq a hs.le)
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hT
  obtain ⟨C, hC, hCm⟩ := hT (ENNReal.ofReal η) (by simpa using hη)
  obtain ⟨δ, hδ, hmod⟩ := exists_modulus_of_isCompact hC hζ
  refine ⟨δ, hδ, fun ε hε => ?_⟩
  have hc := hh.ae_tendstoLocallyUniformly_heatMollify ε hε.1.ne'
  have hμ := hCm _ ⟨ε, hε, rfl⟩
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_lfppSqC hh.1 (hc.mono fun ω hω => hω.2) hs)
    hC.isClosed.isOpen_compl.measurableSet] at hμ
  refine le_trans (measure_mono_ae ?_) hμ
  filter_upwards [hc] with ω hω hbad hFC
  refine hbad fun z hz w hw hzw => ?_
  have := hmod _ hFC (⟨z, hz⟩, ⟨z, hz⟩) (⟨z, hz⟩, ⟨w, hw⟩) (by
    rw [Prod.dist_eq, dist_self, Subtype.dist_eq, dist_eq_norm, norm_sub_rev]
    exact max_le hδ.le hzw)
  rw [lfppSqC_apply_of_continuous hω.2 hs, lfppSqC_apply_of_continuous hω.2 hs] at this
  simp only at this
  rw [lfppDOn_self (convex_closedSq a s) hz, ENNReal.toReal_zero, mul_zero, zero_sub,
    abs_neg] at this
  exact (le_abs_self _).trans this

/-- separation of the squares of a finite family: close points lie in intersecting squares -/
theorem exists_sep_finset (𝒮 : Finset (Set ℂ)) (h𝒮 : ∀ S ∈ 𝒮, ∃ a s, 0 < s ∧ S = closedSq a s) :
    ∃ δ > (0 : ℝ), ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, ∀ x ∈ S, ∀ y ∈ T, ‖y - x‖ < δ → (S ∩ T).Nonempty := by
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ∩ T = ∅ →
      ∀ x ∈ S, ∀ y ∈ T, δ ≤ dist x y := by
    refine (eventually_all_finset 𝒮).2 fun S hS => (eventually_all_finset 𝒮).2 fun T hT => ?_
    obtain ⟨a, s, hs, rfl⟩ := h𝒮 S hS
    obtain ⟨b, t, ht, rfl⟩ := h𝒮 T hT
    obtain ⟨δ, hδ, hsep⟩ := exists_sep_of_isCompact (isCompact_closedSq a hs.le)
      (isCompact_closedSq b ht.le)
    filter_upwards [Ioo_mem_nhdsGT hδ] with δ' hδ' he x hx y hy
    exact hδ'.2.le.trans (hsep he x hx y hy)
  obtain ⟨δ, hδS, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨δ, hδ0, fun S hS T hT x hx y hy hxy => ?_⟩
  by_contra hc
  have := hδS S hS T hT (not_nonempty_iff_eq_empty.1 hc) x hx y hy
  rw [dist_eq_norm, norm_sub_rev] at this
  linarith

theorem isCompact_biUnion_closedSq (𝒮 : Finset (Set ℂ))
    (h𝒮 : ∀ S ∈ 𝒮, ∃ a s, 0 < s ∧ S = closedSq a s) : IsCompact (⋃ S ∈ 𝒮, S) :=
  𝒮.isCompact_biUnion fun S hS => by
    obtain ⟨a, s, hs, rfl⟩ := h𝒮 S hS
    exact isCompact_closedSq a hs.le

end LQGMetric.DFGPS
