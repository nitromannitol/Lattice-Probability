/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W5Chi at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Hat

/-!
# W5 (part 2): the density of the killed occupation measure

Preparation for W5(i), reversed side, of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1). The blueprint
identifies the density of the killed occupation measure of `X + c` (`X = dpath σ (-μ) b`, killed at
`T_c`) with `C · χ_c(z)`, `C = occDens σ μ 0`, via
`ν^X(· - c) - ν^X(·)` and the hitting probabilities of W3. The two ingredients proved here:

* `occDens_neg_drift`: the occupation density of `X` is the reflected one of `Y`,
  `occDens σ (-μ) x = occDens σ μ (-x)` (symmetry of the Gaussian density);
* `chiKill_toReal_mul`: for `z > 0`, `z ≠ c`, `c > 0`,
  `χ_c(z) · C = occDens σ μ (c - z) - occDens σ μ (-z)`,
  i.e. the density `occDens σ μ (c - z)` of `ν^X(· - c)` at `z` is `C χ_c(z)` plus the density
  `occDens σ μ (-z)` of `ν^X` at `z`.

Proof of the second item (blueprint sketch, W5(i)): for `z > 0`, `z ≠ c`,
`{z + Y > 0 forever, z + Y hits c at a positive time} = {Y hits c - z} \ {Y hits -z}`
(intermediate value theorem), and the hitting probabilities are `1` for positive levels
(`ae_exists_eq_level`) and `occDens σ μ y / C` for negative ones (`prob_hit_neg`, W3). The
blueprint's route through the factorization `P(τ_{-z}) = P(τ_{c-z}) P(τ_{-c})` is not needed: the
difference form above gives the case `z > c` directly (own simplification).

Sources: Revuz–Yor, *Continuous Martingales and Brownian Motion*, VII §3 (Prop. 3.2 and the
scale-function computation of hitting probabilities); D. Williams (1974).
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- **The kernel `χ_c` in terms of occupation densities.** -/
theorem chiKill_toReal_mul (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) {c z : ℝ} (hc : 0 < c)
    (hz : 0 < z) (hzc : z ≠ c) :
    (chiKill b P σ μ c z).toReal * occDens σ μ 0 = occDens σ μ (c - z) - occDens σ μ (-z) := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  set A := {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = c - z} with hAdef
  set B := {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = -z} with hBdef
  have hBm : MeasurableSet B := measurableSet_exists_dpath_eq hb σ μ (-z)
  have hE : {ω | (∀ t, 0 < z + dpath σ μ b ω t) ∧ ∃ t, 0 < t ∧ z + dpath σ μ b ω t = c}
      = A \ B := by
    ext ω
    have hw := continuous_dpath hb σ μ ω
    have hw0 := dpath_zero hb σ μ ω
    simp only [hAdef, hBdef, mem_setOf_eq, mem_diff]
    constructor
    · rintro ⟨h1, t, -, ht⟩
      exact ⟨⟨t, by linarith⟩, fun ⟨s, hs⟩ => by have := h1 s; linarith⟩
    · rintro ⟨⟨t, ht⟩, hB⟩
      refine ⟨fun s => ?_, t, ?_, by linarith⟩
      · have := lt_of_never_hit_neg hw hw0 (by linarith : -z < 0) hB s
        linarith
      · exact pos_iff_ne_zero.2 fun h0 => hzc (by rw [h0, hw0] at ht; linarith)
  obtain ⟨hC, hPB⟩ := prob_hit_neg hb hσ hμ (show -z < 0 by linarith)
  rw [chiKill, hE, ← measureReal_def]
  rcases lt_or_gt_of_ne hzc with hlt | hgt
  · -- `z < c`: the level `c - z > 0` is hit almost surely
    have hA : P Aᶜ = 0 := ae_iff.1 (ae_exists_eq_level hb hσ hμ (by linarith : 0 < c - z))
    have hset : A \ B = Bᶜ \ Aᶜ := by
      ext ω; simp only [mem_diff, mem_compl_iff, not_not]; tauto
    rw [hset, measureReal_def, measure_sdiff_null hA, ← measureReal_def,
      probReal_compl_eq_one_sub hBm, hPB, occDens_nonneg_const hσ hμ (c - z) (by linarith)]
    field_simp
  · -- `z > c`: hitting `-z` forces hitting `c - z`
    have hsub : B ⊆ A := by
      intro ω hω
      by_contra hA
      have hw := continuous_dpath hb σ μ ω
      have hw0 := dpath_zero hb σ μ ω
      have h1 := lt_of_never_hit_neg hw hw0 (by linarith : c - z < 0) hA
      obtain ⟨t, ht⟩ := hω
      have := h1 t
      linarith
    obtain ⟨-, hPA⟩ := prob_hit_neg hb hσ hμ (show c - z < 0 by linarith)
    rw [measureReal_sdiff hsub hBm, hPA, hPB]
    field_simp

end QuantumZipper.Williams
