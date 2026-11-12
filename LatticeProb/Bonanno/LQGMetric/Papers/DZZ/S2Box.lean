/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2Box at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ

/-!
# DZZ §2.2: Gaussian tail of the supremum of a field on a small box (task P2-DZZPRE, WP-112)

The step used repeatedly in Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`): proofs of
Lemma 2.6 (l. 556–567), Lemma 2.7 (l. 573–592, "Combined with Lemmas 2.1 and 2.3 this gives
(eq-boring-2)"), Lemma 2.8 (l. 616–621) and Lemma 2.9 (l. 628–633): a continuous centered Gaussian
field on a box `Q` of side `b` with `E(X_v − X_u)² ≤ L|u − v|` and `Var X_v ≤ σ²` has
`E sup_Q X ≤ C_F √(L b)` (DZZ Lemma 2.3, `SupTail.dzz_lemma23_continuous`, after rescaling) and
hence, by the Borell–TIS inequality (the supremum form of DZZ Lemma 2.1,
`SupTail.tail_iSup_abs_le_gaussian`), `P(sup_Q |X| ≥ x) ≤ 2 e^{M²/(2σ²)} e^{−x²/(4σ²)}` for
every `M ≥ C_F √(L b)`.

* `dzz_box_sup_abs_tail` — this statement.
* `exists_mem_subBox`, `subBox_subset` — the box `ferniqueBox x₀ s` is the union of the `m²`
  sub-boxes `subBox x₀ s m k l` of side `s/m` (DZZ's dyadic sub-squares, `eq-def-mathfrak-C`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DZZ

open SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Gaussian tail of `sup_Q |X|` on a box** (DZZ Lemmas 2.1 + 2.3, as used in the proofs of
Lemmas 2.6–2.9). -/
theorem dzz_box_sup_abs_tail {X : ℂ → Ω → ℝ} (hX : IsGaussianProcess X P)
    (h0 : ∀ v, ∫ ω, X v ω ∂P = 0) {y : ℂ} {b L σ : ℝ} (hb : 0 < b) (hL : 0 < L)
    (hc : ∀ ω, ContinuousOn (fun v => X v ω) (ferniqueBox y b))
    (hinc : ∀ u ∈ ferniqueBox y b, ∀ v ∈ ferniqueBox y b,
      ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ L * ‖u - v‖)
    (hvar : ∀ v ∈ ferniqueBox y b, Var[X v; P] ≤ σ ^ 2) {M : ℝ}
    (hM : ferniqueCF * Real.sqrt (L * b) ≤ M) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | x ≤ ⨆ v : ferniqueBox y b, |X v ω|} ≤
      2 * Real.exp (M ^ 2 / (2 * σ ^ 2)) * Real.exp (-x ^ 2 / (2 * (2 * σ ^ 2))) := by
  set B := ferniqueBox y b
  have : CompactSpace B := isCompact_iff_compactSpace.1 (isCompact_ferniqueBox y b)
  have : Nonempty B := ⟨⟨y, mem_ferniqueBox_self hb.le⟩⟩
  set XB : B → Ω → ℝ := fun v => X v
  have hXB : IsGaussianProcess XB P := hX.comp_right (fun v : B => (v : ℂ))
  have hLb : 0 < L * b := mul_pos hL hb
  set c : ℝ := (Real.sqrt (L * b))⁻¹ with hc_def
  have hsq : 0 < Real.sqrt (L * b) := Real.sqrt_pos.2 hLb
  have hc0 : 0 < c := inv_pos.2 hsq
  have hc2 : c ^ 2 * L = b⁻¹ := by
    rw [hc_def, inv_pow, Real.sq_sqrt hLb.le]; field_simp
  have hincG : ∀ (ε : ℝ), ε ^ 2 = 1 → ∀ u ∈ B, ∀ v ∈ B,
      ∫ ω, (ε * c * X v ω - ε * c * X u ω) ^ 2 ∂P ≤ ‖u - v‖ / b := by
    intro ε hε u hu v hv
    have e : (fun ω => (ε * c * X v ω - ε * c * X u ω) ^ 2) =
        fun ω => c ^ 2 * (X v ω - X u ω) ^ 2 := by
      funext ω; rw [← mul_sub, mul_pow, mul_pow, hε, one_mul]
    rw [e, integral_const_mul]
    calc c ^ 2 * ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ c ^ 2 * (L * ‖u - v‖) :=
          mul_le_mul_of_nonneg_left (hinc u hu v hv) (sq_nonneg c)
      _ = ‖u - v‖ / b := by rw [← mul_assoc, hc2]; ring
  have hsupG : ∀ (ε : ℝ), ε ^ 2 = 1 →
      Integrable (fun ω => ⨆ v : B, ε * c * X v ω) P ∧
        ∫ ω, (⨆ v : B, ε * c * X v ω) ∂P ≤ ferniqueCF := by
    intro ε hε
    refine dzz_lemma23_continuous hb ?_ (fun v _ => ?_) (hincG ε hε)
      (fun ω => continuousOn_const.mul (hc ω))
    · exact (hXB.smul fun _ => ε * c).congr fun v => Eventually.of_forall fun ω => rfl
    · rw [integral_const_mul, h0, mul_zero]
  have hsup_eq : ∀ (ε : ℝ) ω, (⨆ v : B, ε * X v ω) = c⁻¹ * ⨆ v : B, ε * c * X v ω := by
    intro ε ω
    rw [Real.mul_iSup_of_nonneg (inv_nonneg.2 hc0.le)]
    congr 1; funext v; field_simp
  have hYsup : ∀ (ε : ℝ), ε ^ 2 = 1 → Integrable (fun ω => ⨆ v : B, ε * X v ω) P ∧
      ∫ ω, (⨆ v : B, ε * X v ω) ∂P ≤ M := by
    intro ε hε
    obtain ⟨h1, h2⟩ := hsupG ε hε
    simp_rw [hsup_eq ε]
    refine ⟨h1.const_mul _, ?_⟩
    rw [integral_const_mul]
    refine (mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hc0.le)).trans ?_
    rw [hc_def, inv_inv, mul_comm]
    exact hM
  obtain ⟨hi1, hM1⟩ := hYsup 1 (by norm_num)
  obtain ⟨hi2, hM2⟩ := hYsup (-1) (by norm_num)
  simp only [one_mul, neg_one_mul] at hi1 hM1 hi2 hM2
  exact tail_iSup_abs_le_gaussian hXB (fun v => h0 v)
    (fun ω => continuousOn_iff_continuous_domRestrict.1 (hc ω)) hi1 hi2 hM1 hM2
    (fun v => hvar v v.2) hx

end DZZ
end LQGMetric
