/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28U1Link at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28Up2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamMean

/-!
# DDDF Prop 28 Part 1 Step 1 for the family: the finest link (task P2-DDDF28U)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1416 and 1440–1446: the last term of the chaining
`C λ_n^{-1} 2^{-n} e^{ξ sup_{[0,1]²} φ_{0,n}}` is controlled by the maximum of the field. Here, as
in Step 2 (`upper_small`, l. 1440–1446), with high probability `sup_{[0,1]²} |φ_δ| ≤ M` where
`e^{ξM} ≤ C_L λ_δ δ^{β−1}` (`link_small`; DDDF take the expectation, with
`E e^{ξ sup φ_{0,n}} ≤ 2^{2ξn} e^{C√n}`; here the sup tail `phiVer_sup_tail_unif` and (5.54),
(6.98) are used instead, which also covers `β > 1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace LQGMetric
namespace DDDF
namespace S6P28U

open WhiteNoise Blueprint SupTail S6P28

variable {Ω : Type} [MeasurableSpace Ω]

/-- **the finest link** (DDDF l. 1416, 1440–1446): with probability `≥ 1 − ε`,
`sup_{[0,1]²} |φ_δ| ≤ M` with `e^{ξM} ≤ C_L λ_δ δ^{β−1}`, uniformly in `δ = 2^{-(N+r)}`. -/
theorem link_small {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {ξ q : ℝ}
    (hξ : 0 < ξ) (h554 : S6Eq5_54 ξ q W P) (h698 : S6Eq6_98 ξ W P) {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < ξ * (q - 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ CL : ℝ, 0 ≤ CL ∧ ∀ (N : ℕ) (r : ℝ), 0 ≤ r → r ≤ 1 →
      (2 : ℝ) ^ (-((N : ℝ) + r)) < 1 → ∃ M : ℝ,
        P {ω | M < ⨆ z : ferniqueBox 0 1, |phiVer W P ((2 : ℝ) ^ (-((N : ℝ) + r))) 1 z ω|} ≤
          ENNReal.ofReal ε ∧
        Real.exp (ξ * M) ≤ CL * lambdaDelta ξ W P ((2 : ℝ) ^ (-((N : ℝ) + r))) *
          ((2 : ℝ) ^ (-((N : ℝ) + r))) ^ (β - 1) := by
  intro ε hε
  have hP := hW.isProbabilityMeasure
  set ζ := (ξ * (q - 2) - β) / 2 with hζ_def
  have hζ : 0 < ζ := by rw [hζ_def]; linarith
  obtain ⟨c, hc, hlam⟩ := S6D.lambdaN_lower_of_554 hW h554 hζ
  obtain ⟨C0, hC0⟩ := h698
  set m := |Real.log ε| / 2 with hm_def
  have hm : 0 ≤ m := by positivity
  have hεm : Real.exp (-(2 * m)) ≤ ε := by
    calc Real.exp (-(2 * m)) = Real.exp (-|Real.log ε|) := by congr 1; rw [hm_def]; ring
      _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.2 (neg_abs_le _)
      _ = ε := Real.exp_log hε
  set L := Real.log 2 with hL_def
  have hL : 0 < L := Real.log_pos (by norm_num)
  set T := ferniqueCF * Real.sqrt 6 + 2 * Real.log 2 + m with hT_def
  refine ⟨Real.exp (ξ * T + C0 + L * |1 - β|) / c, by positivity, fun N r hr0 hr1 hδ1 => ?_⟩
  set δ := (2 : ℝ) ^ (-((N : ℝ) + r)) with hδ_def
  have hδ0 : 0 < δ := by positivity
  obtain ⟨hδa, hδb⟩ := split_bounds N hr0 hr1
  rw [← hδ_def] at hδa hδb
  refine ⟨ferniqueCF * Real.sqrt 6 + (2 * (N + 1) * Real.log 2 + m), ?_, ?_⟩
  · have hsub : {ω | ferniqueCF * Real.sqrt 6 + (2 * (N + 1) * Real.log 2 + m) <
        ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|} ⊆
        {ω | ferniqueCF * Real.sqrt 6 + (2 * (N + 1) * Real.log 2 + m) ≤
        ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|} := fun ω hω => by simp only [mem_setOf_eq] at hω ⊢; exact hω.le
    refine (measure_mono hsub).trans ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal ((phiVer_sup_tail_unif hW N hδa hδb hδ1 hm).trans hεm)
  · set a := 1 - ξ * q + ζ with ha
    have hΛ : Real.exp (-C0) * (c * Real.exp (-L * a * N)) ≤ lambdaDelta ξ W P δ :=
      (mul_le_mul_of_nonneg_left (hlam N) (Real.exp_pos _).le).trans (hC0 N r hr0 hr1).1
    have hpow : δ ^ (β - 1) = Real.exp (L * ((N + r) * (1 - β))) := by
      rw [hδ_def, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
      congr 1; ring
    have hprod : Real.exp (ξ * T + C0 + L * |1 - β|) / c *
        (Real.exp (-C0) * (c * Real.exp (-L * a * N))) * δ ^ (β - 1) =
        Real.exp (ξ * T + L * |1 - β| + -L * a * N + L * ((N + r) * (1 - β))) := by
      rw [hpow]
      have e1 : Real.exp (ξ * T + C0 + L * |1 - β|) =
          Real.exp (ξ * T + L * |1 - β|) * Real.exp C0 := by rw [← Real.exp_add]; ring_nf
      rw [e1, Real.exp_add, Real.exp_add]
      have : Real.exp C0 * Real.exp (-C0) = 1 := by rw [← Real.exp_add]; simp
      field_simp
      rw [mul_assoc (Real.exp (ξ * T) * Real.exp (L * |1 - β|)) (Real.exp C0), this, mul_one,
        ← Real.exp_add, ← Real.exp_add]
    have habs : 0 ≤ |1 - β| + r * (1 - β) := by
      rcases le_total 0 (1 - β) with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_nonpos h]; nlinarith
    have hexp : ξ * (ferniqueCF * Real.sqrt 6 + (2 * (N + 1) * Real.log 2 + m)) ≤
        ξ * T + L * |1 - β| + -L * a * N + L * ((N + r) * (1 - β)) := by
      have e : ξ * T + L * |1 - β| + -L * a * N + L * ((N + r) * (1 - β)) =
          ξ * (ferniqueCF * Real.sqrt 6 + (2 * (N + 1) * Real.log 2 + m)) +
            L * ζ * N + L * (|1 - β| + r * (1 - β)) := by
        rw [hT_def, ha, hL_def, hζ_def]; ring
      rw [e]
      have : 0 ≤ L * ζ * N := by positivity
      have : 0 ≤ L * (|1 - β| + r * (1 - β)) := mul_nonneg hL.le habs
      linarith
    calc Real.exp (ξ * (ferniqueCF * Real.sqrt 6 + (2 * (N + 1) * Real.log 2 + m)))
        ≤ Real.exp (ξ * T + L * |1 - β| + -L * a * N + L * ((N + r) * (1 - β))) :=
          Real.exp_le_exp.2 hexp
      _ = Real.exp (ξ * T + C0 + L * |1 - β|) / c *
          (Real.exp (-C0) * (c * Real.exp (-L * a * N))) * δ ^ (β - 1) := hprod.symm
      _ ≤ _ := by gcongr

end S6P28U
end DDDF
end LQGMetric
