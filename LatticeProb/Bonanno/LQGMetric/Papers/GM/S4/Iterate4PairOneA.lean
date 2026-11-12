/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate4PairOneA at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4RegWG
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.IterateWitness

/-!
# `T4_2PairOne` at a fixed scale: from Prop 4.17 to the witness (DEC-89, packet C, last step)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, end of the proof of Thm 4.2
(l. 2437–2441): on `ℰ_𝕣`, if some `𝒵^𝔈_k` (`k ≤ K`) is nonempty, its pair is a witness; Prop 4.17
bounds the probability that fewer than `ε^{2ν+ζ}K` of them are nonempty.

* `gm_T4_2_pair_bound`: `P[Reg ∩ ¬wit] ≤` the bound of `gm_P4_17_ae`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

open scoped Classical in
/-- **from Prop 4.17 to the witness** (GM l. 2437–2441) -/
theorem gm_T4_2_pair_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {D : DistC → ContMetric} (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)) (h : Ω → DistC)
    (R : RegPar) (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC) {𝕫 𝕨 : ℂ} {𝕣 ε β L c Bd : ℝ} {K : ℕ}
    (Reg : Set Ω) (hK : 1 ≤ K) (hc : 0 < c) (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε) (h𝕣 : 0 < 𝕣)
    (hl3 : 0 < R.lam 3) (hRle : ∀ r ∈ p4Rads R 𝕣 ε, r ≤ ε * 𝕣)
    (hfar : L + 3 * R.lam 3 * ε * 𝕣 < ‖𝕫 - 𝕨‖)
    (hgeo : ∀ ω ∈ Reg, ∀ k ≤ K,
      filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ⊆ ball 𝕫 L)
    (h417 : P.real (Reg ∩ {ω | ((((Finset.range (K + 1)).filter
        (fun k => ω ∈ {ω | (zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω).Nonempty})).card : ℕ) : ℝ) <
        c * K}) ≤ Bd) [IsFiniteMeasure P] :
    P.real (Reg ∩ {ω | ¬ t42Wit sel h Ef R.lam R.rr R.μ 𝕣 ε 𝕫 𝕨 ω}) ≤ Bd := by
  refine le_trans (measureReal_mono ?_) h417
  refine subset_trans ?_ (gm_noZF_subset Reg
    (fun k => {ω | (zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω).Nonempty}) hK hc)
  rintro ω ⟨hR, hw⟩
  refine ⟨hR, fun k hk hZ => hw ?_⟩
  obtain ⟨p, hp⟩ := hZ
  have hpos : 0 < R.lam 3 * ε * 𝕣 := by positivity
  have htk : 0 < s4T D h 𝕫 R.ℓ 𝕣 ε β k ω := by
    rw [gm_s4T_eq]
    have hτ := gm_tauD_pos (D (h ω)) 𝕫 hℓ𝕣
    have : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
    have : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
    positivity
  have hcl := gm_filledBall_isClosed (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)
  have h𝕫 : 𝕫 ∈ filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) :=
    subset_closure.trans subset_union_left
      (show (D (h ω)).1 (𝕫, 𝕫) < _ by rw [(D (h ω)).2.self_eq_zero 𝕫]; exact htk)
  have hKL : frontier (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) ⊆ closedBall 𝕫 L :=
    hcl.frontier_subset.trans ((hgeo ω hR k hk).trans ball_subset_closedBall)
  exact gm_t42Wit_of_zkF hp hRle hl3.le hpos hcl h𝕫 hKL hfar

end LQGMetric.GM
