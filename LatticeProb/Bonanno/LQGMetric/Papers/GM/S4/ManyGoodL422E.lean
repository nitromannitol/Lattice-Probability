/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.ManyGoodL422E at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL422b
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityDet
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det3

/-!
# GM Lemma 4.22 on `ℰ_𝕣`: deterministic consequences of `ℰ_𝕣` used in the proof

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.22 (l. 2541–2565)
and decision D-B1 (`decisions/DEC-B.md` (a), GM.S4.11 (i): `τ_{ℓ𝕣}(𝕫)` is bounded below by a
multiple of the Hölder unit, "from cond 3 lower bound at `|w − z| = a𝕣`").

* `gm_filledBall_subset_ball_of_lt_tauR` — `𝓑^•_s(z) ⊆ B_R(z)` for `0 < s < τ_R(z)` (definition
  of `τ_R` as an infimum).
* `gm_tauR_ge_of_sphere` — if every point `w` of `∂B_ρ(z)` has `D(z,w) ≥ X` and `ρ < R`, then
  `τ_R(z) ≥ X` (`D` a length metric): GM.S4.11 (i) of DEC-B, with `ρ = a𝕣/2` (own write-up of
  DEC-B's one-line argument: a filled ball of radius `< X` stays in `cl B_ρ(z)` by connectedness).
* `gm_regC3_upper` — condition 3 (upper bound) in the form used by `gm_L4_22_det`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

section
variable {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC}

/-- `𝓑^•_s(z) ⊆ B_R(z)` for `0 < s < τ_R(z)` -/
theorem gm_filledBall_subset_ball_of_lt_tauR {z : ℂ} {Rr s : ℝ} {ω : Ω} (hs : 0 < s)
    (hsτ : s < tauR D h z Rr ω) : filledBall (D (h ω)) z s ⊆ ball z Rr := by
  by_contra hns
  have hbdd : BddBelow {s | 0 < s ∧ ¬ filledBall (D (h ω)) z s ⊆ ball z Rr} :=
    ⟨0, fun x hx => hx.1.le⟩
  have := csInf_le hbdd ⟨hs, hns⟩
  exact absurd this (not_le.2 hsτ)

/-- **GM.S4.11 (i)** of DEC-B (lower bound for `τ_R`), deterministic form -/
theorem gm_tauR_ge_of_sphere {z : ℂ} {ρ Rr X : ℝ} {ω : Ω} (hL : (D (h ω)).IsLength)
    (hρ : 0 < ρ) (hρR : ρ < Rr) (hX : ∀ w ∈ sphere z ρ, X ≤ (D (h ω)).1 (z, w)) :
    X ≤ tauR D h z Rr ω := by
  refine le_csInf (gm_tauR_set_nonempty (D (h ω)) z Rr) ?_
  rintro s ⟨hs, hns⟩
  by_contra hsX
  push_neg at hsX
  apply hns
  -- `𝓑_s ⊆ B_ρ(z)`
  have hB : ballM (D (h ω)) z s ⊆ ball z ρ := by
    intro x hx
    by_contra hxρ
    obtain ⟨p, hpB, hpfr⟩ := jb_inter_frontier_nonempty (K := (ball z ρ)ᶜ)
      isOpen_ball.isClosed_compl (jb_isPreconnected_ballM (D (h ω)) z s hL)
      (jb_mem_ballM (D (h ω)) z s hs) (by simp [hρ]) hx hxρ
    rw [frontier_compl, frontier_ball z hρ.ne'] at hpfr
    have h1 := hX p hpfr
    have h2 : (D (h ω)).1 (z, p) < s := hpB
    linarith
  have hcl : closure (ballM (D (h ω)) z s) ⊆ closedBall z ρ :=
    closure_minimal (hB.trans ball_subset_closedBall) isClosed_closedBall
  exact (gm_filledBall_subset_closedBall hcl).trans (closedBall_subset_ball hρR)

end

/-- condition 3 of `ℰ_𝕣` (upper bound) as an internal-metric bound in units `S` -/
theorem gm_regC3_upper {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar}
    {𝕣 a : ℝ} {ω : Ω} (hω : ω ∈ regC3 D h R 𝕣 a) (h𝕣 : 0 < 𝕣)
    (hS : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0) {u v : ℂ} (hu : u ∈ regRegion R 𝕣)
    (hv : v ∈ regRegion R 𝕣) (huv : ‖u - v‖ ≤ a * 𝕣) (hne : u ≠ v) :
    (D (h ω)).internal (ball u (2 * ‖u - v‖)) u v ≤
      ENNReal.ofReal ((‖u - v‖ / 𝕣) ^ R.χ * scaleFac R.ξ R.c (h ω) 𝕣 0) := by
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0
  have H := (hω u hu v hv huv).2 hne
  have hn : ‖(u - v) / (𝕣 : ℂ)‖ = ‖u - v‖ / 𝕣 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣]
  rw [hn] at H
  have h1 : ENNReal.ofReal S * ENNReal.ofReal S⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hS.le, mul_inv_cancel₀ hS.ne', ENNReal.ofReal_one]
  calc (D (h ω)).internal (ball u (2 * ‖u - v‖)) u v
      = ENNReal.ofReal S * (ENNReal.ofReal S⁻¹ * (D (h ω)).internal (ball u (2 * ‖u - v‖)) u v) := by
        rw [← mul_assoc, h1, one_mul]
    _ ≤ ENNReal.ofReal S * ENNReal.ofReal ((‖u - v‖ / 𝕣) ^ R.χ) := by gcongr
    _ = _ := by rw [← ENNReal.ofReal_mul hS.le, mul_comm]

/-- condition 3 of `ℰ_𝕣` (lower bound) in units `S` -/
theorem gm_regC3_lower {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar}
    {𝕣 a : ℝ} {ω : Ω} (hω : ω ∈ regC3 D h R 𝕣 a) (h𝕣 : 0 < 𝕣)
    (hS : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0) {u v : ℂ} (hu : u ∈ regRegion R 𝕣)
    (hv : v ∈ regRegion R 𝕣) (huv : ‖u - v‖ ≤ a * 𝕣) :
    (‖u - v‖ / 𝕣) ^ R.χ' * scaleFac R.ξ R.c (h ω) 𝕣 0 ≤ (D (h ω)).1 (u, v) := by
  have H := (hω u hu v hv huv).1
  have hn : ‖(u - v) / (𝕣 : ℂ)‖ = ‖u - v‖ / 𝕣 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣]
  rw [hn] at H
  rw [← le_div_iff₀ hS]
  calc (‖u - v‖ / 𝕣) ^ R.χ' ≤ (scaleFac R.ξ R.c (h ω) 𝕣 0)⁻¹ * (D (h ω)).1 (u, v) := H
    _ = _ := by rw [div_eq_inv_mul]

end LQGMetric.GM
