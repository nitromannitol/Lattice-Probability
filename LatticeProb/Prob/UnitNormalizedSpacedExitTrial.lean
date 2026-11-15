import LatticeProb.Prob.NormalizedFullExitTrial
import LatticeProb.Prob.RealSpacedBallExitTrial
import LatticeProb.Topology.ScaledNestedExitBall

/-! # Normalized estimates for equally spaced exit trials -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Normalized conditional estimates on intermediate exit segments imply an
inverse-scale bound for failure of the full exit trace to contain a ball. -/
theorem measureReal_real_ballExitTrace_failure_le_of_unit_normalized
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (z : EuclideanSpace ℝ (Fin d)) (R C ε η : ℝ)
    (hR : 0 < R) (hC : 0 < C) (hε : 0 < ε) (hηC : 2 ≤ η * C)
    (hstart : ∀ᵐ ω ∂μ, X 0 ω = z)
    (hfin : ∀ᵐ ω ∂μ, openExitTime X (ball z R) ω ≠ ⊤)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1,
      let s : ℝ≥0 := ⟨((k + 1 : ℕ) : ℝ) * (C * ε * R) + (C * ε * R) / 2, by positivity⟩
      let hs : 0 < s := by
        have ht : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * (C * ε * R) + (C * ε * R) / 2 := by positivity
        exact_mod_cast ht
      let q := (C * ε * R) / (2 * (s : ℝ))
      let w := pathMap X hc
      let v := fun ω => ((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ :
        C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d))).comp (w ω)).comp
          ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩
      let B := {ω | ∃ y, ball y (η * q) ⊆ (fun t : ℝ => v ω t.toNNReal) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ v ω t.toNNReal ∉ ball 0 1})
        (sInf {t : ℝ | 0 ≤ t ∧ v ω t.toNNReal ∉ ball 0 (1 + q)})}
      let Y := fun ω => stoppedPath
        (openExitTime (fun t (_ : Unit) => ballNormalize z s hs (w ω (areaTimeScale s hs t)))
          (ball 0 1) ()) (v ω)
      ∀ᵐ ω ∂μ, p ≤ μ[B.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap Y inferInstance] ω) :
    μ.real {ω | ¬ ∃ w, ball w (ε * R) ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc 0
      (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  apply measureReal_real_ballExitTrace_failure_le_spaced hm hc z R C ε hR hC hε hfin hp0 hp1
  intro k hk
  let a : ℝ := ((k + 1 : ℕ) : ℝ) * (C * ε * R)
  have ha : 0 < a := by dsimp [a]; positivity
  have hd : 0 < C * ε * R := mul_pos (mul_pos hC hε) hR
  let s : ℝ≥0 := ⟨a + (C * ε * R) / 2, by positivity⟩
  have hs : 0 < s := by
    have ht : 0 < a + (C * ε * R) / 2 := by positivity
    exact_mod_cast ht
  let q : ℝ := (C * ε * R) / (2 * (s : ℝ))
  have hq : 0 < q := by dsimp [q]; positivity
  have hqa : q * (s : ℝ) = (C * ε * R) / 2 := by
    dsimp [q]
    field_simp
  have houter : ((k + 1 + 1 : ℕ) : ℝ) * (C * ε * R) ≤ R := by
    apply spaced_radius_le hC hε hR
    omega
  have hfin' : ∀ᵐ ω ∂μ, openExitTime X
      (ball z (((k + 1 + 1 : ℕ) : ℝ) * (C * ε * R))) ω ≠ ⊤ := by
    filter_upwards [hfin] with ω hω
    exact ne_top_of_le_ne_top hω (monotone_openExitTime_ball X ω z houter)
  have hstart' : ∀ᵐ ω ∂μ, X 0 ω ∈ ball z a := by
    filter_upwards [hstart] with ω hω
    simpa [hω, mem_ball] using ha
  have hleft : a < (s : ℝ) * 1 := by
    change a < (a + (C * ε * R) / 2) * 1
    linarith
  have hright : (s : ℝ) * (1 + q) ≤
      ((k + 1 + 1 : ℕ) : ℝ) * (C * ε * R) := by
    have heq : ((k + 1 + 1 : ℕ) : ℝ) * (C * ε * R) = a + C * ε * R := by
      dsimp [a]
      push_cast
      ring
    rw [heq]
    change (a + (C * ε * R) / 2) * (1 + q) ≤ a + C * ε * R
    change q * (a + (C * ε * R) / 2) = (C * ε * R) / 2 at hqa
    nlinarith [hqa]
  have hball : ε * R ≤ (s : ℝ) * (η * q) := by
    have ht := target_radius_le_half_width hε.le hR.le hηC
    calc
      ε * R ≤ η * (C * ε * R) / 2 := ht
      _ = η * ((C * ε * R) / 2) := by ring
      _ = η * (q * (s : ℝ)) := by rw [hqa]
      _ = (s : ℝ) * (η * q) := by ring
  exact ballExitHistory_condExp_full_segment_of_normalized hm hc μ z
    (fun j => ((j + 1 : ℕ) : ℝ) * (C * ε * R))
    (monotone_spaced_ball_radius hC hε hR) k s hs 1 (1 + q)
    (ε * R) (η * q) p (by linarith) hleft hright hball hstart' hfin' (hp k hk)

end LatticeProb
