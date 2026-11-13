/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.L46TGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.GeneralPairBridge

/-!
# Geometry of the shifted disks used in Lemma 4.6

For `ρ∈(0,1)` and `w∈closedBall(0,ρ)`, the observation disk
`B_{(1-ρ)/4}(w)` is translated into the punctured unit disk by
`t=−(w+(1−ρ)/2)`. The larger Markov disk `B_{(1-ρ)/2}(w)` avoids both
normalization circles.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set TopologicalSpace Metric LQGMetric LQGMetric.MarkovZB

namespace MatedCRTHarmonic.GMSCM

theorem l46t_affine_geometry {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) ρ) :
    let s : ℝ := 1 - ρ
    let a : ℝ := s / 4
    let b : ℝ := s / 2
    let z₀ : ℂ := w + ((b : ℝ) : ℂ)
    let t : ℂ := -z₀
    let W : Opens ℂ := ⟨ball w a, isOpen_ball⟩
    let V : Opens ℂ := ⟨ball w b, isOpen_ball⟩
    IsCompact (closure ((affOpens 1 t W : Opens ℂ) : Set ℂ)) ∧
    closure ((affOpens 1 t W : Opens ℂ) : Set ℂ) ⊆ ball (0 : ℂ) 1 \ {0} ∧
    W ≤ V ∧ IsCompact (closure (W : Set ℂ)) ∧
    closure (W : Set ℂ) ⊆ (V : Set ℂ) ∧
    ZBAdmissible V ∧ (V : Set ℂ).Nonempty ∧
    Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1) ∧
    Disjoint (V : Set ℂ) (sphere (-t) 1) ∧
    (W : Set ℂ) ⊆ ball (0 : ℂ) 1 := by
  let s : ℝ := 1 - ρ
  let a : ℝ := s / 4
  let b : ℝ := s / 2
  let z₀ : ℂ := w + ((b : ℝ) : ℂ)
  let t : ℂ := -z₀
  let W : Opens ℂ := ⟨ball w a, isOpen_ball⟩
  let V : Opens ℂ := ⟨ball w b, isOpen_ball⟩
  have hs : 0 < s := by dsimp [s]; linarith [hρ.2]
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hwρ : ‖w‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
  have htw : t + w = -((b : ℝ) : ℂ) := by simp [t, z₀]
  have hbt : ‖t + w‖ = b := by rw [htw]; simp [Real.norm_eq_abs, abs_of_pos hb]
  have hbw : dist w z₀ = b := by
    rw [dist_eq_norm]
    have he : w - z₀ = -((b : ℝ) : ℂ) := by simp [z₀]
    rw [he]
    simp [Real.norm_eq_abs, abs_of_pos hb]
  have hAffine : ((affOpens 1 t W : Opens ℂ) : Set ℂ) = ball (t + w) a := by
    ext x
    simp only [affOpens, Opens.coe_mk, Set.mem_preimage, affMap, inv_one,
      one_smul, Metric.mem_ball]
    simp only [W, Opens.coe_mk, Metric.mem_ball]
    simp only [dist_eq_norm]
    abel
  have hcloseAffine : closure ((affOpens 1 t W : Opens ℂ) : Set ℂ) ⊆
      closedBall (t + w) a := by
    rw [hAffine]
    exact Metric.closure_ball_subset_closedBall
  have hK : IsCompact (closure ((affOpens 1 t W : Opens ℂ) : Set ℂ)) :=
    (isCompact_closedBall (t + w) a).of_isClosed_subset isClosed_closure hcloseAffine
  have hCone : closure ((affOpens 1 t W : Opens ℂ) : Set ℂ) ⊆
      ball (0 : ℂ) 1 \ {0} := by
    intro x hx
    have hxa : ‖x - (t + w)‖ ≤ a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hcloseAffine hx
    have hup : ‖x‖ ≤ ‖x - (t + w)‖ + ‖t + w‖ := by
      calc
        ‖x‖ = ‖(x - (t + w)) + (t + w)‖ := by simp
        _ ≤ _ := norm_add_le _ _
    have hlo : ‖t + w‖ ≤ ‖x - (t + w)‖ + ‖x‖ := by
      calc
        ‖t + w‖ = ‖-(x - (t + w)) + x‖ := by congr 1; abel
        _ ≤ _ := by simpa only [norm_neg] using norm_add_le (-(x - (t + w))) x
    rw [hbt] at hup hlo
    constructor
    · simpa [Metric.mem_ball, dist_zero_right] using
        (show ‖x‖ < 1 by dsimp [a, b, s] at *; linarith [hρ.1, hρ.2])
    · intro hx0
      have hx0' : x = 0 := by simpa using hx0
      subst x
      have hnorm : ‖-w + -t‖ = b := by
        calc
          ‖-w + -t‖ = ‖-(t + w)‖ := by congr 1; abel
          _ = b := by rw [norm_neg]; exact hbt
      have hba : b ≤ a := by simpa [hnorm] using hxa
      linarith [hab]
  have hcloseW : closure (W : Set ℂ) ⊆ closedBall w a :=
    Metric.closure_ball_subset_closedBall
  have hKW : IsCompact (closure (W : Set ℂ)) :=
    (isCompact_closedBall w a).of_isClosed_subset isClosed_closure hcloseW
  have hKV : closure (W : Set ℂ) ⊆ (V : Set ℂ) := by
    intro x hx
    have hxa : dist x w ≤ a := by
      simpa [Metric.mem_closedBall] using hcloseW hx
    simpa [V, Metric.mem_ball] using (lt_of_le_of_lt hxa hab)
  have hWV : W ≤ V := fun _ hx => hKV (subset_closure hx)
  have hadm : ZBAdmissible V := zbAdmissible_of_isBounded isBounded_ball
  have hne : (V : Set ℂ).Nonempty := ⟨w, by simp [V, hb]⟩
  have hV₁ : Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hx1
    have hxb : dist x w < b := by simpa [V, Metric.mem_ball] using hx
    have hnorm : ‖x‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hx1
    have htri : ‖x‖ ≤ dist x w + ‖w‖ := by
      calc
        ‖x‖ = ‖(x - w) + w‖ := by simp
        _ ≤ ‖x - w‖ + ‖w‖ := norm_add_le _ _
        _ = dist x w + ‖w‖ := by rw [dist_eq_norm]
    dsimp [b, s] at *
    linarith
  have hVR : Disjoint (V : Set ℂ) (sphere (-t) 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hx1
    have hxb : dist x w < b := by simpa [V, Metric.mem_ball] using hx
    have hnorm : dist x z₀ = 1 := by
      change dist x (-t) = 1 at hx1
      simpa [t] using hx1
    have htri := dist_triangle x w z₀
    rw [hbw] at htri
    dsimp [b, s] at *
    linarith [hρ.1]
  have hWunit : (W : Set ℂ) ⊆ ball (0 : ℂ) 1 := by
    intro x hx
    have hxa : dist x w < a := by simpa [W, Metric.mem_ball] using hx
    have htri : ‖x‖ ≤ dist x w + ‖w‖ := by
      calc
        ‖x‖ = ‖(x - w) + w‖ := by simp
        _ ≤ ‖x - w‖ + ‖w‖ := norm_add_le _ _
        _ = dist x w + ‖w‖ := by rw [dist_eq_norm]
    simp only [Metric.mem_ball, dist_zero_right]
    dsimp [a, s] at *
    linarith
  exact ⟨hK, hCone, hWV, hKW, hKV, hadm, hne, hV₁, hVR, hWunit⟩

end MatedCRTHarmonic.GMSCM
