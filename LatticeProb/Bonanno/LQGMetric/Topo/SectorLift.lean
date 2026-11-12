/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.SectorLift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.SectorOrder
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanJ1bTop
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoEilenberg
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoSep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Sector lemma, lifting part: crossing continua of an annulus lift to crossers of a rectangle

A continuum `K` crossing the closed annulus `{r₁ ≤ |y − x| ≤ r₂}`, disjoint from a second crossing
continuum `K'`, does not separate `x` from `∞` (the connected set `B(x, r₁) ∪ K' ∪ {|y − x| > r₂}`
avoids it), so by Eilenberg's theorem (`QuantumZipper.CA.Topo.hasLogOn_of_not_separates`, Burckel,
*Classical Analysis in the Complex Plane*, Ex. 4.37(i)) `y ↦ y − x` has a continuous logarithm
`ℓ` on `K` (`hasLog_crossing`). Each translate `(ℓ + d)(K)` with `e^d = 1` is a crosser of the
rectangle `[log r₁, log r₂] × [y₀, y₁]` when its imaginary parts lie in `(y₀, y₁)`
(`isCrosser_lift`), and `x + e^{(·)}` maps it back into `K` (`exp_mem_of_mem_lift`).
Own write-up (DEVIATIONS, proposed).
-/

namespace LQGMetric

namespace Sector

open Set Metric

theorem preconn_union_closure {A B : Set ℂ} (hA : IsPreconnected A) (hB : IsPreconnected B)
    (h : (closure A ∩ B).Nonempty) : IsPreconnected (A ∪ B) := by
  obtain ⟨p, hpA, hpB⟩ := h
  have h1 : IsPreconnected (A ∪ {p}) := hA.subset_closure subset_union_left
    (union_subset subset_closure (singleton_subset_iff.2 hpA))
  have h2 := h1.union' ⟨p, Or.inr rfl, hpB⟩ hB
  rwa [union_assoc, singleton_union, insert_eq_of_mem hpB] at h2

theorem re_of_exp_eq {w z : ℂ} (h : Complex.exp w = z) : w.re = Real.log ‖z‖ := by
  rw [← h, Complex.norm_exp, Real.log_exp]

theorem isPreconnected_ext (x : ℂ) (r : ℝ) : IsPreconnected {z : ℂ | r < ‖z - x‖} := by
  have := (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm r).image (fun w => x + w)
    (continuous_const.add continuous_id).continuousOn
  convert this using 1
  ext z
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · intro h; exact ⟨z - x, h, by ring⟩
  · rintro ⟨w, hw, rfl⟩; simpa using hw

/-- A crossing continuum disjoint from another one carries a continuous logarithm of `y − x`. -/
theorem hasLog_crossing {x : ℂ} {r₁ r₂ : ℝ} {K K' : Set ℂ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂)
    (hK : GM.j1bCrossing x r₁ r₂ K) (hK' : GM.j1bCrossing x r₁ r₂ K') (hd : Disjoint K K') :
    ∃ ℓ : ℂ → ℂ, ContinuousOn ℓ K ∧ ∀ z ∈ K, Complex.exp (ℓ z) = z - x := by
  obtain ⟨hKc, -, hKA, -, -⟩ := hK
  obtain ⟨-, hK'p, -, ⟨y₁, hy₁K', hy₁⟩, ⟨y₂, hy₂K', hy₂⟩⟩ := hK'
  set B : ℂ := x + ((r₂ + 1 : ℝ) : ℂ) with hBdef
  have hext : {z : ℂ | r₂ < ‖z - x‖} = (closedBall x r₂)ᶜ := by
    ext z; simp [dist_eq_norm]
  have hS : IsPreconnected (ball x r₁ ∪ K' ∪ {z : ℂ | r₂ < ‖z - x‖}) := by
    rw [union_comm (ball x r₁ ∪ K')]
    refine preconn_union_closure (isPreconnected_ext x r₂)
      (preconn_union_closure (convex_ball x r₁).isPreconnected hK'p ⟨y₁, ?_, hy₁K'⟩)
      ⟨y₂, ?_, Or.inr hy₂K'⟩
    · rw [closure_ball x hr₁.ne', mem_closedBall, dist_eq_norm, hy₁]
    · rw [hext, closure_compl, interior_closedBall x (by linarith : r₂ ≠ 0)]
      simp [dist_eq_norm, hy₂]
  have hSsub : ball x r₁ ∪ K' ∪ {z : ℂ | r₂ < ‖z - x‖} ⊆ Kᶜ := by
    rintro z ((hz | hz) | hz) hzK
    · rw [mem_ball, dist_eq_norm] at hz; linarith [(hKA z hzK).1]
    · exact hd.le_bot ⟨hzK, hz⟩
    · simp only [mem_ofPred_eq] at hz; linarith [(hKA z hzK).2]
  have hBn : ‖B - x‖ = r₂ + 1 := by
    rw [hBdef, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hB := hS.subset_connectedComponentIn (Or.inl (Or.inl (mem_ball_self hr₁))) hSsub
    (show B ∈ _ from Or.inr (by simp only [mem_ofPred_eq, hBn]; linarith))
  obtain ⟨ℓ₀, hℓ₀c, hℓ₀⟩ := QuantumZipper.CA.Topo.hasLogOn_of_not_separates hKc hB
  have hre : ∀ z ∈ K, 0 < (B - z).re := fun z hz => by
    have h1 := Complex.abs_re_le_norm (z - x)
    have h2 := (hKA z hz).2
    simp only [hBdef, Complex.sub_re, Complex.add_re, Complex.ofReal_re] at h1 ⊢
    linarith [(abs_le.1 h1).2]
  refine ⟨fun z => ℓ₀ z + Complex.log (B - z) + Real.pi * Complex.I,
    (hℓ₀c.add ((continuousOn_const.sub continuousOn_id).clog fun z hz =>
      Complex.mem_slitPlane_iff.2 (Or.inl (hre z hz)))).add continuousOn_const, fun z hz => ?_⟩
  have hBz : B - z ≠ 0 := fun h => by have := hre z hz; rw [h, Complex.zero_re] at this; linarith
  have hzB : z - B ≠ 0 := fun h => hBz (by rw [← neg_sub, h, neg_zero])
  rw [Complex.exp_add, Complex.exp_add, hℓ₀ z hz, Complex.exp_log hBz, Complex.exp_pi_mul_I]
  field_simp
  ring

theorem exp_mem_of_mem_lift {x : ℂ} {K : Set ℂ} {ℓ : ℂ → ℂ}
    (hℓ : ∀ z ∈ K, Complex.exp (ℓ z) = z - x) {d : ℂ} (hd : Complex.exp d = 1) {w : ℂ}
    (hw : w ∈ (fun z => ℓ z + d) '' K) : x + Complex.exp w ∈ K := by
  obtain ⟨z, hz, rfl⟩ := hw
  rw [Complex.exp_add, hℓ z hz, hd, mul_one, add_sub_cancel]
  exact hz

/-- A translate of the lift of a crossing continuum is a crosser of the rectangle. -/
theorem isCrosser_lift {x : ℂ} {r₁ r₂ y₀ y₁ : ℝ} (hr₁ : 0 < r₁) {K : Set ℂ}
    (hK : GM.j1bCrossing x r₁ r₂ K) {ℓ : ℂ → ℂ} (hℓc : ContinuousOn ℓ K)
    (hℓ : ∀ z ∈ K, Complex.exp (ℓ z) = z - x) {d : ℂ} (hd : Complex.exp d = 1)
    (hy : ∀ z ∈ K, y₀ < (ℓ z + d).im ∧ (ℓ z + d).im < y₁) :
    IsCrosser (Real.log r₁) (Real.log r₂) y₀ y₁ ((fun z => ℓ z + d) '' K) := by
  obtain ⟨hKc, hKp, hKA, ⟨p₁, hp₁, hp₁r⟩, ⟨p₂, hp₂, hp₂r⟩⟩ := hK
  have hd0 : d.re = 0 := by
    obtain ⟨n, rfl⟩ := Complex.exp_eq_one_iff.1 hd; simp
  have hre : ∀ z ∈ K, (ℓ z + d).re = Real.log ‖z - x‖ := fun z hz => by
    rw [Complex.add_re, hd0, add_zero, re_of_exp_eq (hℓ z hz)]
  have hcont : ContinuousOn (fun z => ℓ z + d) K := hℓc.add continuousOn_const
  refine ⟨hKc.image_of_continuousOn hcont, hKp.image _ hcont, ?_, ⟨_, ⟨p₁, hp₁, rfl⟩, ?_⟩,
    ⟨_, ⟨p₂, hp₂, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨⟨?_, ?_⟩, (hy z hz).1.le, (hy z hz).2.le⟩ <;> rw [hre z hz]
    · exact Real.log_le_log hr₁ (hKA z hz).1
    · exact Real.log_le_log (hr₁.trans_le (hKA z hz).1) (hKA z hz).2
  · rw [hre p₁ hp₁, hp₁r]
  · rw [hre p₂ hp₂, hp₂r]
  · rintro _ ⟨z, hz, rfl⟩; exact hy z hz

end Sector

end LQGMetric
