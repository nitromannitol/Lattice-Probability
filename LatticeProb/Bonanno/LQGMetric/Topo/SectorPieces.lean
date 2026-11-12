/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.SectorPieces at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.SectorLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Sector lemma, pieces: spurs and lifted paths in log coordinates

With `E w = x + e^w`:
* `exists_spur`: a point `k` of the closed annulus in the closure of `W ⊆` open annulus and in an
  open set `O` is reached from a point `E ω ∈ W` by a straight segment `[ω, κ]` (`E κ = k`) in
  log coordinates along which `E` stays in `O` and the real part stays in `[log r₁, log r₂]`.
* `exists_lift_path`: two points of an open connected `U ∌ x` are joined by a path whose lift
  through `E` starts at a prescribed logarithm and ends at a `2πiℤ`-translate of another
  (path lifting `QuantumZipper.CA.Topo.exists_lift_exp`, i.e. mathlib's covering-space lifting).
-/

namespace LQGMetric

namespace Sector

open Set Metric

/-- The segment from `ω` to `κ`, parametrised by `[0, 1]`. -/
def spur (ω κ : ℂ) (s : ℝ) : ℂ := ω + (s : ℂ) * (κ - ω)

theorem continuous_spur (ω κ : ℂ) : Continuous (spur ω κ) := by unfold spur; fun_prop

theorem exists_spur {x : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) {W O : Set ℂ}
    (hW : W ⊆ GM.j1bAnn x r₁ r₂) (hO : IsOpen O) {k : ℂ} (hkW : k ∈ closure W) (hkO : k ∈ O)
    (hkA : r₁ ≤ ‖k - x‖ ∧ ‖k - x‖ ≤ r₂) :
    ∃ ω κ : ℂ, x + Complex.exp κ = k ∧ x + Complex.exp ω ∈ W ∧
      ∀ s ∈ Icc (0 : ℝ) 1, x + Complex.exp (spur ω κ s) ∈ O ∧
        (spur ω κ s).re ∈ Icc (Real.log r₁) (Real.log r₂) := by
  have hkx : k - x ≠ 0 := fun h => by rw [h, norm_zero] at hkA; linarith [hkA.1]
  set κ := Complex.log (k - x) with hκ
  have hEκ : x + Complex.exp κ = k := by rw [hκ, Complex.exp_log hkx]; ring
  have hEc : Continuous fun w : ℂ => x + Complex.exp w := by fun_prop
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 (hO.preimage hEc) κ (by simp only [mem_preimage, hEκ, hkO])
  have hopen : IsOpen ((fun w : ℂ => x + Complex.exp w) '' ball κ ε) :=
    ((isOpenMap_add_left x).comp Complex.isOpenMap_exp) _ isOpen_ball
  obtain ⟨_, ⟨ω, hω, rfl⟩, hωW⟩ :=
    mem_closure_iff.1 hkW _ hopen ⟨κ, mem_ball_self hε, hEκ⟩
  refine ⟨ω, κ, hEκ, hωW, fun s hs => ⟨hεO ?_, ?_⟩⟩
  · rw [mem_ball, dist_eq_norm] at hω ⊢
    have : spur ω κ s - κ = ((1 - s : ℝ) : ℂ) * (ω - κ) := by unfold spur; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
    nlinarith [hs.1, norm_nonneg (ω - κ)]
  · have hωA := hW hωW
    have hre : (spur ω κ s).re = (1 - s) * ω.re + s * κ.re := by
      unfold spur; simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, Complex.sub_im]; ring
    have hω1 : ω.re = Real.log ‖x + Complex.exp ω - x‖ := re_of_exp_eq (by ring)
    have hκ1 : κ.re = Real.log ‖k - x‖ := re_of_exp_eq (by rw [← hEκ]; ring)
    simp only [GM.j1bAnn, mem_ofPred_eq] at hωA
    have a1 := Real.log_le_log hr₁ hωA.1.le
    have a2 := Real.log_le_log (hr₁.trans hωA.1) hωA.2.le
    have b1 := Real.log_le_log hr₁ hkA.1
    have b2 := Real.log_le_log (hr₁.trans_le hkA.1) hkA.2
    rw [← hω1] at a1 a2
    rw [← hκ1] at b1 b2
    rw [hre]
    constructor <;> nlinarith [hs.1, hs.2]

theorem exists_lift_path {x : ℂ} {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUx : x ∉ U) {ω ω' : ℂ} (hω : x + Complex.exp ω ∈ U) (hω' : x + Complex.exp ω' ∈ U) :
    ∃ P : Set ℂ, IsCompact P ∧ IsPreconnected P ∧ ω ∈ P ∧
      (∀ z ∈ P, x + Complex.exp z ∈ U) ∧ ∃ c, Complex.exp c = 1 ∧ ω' + c ∈ P := by
  have hpc : IsPathConnected U := hUo.isConnected_iff_isPathConnected.1 ⟨⟨_, hω⟩, hUc⟩
  have hj := hpc.joinedIn _ hω _ hω'
  set γ := hj.somePath
  let g : C(unitInterval, ℂ) := ⟨fun t => γ t - x, by fun_prop⟩
  have hg : ∀ t, g t ≠ 0 := fun t h => hUx (by
    have := hj.somePath_mem t
    rw [show γ t = x from sub_eq_zero.1 h] at this; exact this)
  obtain ⟨Λ, hΛ⟩ := QuantumZipper.CA.Topo.exists_lift_exp g hg
  have hΛ0 : Complex.exp (Λ 0) = Complex.exp ω := by
    rw [hΛ 0]; show γ 0 - x = _; rw [γ.source]; ring
  have hsh : Complex.exp (ω - Λ 0) = 1 := by
    rw [Complex.exp_sub, hΛ0, div_self (Complex.exp_ne_zero _)]
  set Λ' : unitInterval → ℂ := fun t => Λ t + (ω - Λ 0)
  have hΛ'c : Continuous Λ' := Λ.continuous.add continuous_const
  have hE : ∀ t, x + Complex.exp (Λ' t) = γ t := fun t => by
    simp only [Λ', Complex.exp_add, hsh, mul_one, hΛ t]; show x + (γ t - x) = γ t; ring
  refine ⟨range Λ', isCompact_range hΛ'c, isPreconnected_range hΛ'c, ⟨0, by simp [Λ']⟩,
    ?_, Λ' 1 - ω', ?_, ⟨1, by ring⟩⟩
  · rintro _ ⟨t, rfl⟩; rw [hE]; exact hj.somePath_mem t
  · have h1 : Complex.exp (Λ' 1) = Complex.exp ω' := by
      have := hE 1; rw [γ.target] at this; linear_combination this
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]

end Sector

end LQGMetric
