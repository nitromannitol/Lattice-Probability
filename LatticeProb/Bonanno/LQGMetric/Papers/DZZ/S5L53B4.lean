/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53B4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePushCoupling
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePhi
import LatticeProb.Bonanno.LQGMetric.Dimension.LGDScale

/-!
# Similarity coupling of `ĥ` (rotations included) for DZZ (eq-translation-invariant) (P2-DZZ53b)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2266–2270, (eq-translation-invariant)): for
`u, v, u', v' ∈ 𝕍̄` with `|u − v| = |u' − v'|` and an isometry `θ` mapping `𝕍̃_{u,v}` onto
`𝕍̃_{u',v'}`, the field `{η(x)}_{x ∈ 𝕍̃_{u,v}}` has the law of `{η(θx)}`; together with the scaling
of Lemma 2.9 (l. 635–641) this is what makes the law of `D̃_{γ,δ,η}(u,v)` depend on `u, v` only
through `|u − v|` ((eq-depend-on-Euclidean), l. 2273–2276). The tilde boxes are *rotated*, so the
real-scaling coupling `phi_coupledNoise_affine` (S2L9Push, `θ z = a z + b`, `a > 0`) does not
suffice; here the same DDDF conformal coupling (`WNPush.coupledNoise`) is run for the similarity
`θ = simMap a b`, `θ z = a z + b` with `a ∈ ℂ ∖ {0}` (rotation by `arg a`, scaling by `|a|`):

* `heatKernel_simMap`: `|a|² p(|a|²t/2; θv, θy) = p(t/2; v, y)`;
* `pushL2_phiKernelL2_simMap`: `T(k_{|a|α, |a|β, θv}) = k_{α, β, v}` in `L²`;
* **`phi_coupledNoise_simMap`**: `ĥ_{|a|α}^{|a|β}[W̃](θv) = ĥ_α^β[W](v)` a.s.

The proofs are those of S2L9Push with `|a|` in place of `a` (rotation invariance of the heat kernel).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DZZ

open WhiteNoise WNPush

lemma hasDerivAt_simMap (a b : ℂ) (z : ℂ) : HasDerivAt (simMap a b) a z := by
  have h := ((hasDerivAt_id z).const_mul a).add_const b
  rw [mul_one] at h
  exact h

lemma deriv_simMap (a b : ℂ) (z : ℂ) : deriv (simMap a b) z = a :=
  (hasDerivAt_simMap a b z).deriv

/-- The conformal hypotheses hold for `θ z = a z + b` (`a ≠ 0`) on `U = ℂ`. -/
lemma confHyp_simMap {a : ℂ} (ha : a ≠ 0) (b : ℂ) : ConfHyp (simMap a b) univ where
  isOpen := isOpen_univ
  diff := fun z _ => (hasDerivAt_simMap a b z).differentiableAt.differentiableWithinAt
  inj := fun z _ w _ h => by
    simp only [simMap, add_left_inj] at h
    exact mul_left_cancel₀ ha h
  deriv_ne := fun z _ => by rw [deriv_simMap]; exact ha

/-- Heat-kernel invariance under similarities: `|a|² p(|a|²t/2; θv, θy) = p(t/2; v, y)`. -/
lemma heatKernel_simMap {a : ℂ} (ha : a ≠ 0) (b : ℂ) (t : ℝ) (v y : ℂ) :
    ‖a‖ ^ 2 * heatKernel (t * ‖a‖ ^ 2 / 2) (simMap a b v) (simMap a b y) =
      heatKernel (t / 2) v y := by
  have hn : ‖simMap a b v - simMap a b y‖ = ‖a‖ * ‖v - y‖ := by
    simp only [simMap, add_sub_add_right_eq_sub, ← mul_sub, norm_mul]
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  unfold heatKernel
  rw [hn]
  by_cases ht : t = 0
  · subst ht; simp
  have ha2 : ‖a‖ ^ 2 ≠ 0 := by positivity
  have e : -(‖a‖ * ‖v - y‖) ^ 2 / (2 * (t * ‖a‖ ^ 2 / 2)) = -‖v - y‖ ^ 2 / (2 * (t / 2)) := by
    field_simp
  rw [e, ← mul_assoc]
  congr 1
  field_simp

/-- The pushforward of the pointwise kernel under a similarity. -/
lemma pushFunOf_phiKernel_simMap {a : ℂ} (ha : a ≠ 0) (b : ℂ) {α : ℝ} (hα : 0 < α) (β : ℝ)
    (v : ℂ) :
    pushFunOf (simMap a b) univ (phiKernel (‖a‖ * α) (‖a‖ * β) (simMap a b v)) =
      phiKernel α β v := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  funext p
  simp only [pushFunOf, phiKernel, pushMap, deriv_simMap]
  by_cases hp : p.1 ∈ Icc (α ^ 2) (β ^ 2)
  · have hp0 : 0 < p.1 := lt_of_lt_of_le (by positivity) hp.1
    have hp' : p.1 * ‖a‖ ^ 2 ∈ Icc ((‖a‖ * α) ^ 2) ((‖a‖ * β) ^ 2) := by
      constructor <;> [nlinarith [hp.1]; nlinarith [hp.2]]
    rw [indicator_of_mem (show p ∈ Ioi 0 ×ˢ univ from ⟨hp0, trivial⟩),
      indicator_of_mem (show (p.1 * ‖a‖ ^ 2, simMap a b p.2) ∈
        Icc ((‖a‖ * α) ^ 2) ((‖a‖ * β) ^ 2) ×ˢ univ from ⟨hp', trivial⟩),
      indicator_of_mem (show p ∈ Icc (α ^ 2) (β ^ 2) ×ˢ univ from ⟨hp, trivial⟩)]
    exact heatKernel_simMap ha b p.1 v p.2
  · rw [indicator_of_notMem (show p ∉ Icc (α ^ 2) (β ^ 2) ×ˢ univ from fun h => hp h.1)]
    by_cases hp0 : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)
    · rw [indicator_of_mem hp0]
      have hp' : (p.1 * ‖a‖ ^ 2, simMap a b p.2) ∉
          Icc ((‖a‖ * α) ^ 2) ((‖a‖ * β) ^ 2) ×ˢ univ := by
        rintro ⟨⟨h1, h2⟩, -⟩
        refine hp ⟨?_, ?_⟩
        · have : ‖a‖ ^ 2 * α ^ 2 ≤ ‖a‖ ^ 2 * p.1 := by nlinarith
          exact le_of_mul_le_mul_left this (by positivity)
        · have : ‖a‖ ^ 2 * p.1 ≤ ‖a‖ ^ 2 * β ^ 2 := by nlinarith
          exact le_of_mul_le_mul_left this (by positivity)
      rw [indicator_of_notMem hp', mul_zero]
    · rw [indicator_of_notMem hp0]

/-- `T(k_{|a|α, |a|β, θv}) = k_{α, β, v}` in `L²(ℝ × ℂ)`. -/
theorem pushL2_phiKernelL2_simMap {a : ℂ} (ha : a ≠ 0) (b : ℂ) {α : ℝ} (hα : 0 < α) (β : ℝ)
    (v : ℂ) :
    pushL2 (simMap a b) univ (phiKernelL2 (‖a‖ * α) (‖a‖ * β) (simMap a b v)) =
      phiKernelL2 α β v := by
  have h := confHyp_simMap ha b
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  apply Lp.ext
  refine (coeFn_pushL2 h.isOpen h.diff h.inj h.deriv_ne _).trans ?_
  refine (pushFunOf_congr h.isOpen h.diff h.inj h.deriv_ne
    (coeFn_phiKernelL2 _ _ (mul_pos hpos hα) _)).trans ?_
  rw [pushFunOf_phiKernel_simMap ha b hα β v]
  exact (coeFn_phiKernelL2 α β hα v).symm

/-- The kernel `k_{|a|α, |a|β, x}` is supported in `(0, ∞) × θ(ℂ)`. -/
lemma supportedIn_phiKernelL2_simMap {a : ℂ} (ha : a ≠ 0) (b : ℂ) {α : ℝ} (hα : 0 < α)
    (β : ℝ) (x : ℂ) :
    SupportedIn (pushTarget (simMap a b) univ) (phiKernelL2 (‖a‖ * α) (‖a‖ * β) x) := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  unfold SupportedIn
  rw [ae_restrict_iff' (confHyp_simMap ha b).measurableSet_pushTarget.compl]
  filter_upwards [coeFn_phiKernelL2 _ _ (mul_pos hpos hα) x] with p hp hpc
  rw [hp, phiKernel, indicator_of_notMem]
  rintro ⟨⟨h1, -⟩, -⟩
  refine hpc ⟨lt_of_lt_of_le (by positivity) h1, ?_⟩
  exact ⟨(p.2 - b) / a, trivial, by simp only [simMap]; field_simp; ring⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **DZZ (eq-translation-invariant), l. 2266–2270, with the scaling of Lemma 2.9**: in the
coupling `W̃ = coupledNoise θ W W'` for the similarity `θ z = a z + b` (`a ∈ ℂ ∖ {0}`),
`ĥ_{|a|α}^{|a|β}[W̃](θ v) = ĥ_α^β[W](v)` almost surely, for every `v` and every band `0 < α`. -/
theorem phi_coupledNoise_simMap {a : ℂ} (ha : a ≠ 0) (b : ℂ) {W W' : WNSpace → Ω → ℝ}
    (hW' : IsWhiteNoise P W') {α : ℝ} (hα : 0 < α) (β : ℝ) (v : ℂ) :
    phi (coupledNoise (confHyp_simMap ha b) W W') (‖a‖ * α) (‖a‖ * β) (simMap a b v) =ᵐ[P]
      phi W α β v := by
  filter_upwards [coupledNoise_ae_of_supportedIn (confHyp_simMap ha b) (W := W) hW'
    (supportedIn_phiKernelL2_simMap ha b hα β (simMap a b v))] with ω hω
  simp only [phi, hω, pushL2_phiKernelL2_simMap ha b hα β v]

/-- the coupled noise is again a white noise (DDDF l. 541–543) -/
theorem isWhiteNoise_coupledNoise_simMap {a : ℂ} (ha : a ≠ 0) (b : ℂ) {W W' : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P W')
    (hind : IndepFun (fun ω f => W f ω) (fun ω f => W' f ω) P) :
    IsWhiteNoise P (coupledNoise (confHyp_simMap ha b) W W') :=
  isWhiteNoise_coupledNoise _ hW hW' hind

end DZZ
end LQGMetric
