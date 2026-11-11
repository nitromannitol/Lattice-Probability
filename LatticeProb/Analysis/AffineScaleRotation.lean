import Mathlib

/-!
# Affine rerooting of curves and integer-rotation period identities

For a continuous curve `c : ℝ → ℂ` and a point `z₀ : ℂ`, the first hitting time of `z₀` is
`firstHitTime c z₀ = sInf {t | c t = z₀}`. For `z₀ : ℂ`, a scale `s : ℝ`, an angle `φ : ℝ`, the
affine rerooting `affineReroot z₀ s φ c` is the curve `t ↦ (s e^{iφ})⁻¹ (c (τ + s² t) − z₀)`, where
`τ = firstHitTime c z₀`. For a real constant `χ` and a function `H : ℝ → ℂ → ℝ`, the affine pullback
`affinePullback χ z₀ s φ H` is the function `(ρ, w) ↦ H (s ρ) (z₀ + s e^{iφ} w) − χ φ`.

All statements are general: the constant `χ`, the field `H`, the curve `c` and the witness map `Φ`
of a representation `L = Φ K` are arbitrary, subject only to the stated hypotheses. The file proves:

* `no_nonzero_period_of_tendsto_cocompact`: a continuous curve tending to infinity at infinity has
  no nonzero translation period;
* `affineReroot_zero_one_eq`, `affineReroot_zero_one_zero_apply`, `affineReroot_rotation_eq`,
  `affineReroot_scale_rotation_eq`: the rerooting at the integer rotations `φ = -(2πk)`;
* `affinePullback_zero_one_zero`, `affinePullback_rotation`, `affinePullback_scale_rotation`: the same
  identities for the affine pullback, where the rotation shifts the field by `k · 2πχ`;
* `witness_period_identity`, `witness_scale_identity`, `witness_scale_normalized_identity`: if `Φ`
  represents `L` from `K` almost surely and intertwines the pullbacks with the reroots, then the first
  hitting time of `0` vanishes almost surely, `Φ` is invariant under the shifts `K ↦ K + k · 2πχ`
  simultaneously for all `k : ℤ` almost surely, and the positive-scale identity holds with the integer
  removed.

The factor `e^{-2πik} = 1` is Mathlib's `Complex.exp_int_mul_two_pi_mul_I`.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace LatticeProb.AffineScaleRotation

/-- The first hitting time `sInf {t | c t = z}` of a point `z` by a curve `c`. -/
def firstHitTime (c : C(ℝ, ℂ)) (z : ℂ) : ℝ := sInf {t : ℝ | c t = z}

/-- The affine rerooting of a curve at `(z₀, s, φ)`: the curve `t ↦ (s e^{iφ})⁻¹ (c (τ + s² t) − z₀)`
with `τ = firstHitTime c z₀`. -/
def affineReroot (z₀ : ℂ) (s φ : ℝ) (c : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t => (((s : ℂ) * Complex.exp (φ * Complex.I))⁻¹) * (c (firstHitTime c z₀ + s ^ 2 * t) - z₀),
    by fun_prop⟩

/-- The affine pullback of a field `H : ℝ → ℂ → ℝ` by the map `w ↦ z₀ + s e^{iφ} w`, shifted by `-χ φ`
for a real constant `χ`: `(ρ, w) ↦ H (s ρ) (z₀ + s e^{iφ} w) − χ φ`. -/
def affinePullback (χ : ℝ) (z₀ : ℂ) (s φ : ℝ) (H : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun ρ w => H (s * ρ) (z₀ + (s : ℂ) * Complex.exp (φ * Complex.I) * w) - χ * φ

/-- A continuous curve `c` that tends to infinity at infinity, `Tendsto c (cocompact ℝ) (cocompact ℂ)`,
has no nonzero translation period: `c (τ + t) = c t` for all `t` forces `τ = 0`. -/
theorem no_nonzero_period_of_tendsto_cocompact (c : C(ℝ, ℂ))
    (hc : Tendsto c (cocompact ℝ) (cocompact ℂ)) (τ : ℝ) (hper : ∀ t, c (τ + t) = c t) :
    τ = 0 := by
  by_contra hτ
  have hS : ({c 0}ᶜ : Set ℂ) ∈ cocompact ℂ :=
    mem_cocompact.2 ⟨{c 0}, isCompact_singleton, subset_rfl⟩
  obtain ⟨T, hT, hTsub⟩ := mem_cocompact.1 (hc hS)
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hT.isBounded
  have hrep : ∀ n : ℕ, c ((n : ℝ) * τ) = c 0 := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [show ((m + 1 : ℕ) : ℝ) * τ = τ + (m : ℝ) * τ by push_cast; ring, hper, ih]
  obtain ⟨n, hn⟩ := exists_nat_gt (R / |τ|)
  have hmem : (n : ℝ) * τ ∈ T := by
    by_contra hnT
    have h1 : c ((n : ℝ) * τ) ∈ ({c 0}ᶜ : Set ℂ) := hTsub hnT
    exact (Set.mem_compl_iff _ _).1 h1 (Set.mem_singleton_iff.2 (hrep n))
  have hle : ‖(n : ℝ) * τ‖ ≤ R := hR _ hmem
  have habs : ‖(n : ℝ) * τ‖ = (n : ℝ) * |τ| := by
    rw [norm_mul, Real.norm_natCast, Real.norm_eq_abs]
  have hlt : R < (n : ℝ) * |τ| := (div_lt_iff₀ (abs_pos.2 hτ)).1 hn
  linarith

/-- At `(z₀, s, φ) = (0, 1, φ)`, `affineReroot` returns the curve itself once its first hitting time of
`0` is `0` and `e^{iφ} = 1`. -/
theorem affineReroot_zero_one_eq (c : C(ℝ, ℂ)) (φ : ℝ) (hfh : firstHitTime c 0 = 0)
    (hφ : Complex.exp (φ * Complex.I) = 1) : affineReroot 0 1 φ c = c := by
  ext t
  simp [affineReroot, hfh, hφ]

/-- At the identity affine map with `φ = 0`, `affineReroot` is the translation of the curve by its first
hitting time of `0`: `affineReroot 0 1 0 c t = c (firstHitTime c 0 + t)`. -/
theorem affineReroot_zero_one_zero_apply (c : C(ℝ, ℂ)) (t : ℝ) :
    affineReroot 0 1 0 c t = c (firstHitTime c 0 + t) := by
  simp [affineReroot]

/-- The affine pullback at the identity map with `φ = 0` is the identity on fields. -/
theorem affinePullback_zero_one_zero (χ : ℝ) (H : ℝ → ℂ → ℝ) :
    affinePullback χ 0 1 0 H = H := by
  funext ρ w
  simp [affinePullback]

/-- The affine pullback at the integer rotation `φ = -(2πk)` shifts the field by `k · 2πχ`. -/
theorem affinePullback_rotation (χ : ℝ) (k : ℤ) (H : ℝ → ℂ → ℝ) :
    affinePullback χ 0 1 (-(2 * Real.pi * k)) H
      = fun ρ w => H ρ w + k * (2 * Real.pi * χ) := by
  have hexp : Complex.exp (((-(2 * Real.pi * k) : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show (((-(2 * Real.pi * k) : ℝ) : ℂ) * Complex.I)
        = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  funext ρ w
  simp only [affinePullback, Complex.ofReal_one, one_mul, zero_add, hexp]
  ring

/-- The affine rerooting at the integer rotation `φ = -(2πk)` fixes a curve whose first hitting time
of `0` is `0`. -/
theorem affineReroot_rotation_eq (c : C(ℝ, ℂ)) (k : ℤ) (hfh : firstHitTime c 0 = 0) :
    affineReroot 0 1 (-(2 * Real.pi * k)) c = c := by
  have hexp : Complex.exp (((-(2 * Real.pi * k) : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show (((-(2 * Real.pi * k) : ℝ) : ℂ) * Complex.I)
        = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  exact affineReroot_zero_one_eq c _ hfh hexp

/-- At `(0, s, -(2πk))` the rerooting agrees with the one at `(0, s, 0)`, once the first hitting time
of `0` is `0`. -/
theorem affineReroot_scale_rotation_eq (c : C(ℝ, ℂ)) (s : ℝ) (k : ℤ)
    (hfh : firstHitTime c 0 = 0) :
    affineReroot 0 s (-(2 * Real.pi * k)) c = affineReroot 0 s 0 c := by
  have hexp : Complex.exp (((-(2 * Real.pi * k) : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show (((-(2 * Real.pi * k) : ℝ) : ℂ) * Complex.I)
        = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  ext t
  simp only [affineReroot, ContinuousMap.coe_mk, hexp, hfh, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero]

/-- The affine pullback at scale `s` and integer rotation `-(2πk)` sends `H` to
`(ρ, w) ↦ H (sρ, sw) + k · 2πχ`. -/
theorem affinePullback_scale_rotation (χ s : ℝ) (k : ℤ) (H : ℝ → ℂ → ℝ) :
    affinePullback χ 0 s (-(2 * Real.pi * k)) H
      = fun ρ w => H (s * ρ) ((s : ℂ) * w) + k * (2 * Real.pi * χ) := by
  have hexp : Complex.exp (((-(2 * Real.pi * k) : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show (((-(2 * Real.pi * k) : ℝ) : ℂ) * Complex.I)
        = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  funext ρ w
  simp only [affinePullback, hexp, mul_one, zero_add]
  ring

/-- **Period identity.** Let `Φ` be a map on fields with `L ω = Φ (K ω)` almost surely, such that
`Φ (affinePullback χ z₀ s φ (K ω)) = affineReroot z₀ s φ (L ω)` almost surely for every `(z₀, s, φ)` with
`s > 0`, and let `L ω` tend to infinity at infinity almost surely. Then `firstHitTime (L ω) 0 = 0` almost
surely, and simultaneously for every `k : ℤ`, `Φ (K + k · 2πχ) = Φ (K)` almost surely. -/
theorem witness_period_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (χ : ℝ)
    (K : Ω → ℝ → ℂ → ℝ) (L : Ω → C(ℝ, ℂ)) (Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ))
    (hrep : ∀ᵐ ω ∂P, L ω = Φ (K ω))
    (hcov : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s →
      ∀ᵐ ω ∂P, Φ (affinePullback χ z₀ s φ (K ω)) = affineReroot z₀ s φ (L ω))
    (htr : ∀ᵐ ω ∂P, Tendsto (L ω) (cocompact ℝ) (cocompact ℂ)) :
    (∀ᵐ ω ∂P, firstHitTime (L ω) 0 = 0) ∧
      ∀ᵐ ω ∂P, ∀ k : ℤ,
        Φ (fun ρ w => K ω ρ w + k * (2 * Real.pi * χ)) = Φ (K ω) := by
  have hid : ∀ᵐ ω ∂P, L ω = affineReroot 0 1 0 (L ω) := by
    filter_upwards [hrep, hcov 0 1 0 one_pos] with ω h1 h2
    rw [affinePullback_zero_one_zero] at h2
    exact h1.trans h2
  have hfh : ∀ᵐ ω ∂P, firstHitTime (L ω) 0 = 0 := by
    filter_upwards [hid, htr] with ω h1 h2
    refine no_nonzero_period_of_tendsto_cocompact (L ω) h2 (firstHitTime (L ω) 0) fun t => ?_
    have h3 := DFunLike.congr_fun h1 t
    rw [affineReroot_zero_one_zero_apply] at h3
    exact h3.symm
  have hper : ∀ k : ℤ, ∀ᵐ ω ∂P,
      Φ (fun ρ w => K ω ρ w + k * (2 * Real.pi * χ)) = Φ (K ω) := by
    intro k
    filter_upwards [hcov 0 1 (-(2 * Real.pi * k)) one_pos, hfh, hrep] with ω h1 h2 h3
    rw [affinePullback_rotation, affineReroot_rotation_eq _ k h2] at h1
    exact h1.trans h3
  exact ⟨hfh, ae_all_iff.2 hper⟩

/-- **Positive-scale identity with the integer removed.** Under the hypotheses of
`witness_period_identity`, for `s > 0`, almost surely and simultaneously for every `m : ℤ`,
`Φ (K(s·, s·) + m · 2πχ) = affineReroot 0 s 0 (L ω)`. -/
theorem witness_scale_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (χ : ℝ)
    (K : Ω → ℝ → ℂ → ℝ) (L : Ω → C(ℝ, ℂ)) (Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ))
    (hrep : ∀ᵐ ω ∂P, L ω = Φ (K ω))
    (hcov : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s →
      ∀ᵐ ω ∂P, Φ (affinePullback χ z₀ s φ (K ω)) = affineReroot z₀ s φ (L ω))
    (htr : ∀ᵐ ω ∂P, Tendsto (L ω) (cocompact ℝ) (cocompact ℂ))
    (s : ℝ) (hs : 0 < s) :
    ∀ᵐ ω ∂P, ∀ m : ℤ,
      Φ (fun ρ w => K ω (s * ρ) ((s : ℂ) * w) + m * (2 * Real.pi * χ))
        = affineReroot 0 s 0 (L ω) := by
  obtain ⟨hfh, -⟩ := witness_period_identity P χ K L Φ hrep hcov htr
  have hm : ∀ m : ℤ, ∀ᵐ ω ∂P,
      Φ (fun ρ w => K ω (s * ρ) ((s : ℂ) * w) + m * (2 * Real.pi * χ))
        = affineReroot 0 s 0 (L ω) := by
    intro m
    filter_upwards [hcov 0 s (-(2 * Real.pi * m)) hs, hfh] with ω h1 h2
    rw [affinePullback_scale_rotation, affineReroot_scale_rotation_eq _ s m h2] at h1
    exact h1
  exact ae_all_iff.2 hm

/-- **Normalized positive-scale identity.** Let `A ω r w = K ω (s r) (s w) - U ω` be the rescaled
field with the shift `U`, let `a ω` be a normalizing constant and let `k = ⌊(U + a) / p⌋` for the period
`p = 2πχ`. Then almost surely `Φ (A - a + V) = affineReroot 0 s 0 (L ω)` with `V = U + a - k p ∈ [0, p)`. -/
theorem witness_scale_normalized_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : ℝ) (K : Ω → ℝ → ℂ → ℝ) (L : Ω → C(ℝ, ℂ)) (Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ))
    (hrep : ∀ᵐ ω ∂P, L ω = Φ (K ω))
    (hcov : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s →
      ∀ᵐ ω ∂P, Φ (affinePullback χ z₀ s φ (K ω)) = affineReroot z₀ s φ (L ω))
    (htr : ∀ᵐ ω ∂P, Tendsto (L ω) (cocompact ℝ) (cocompact ℂ))
    (s : ℝ) (hs : 0 < s) (A : Ω → ℝ → ℂ → ℝ) (a U : Ω → ℝ)
    (hKA : ∀ ω r w, K ω (s * r) ((s : ℂ) * w) = A ω r w + U ω) :
    ∀ᵐ ω ∂P,
      Φ (fun r w => A ω r w - a ω + (U ω + a ω
          - ((⌊(U ω + a ω) / (2 * Real.pi * χ)⌋ : ℤ) : ℝ) * (2 * Real.pi * χ)))
        = affineReroot 0 s 0 (L ω) := by
  filter_upwards [witness_scale_identity P χ K L Φ hrep hcov htr s hs] with ω hω
  have h := hω (-⌊(U ω + a ω) / (2 * Real.pi * χ)⌋)
  convert h using 2
  funext r w
  rw [hKA]
  push_cast
  ring

end LatticeProb.AffineScaleRotation

end
