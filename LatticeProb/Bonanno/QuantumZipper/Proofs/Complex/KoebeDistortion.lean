/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.KoebeDistortion at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeCovering
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Growth and distortion for univalent maps (EXT-CA nodes K2, K4)

For `f` injective and holomorphic on `ball c r`:

* `norm_sub_le_growth` (local growth): `‖w − c‖ ≤ 3r/4 → ‖f w − f c‖ ≤ M r ‖f'(c)‖`,
  `M = koebeGrowthConst = e^144 − 1`;
* `norm_deriv_le_of_dist_le_half`: `‖w − c‖ ≤ r/2 → ‖f'(w)‖ ≤ 8M ‖f'(c)‖`;
* `mul_norm_deriv2_le` (K2, weak Bieberbach inequality, pre-Schwarzian form):
  `r ‖f''(c)‖ ≤ C₂ ‖f'(c)‖`, `C₂ = koebeDistExp = 2 (8M + 1)`;
  for schlicht `f` this reads `‖f''(0)‖ ≤ C₂` (`IsSchlicht.norm_deriv2_le`);
* `norm_deriv_le_distortion`, `distortion_le_norm_deriv` (K4, distortion theorem with exponent
  `C₂`): with `s = ‖w − c‖ / r`,
  `‖f'(c)‖ (1 − s)^C₂ ≤ ‖f'(w)‖ ≤ ‖f'(c)‖ (1 − s)^(−C₂)`;
* `norm_sub_le_growth_global` (K4, growth): `‖f w − f c‖ ≤ ‖w − c‖ ‖f'(c)‖ (1 − s)^(−C₂)`.

## Sources and deviations

The distortion theorem is Garnett–Marshall, *Harmonic Measure*, Ch. I, Theorem 4.5,
(4.16)–(4.17), p. 22 (= Pommerenke, *Univalent Functions*, Theorem 1.6, p. 21). We follow their
proof: a bound on the second coefficient (their (4.8), `|a₂| ≤ 2`) applied at every point via
a change of variables (their (4.19)–(4.20)), then integration along the radius (their (4.21)).
Deviations (recorded in `DEVIATIONS.md`, D-KOEBE):

* The coefficient bound (4.8) is proved with the area theorem in the sources. We prove instead
  the non-sharp `r ‖f''(c)‖ ≤ C₂ ‖f'(c)‖` from the covering theorem of `KoebeCovering.lean`:
  Koebe's two-sided estimate gives `c₁ ρ(u) |f'(u)| ≤ dist(f u, ∂Ω) ≤ r |f'(c)| + |f u − f c|`
  along the segment `[c, w]`, which is a linear differential inequality; Gronwall's lemma
  (mathlib `norm_le_gronwallBound_of_norm_deriv_right_le`) gives the local growth bound, and
  Cauchy/Schwarz estimates give the bounds on `f'` and `f''` (own argument, standard technique).
* The change of variables (4.19) by a disk automorphism is replaced by applying K2 on the
  largest disk `ball u (r − ‖u − c‖)` centered at `u` (no Möbius maps needed); the radial
  integration (4.21) is replaced by Gronwall's lemma in the logarithmic parameter
  `τ = −log(1 − t)`, where the inequality has constant coefficients.
* Consequently the exponents are `C₂` instead of the sharp `2`, `3`; the constants are universal.
-/

noncomputable section

open Set Metric Filter Complex
open scoped Topology Real

namespace QuantumZipper.CA.Koebe

/-- The local growth constant `M = e^144 − 1`. -/
def koebeGrowthConst : ℝ := Real.exp 144 - 1

/-- The distortion exponent `C₂ = 2 (8M + 1)` (sharp value: `2`). -/
def koebeDistExp : ℝ := 2 * (8 * koebeGrowthConst + 1)

theorem koebeGrowthConst_pos : 0 < koebeGrowthConst := by
  unfold koebeGrowthConst
  have := Real.add_one_lt_exp (show (144 : ℝ) ≠ 0 by norm_num)
  linarith

theorem koebeDistExp_pos : 0 < koebeDistExp := by
  unfold koebeDistExp; have := koebeGrowthConst_pos; positivity

/-- Koebe's lower estimate at an interior point, relative to the image of the big disk. -/
theorem koebeCovConst_mul_le_infDist_of_mem {f : ℂ → ℂ} {c u : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) (hu : u ∈ ball c r) :
    koebeCovConst * (r - dist u c) * ‖deriv f u‖ ≤ infDist (f u) (f '' ball c r)ᶜ := by
  have hr : 0 < r := pos_of_mem_ball hu
  have hρ : 0 < r - dist u c := sub_pos.2 (mem_ball.1 hu)
  have hsub : ball u (r - dist u c) ⊆ ball c r := ball_subset_ball' (by linarith)
  have h1 := koebeCovConst_mul_le_infDist hρ (hd.mono hsub) (hinj.mono hsub)
  have hne : ((f '' ball c r)ᶜ).Nonempty := by
    rw [nonempty_compl]; exact image_ball_ne_univ hr hd hinj
  exact h1.trans (infDist_le_infDist_of_subset
    (compl_subset_compl.2 (image_mono hsub)) hne)

/-- Derivative of the affine path `t ↦ c + g(t) e` for a real function `g`. -/
theorem hasDerivAt_affinePath {g : ℝ → ℝ} {g' t : ℝ} (hg : HasDerivAt g g' t) (c e : ℂ) :
    HasDerivAt (fun τ : ℝ => c + (g τ : ℂ) * e) ((g' : ℂ) * e) t :=
  (hg.ofReal_comp.mul_const e).const_add c

/-- **Local growth.** If `‖w − c‖ ≤ 3r/4` then `‖f w − f c‖ ≤ M r ‖f'(c)‖`. -/
theorem norm_sub_le_growth {f : ℂ → ℂ} {c w : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) (hr : 0 < r)
    (hw : dist w c ≤ 3 / 4 * r) :
    ‖f w - f c‖ ≤ koebeGrowthConst * r * ‖deriv f c‖ := by
  set ℓ : ℝ → ℂ := fun t => c + (t : ℂ) * (w - c) with hℓ
  have hℓmem : ∀ t ∈ Icc (0 : ℝ) 1, ℓ t ∈ ball c r ∧ r / 4 ≤ r - dist (ℓ t) c := by
    intro t ht
    have hdist : dist (ℓ t) c = t * dist w c := by
      show dist (c + (t : ℂ) * (w - c)) c = _
      rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht.1]
    have : dist (ℓ t) c ≤ 3 / 4 * r := by
      rw [hdist]; nlinarith [ht.1, ht.2, dist_nonneg (x := w) (y := c)]
    exact ⟨mem_ball.2 (by linarith), by linarith⟩
  have hℓd : ∀ t, HasDerivAt ℓ (w - c) t := fun t => by
    have h := hasDerivAt_affinePath (hasDerivAt_id t) c (w - c)
    simp only [id, Complex.ofReal_one, one_mul] at h
    exact h
  set φ : ℝ → ℂ := fun t => f (ℓ t) - f c with hφ
  have hφd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ (deriv f (ℓ t) * (w - c)) t := by
    intro t ht
    have hfd : HasDerivAt f (deriv f (ℓ t)) (ℓ t) :=
      (hd.differentiableAt (isOpen_ball.mem_nhds (hℓmem t ht).1)).hasDerivAt
    exact (hfd.comp t (hℓd t)).sub_const (f c)
  set S := (f '' ball c r)ᶜ
  have hdc : infDist (f c) S ≤ r * ‖deriv f c‖ := infDist_le_mul_norm_deriv hr hd hinj
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖deriv f (ℓ t) * (w - c)‖ ≤ 144 * ‖φ t‖ + 144 * r * ‖deriv f c‖ := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    obtain ⟨hmem, hrad⟩ := hℓmem t ht'
    have h1 := koebeCovConst_mul_le_infDist_of_mem hd hinj hmem
    have h2 : infDist (f (ℓ t)) S ≤ infDist (f c) S + ‖φ t‖ := by
      have := infDist_le_infDist_add_dist (x := f (ℓ t)) (y := f c) (s := S)
      rwa [dist_eq_norm] at this
    have hX := norm_nonneg (deriv f (ℓ t))
    have hwc : ‖w - c‖ ≤ 3 / 4 * r := by rwa [← dist_eq_norm]
    rw [norm_mul]
    unfold koebeCovConst at h1
    have h3 : r / 4 * ‖deriv f (ℓ t)‖ ≤ (r - dist (ℓ t) c) * ‖deriv f (ℓ t)‖ :=
      mul_le_mul_of_nonneg_right hrad hX
    nlinarith [mul_le_mul_of_nonneg_left hwc hX]
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := φ) (a := 0) (b := 1)
    (δ := 0) (K := 144) (ε := 144 * r * ‖deriv f c‖)
    (fun t ht => (hφd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hφd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [hφ, hℓ]) hbound 1 ⟨zero_le_one, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 (by norm_num)] at hgr
  have hφ1 : φ 1 = f w - f c := by simp [hφ, hℓ]
  rw [hφ1] at hgr
  unfold koebeGrowthConst
  calc ‖f w - f c‖ ≤ 0 * Real.exp (144 * (1 - 0)) +
        144 * r * ‖deriv f c‖ / 144 * (Real.exp (144 * (1 - 0)) - 1) := hgr
    _ = (Real.exp 144 - 1) * r * ‖deriv f c‖ := by ring_nf

/-- **Local derivative bound.** If `‖w − c‖ ≤ r/2` then `‖f'(w)‖ ≤ 8 M ‖f'(c)‖`. -/
theorem norm_deriv_le_of_dist_le_half {f : ℂ → ℂ} {c w : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) (hr : 0 < r)
    (hw : dist w c ≤ r / 2) :
    ‖deriv f w‖ ≤ 8 * koebeGrowthConst * ‖deriv f c‖ := by
  have hsub : ball w (r / 4) ⊆ ball c r := ball_subset_ball' (by linarith)
  have hgw := norm_sub_le_growth hd hinj hr (w := w) (by linarith)
  have hmaps : MapsTo f (ball w (r / 4)) (closedBall (f w) (2 * koebeGrowthConst * r *
      ‖deriv f c‖)) := by
    intro z hz
    have hzc : dist z c ≤ 3 / 4 * r := by
      have := dist_triangle z w c
      have := mem_ball.1 hz
      linarith
    have hgz := norm_sub_le_growth hd hinj hr hzc
    rw [mem_closedBall, dist_eq_norm]
    calc ‖f z - f w‖ = ‖(f z - f c) - (f w - f c)‖ := by ring_nf
      _ ≤ ‖f z - f c‖ + ‖f w - f c‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have := norm_deriv_le_div_of_mapsTo_ball (hd.mono hsub) hmaps (by linarith)
  calc ‖deriv f w‖ ≤ 2 * koebeGrowthConst * r * ‖deriv f c‖ / (r / 4) := this
    _ = 8 * koebeGrowthConst * ‖deriv f c‖ := by field_simp; ring

/-- **K2 (weak Bieberbach inequality).** `r ‖f''(c)‖ ≤ C₂ ‖f'(c)‖`. -/
theorem mul_norm_deriv2_le {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) (hr : 0 < r) :
    r * ‖deriv (deriv f) c‖ ≤ koebeDistExp * ‖deriv f c‖ := by
  have hsub : ball c (r / 2) ⊆ ball c r := ball_subset_ball (by linarith)
  have hmaps : MapsTo (deriv f) (ball c (r / 2))
      (closedBall (deriv f c) ((8 * koebeGrowthConst + 1) * ‖deriv f c‖)) := by
    intro z hz
    have := norm_deriv_le_of_dist_le_half hd hinj hr (w := z) (mem_ball.1 hz).le
    rw [mem_closedBall, dist_eq_norm]
    calc ‖deriv f z - deriv f c‖ ≤ ‖deriv f z‖ + ‖deriv f c‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have := norm_deriv_le_div_of_mapsTo_ball ((hd.deriv isOpen_ball).mono hsub) hmaps
    (by linarith)
  rw [le_div_iff₀ (by linarith)] at this
  unfold koebeDistExp
  linarith

/-- The logarithmic radial path used for the distortion theorem, with its basic properties. -/
theorem radialPath_props {c e : ℂ} {r : ℝ} (hr : 0 < r) (he : ‖e‖ = 1) (τ : ℝ) (hτ : 0 ≤ τ) :
    c + ((r * (1 - Real.exp (-τ)) : ℝ) : ℂ) * e ∈ ball c r ∧
    r - dist (c + ((r * (1 - Real.exp (-τ)) : ℝ) : ℂ) * e) c = r * Real.exp (-τ) ∧
    HasDerivAt (fun τ : ℝ => c + ((r * (1 - Real.exp (-τ)) : ℝ) : ℂ) * e)
      (((r * Real.exp (-τ)) : ℝ) * e) τ := by
  have hexp : 0 < Real.exp (-τ) := Real.exp_pos _
  have hexp1 : Real.exp (-τ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hdist : dist (c + ((r * (1 - Real.exp (-τ)) : ℝ) : ℂ) * e) c =
      r * (1 - Real.exp (-τ)) := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, he, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
  refine ⟨mem_ball.2 (by rw [hdist]; nlinarith), by rw [hdist]; ring, ?_⟩
  have hg : HasDerivAt (fun τ : ℝ => r * (1 - Real.exp (-τ))) (r * Real.exp (-τ)) τ := by
    have := ((Real.hasDerivAt_exp (-τ)).comp τ (hasDerivAt_neg τ)).const_sub 1 |>.const_mul r
    exact this.congr_deriv (by ring)
  exact hasDerivAt_affinePath hg c e

/-- Gronwall along the logarithmic radial path: two-sided distortion (shared computation).
Returns the bounds `‖f'(w)‖ ≤ ‖f'(c)‖ e^{C₂ T}` and `‖f'(w)‖⁻¹ ≤ ‖f'(c)‖⁻¹ e^{C₂ T}` with
`T = −log(1 − s)`. -/
theorem distortion_aux {f : ℂ → ℂ} {c w : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) (hw : w ∈ ball c r) :
    ‖deriv f w‖ ≤ ‖deriv f c‖ * Real.exp (koebeDistExp * -Real.log (1 - dist w c / r)) ∧
    ‖deriv f w‖⁻¹ ≤ ‖deriv f c‖⁻¹ * Real.exp (koebeDistExp * -Real.log (1 - dist w c / r)) := by
  have hr : 0 < r := pos_of_mem_ball hw
  have hs1 : dist w c / r < 1 := (div_lt_one hr).2 (mem_ball.1 hw)
  have hs0 : 0 ≤ dist w c / r := div_nonneg dist_nonneg hr.le
  have hcB : c ∈ ball c r := mem_ball_self hr
  have hopen := isOpen_ball (x := c) (ε := r)
  have hne : ∀ z ∈ ball c r, deriv f z ≠ 0 := fun z hz =>
    deriv_ne_zero_of_injOn isOpen_ball hd hinj hz
  rcases eq_or_ne w c with rfl | hwc
  · simp
  set T := -Real.log (1 - dist w c / r) with hT
  have hT0 : 0 ≤ T := by
    rw [hT, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  set e : ℂ := (w - c) / ((‖w - c‖ : ℝ) : ℂ) with he
  have hwc' : 0 < ‖w - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hwc)
  have henorm : ‖e‖ = 1 := by
    rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwc', div_self hwc'.ne']
  set ℓ : ℝ → ℂ := fun τ => c + ((r * (1 - Real.exp (-τ)) : ℝ) : ℂ) * e with hℓ
  have hℓT : ℓ T = w := by
    have h1 : Real.exp (-T) = 1 - dist w c / r := by
      rw [hT, neg_neg, Real.exp_log (by linarith)]
    simp only [hℓ, h1]
    rw [he, dist_eq_norm]
    have : r * (1 - (1 - ‖w - c‖ / r)) = ‖w - c‖ := by
      rw [sub_sub_cancel, mul_div_cancel₀ _ hr.ne']
    have hne' : ((‖w - c‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hwc'.ne'
    rw [this, mul_div_cancel₀ _ hne']
    ring
  have hP : ∀ τ ∈ Icc 0 T, ℓ τ ∈ ball c r ∧ r - dist (ℓ τ) c = r * Real.exp (-τ) ∧
      HasDerivAt ℓ (((r * Real.exp (-τ)) : ℝ) * e) τ :=
    fun τ hτ => radialPath_props (c := c) hr henorm τ hτ.1
  -- the derivative of `f'` along the path
  have hψd : ∀ τ ∈ Icc 0 T, HasDerivAt (fun τ => deriv f (ℓ τ))
      (deriv (deriv f) (ℓ τ) * (((r * Real.exp (-τ)) : ℝ) : ℂ) * e) τ := by
    intro τ hτ
    have h1 : HasDerivAt (deriv f) (deriv (deriv f) (ℓ τ)) (ℓ τ) :=
      ((hd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds (hP τ hτ).1)).hasDerivAt
    exact (h1.comp τ (hP τ hτ).2.2).congr_deriv (by ring)
  have hK : ∀ τ ∈ Icc 0 T, ‖deriv (deriv f) (ℓ τ) * (((r * Real.exp (-τ)) : ℝ) : ℂ) * e‖ ≤
      koebeDistExp * ‖deriv f (ℓ τ)‖ := by
    intro τ hτ
    obtain ⟨hmem, hrad, -⟩ := hP τ hτ
    have hsub : ball (ℓ τ) (r * Real.exp (-τ)) ⊆ ball c r := by
      apply ball_subset_ball'; rw [← hrad]; linarith
    have := mul_norm_deriv2_le (hd.mono hsub) (hinj.mono hsub) (by positivity)
    rw [norm_mul, norm_mul, henorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  constructor
  · have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := fun τ => deriv f (ℓ τ)) (a := 0) (b := T) (δ := ‖deriv f c‖) (K := koebeDistExp)
      (ε := 0) (fun τ hτ => (hψd τ hτ).continuousAt.continuousWithinAt)
      (fun τ hτ => (hψd τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt)
      (by simp [hℓ]) (fun τ hτ => by simpa using hK τ (Ico_subset_Icc_self hτ)) T
      ⟨hT0, le_rfl⟩
    rw [gronwallBound_ε0, sub_zero] at hgr
    simpa [hℓT] using hgr
  · have hχd : ∀ τ ∈ Icc 0 T, HasDerivAt (fun τ => (deriv f (ℓ τ))⁻¹)
        (-(deriv (deriv f) (ℓ τ) * (((r * Real.exp (-τ)) : ℝ) : ℂ) * e) /
          (deriv f (ℓ τ)) ^ 2) τ :=
      fun τ hτ => (hψd τ hτ).inv (hne _ (hP τ hτ).1)
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := fun τ => (deriv f (ℓ τ))⁻¹) (a := 0) (b := T) (δ := ‖deriv f c‖⁻¹)
      (K := koebeDistExp) (ε := 0) (fun τ hτ => (hχd τ hτ).continuousAt.continuousWithinAt)
      (fun τ hτ => (hχd τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt)
      (by simp [hℓ])
      (fun τ hτ => by
        have hτ' := Ico_subset_Icc_self hτ
        have hpos : 0 < ‖deriv f (ℓ τ)‖ := norm_pos_iff.2 (hne _ (hP τ hτ').1)
        have hne' := hpos.ne'
        rw [norm_div, norm_neg, norm_pow, norm_inv, add_zero, div_le_iff₀ (by positivity)]
        calc _ ≤ koebeDistExp * ‖deriv f (ℓ τ)‖ := hK τ hτ'
          _ = koebeDistExp * ‖deriv f (ℓ τ)‖⁻¹ * ‖deriv f (ℓ τ)‖ ^ 2 := by
            field_simp) T ⟨hT0, le_rfl⟩
    rw [gronwallBound_ε0, sub_zero] at hgr
    simpa [hℓT] using hgr

theorem exp_mul_neg_log_eq_rpow {C s : ℝ} (hs : s < 1) :
    Real.exp (C * -Real.log (1 - s)) = (1 - s) ^ (-C) := by
  rw [Real.rpow_def_of_pos (by linarith)]; ring_nf

/-- **K4, distortion theorem, lower bound** (exponent `C₂`; Garnett–Marshall Thm I.4.5 (4.17)). -/
theorem distortion_le_norm_deriv {f : ℂ → ℂ} {c w : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) (hw : w ∈ ball c r) :
    ‖deriv f c‖ * (1 - dist w c / r) ^ koebeDistExp ≤ ‖deriv f w‖ := by
  have hr : 0 < r := pos_of_mem_ball hw
  have hs1 : dist w c / r < 1 := (div_lt_one hr).2 (mem_ball.1 hw)
  have hcB : c ∈ ball c r := mem_ball_self hr
  have hpc : 0 < ‖deriv f c‖ := norm_pos_iff.2 (deriv_ne_zero_of_injOn isOpen_ball hd hinj hcB)
  have hpw : 0 < ‖deriv f w‖ := norm_pos_iff.2 (deriv_ne_zero_of_injOn isOpen_ball hd hinj hw)
  have h := (distortion_aux hd hinj hw).2
  rw [exp_mul_neg_log_eq_rpow hs1, Real.rpow_neg (by linarith)] at h
  have hq : 0 < (1 - dist w c / r) ^ koebeDistExp := Real.rpow_pos_of_pos (by linarith) _
  rw [← mul_inv, inv_le_inv₀ hpw (by positivity)] at h
  exact h

end QuantumZipper.CA.Koebe
