/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L19R4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L19R3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc5

/-!
# DG Lemma 3.19 at `μ = μ_ĥ`: the pathwise step `E_𝕊(ĥ^tr, unit frame) ⟹ condition 1 for μ_ĥ`
(P2-DG105r)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`: (3.7) (DG:1032–1036) as used in
the proof of Lemma 3.21 (DG:1699–1706, the conditional law of `D_ĥ^ε(∂S, ∂S(1))` given the
coarse field dominates that of the unit-frame distance at level `T_S ε`), DG Lemma 3.2's
comparison `μ_ĥ` vs `μ_{ĥ^tr}` (DG:1005–1007, applied with `A = c n^{1/2}`, DG:1650) and DG's
condition 2 of `E_S` (DG:1643: the disks of small mass meeting `S(1/2)` stay in `S(3/4)`, so the
unrestricted distance is seen by the unit-frame measure).

For the cell map `T y = s y + c` (`s = 2^{-j}`) with inverse `f`:
* (3.7) on `T(B̄(u,13/280))`: `μ_ĥ(X) ≥ s^{2+γ²/2} e^{γ m_φ} μ_{ĥ'}(T^{-1}X)` (`ae_muHat_scale_set`);
* Lemma 3.2: `μ_{ĥ'^tr}(B) ≤ e^{γA} μ_{ĥ'}(B)` for `B ⊆ K₀` on `max_{K₀}|ĥ' − ĥ'^tr| ≤ A`;
* heavy grid balls (`l319_heavy`) keep every `μ_ĥ`-light ball meeting `T(𝕍̄_u)` inside
  `T(B̄(u,13/280))`;
* `dgLGDSet_ge_of_map` and `l319_cross_mono` (S3L19R1) give
  `D^ε_ĥ(A₀, ∂B₀) ≥ D^t_{ĥ'^tr}(𝕍̄_{u,5/8}, ∂𝕍̄_u; B̄(u,13/280))` for `t ≥ e^{γA} (s^{2+γ²/2}
  e^{γ m_φ})^{-1} ε`.
Own elementary glue for the bookkeeping.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail GMCIdent

/-- the inverse `y ↦ (y − c)/s` of the cell map `affineC s c` -/
def l319f (s : ℝ) (c : ℂ) (y : ℂ) : ℂ := ((s : ℂ))⁻¹ * (y - c)

/-- `l319f` as a homeomorphism -/
def l319fH {s : ℝ} (hs : 0 < s) (c : ℂ) : ℂ ≃ₜ ℂ where
  toFun := l319f s c
  invFun := affineC s c
  left_inv y := by
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    simp only [l319f, affineC]; field_simp; ring
  right_inv y := by
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    simp only [l319f, affineC]; field_simp; ring
  continuous_toFun := by unfold l319f; fun_prop
  continuous_invFun := continuous_affineC s c

lemma l319f_affineC {s : ℝ} (hs : 0 < s) (c y : ℂ) : l319f s c (affineC s c y) = y :=
  (l319fH hs c).left_inv' y |>.symm ▸ by
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    simp only [l319f, affineC]; field_simp; ring

lemma affineC_l319f {s : ℝ} (hs : 0 < s) (c y : ℂ) : affineC s c (l319f s c y) = y := by
  have : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [l319f, affineC]; field_simp; ring

lemma dist_l319f {s : ℝ} (hs : 0 < s) (c a b : ℂ) :
    dist (l319f s c a) (l319f s c b) = s⁻¹ * dist a b := by
  rw [dist_eq_norm, dist_eq_norm, l319f, l319f, ← mul_sub, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs]
  congr 1; congr 1; ring

lemma l312Box_sub_interior (c : ℂ) {l l' : ℝ} (h : l < l') :
    l312Box c l ⊆ interior (l312Box c l') := by
  have hopen : IsOpen {z : ℂ | |z.re - c.re| < l' / 2 ∧ |z.im - c.im| < l' / 2} := by
    show IsOpen ({z : ℂ | |z.re - c.re| < l' / 2} ∩ {z : ℂ | |z.im - c.im| < l' / 2})
    exact (isOpen_lt (by fun_prop) continuous_const).inter
      (isOpen_lt (by fun_prop) continuous_const)
  refine subset_trans ?_ (interior_maximal (fun z hz => ⟨hz.1.le, hz.2.le⟩) hopen)
  intro z hz
  have h2 : l / 2 < l' / 2 := by linarith
  exact ⟨hz.1.trans_lt h2, hz.2.trans_lt h2⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Lemma 3.2, lower comparison** (DG:1005–1007): on `max_K |ĥ'|, |ĥ'^tr| ≤ A/2`,
`e^{−γA} μ_{ĥ'^tr}(B) ≤ μ_{ĥ'}(B)` for `B ⊆ K` -/
lemma muTr_le_muHat {W' : WNSpace → Ω → ℝ} (hW' : IsWhiteNoise P W') {γ : ℝ} (hγ : 0 ≤ γ)
    {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) {A : ℝ} {ω : Ω}
    (hω : ∀ z ∈ ferniqueBox y b, |hatMod hW' hb hK z ω| ≤ A / 2 ∧ |trMod hW' hb hK z ω| ≤ A / 2)
    {B : Set ℂ} (hB : MeasurableSet B) (hBK : B ⊆ ferniqueBox y b) :
    ENNReal.ofReal (Real.exp (-(γ * A))) * muTr hW' γ hb hK ω B ≤ muHat hW' γ hb hK ω B := by
  obtain ⟨hc₁, -, -, -⟩ := hatMod_spec hW' hb hK
  obtain ⟨hc₂, -, -, -⟩ := trMod_spec hW' hb hK
  have e : muHat hW' γ hb hK ω = (muTr hW' γ hb hK ω).withDensity
      fun z => ENNReal.ofReal (Real.exp (γ * (trMod hW' hb hK z ω - hatMod hW' hb hK z ω))) :=
    muOfMod_eq_withDensity W' γ _ hc₁ hc₂ ω
  rw [e, withDensity_apply _ hB, ← setLIntegral_const]
  refine setLIntegral_mono' hB fun z hz => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  obtain ⟨h1, h2⟩ := hω z (hBK hz)
  have h3 : |trMod hW' hb hK z ω - hatMod hW' hb hK z ω| ≤ A := by
    calc _ ≤ |trMod hW' hb hK z ω| + |hatMod hW' hb hK z ω| := abs_sub _ _
      _ ≤ A / 2 + A / 2 := add_le_add h2 h1
      _ = A := by ring
  have := (abs_le.1 h3).1
  nlinarith

/-- **the pathwise step of DG Lemma 3.19 at `μ = μ_ĥ`** ((3.7), DG:1032–1036, 1699–1706, with
DG Lemma 3.2 and DG's condition 2, DG:1643): a.s., for the cell map `T = affineC s c`, a closed
`A₀` with `f(A₀) ⊆ 𝕍̄_{u,5/8}` and `B₀ ⊇ T(𝕍̄_u)`, if `ĥ_s ≥ m_φ` on `T(B̄(u,13/280))`,
`max_{K₀} |ĥ'|, |ĥ'^tr| ≤ A/2`, `t ≥ e^{γA} (s^{2+γ²/2} e^{γ m_φ})^{-1} ε` and the unit-frame
event `E_𝕊^t` with threshold `M` holds for `μ_{ĥ'^tr}`, then `D^ε_ĥ(A₀, ∂B₀) ≥ M`. -/
theorem ae_l319_scale (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {y₀ : ℂ} {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hK : ∀ z ∈ ferniqueBox y₀ b₀, Metric.ball z (1 / 10) ⊆ openSquare) (j : ℕ) (c : ℂ)
    (hTK : affineC ((2 : ℝ)⁻¹ ^ j) c '' ferniqueBox y₀ b₀ ⊆ interior (ferniqueBox y₀ b₀))
    (hDK : closedBall l319U l319r ⊆ interior (ferniqueBox y₀ b₀))
    {A₀ B₀ : Set ℂ} (hA₀c : IsClosed A₀)
    (hA₀ : ∀ y ∈ A₀, l319f ((2 : ℝ)⁻¹ ^ j) c y ∈ l312Box l319U (1 / 32))
    (hB₀ : ∀ y, l319f ((2 : ℝ)⁻¹ ^ j) c y ∈ l312Box l319U (1 / 20) → y ∈ B₀) :
    ∀ᵐ ω ∂P, ∀ ε mφ A t M : ℝ,
      (∀ x ∈ affineC ((2 : ℝ)⁻¹ ^ j) c '' closedBall l319U l319r,
        mφ ≤ hatDelta W P ((2 : ℝ)⁻¹ ^ j) x ω) →
      (∀ z ∈ ferniqueBox y₀ b₀, |hatMod (dgN5_wnScaleDy hW j c).1 hb₀ hK z ω| ≤ A / 2 ∧
        |trMod (dgN5_wnScaleDy hW j c).1 hb₀ hK z ω| ≤ A / 2) →
      Real.exp (γ * A) * ((((2 : ℝ)⁻¹ ^ j) ^ (2 + γ ^ 2 / 2) * Real.exp (γ * mφ))⁻¹ * ε) ≤ t →
      l319Ev (muTr (dgN5_wnScaleDy hW j c).1 γ hb₀ hK ω) t M →
      ENNReal.ofReal M ≤ (dgLGDSet (muHat hW γ hb₀ hK ω) ε univ A₀ (frontier B₀) : ℝ≥0∞) := by
  set s : ℝ := (2 : ℝ)⁻¹ ^ j with hsdef
  have hs : 0 < s := by positivity
  filter_upwards [ae_muHat_scale_set hW hγ hγ2 hb₀ hK j c hTK] with ω hsc ε mφ A t M hmφ hA ht hev
  set hW' := (dgN5_wnScaleDy hW j c).1
  set T := affineC s c with hTdef
  set f := l319f s c with hfdef
  set μ := muHat hW γ hb₀ hK ω
  set ν₀ := muHat hW' γ hb₀ hK ω
  set μt := muTr hW' γ hb₀ hK ω
  set C : ℝ := s ^ (2 + γ ^ 2 / 2) * Real.exp (γ * mφ) with hCdef
  have hC : 0 < C := by positivity
  have hfT : ∀ y, f (T y) = y := l319f_affineC hs c
  have hTf : ∀ y, T (f y) = y := affineC_l319f hs c
  have hpre : ∀ X : Set ℂ, T '' X = f ⁻¹' X := fun X =>
    congrFun (image_eq_preimage_of_inverse hfT hTf) X
  have hTpre : ∀ X : Set ℂ, T ⁻¹' (f ⁻¹' X) = X := fun X => by
    ext y; simp only [mem_preimage, hfT]
  have hfm : Measurable f := (l319fH hs c).continuous.measurable
  have hfd := dist_l319f hs c
  have hK0 : ferniqueBox y₀ b₀ ⊆ ferniqueBox y₀ b₀ := subset_rfl
  have hDK' : closedBall l319U l319r ⊆ ferniqueBox y₀ b₀ := hDK.trans interior_subset
  -- (3.7) on `T(B̄(u,13/280))`
  have hF1 : ∀ X : Set ℂ, MeasurableSet X → X ⊆ T '' closedBall l319U l319r →
      ENNReal.ofReal C * ν₀ (T ⁻¹' X) ≤ μ X := by
    intro X hX hXD
    have h := hsc X hX
    have hXS : X ⊆ T '' interior (ferniqueBox y₀ b₀) := hXD.trans (image_mono hDK)
    rw [Measure.restrict_apply hX, inter_eq_left.2 hXS] at h
    rw [h, hCdef, ENNReal.ofReal_mul (by positivity), mul_assoc]
    gcongr
    rw [← setLIntegral_const]
    refine setLIntegral_mono' (hX.preimage (continuous_affineC s c).measurable) fun y hy => ?_
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (hmφ (T y) (hXD hy)) hγ.le))
  have hε : ENNReal.ofReal ε ≤ ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (-(γ * A))) *
      ENNReal.ofReal t) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : C⁻¹ * ε ≤ Real.exp (-(γ * A)) * t := by
      rw [Real.exp_neg]
      have := mul_le_mul_of_nonneg_left ht (inv_pos.2 (Real.exp_pos (γ * A))).le
      rwa [← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul] at this
    have := mul_le_mul_of_nonneg_left h1 hC.le
    rwa [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] at this
  have hball : ∀ x ρ, 0 < ρ → (∃ p ∈ ball x ρ, p ∈ f ⁻¹' l312Box l319U (1 / 20)) →
      μ (ball x ρ) ≤ ENNReal.ofReal ε →
      ball (f x) (s⁻¹ * ρ) ⊆ closure (closedBall l319U l319r) ∧
        μt (ball (f x) (s⁻¹ * ρ)) ≤ ENNReal.ofReal t := by
    intro x ρ hρ ⟨p, hp, hpB⟩ hμ
    have hbe : f ⁻¹' ball (f x) (s⁻¹ * ρ) = ball x ρ := by
      ext y
      simp only [mem_preimage, mem_ball]
      rw [hfd]
      exact mul_lt_mul_iff_of_pos_left (inv_pos.2 hs)
    have hsub : ball (f x) (s⁻¹ * ρ) ⊆ closedBall l319U l319r := by
      by_contra hnot
      have hpu : ‖f p - l319U‖ ≤ 1 / 28 := by
        have := l312Box_sub_closedBall l319U hpB
        rwa [mem_closedBall, dist_eq_norm] at this
      have hfp : f p ∈ ball (f x) (s⁻¹ * ρ) := by
        rw [← hbe] at hp; exact hp
      have hgrid : ∀ i j : ℤ, ‖(⟨i * l319g, j * l319g⟩ : ℂ) - l319U‖ ≤ 1 / 28 + 3 / 560 + l319g →
          ENNReal.ofReal ε < (μ.map f) (ball ⟨i * l319g, j * l319g⟩ l319g) := by
        intro i j hij
        set w : ℂ := ⟨i * l319g, j * l319g⟩
        rw [Measure.map_apply hfm measurableSet_ball]
        have hwD : ball w l319g ⊆ closedBall l319U l319r := by
          intro x hx
          rw [mem_ball, dist_eq_norm] at hx
          rw [mem_closedBall, dist_eq_norm]
          have := norm_sub_le_norm_sub_add_norm_sub x w l319U
          norm_num at hij hx ⊢; linarith
        have h1 := hF1 _ (measurableSet_ball.preimage hfm)
          (by rw [hpre]; exact preimage_mono hwD)
        rw [hTpre] at h1
        have h2 := muTr_le_muHat hW' hγ.le hb₀ hK hA measurableSet_ball
          ((hwD.trans hDK'))
        have h3 := hev.1 i j hij
        calc ENNReal.ofReal ε ≤ ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (-(γ * A))) *
              ENNReal.ofReal t) := hε
          _ < ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (-(γ * A))) * μt (ball w l319g)) := by
            refine (ENNReal.mul_lt_mul_iff_right (by simpa using hC) ENNReal.ofReal_ne_top).2 ?_
            exact (ENNReal.mul_lt_mul_iff_right (by simpa using Real.exp_pos _)
              ENNReal.ofReal_ne_top).2 h3
          _ ≤ ENNReal.ofReal C * ν₀ (ball w l319g) := by gcongr
          _ ≤ _ := h1
      have hh := l319_heavy (μ := μ.map f) (by norm_num) (by norm_num) hgrid hfp hpu hnot
      rw [Measure.map_apply hfm measurableSet_ball, hbe] at hh
      exact absurd hμ (not_le.2 hh)
    refine ⟨by rw [closure_closedBall]; exact hsub, ?_⟩
    have hX : f ⁻¹' ball (f x) (s⁻¹ * ρ) ⊆ T '' closedBall l319U l319r := by
      rw [hpre]; exact preimage_mono hsub
    have h1 := hF1 _ (measurableSet_ball.preimage hfm) hX
    rw [hTpre, hbe] at h1
    have h2 := muTr_le_muHat hW' hγ.le hb₀ hK hA measurableSet_ball (hsub.trans hDK')
    have h4 : ν₀ (ball (f x) (s⁻¹ * ρ)) ≤ ENNReal.ofReal C⁻¹ * ENNReal.ofReal ε := by
      calc ν₀ (ball (f x) (s⁻¹ * ρ)) = ENNReal.ofReal C⁻¹ * (ENNReal.ofReal C *
            ν₀ (ball (f x) (s⁻¹ * ρ))) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hC).le, inv_mul_cancel₀ hC.ne',
              ENNReal.ofReal_one, one_mul]
        _ ≤ _ := by gcongr; exact h1.trans hμ
    have h5 : ENNReal.ofReal (Real.exp (-(γ * A))) * μt (ball (f x) (s⁻¹ * ρ)) ≤
        ENNReal.ofReal (Real.exp (-(γ * A))) * ENNReal.ofReal t := by
      refine h2.trans (h4.trans ?_)
      rw [← ENNReal.ofReal_mul (inv_pos.2 hC).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left ht (Real.exp_pos (-(γ * A))).le
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at this
      exact this
    exact (ENNReal.mul_le_mul_iff_right (by simpa using Real.exp_pos _) ENNReal.ofReal_ne_top).1 h5
  have hAB : A₀ ⊆ interior (f ⁻¹' l312Box l319U (1 / 20)) := by
    have e := (l319fH hs c).preimage_interior (l312Box l319U (1 / 20))
    rw [show ⇑(l319fH hs c) = f from rfl] at e
    rw [← e]
    intro y hy
    exact l312Box_sub_interior l319U (by norm_num) (hA₀ y hy)
  have hBc : IsClosed (f ⁻¹' l312Box l319U (1 / 20)) :=
    (isClosed_l312Box _ _).preimage (l319fH hs c).continuous
  have hB' : f '' frontier (f ⁻¹' l312Box l319U (1 / 20)) ⊆ frontier (l312Box l319U (1 / 20)) := by
    have e := (l319fH hs c).preimage_frontier (l312Box l319U (1 / 20))
    rw [show ⇑(l319fH hs c) = f from rfl] at e
    rw [← e]
    exact image_preimage_subset _ _
  have key := dgLGDSet_ge_of_map (μ := μ) (ν := μt) (inv_pos.2 hs) hfd hA₀c hBc hAB
    (A' := l312Box l319U (1 / 32)) (fun _ ⟨y, hy, e⟩ => e ▸ hA₀ y hy) hB'
    (U' := closedBall l319U l319r) hball
  have cross := l319_cross_mono (μ := μ) (ε := ε) hA₀c hAB (T := B₀) fun y hy => hB₀ y hy
  calc ENNReal.ofReal M ≤ _ := hev.2
    _ ≤ _ := ENat.toENNReal_le.2 key
    _ ≤ _ := ENat.toENNReal_le.2 cross

end DG
end LQGMetric
