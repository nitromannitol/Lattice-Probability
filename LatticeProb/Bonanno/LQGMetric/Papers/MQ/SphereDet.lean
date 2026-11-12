/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.MQ.SphereDet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Meas.GeodCurve
import LatticeProb.Bonanno.LQGMetric.Metric.WeylBasic
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling

/-!
# MQ Theorem 1.2: the deterministic monotonicity step (task P2-MQ2)

Source: J. Miller, W. Qian, arXiv:1812.03913, `literature/src/1812.03913/lqg_geodesics.tex`,
proof of Theorem 1.2, l. 502–506: "`X_i^α` is strictly increasing and continuous in `α` by
part (iii) of Assumption 1.1 [Weyl scaling]. Thus if we take `A` to be uniform in `[0,1]` then
the probability that `X_i^A = X_j` is equal to `0`."

We use MQ's bump/shift idea in the following form (decision D-C4, `decisions/DEC-C.md`
l. 273–295: a fixed countable family of bumps `φ ≥ 0`; see `SphereMain.lean` for the
deviation from MQ's `E(R,ε,δ)`/`X_ℓ` bookkeeping). For a field `g` and a bump `φ`
(`φ = 1` on `B(q, 2ρ)`), write `F(a) = D_{g+aφ}(x, y)`. By Weyl scaling `a ↦ F(a)` is
nondecreasing (`weylScale_mono_of_le`). The "tie" event at level `a` is

* `F(a+1) ≤ F(a)` (some `D_{g+aφ}`-geodesic avoids the bump), and
* some `w ∈ B̄(q, ρ)` lies on a `D_{g+aφ}`-geodesic from `x` to `y`.

`shift_set_subsingleton`: for `a ∈ [0,1]` this happens for at most one `a`, because along
paths ending in `B(q, 2ρ)` the Weyl cost strictly increases with `a`
(`weylScale_add_le_of_gap`, MQ's "strictly increasing"). Own elementary proofs of the
deterministic facts (MQ states them without proof).

`weylScale_le_of_isGeod01`: a geodesic on which `f` vanishes shows `e^{ξ f}·D(z,w) ≤ D(z,w)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.MQ

open MetricGeometry

/-- unit speed ⇒ `D(P s, P t) ≤ |s − t|` -/
lemma dist_le_of_unitSpeed {D : ContMetric} {L : ℝ} {P : ℝ → ℂ}
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) {s t : ℝ} (hs : s ∈ Icc 0 L)
    (ht : t ∈ Icc 0 L) : D.1 (P s, P t) ≤ |s - t| := by
  have h := (lipschitzOnWith_of_hasUnitSpeedOn hu).dist_le_mul s hs t ht
  have e : dist ((D.pt ∘ P) s) ((D.pt ∘ P) t) = D.1 (P s, P t) := rfl
  rw [e, NNReal.coe_one, one_mul, Real.dist_eq] at h
  exact h

/-- **Strict monotonicity of the Weyl cost (MQ l. 503).** If `f₁ ≤ f₂`, and `f₁ ≡ b₁ < b₂ ≡ f₂`
on `B(w, ρ)`, `|x − w| ≥ ρ`, then `e^{ξ f₁}·D(x,w) + c ≤ e^{ξ f₂}·D(x,w)` for some `c > 0`: the
last `δ/2` units of `D`-length of every path from `x` to `w` lie in `B(w, ρ)`. -/
theorem weylScale_add_le_of_gap {ξ : ℝ} (hξ : 0 < ξ) (D0 : ContMetric) {f₁ f₂ : C(ℂ, ℝ)}
    (h12 : ∀ z, f₁ z ≤ f₂ z) {x w : ℂ} {ρ b₁ b₂ : ℝ} (hρ : 0 < ρ)
    (hb₁ : ∀ z, ‖z - w‖ < ρ → f₁ z = b₁) (hb₂ : ∀ z, ‖z - w‖ < ρ → f₂ z = b₂) (hb : b₁ < b₂)
    (hx : ρ ≤ ‖x - w‖) :
    ∃ c : ℝ, 0 < c ∧ weylScale ξ f₁ D0 x w + ENNReal.ofReal c ≤ weylScale ξ f₂ D0 x w := by
  obtain ⟨δ, hδ, hsmall⟩ := D0.2.euclidean_of_small w ρ hρ
  have he : Real.exp (ξ * b₁) < Real.exp (ξ * b₂) :=
    Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hb hξ)
  refine ⟨(Real.exp (ξ * b₂) - Real.exp (ξ * b₁)) * (δ / 2),
    mul_pos (sub_pos.2 he) (half_pos hδ), ?_⟩
  rw [← weylScaleOn_univ ξ f₂]
  refine le_weylScaleOn fun L P hL hc hu h0 h1 _ => ?_
  have hLδ : δ / 2 ≤ L := by
    by_contra hlt
    push Not at hlt
    have h := dist_le_of_unitSpeed hu (⟨le_rfl, hL⟩ : (0 : ℝ) ∈ Icc 0 L) ⟨hL, le_rfl⟩
    rw [h0, h1, zero_sub, abs_neg, abs_of_nonneg hL] at h
    have := hsmall x (by rw [D0.2.symm]; linarith)
    rw [norm_sub_rev] at this
    linarith
  set τ := L - δ / 2 with hτ
  have hτ0 : 0 ≤ τ := by linarith
  have hsplit : Icc (0 : ℝ) L = Icc 0 τ ∪ Ioc τ L :=
    (Icc_union_Ioc_eq_Icc hτ0 (by linarith)).symm
  have hin : ∀ t ∈ Ioc τ L, ‖P t - w‖ < ρ := fun t ht => by
    have h := dist_le_of_unitSpeed hu ⟨by linarith [ht.1], ht.2⟩ ⟨hL, le_rfl⟩
    rw [h1, abs_of_nonpos (by linarith [ht.2])] at h
    have := hsmall (P t) (by rw [D0.2.symm]; linarith [ht.1])
    rwa [norm_sub_rev] at this
  have hdisj : Disjoint (Icc 0 τ) (Ioc τ L) :=
    Set.disjoint_left.2 fun t h1 h2 => absurd h1.2 (not_le.2 h2.1)
  have hvol : volume (Ioc τ L) = ENNReal.ofReal (δ / 2) := by
    rw [Real.volume_Ioc]; congr 1; rw [hτ]; ring
  have e₁ : ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f₁ (P t))) =
      (∫⁻ t in Icc 0 τ, ENNReal.ofReal (Real.exp (ξ * f₁ (P t)))) +
        ENNReal.ofReal (Real.exp (ξ * b₁)) * ENNReal.ofReal (δ / 2) := by
    rw [hsplit, lintegral_union measurableSet_Ioc hdisj,
      setLIntegral_congr_fun measurableSet_Ioc
        (g := fun _ => ENNReal.ofReal (Real.exp (ξ * b₁)))
        (fun t ht => by simp only [hb₁ _ (hin t ht)]), setLIntegral_const, hvol]
  have e₂ : ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f₂ (P t))) =
      (∫⁻ t in Icc 0 τ, ENNReal.ofReal (Real.exp (ξ * f₂ (P t)))) +
        ENNReal.ofReal (Real.exp (ξ * b₂)) * ENNReal.ofReal (δ / 2) := by
    rw [hsplit, lintegral_union measurableSet_Ioc hdisj,
      setLIntegral_congr_fun measurableSet_Ioc
        (g := fun _ => ENNReal.ofReal (Real.exp (ξ * b₂)))
        (fun t ht => by simp only [hb₂ _ (hin t ht)]), setLIntegral_const, hvol]
  have hmono : ∫⁻ t in Icc 0 τ, ENNReal.ofReal (Real.exp (ξ * f₁ (P t))) ≤
      ∫⁻ t in Icc 0 τ, ENNReal.ofReal (Real.exp (ξ * f₂ (P t))) :=
    lintegral_mono fun t => ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (h12 _) hξ.le))
  have hW1 : weylScale ξ f₁ D0 x w ≤
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f₁ (P t))) := by
    rw [← weylScaleOn_univ]
    exact weylScaleOn_le hL hc hu h0 h1 (fun _ _ => mem_univ _)
  have hδ2 : (0 : ℝ) ≤ δ / 2 := by positivity
  have hsum : ENNReal.ofReal (Real.exp (ξ * b₁)) * ENNReal.ofReal (δ / 2) +
      ENNReal.ofReal ((Real.exp (ξ * b₂) - Real.exp (ξ * b₁)) * (δ / 2)) =
      ENNReal.ofReal (Real.exp (ξ * b₂)) * ENNReal.ofReal (δ / 2) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le hδ2)
        (mul_nonneg (sub_pos.2 he).le hδ2)]
    congr 1; ring
  calc weylScale ξ f₁ D0 x w +
        ENNReal.ofReal ((Real.exp (ξ * b₂) - Real.exp (ξ * b₁)) * (δ / 2))
      ≤ ((∫⁻ t in Icc 0 τ, ENNReal.ofReal (Real.exp (ξ * f₁ (P t)))) +
          ENNReal.ofReal (Real.exp (ξ * b₁)) * ENNReal.ofReal (δ / 2)) +
        ENNReal.ofReal ((Real.exp (ξ * b₂) - Real.exp (ξ * b₁)) * (δ / 2)) := by
        rw [← e₁]; gcongr
    _ = (∫⁻ t in Icc 0 τ, ENNReal.ofReal (Real.exp (ξ * f₁ (P t)))) +
          ENNReal.ofReal (Real.exp (ξ * b₂)) * ENNReal.ofReal (δ / 2) := by
        rw [add_assoc, hsum]
    _ ≤ (∫⁻ t in Icc 0 τ, ENNReal.ofReal (Real.exp (ξ * f₂ (P t)))) +
          ENNReal.ofReal (Real.exp (ξ * b₂)) * ENNReal.ofReal (δ / 2) := by gcongr
    _ = _ := e₂.symm

/-- **MQ l. 503–505 (deterministic core).** With `ofReal (D_a(z,w)) = e^{ξ aφ}·D_0(z,w)` for all
`a` (Weyl scaling), `φ ≥ 0`, `φ = 1` on `B(q, 2ρ)` and `|x − q| ≥ 2ρ`, there is at most one
`a ∈ [0,1]` with `D_{a+1}(x,y) ≤ D_a(x,y)` and a point `w ∈ B̄(q,ρ)` on a `D_a`-geodesic from
`x` to `y`. -/
theorem shift_set_subsingleton {ξ : ℝ} (hξ : 0 < ξ) (D0 : ContMetric) (Ds : ℝ → ContMetric)
    (φ : C(ℂ, ℝ)) (hφ0 : ∀ z, 0 ≤ φ z) {q x y : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hφ1 : ∀ z, ‖z - q‖ < 2 * ρ → φ z = 1) (hx : 2 * ρ ≤ ‖x - q‖)
    (hW : ∀ (a : ℝ) (z w : ℂ), weylScale ξ (a • φ) D0 z w = ENNReal.ofReal ((Ds a).1 (z, w))) :
    {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧ (Ds (a + 1)).1 (x, y) ≤ (Ds a).1 (x, y) ∧
      ∃ w ∈ closedBall q ρ, (Ds a).1 (x, w) + (Ds a).1 (w, y) ≤ (Ds a).1 (x, y)}.Subsingleton := by
  have hmono : ∀ (a a' : ℝ) (z w : ℂ), a ≤ a' → (Ds a).1 (z, w) ≤ (Ds a').1 (z, w) := by
    intro a a' z w h
    have := weylScale_mono_of_le (D := D0) (z := z) (w := w) hξ.le (f := a • φ) (g := a' • φ)
      (fun u => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        exact mul_le_mul_of_nonneg_right h (hφ0 u))
    rwa [hW, hW, ENNReal.ofReal_le_ofReal_iff ((Ds a').nonneg z w)] at this
  have key : ∀ a₁ a₂ : ℝ, a₁ < a₂ →
      (a₁ ∈ Icc (0 : ℝ) 1 ∧ (Ds (a₁ + 1)).1 (x, y) ≤ (Ds a₁).1 (x, y) ∧
        ∃ w ∈ closedBall q ρ, (Ds a₁).1 (x, w) + (Ds a₁).1 (w, y) ≤ (Ds a₁).1 (x, y)) →
      (a₂ ∈ Icc (0 : ℝ) 1 ∧ (Ds (a₂ + 1)).1 (x, y) ≤ (Ds a₂).1 (x, y) ∧
        ∃ w ∈ closedBall q ρ, (Ds a₂).1 (x, w) + (Ds a₂).1 (w, y) ≤ (Ds a₂).1 (x, y)) →
      False := by
    intro a₁ a₂ hlt h₁ h₂
    obtain ⟨⟨ha₁0, -⟩, hA1, -⟩ := h₁
    obtain ⟨⟨-, ha₂1⟩, -, w, hw, hT⟩ := h₂
    have hF : (Ds a₂).1 (x, y) ≤ (Ds a₁).1 (x, y) :=
      (hmono a₂ (a₁ + 1) x y (by linarith)).trans hA1
    have hw' : ‖w - q‖ ≤ ρ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hw
    have hball : ∀ z, ‖z - w‖ < ρ → ‖z - q‖ < 2 * ρ := fun z hz => by
      have := norm_sub_le_norm_sub_add_norm_sub z w q
      linarith
    have hxw : ρ ≤ ‖x - w‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub x w q
      linarith
    obtain ⟨c, hc, hle⟩ := weylScale_add_le_of_gap hξ D0 (f₁ := a₁ • φ) (f₂ := a₂ • φ)
      (fun u => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        exact mul_le_mul_of_nonneg_right hlt.le (hφ0 u))
      hρ (b₁ := a₁) (b₂ := a₂)
      (fun z hz => by simp [hφ1 z (hball z hz)])
      (fun z hz => by simp [hφ1 z (hball z hz)]) hlt hxw
    rw [hW, hW, ← ENNReal.ofReal_add ((Ds a₁).nonneg x w) hc.le,
      ENNReal.ofReal_le_ofReal_iff ((Ds a₂).nonneg x w)] at hle
    have htri := (Ds a₁).2.triangle x w y
    have h2 := hmono a₁ a₂ w y hlt.le
    linarith
  intro a₁ h₁ a₂ h₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a₁ a₂ h h₁ h₂
  · exact key a₂ a₁ h h₂ h₁

/-- A `D`-geodesic from `z` to `w` on which `f` vanishes: `e^{ξ f}·D(z, w) ≤ D(z, w)`. -/
theorem weylScale_le_of_isGeod01 {ξ : ℝ} {D0 : ContMetric} {f : C(ℂ, ℝ)} {z w : ℂ}
    {η : C(unitInterval, ℂ)} (hη : D0.IsGeod01 z w η) (hf : ∀ t, f (η t) = 0) :
    weylScale ξ f D0 z w ≤ ENNReal.ofReal (D0.1 (z, w)) := by
  obtain ⟨-, hu, h0, h1⟩ := hη.isGeodesicCurve
  set L := D0.1 (z, w)
  set P : ℝ → ℂ := fun t => η (projIcc 0 1 zero_le_one (t / L))
  have hu' : HasUnitSpeedOn (D0.pt ∘ P) (Icc 0 L) := hu
  have h0' : P 0 = z := h0
  have h1' : P L = w := h1
  rw [← weylScaleOn_univ]
  calc weylScaleOn ξ f D0 univ z w
      ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
        weylScaleOn_le (D0.nonneg z w) (continuousOn_of_hasUnitSpeedOn hu') hu' h0' h1'
          (fun _ _ => mem_univ _)
    _ = ENNReal.ofReal (Real.exp 0) * ENNReal.ofReal L :=
        setLIntegral_exp_of_eq_const (fun t _ => by simp only [P, hf, mul_zero])
    _ = ENNReal.ofReal L := by simp

end LQGMetric.MQ
