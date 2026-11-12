/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P6A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.WeylMetric
import LatticeProb.Bonanno.LQGMetric.Metric.WeylPathLength

/-!
# DFGPS Thm 1.2, P-4 item 1: composition of Weyl scalings

`weylScale_weylMetric`: for a continuous length metric `D` and continuous `f, g`,
`e^{ξ f}·(e^{ξ g}·D) = e^{ξ (g + f)}·D` (GM (1.6), arXiv:1905.00383v3 `uniqueness-final.tex`
l. 300–302; used implicitly by DFGPS T:1339–1386 when Axiom III is checked for a field
`h₀ + g` with `h₀` a normalized GFF). GM and DFGPS take this identity for granted.

Own elementary proof (DEVIATIONS: "own elementary proof"): on a short piece of a path where
`ξ f, ξ g` oscillate by `< η`, the two-sided bounds of `LQGMetric.Metric.WeylPathLength`
(`curveLength_weyl_le`, `le_curveLength_weyl`) give that the two lengths agree up to the factor
`e^{4η}`; a Lebesgue-number partition sums this over the path (`curveLength_le_mul_of_local`),
`η → 0` gives equal lengths of all curves, and two length metrics with the same curve lengths
coincide (`dist_le_of_curveLength_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open MetricGeometry

/-- local-to-global comparison of curve lengths along a partition with small mesh -/
theorem curveLength_le_mul_of_local {A B : ContMetric} {P : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t)
    {κ : ℝ≥0∞}
    (hloc : ∀ τ ∈ Icc s t, ∃ δ > 0, ∀ a b, a ≤ b → Icc a b ⊆ ball τ δ →
      curveLength (A.pt ∘ P) a b ≤ κ * curveLength (B.pt ∘ P) a b) :
    curveLength (A.pt ∘ P) s t ≤ κ * curveLength (B.pt ∘ P) s t := by
  choose δ hδ hδl using hloc
  obtain ⟨ε, hε, hleb⟩ := lebesgue_number_lemma_of_metric (s := Icc s t)
    (c := fun τ : Icc s t => ball (τ : ℝ) (δ τ τ.2)) isCompact_Icc (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hδ x hx)⟩)
  obtain ⟨n, hn⟩ := exists_nat_gt ((t - s) / ε)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (sub_nonneg.2 hst) hε.le) hn
  set h : ℝ := (t - s) / n with hh
  have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.2 hst) hn0.le
  have hhε : h < ε := by
    rw [div_lt_iff₀ hε] at hn
    rw [hh, div_lt_iff₀ hn0]; linarith [mul_comm ε (n : ℝ)]
  set u : ℕ → ℝ := fun i => s + i * h with hu_def
  have hu : Monotone u := fun i j hij => by
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    simp only [hu_def]; nlinarith
  have hu0 : u 0 = s := by simp [hu_def]
  have hun : u n = t := by
    simp only [hu_def, hh]; field_simp; ring
  rw [← hu0, ← hun, ← sum_curveLength_eq' _ hu n, ← sum_curveLength_eq' _ hu n, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hin : i ≤ n := (Finset.mem_range.1 hi).le
  have hmem : u i ∈ Icc s t := by
    rw [← hu0, ← hun]; exact ⟨hu (Nat.zero_le i), hu hin⟩
  obtain ⟨τ, hτ⟩ := hleb (u i) hmem
  refine hδl τ τ.2 (u i) (u (i + 1)) (hu (Nat.le_succ i)) (fun y hy => hτ ?_)
  rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hy.1)]
  have : u (i + 1) - u i = h := by simp only [hu_def]; push_cast; ring
  linarith [hy.2]

/-- `x ≤ e^{4η} y` for all `η > 0` gives `x ≤ y` -/
theorem le_of_forall_exp_mul {x y : ℝ≥0∞}
    (h : ∀ η : ℝ, 0 < η → x ≤ ENNReal.ofReal (Real.exp (4 * η)) * y) : x ≤ y := by
  by_cases hy : y = ∞
  · rw [hy]; exact le_top
  have h1 : Tendsto (fun η : ℝ => ENNReal.ofReal (Real.exp (4 * η))) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous fun η : ℝ => ENNReal.ofReal (Real.exp (4 * η)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hy)
  rw [one_mul] at h2
  exact ge_of_tendsto h2 (eventually_nhdsWithin_of_forall fun η hη => h η hη)

/-- two continuous metrics, `B` a length metric: if `A`-lengths of curves are at most
`B`-lengths, then `A ≤ B` -/
theorem dist_le_of_curveLength_le {A B : ContMetric} (hB : B.IsLength)
    (hlen : ∀ P : ℝ → ℂ, Continuous P →
      curveLength (A.pt ∘ P) 0 1 ≤ curveLength (B.pt ∘ P) 0 1) (z w : ℂ) :
    A.1 (z, w) ≤ B.1 (z, w) := by
  have hB0 : 0 ≤ B.1 (z, w) := dist_nonneg (x := B.pt z) (y := B.pt w)
  rw [← ENNReal.ofReal_le_ofReal_iff hB0]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨γ, hγ⟩ := hB (B.pt z) (B.pt w) ε hε
  set P : ℝ → ℂ := weylToC B ∘ γ.extend with hP
  have hPc : Continuous P := (continuous_weylToC B).comp γ.continuous_extend
  obtain ⟨γ', hγ', -⟩ := exists_path_of_curve zero_le_one
    ((continuous_weylPt A).comp hPc).continuousOn
  have h0 : P 0 = z := by simp only [hP, Function.comp_apply, Path.extend_zero]; rfl
  have h1 : P 1 = w := by simp only [hP, Function.comp_apply, Path.extend_one]; rfl
  have hA := edist_le_pathLength γ'
  simp only [Function.comp_apply, h0, h1] at hA
  have hBl : curveLength (B.pt ∘ P) 0 1 = pathLength γ := rfl
  calc ENNReal.ofReal (A.1 (z, w)) = edist (A.pt z) (A.pt w) := by rw [edist_dist]; rfl
    _ ≤ curveLength (A.pt ∘ P) 0 1 := hA.trans hγ'.le
    _ ≤ curveLength (B.pt ∘ P) 0 1 := hlen P hPc
    _ ≤ edist (B.pt z) (B.pt w) + ENNReal.ofReal ε := hBl ▸ hγ
    _ = ENNReal.ofReal (B.1 (z, w)) + ε := by rw [edist_dist, ENNReal.ofReal_coe_nnreal]; rfl

variable {ξ : ℝ} {f g : C(ℂ, ℝ)} {D : ContMetric}

theorem exp_mul_exp_eq (a b c d : ℝ) (h : a + b = c + d) (x : ℝ≥0∞) :
    ENNReal.ofReal (Real.exp a) * (ENNReal.ofReal (Real.exp b) * x) =
      ENNReal.ofReal (Real.exp c) * (ENNReal.ofReal (Real.exp d) * x) := by
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Real.exp_add, h]

/-- local comparison of `e^{ξ f}·(e^{ξ g}·D)` and `e^{ξ (g+f)}·D` on short pieces of a curve -/
theorem weylWeyl_local (hD : D.IsLength) {P : ℝ → ℂ} (hP : Continuous P) {η : ℝ} (hη : 0 < η)
    (τ : ℝ) : ∃ δ > 0, ∀ a b, a ≤ b → Icc a b ⊆ ball τ δ →
      curveLength ((weylMetric ξ f (weylMetric ξ g D hD) (weylMetric_isLength hD)).pt ∘ P) a b ≤
        ENNReal.ofReal (Real.exp (4 * η)) *
          curveLength ((weylMetric ξ (g + f) D hD).pt ∘ P) a b ∧
      curveLength ((weylMetric ξ (g + f) D hD).pt ∘ P) a b ≤
        ENNReal.ofReal (Real.exp (4 * η)) * curveLength
          ((weylMetric ξ f (weylMetric ξ g D hD) (weylMetric_isLength hD)).pt ∘ P) a b := by
  set D' := weylMetric ξ g D hD
  set M1 := weylMetric ξ f D' (weylMetric_isLength hD)
  set M2 := weylMetric ξ (g + f) D hD
  set x0 := P τ
  have hcg : Continuous fun x => ξ * g x := continuous_const.mul g.continuous
  have hcf : Continuous fun x => ξ * f x := continuous_const.mul f.continuous
  obtain ⟨r1, hr1, h1⟩ := Metric.continuous_iff.1 hcg x0 η hη
  obtain ⟨r2, hr2, h2⟩ := Metric.continuous_iff.1 hcf x0 η hη
  obtain ⟨δ, hδ, hPδ⟩ := Metric.continuous_iff.1 hP τ (min r1 r2) (lt_min hr1 hr2)
  refine ⟨δ, hδ, fun a b hab hsub => ?_⟩
  have hPV : ∀ σ ∈ Icc a b, P σ ∈ ball x0 (min r1 r2) := fun σ hσ => hPδ σ (hsub hσ)
  have hVg : ∀ x ∈ ball x0 (min r1 r2), |ξ * g x - ξ * g x0| < η := fun x hx => by
    have := h1 x (lt_of_lt_of_le hx (min_le_left _ _)); rwa [Real.dist_eq] at this
  have hVf : ∀ x ∈ ball x0 (min r1 r2), |ξ * f x - ξ * f x0| < η := fun x hx => by
    have := h2 x (lt_of_lt_of_le hx (min_le_right _ _)); rwa [Real.dist_eq] at this
  have hcD : ContinuousOn (D.pt ∘ P) (Icc a b) := ((continuous_weylPt D).comp hP).continuousOn
  have hcD' : ContinuousOn (D'.pt ∘ P) (Icc a b) :=
    ((continuous_weylPt D').comp hP).continuousOn
  have hs' : ∀ x y, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ g D x y := weylMetric_spec hD
  have hs1 : ∀ x y, ENNReal.ofReal (M1.1 (x, y)) = weylScale ξ f D' x y :=
    weylMetric_spec (weylMetric_isLength hD)
  have hs2 : ∀ x y, ENNReal.ofReal (M2.1 (x, y)) = weylScale ξ (g + f) D x y :=
    weylMetric_spec hD
  have hgf : ∀ x, ξ * (g + f) x = ξ * g x + ξ * f x := fun x => by
    rw [ContinuousMap.add_apply, mul_add]
  have u1 := curveLength_weyl_le M1 hs1 hab hcD' hPV (b := ξ * f x0 + η)
    (fun x hx => by linarith [(abs_lt.1 (hVf x hx)).2])
  have u1' := curveLength_weyl_le D' hs' hab hcD hPV (b := ξ * g x0 + η)
    (fun x hx => by linarith [(abs_lt.1 (hVg x hx)).2])
  have l2 := le_curveLength_weyl M2 hs2 hcD isOpen_ball hPV (a := ξ * g x0 + ξ * f x0 - 2 * η)
    (fun x hx => by rw [hgf]; linarith [(abs_lt.1 (hVf x hx)).1, (abs_lt.1 (hVg x hx)).1])
  have u2 := curveLength_weyl_le M2 hs2 hab hcD hPV (b := ξ * g x0 + ξ * f x0 + 2 * η)
    (fun x hx => by rw [hgf]; linarith [(abs_lt.1 (hVf x hx)).2, (abs_lt.1 (hVg x hx)).2])
  have l1 := le_curveLength_weyl M1 hs1 hcD' isOpen_ball hPV (a := ξ * f x0 - η)
    (fun x hx => by linarith [(abs_lt.1 (hVf x hx)).1])
  have l1' := le_curveLength_weyl D' hs' hcD isOpen_ball hPV (a := ξ * g x0 - η)
    (fun x hx => by linarith [(abs_lt.1 (hVg x hx)).1])
  constructor
  · calc curveLength (M1.pt ∘ P) a b
        ≤ ENNReal.ofReal (Real.exp (ξ * f x0 + η)) *
            (ENNReal.ofReal (Real.exp (ξ * g x0 + η)) * curveLength (D.pt ∘ P) a b) :=
          u1.trans (mul_le_mul_right u1' _)
      _ = ENNReal.ofReal (Real.exp (4 * η)) * (ENNReal.ofReal
            (Real.exp (ξ * g x0 + ξ * f x0 - 2 * η)) * curveLength (D.pt ∘ P) a b) :=
          exp_mul_exp_eq _ _ _ _ (by ring) _
      _ ≤ _ := mul_le_mul_right l2 _
  · calc curveLength (M2.pt ∘ P) a b
        ≤ ENNReal.ofReal (Real.exp (ξ * g x0 + ξ * f x0 + 2 * η)) * curveLength (D.pt ∘ P) a b :=
          u2
      _ = ENNReal.ofReal (Real.exp (4 * η)) * (ENNReal.ofReal (Real.exp (ξ * f x0 - η)) *
            (ENNReal.ofReal (Real.exp (ξ * g x0 - η)) * curveLength (D.pt ∘ P) a b)) := by
          rw [exp_mul_exp_eq (ξ * f x0 - η) (ξ * g x0 - η) (ξ * g x0 + ξ * f x0 - 2 * η) 0
            (by ring), Real.exp_zero, ENNReal.ofReal_one, one_mul, ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 3; ring
      _ ≤ ENNReal.ofReal (Real.exp (4 * η)) * (ENNReal.ofReal (Real.exp (ξ * f x0 - η)) *
            curveLength (D'.pt ∘ P) a b) := mul_le_mul_right (mul_le_mul_right l1' _) _
      _ ≤ _ := mul_le_mul_right l1 _

/-- **Composition of Weyl scalings** (GM (1.6)): `e^{ξ f}·(e^{ξ g}·D) = e^{ξ (g+f)}·D` for a
continuous length metric `D`. -/
theorem weylScale_weylMetric (hD : D.IsLength) (z w : ℂ) :
    weylScale ξ f (weylMetric ξ g D hD) z w = weylScale ξ (g + f) D z w := by
  have key : ∀ P : ℝ → ℂ, Continuous P →
      curveLength ((weylMetric ξ f (weylMetric ξ g D hD) (weylMetric_isLength hD)).pt ∘ P) 0 1 ≤
        curveLength ((weylMetric ξ (g + f) D hD).pt ∘ P) 0 1 ∧
      curveLength ((weylMetric ξ (g + f) D hD).pt ∘ P) 0 1 ≤ curveLength
        ((weylMetric ξ f (weylMetric ξ g D hD) (weylMetric_isLength hD)).pt ∘ P) 0 1 :=
    fun P hP => ⟨le_of_forall_exp_mul fun η hη => curveLength_le_mul_of_local zero_le_one
        fun τ _ => let ⟨δ, hδ, h⟩ := weylWeyl_local (f := f) (g := g) hD hP hη τ
          ⟨δ, hδ, fun a b hab hb => (h a b hab hb).1⟩,
      le_of_forall_exp_mul fun η hη => curveLength_le_mul_of_local zero_le_one
        fun τ _ => let ⟨δ, hδ, h⟩ := weylWeyl_local (f := f) (g := g) hD hP hη τ
          ⟨δ, hδ, fun a b hab hb => (h a b hab hb).2⟩⟩
  rw [← weylMetric_spec (weylMetric_isLength hD), ← weylMetric_spec hD]
  congr 1
  exact le_antisymm
    (dist_le_of_curveLength_le (weylMetric_isLength hD) (fun P hP => (key P hP).1) z w)
    (dist_le_of_curveLength_le (weylMetric_isLength (weylMetric_isLength hD))
      (fun P hP => (key P hP).2) z w)

end LQGMetric.DFGPS.T12
