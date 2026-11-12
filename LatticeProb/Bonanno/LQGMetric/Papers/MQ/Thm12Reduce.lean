/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.MQ.Thm12Reduce at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Geodesics

/-!
# MQ Theorem 1.2 (weak metrics): the first reduction (task P2-MQ)

Source: J. Miller, W. Qian, arXiv:1812.03913, `literature/src/1812.03913/lqg_geodesics.tex`,
proof of Theorem 1.2 (`thm:geo_unique`), l. 462–468: "To prove the theorem, it suffices to show
that for any `r > 0`, on the event `{r < 𝔡_h(x,y)}`, `∂B_h(x,r) ∩ ∂B_h(y,s)` a.s. contains a
unique point. Indeed, if `η` is a geodesic from `x` to `y`, … `η(r) ∈ ∂B_h(x,r) ∩ ∂B_h(y,s)`
… for any two geodesics `η, η̃` we a.s. have `η(r) = η̃(r)` for all rational `r` simultaneously.
This can only be the case if we a.s. have `η = η̃`."

* `eq_of_isGeod01_of_sphereInter` : the deterministic step (two constant-speed geodesics that
  agree at all points `w` with `D(x,w) = r`, `D(w,y) = D(x,y) − r`, `r ∈ ℚ ∩ (0, D(x,y))`, are
  equal);
* `MQSphereInter` : MQ's remaining claim (l. 466–467), verbatim, for weak γ-LQG metrics;
* `mqThm1_2Weak_of_sphereInter` : `MQSphereInter` + existence of geodesics (GM.S1.1,
  `gm_S1_1`, which uses DFGPS Lemma 3.8, `Blueprint.DFGPSLem3_8`) give `Blueprint.MQThm1_2Weak`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric.MQ

open Blueprint

/-- **MQ l. 466–468, deterministic step.** -/
theorem eq_of_isGeod01_of_sphereInter (D : ContMetric) {x y : ℂ}
    (hS : ∀ r : ℚ, 0 < (r : ℝ) → (r : ℝ) < D.1 (x, y) → ∀ w w' : ℂ,
      D.1 (x, w) = r → D.1 (w, y) = D.1 (x, y) - r →
      D.1 (x, w') = r → D.1 (w', y) = D.1 (x, y) - r → w = w')
    {η η' : C(unitInterval, ℂ)} (hη : IsGeod01 D x y η) (hη' : IsGeod01 D x y η') : η = η' := by
  set L := D.1 (x, y) with hLdef
  have hL0 : 0 ≤ L := by
    have h := D.2.triangle x y x
    rw [D.2.self_eq_zero, D.2.symm y x] at h
    linarith
  ext s
  rcases hL0.eq_or_lt with hL | hL
  · -- `x = y`: both curves are constant
    have h1 := hη.2.2 0 s
    have h2 := hη'.2.2 0 s
    rw [hη.1, ← hLdef, ← hL, mul_zero] at h1
    rw [hη'.1, ← hLdef, ← hL, mul_zero] at h2
    rw [← D.2.eq_of_eq_zero _ _ h1, ← D.2.eq_of_eq_zero _ _ h2]
  -- `L > 0`: compare at rational distances
  have hpt : ∀ (ζ : C(unitInterval, ℂ)), IsGeod01 D x y ζ → ∀ t : unitInterval,
      D.1 (x, ζ t) = t * L ∧ D.1 (ζ t, y) = L - t * L := by
    intro ζ hζ t
    have h1 := hζ.2.2 0 t
    have h2 := hζ.2.2 t 1
    rw [hζ.1] at h1
    rw [hζ.2.1] at h2
    simp only [Set.Icc.coe_zero, sub_zero, Set.Icc.coe_one] at h1 h2
    rw [abs_of_nonneg t.2.1] at h1
    rw [abs_of_nonneg (by linarith [t.2.2] : (0 : ℝ) ≤ 1 - t)] at h2
    exact ⟨h1, by rw [h2]; ring⟩
  have hd : ∀ ε > 0, D.1 (η s, η' s) ≤ 2 * ε * L := by
    intro ε hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 ((s : ℝ) * L - ε * L) <
        min L ((s : ℝ) * L + ε * L) by
      have hεL : 0 < ε * L := mul_pos hε hL
      have hs0 := s.2.1
      have hs1 := s.2.2
      refine max_lt (lt_min hL (by nlinarith)) (lt_min (by nlinarith) (by linarith)))
    have hq0 : (0 : ℝ) < q := (le_max_left _ _).trans_lt hq1
    have hqL : (q : ℝ) < L := hq2.trans_le (min_le_left _ _)
    set t : unitInterval := ⟨q / L, div_nonneg hq0.le hL.le, (div_le_one hL).2 hqL.le⟩
    have htL : (t : ℝ) * L = q := by simp only [t]; field_simp
    have e1 := hpt η hη t
    have e2 := hpt η' hη' t
    rw [htL] at e1 e2
    have heq : η t = η' t := hS q hq0 hqL _ _ e1.1 e1.2 e2.1 e2.2
    have hts : |(t : ℝ) - s| ≤ ε := by
      rw [abs_le]
      have h1 : (s : ℝ) * L - ε * L < q := (le_max_right _ _).trans_lt hq1
      have h2 : (q : ℝ) < s * L + ε * L := hq2.trans_le (min_le_right _ _)
      constructor
      · by_contra hc; push Not at hc
        have : (t : ℝ) * L < (s - ε) * L := mul_lt_mul_of_pos_right (by linarith) hL
        rw [htL] at this; linarith
      · by_contra hc; push Not at hc
        have : (s + ε) * L < (t : ℝ) * L := mul_lt_mul_of_pos_right (by linarith) hL
        rw [htL] at this; linarith
    have hA := hη.2.2 s t
    have hB := hη'.2.2 t s
    calc D.1 (η s, η' s) ≤ D.1 (η s, η t) + D.1 (η t, η' s) := D.2.triangle _ _ _
      _ = |(t : ℝ) - s| * L + |(s : ℝ) - t| * L := by rw [hA, heq, hB]
      _ ≤ ε * L + ε * L := by
          rw [abs_sub_comm (s : ℝ)]
          exact add_le_add (mul_le_mul_of_nonneg_right hts hL.le)
            (mul_le_mul_of_nonneg_right hts hL.le)
      _ = 2 * ε * L := by ring
  refine D.2.eq_of_eq_zero _ _ (le_antisymm ?_ ?_)
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := hd (δ / (2 * L)) (by positivity)
    calc D.1 (η s, η' s) ≤ 2 * (δ / (2 * L)) * L := this
      _ = 0 + δ := by field_simp; ring
  · have h := D.2.triangle (η s) (η' s) (η s)
    rw [D.2.self_eq_zero, D.2.symm (η' s) (η s)] at h
    linarith

/-- **MQ's remaining claim** (proof of Thm 1.2, l. 466–467), for weak γ-LQG metrics (D33): for
fixed distinct `x, y` and `r > 0`, a.s. on `{r < D_h(x,y)}` the set
`∂B_h(x,r) ∩ ∂B_h(y, D_h(x,y) − r)` (points `w` with `D_h(x,w) = r`, `D_h(w,y) = D_h(x,y) − r`)
has at most one point. -/
def MQSphereInter : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ x y : ℂ, x ≠ y → ∀ r : ℝ, 0 < r →
        ∀ᵐ ω ∂P, r < (D (h ω)).1 (x, y) → ∀ w w' : ℂ,
          (D (h ω)).1 (x, w) = r → (D (h ω)).1 (w, y) = (D (h ω)).1 (x, y) - r →
          (D (h ω)).1 (x, w') = r → (D (h ω)).1 (w', y) = (D (h ω)).1 (x, y) - r → w = w'

/-- **MQ Thm 1.2 (weak metrics) from MQ's remaining claim** (MQ l. 462–468), with existence of
geodesics from GM.S1.1 (`gm_S1_1`, via DFGPS Lemma 3.8). -/
theorem mqThm1_2Weak_of_sphereInter (h38 : DFGPSLem3_8) (hS : MQSphereInter) :
    MQThm1_2Weak := by
  intro γ hγ hγ2 D c hD Ω _ P _ h hh x y hxy
  have hall : ∀ᵐ ω ∂P, ∀ r : ℚ, 0 < (r : ℝ) → (r : ℝ) < (D (h ω)).1 (x, y) → ∀ w w' : ℂ,
      (D (h ω)).1 (x, w) = r → (D (h ω)).1 (w, y) = (D (h ω)).1 (x, y) - r →
      (D (h ω)).1 (x, w') = r → (D (h ω)).1 (w', y) = (D (h ω)).1 (x, y) - r → w = w' := by
    rw [ae_all_iff]
    intro r
    by_cases hr : (0 : ℝ) < r
    · filter_upwards [hS γ hγ hγ2 D c hD P h hh x y hxy r hr] with ω hω _ hlt
      exact hω hlt
    · exact Filter.Eventually.of_forall fun ω h0 => absurd h0 hr
  filter_upwards [GM.gm_S1_1 h38 hγ hγ2 hD P h hh, hall] with ω hex hω
  obtain ⟨η, hη⟩ := hex x y
  exact ⟨η, hη, fun η' hη' => (eq_of_isGeod01_of_sphereInter _ hω hη hη').symm⟩

end LQGMetric.MQ
