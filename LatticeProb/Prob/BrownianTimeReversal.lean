/-
Fixed-time reversal of a Brownian motion, and the duality of Lebesgue starting points.

For a path `w : ℝ≥0 → ℝ` and a time `t` the reversed path `revAt t w` is
`s ↦ w t - w (t - s)` on `[0, t]` and `w` itself after `t`.  A pre-Brownian motion is a centred
Gaussian process with covariance `min s r`; the reversed process is again a centred Gaussian
process with that covariance, so by the identification of path laws it has the law of the
original motion (`map_path_revAt`).

Consequently, integrating a functional of the path started at a Lebesgue-distributed point
`x` and drifted by `m` is the same as integrating it over the reversed, reflected path
`b - (x + W (t - ·) + m (t - ·))`: for fixed `W` the map `x ↦ b - x - W t - m t` preserves
Lebesgue measure and turns the reflected path into `y + revAt t W + m ·`, and the law of
`revAt t W` is that of `W` (`lintegral_lebesgue_drift_rev`).
-/
import Mathlib
import LatticeProb.Prob.BrownianPathLaw

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The path `w` reversed at the time `t`: `s ↦ w t - w (t - s)` for `s ≤ t`, and `w s` after `t`. -/
def revAt (t : ℝ≥0) (w : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  fun s => if s ≤ t then w t - w (t - s) else w s

lemma revAt_of_le {t s : ℝ≥0} (hs : s ≤ t) (w : ℝ≥0 → ℝ) :
    revAt t w s = w t - w (t - s) := by
  simp [revAt, hs]

lemma revAt_of_not_le {t s : ℝ≥0} (hs : ¬ s ≤ t) (w : ℝ≥0 → ℝ) : revAt t w s = w s := by
  simp [revAt, hs]

lemma measurable_revAt (t : ℝ≥0) : Measurable (revAt t) := by
  refine Measurable.of_eval fun s => ?_
  by_cases hs : s ≤ t
  · have : (fun w : ℝ≥0 → ℝ => revAt t w s) = fun w => w t - w (t - s) := by
      funext w; exact revAt_of_le hs w
    rw [this]
    exact (measurable_pi_apply t).sub (measurable_pi_apply (t - s))
  · have : (fun w : ℝ≥0 → ℝ => revAt t w s) = fun w => w s := by
      funext w; exact revAt_of_not_le hs w
    rw [this]
    exact measurable_pi_apply s

lemma isGaussianProcess_revAt (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    IsGaussianProcess (fun s ω => revAt t (fun u => B u ω) s) P := by
  classical
  refine hB.isGaussianProcess.of_isGaussianProcess fun s => ?_
  by_cases hs : s ≤ t
  · refine ⟨{t, t - s}, { toFun := fun x => x ⟨t, by simp⟩ - x ⟨t - s, by simp⟩
                          map_add' := ?_
                          map_smul' := ?_ }, fun ω => ?_⟩
    · intro x y; simp; ring
    · intro c x; simp [mul_sub]
    · simp [revAt_of_le hs, Finset.restrict_def]
  · refine ⟨{s}, { toFun := fun x => x ⟨s, by simp⟩
                   map_add' := by simp
                   map_smul' := by simp }, fun ω => ?_⟩
    simp [revAt_of_not_le hs]

/-- Covariance of two increments of a pre-Brownian motion. -/
lemma covariance_increments_brownian (hB : IsPreBrownianReal B P) (a b c d : ℝ≥0) :
    cov[fun ω => B a ω - B b ω, fun ω => B c ω - B d ω; P]
      = ((min a c : ℝ≥0) : ℝ) - (min a d : ℝ≥0) - (min b c : ℝ≥0) + (min b d : ℝ≥0) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have h2 : ∀ u, MemLp (B u) 2 P := fun u => (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  have h3 : MemLp (fun ω => B c ω - B d ω) 2 P := (h2 c).sub (h2 d)
  rw [covariance_fun_sub_left (h2 a) (h2 b) h3,
    covariance_fun_sub_right (h2 a) (h2 c) (h2 d), covariance_fun_sub_right (h2 b) (h2 c) (h2 d),
    hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, hB.covariance_eval]
  ring

theorem isPreBrownianReal_revAt (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    IsPreBrownianReal (fun s ω => revAt t (fun u => B u ω) s) P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have h2 : ∀ u, MemLp (B u) 2 P := fun u => (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  refine (isGaussianProcess_revAt hB t).isPreBrownianReal_of_covariance (fun s => ?_)
    (fun s r hsr => ?_)
  · by_cases hs : s ≤ t
    · simp only [revAt_of_le hs]
      rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval _), hB.integral_eval,
        hB.integral_eval, sub_zero]
    · simp only [revAt_of_not_le hs]
      exact hB.integral_eval s
  · by_cases hr : r ≤ t
    · have hs : s ≤ t := hsr.trans hr
      simp only [revAt_of_le hs, revAt_of_le hr]
      rw [covariance_increments_brownian hB, min_self, min_eq_right (tsub_le_self : t - r ≤ t),
        min_eq_left (tsub_le_self : t - s ≤ t), min_eq_right (tsub_le_tsub_left hsr t),
        NNReal.coe_sub hs, NNReal.coe_sub hr]
      ring
    · by_cases hs : s ≤ t
      · have htr : t ≤ r := (not_le.1 hr).le
        simp only [revAt_of_le hs, revAt_of_not_le hr]
        rw [covariance_fun_sub_left (h2 t) (h2 (t - s)) (h2 r), hB.covariance_eval,
          hB.covariance_eval, min_eq_left htr, min_eq_left (tsub_le_self.trans htr),
          NNReal.coe_sub hs]
        ring
      · simp only [revAt_of_not_le hs, revAt_of_not_le hr]
        rw [hB.covariance_fun_eval, min_eq_left hsr]

/-- A Brownian motion reversed at a fixed time is a Brownian motion: the path laws agree. -/
theorem map_path_revAt (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t)) (t : ℝ≥0) :
    P.map (fun ω s => revAt t (fun u => B u ω) s) = P.map (fun ω s => B s ω) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hpath : Measurable fun ω (u : ℝ≥0) => B u ω := Measurable.of_eval hm
  refine map_path_eq_of_isPreBrownianReal (isPreBrownianReal_revAt hB t) hB ?_ hm
  intro s
  exact (measurable_pi_apply s).comp ((measurable_revAt t).comp hpath)

/-- **Duality of Lebesgue starting points.**  Integrating a functional `Phi` of a path
`x + W + m ·` (stopped at `t`) over a Lebesgue-distributed starting point `x` and a Brownian
path `W` gives the same value as integrating it over the reversed path
`s ↦ b - (x + W (t - s) + m (t - s))` (stopped at `t`), for every `b`.  No conditioning and no
limit is involved: for fixed `W` the map `x ↦ b - x - W t - m t` preserves Lebesgue measure and
`b - (x + W (t - ·) + m (t - ·)) = y + revAt t W + m ·` with `y` the image of `x`. -/
theorem lintegral_lebesgue_drift_rev (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (m b : ℝ) (t : ℝ≥0) (Phi : (ℝ≥0 → ℝ) → ℝ≥0∞) (hPhi : Measurable Phi) :
    ∫⁻ x : ℝ, ∫⁻ ω, Phi (fun s => x + B (min s t) ω + m * ((min s t : ℝ≥0) : ℝ)) ∂P
      = ∫⁻ x : ℝ, ∫⁻ ω, Phi (fun s => b - (x + B (t - min s t) ω
          + m * ((t - min s t : ℝ≥0) : ℝ))) ∂P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hpath : Measurable fun ω (u : ℝ≥0) => B u ω := Measurable.of_eval hm
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (ℝ≥0 → ℝ) → ℝ≥0∞, ∀ v, Ψ v =
      ∫⁻ y : ℝ, Phi (fun s => y + v (min s t) + m * ((min s t : ℝ≥0) : ℝ)) := ⟨_, fun _ => rfl⟩
  have hF : Measurable fun p : (ℝ≥0 → ℝ) × ℝ =>
      Phi (fun s => p.2 + p.1 (min s t) + m * ((min s t : ℝ≥0) : ℝ)) := by
    refine hPhi.comp (Measurable.of_eval fun s => ?_)
    have h1 : Measurable fun p : (ℝ≥0 → ℝ) × ℝ => p.1 (min s t) :=
      (measurable_pi_apply _).comp measurable_fst
    exact (measurable_snd.add h1).add measurable_const
  have hΨm : Measurable Ψ := by
    have : Ψ = fun v => ∫⁻ y : ℝ, Phi (fun s => y + v (min s t) + m * ((min s t : ℝ≥0) : ℝ)) :=
      funext hΨ
    rw [this]
    exact hF.lintegral_prod_right'
  have hf1 : Measurable (Function.uncurry fun (x : ℝ) (ω : Ω) =>
      Phi (fun s => x + B (min s t) ω + m * ((min s t : ℝ≥0) : ℝ))) := by
    refine hPhi.comp (Measurable.of_eval fun s => ?_)
    exact (measurable_fst.add ((hm _).comp measurable_snd)).add measurable_const
  have hf2 : Measurable (Function.uncurry fun (x : ℝ) (ω : Ω) =>
      Phi (fun s => b - (x + B (t - min s t) ω + m * ((t - min s t : ℝ≥0) : ℝ)))) := by
    refine hPhi.comp (Measurable.of_eval fun s => ?_)
    exact measurable_const.sub ((measurable_fst.add ((hm _).comp measurable_snd)).add
      measurable_const)
  have key : ∀ (x : ℝ) (ω : Ω) (s : ℝ≥0),
      b - (x + B (t - min s t) ω + m * ((t - min s t : ℝ≥0) : ℝ))
        = (b - B t ω - m * t - x) + revAt t (fun u => B u ω) (min s t)
            + m * ((min s t : ℝ≥0) : ℝ) := by
    intro x ω s
    rw [revAt_of_le (min_le_right s t), NNReal.coe_sub (min_le_right s t)]
    ring
  have hpt : ∀ ω, Ψ (revAt t fun u => B u ω)
      = ∫⁻ x : ℝ, Phi (fun s => b - (x + B (t - min s t) ω + m * ((t - min s t : ℝ≥0) : ℝ))) := by
    intro ω
    have hsub := lintegral_sub_left_eq_self (μ := (volume : Measure ℝ))
      (fun y => Phi (fun s => y + revAt t (fun u => B u ω) (min s t)
        + m * ((min s t : ℝ≥0) : ℝ))) (b - B t ω - m * t)
    rw [hΨ, ← hsub]
    refine lintegral_congr fun x => ?_
    congr 1
    funext s
    exact (key x ω s).symm
  calc ∫⁻ x : ℝ, ∫⁻ ω, Phi (fun s => x + B (min s t) ω + m * ((min s t : ℝ≥0) : ℝ)) ∂P
      = ∫⁻ ω, (∫⁻ x : ℝ, Phi (fun s => x + B (min s t) ω + m * ((min s t : ℝ≥0) : ℝ))) ∂P :=
        lintegral_lintegral_swap hf1.aemeasurable
    _ = ∫⁻ ω, Ψ (fun u => B u ω) ∂P := by simp only [hΨ]
    _ = ∫⁻ v, Ψ v ∂(P.map fun ω u => B u ω) := (lintegral_map hΨm hpath).symm
    _ = ∫⁻ v, Ψ v ∂(P.map fun ω s => revAt t (fun u => B u ω) s) := by
        rw [map_path_revAt hB hm t]
    _ = ∫⁻ ω, Ψ (revAt t fun u => B u ω) ∂P :=
        lintegral_map hΨm ((measurable_revAt t).comp hpath)
    _ = ∫⁻ ω, (∫⁻ x : ℝ, Phi (fun s => b - (x + B (t - min s t) ω
          + m * ((t - min s t : ℝ≥0) : ℝ)))) ∂P := lintegral_congr hpt
    _ = _ := (lintegral_lintegral_swap hf2.aemeasurable).symm

end LatticeProb
