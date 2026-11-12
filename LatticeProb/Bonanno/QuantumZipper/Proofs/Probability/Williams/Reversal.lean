/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.Reversal at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm14.FromThm13

/-!
# W2: Lebesgue duality (fixed-time reversal of Brownian motion with drift)

Node W2 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1), a step of the proof of L14
(`WilliamsDriftDecomposition`): for `W = dpath σ μ b` (a drift-`μ` Brownian motion) and every
measurable `F : (ℝ≥0 → ℝ) → ℝ≥0∞`,

`∫⁻ x, ∫⁻ ω, F (x + W(· ∧ T)) ∂P ∂volume = ∫⁻ y, ∫⁻ ω, F (y + (σ b − μ·)(T − ·)) ∂P ∂volume.`

The substitution `x = y − Ŵ(T)`, where `Ŵ = σ · revBM b T + μ·` is the drift-`μ` reverse
Brownian motion on `[0,T]` (a drift-`μ` Brownian motion by
`Thm14FromThm13.isBrownianReal_revBM`), is a *scalar* translation of the outer Lebesgue integral
(separately for each `ω`, so it is measure preserving on `ℝ`), and the `ω`-law of the stopped
reverse path equals that of the stopped direct path (`GermZeroOne.map_path_eq_of_isPreBrownianReal`
pushed forward by the deterministic stopping map `w ↦ w(· ∧ T)`). Tonelli's theorem swaps the two
integrals twice.

Source: `blueprint/EXT_PP_BLUEPRINT.md` §A.1 W2 (route). **Own proof** via the project's
fixed-time reversal `Thm14FromThm13.isBrownianReal_revBM` (itself an own elementary proof); the
classical reference Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Ch. VII §4
("Time Reversal and Applications") reverses at *L-times* (the last-exit / excursion decomposition)
and is not the fixed-time statement used here (AUDIT9 P9-8). The change of variables and the
Tonelli bookkeeping are likewise an own elementary proof following the blueprint's sketch: no
source states them in this form, and both are immediate from translation invariance of Lebesgue
measure on `ℝ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ}

/-! ## Deterministic reversal identity -/

/-- The time-reversed Brownian motion at its own reversal time: `revBM b T T = -b T`, for paths
started at `0`. -/
theorem revBM_at_self (hb : GoodBM b P) (T : ℝ≥0) (ω : Ω) :
    Thm14FromThm13.revBM b T T ω = - b T ω := by
  simp only [Thm14FromThm13.revBM, min_self, max_self, tsub_self, hb.zero ω]
  ring

/-- **Deterministic reversal identity.** For every `ω` and every real `c`, the reversed
drift-`(-μ)` path `t ↦ c + (σ b − μ·)(T − t)` is the stopped reverse drift-`μ` path
`t ↦ dpath σ μ (revBM b T) ω (t ∧ T)`, shifted by `−dpath σ μ (revBM b T) ω T`. (Both paths are
constant after time `T`.) -/
theorem add_dpath_tsub_eq (hb : GoodBM b P) (σ μ : ℝ) (T : ℝ≥0) (ω : Ω) (c : ℝ) :
    (fun t : ℝ≥0 => c + dpath σ (-μ) b ω (T - t)) =
      fun t => (c - dpath σ μ (Thm14FromThm13.revBM b T) ω T)
        + dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T) := by
  funext t
  rcases le_total t T with h | h
  · have hRt : Thm14FromThm13.revBM b T t ω = b (T - t) ω - b T ω := by
      simp only [Thm14FromThm13.revBM, min_eq_left h, max_eq_right h]
    simp only [dpath, min_eq_left h, hRt, revBM_at_self hb T ω, NNReal.coe_sub h]
    ring
  · simp only [dpath, min_eq_right h, tsub_eq_zero_of_le h,
      revBM_at_self hb T ω, hb.zero ω, NNReal.coe_zero, mul_zero, add_zero]
    ring

/-! ## Translation of the outer Lebesgue integral -/

/-- Shifting the value of a path by a constant does not change the Lebesgue integral over `y`:
`∫⁻ y, G (y + c + q) dy = ∫⁻ y, G (y + q) dy` for a fixed path `q`. This is translation invariance
of Lebesgue measure on `ℝ` in the value variable. -/
theorem lintegral_path_add_const_eq (c : ℝ) (q : ℝ≥0 → ℝ) (G : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ y, G (fun t : ℝ≥0 => (y + c) + q t) ∂volume = ∫⁻ y, G (fun t : ℝ≥0 => y + q t) ∂volume := by
  have hm₁ : Measurable fun y : ℝ => (fun t : ℝ≥0 => (y + c) + q t) :=
    measurable_pi_iff.2 fun t => (measurable_id.add_const c).add_const (q t)
  have hm₂ : Measurable fun y : ℝ => (fun t : ℝ≥0 => y + q t) :=
    measurable_pi_iff.2 fun t => measurable_id.add_const (q t)
  have hcm : Measurable fun y : ℝ => y + c := measurable_id.add_const c
  have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + c) = volume :=
    MeasureTheory.map_add_right_eq_self volume c
  have hcomp : (fun y : ℝ => fun t : ℝ≥0 => (y + c) + q t)
      = (fun y : ℝ => fun t : ℝ≥0 => y + q t) ∘ (fun y : ℝ => y + c) := rfl
  calc ∫⁻ y, G (fun t : ℝ≥0 => (y + c) + q t) ∂volume
      = ∫⁻ w, G w ∂(volume.map fun y : ℝ => fun t : ℝ≥0 => (y + c) + q t) :=
        (lintegral_map hG hm₁).symm
    _ = ∫⁻ w, G w ∂(volume.map fun y : ℝ => fun t : ℝ≥0 => y + q t) := by
        congr 1
        rw [hcomp, ← Measure.map_map hm₂ hcm, hmap]
    _ = ∫⁻ y, G (fun t : ℝ≥0 => y + q t) ∂volume := lintegral_map hG hm₂

/-- The functional `w ↦ ∫⁻ y, F (y + w)` on the path space is measurable. -/
theorem measurable_lintegral_path_add_val {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun w : ℝ≥0 → ℝ => ∫⁻ y, F (fun t : ℝ≥0 => y + w t) ∂volume := by
  refine Measurable.lintegral_prod_right
    (f := fun (w : ℝ≥0 → ℝ) (y : ℝ) => F (fun t : ℝ≥0 => y + w t)) ?_
  exact hF.comp (measurable_pi_iff.2 fun t =>
    measurable_snd.add ((measurable_pi_apply t).comp measurable_fst))

/-- Two path-valued maps with the same law give the same integral for every measurable
functional. -/
theorem lintegral_of_map_eq {Φ Φ' : Ω → ℝ≥0 → ℝ} (hm : P.map Φ = P.map Φ')
    {G : (ℝ≥0 → ℝ) → ℝ≥0∞} (hG : Measurable G) (hΦ : Measurable Φ) (hΦ' : Measurable Φ') :
    ∫⁻ ω, G (Φ ω) ∂P = ∫⁻ ω, G (Φ' ω) ∂P := by
  calc ∫⁻ ω, G (Φ ω) ∂P = ∫⁻ w, G w ∂(P.map Φ) := (lintegral_map hG hΦ).symm
    _ = ∫⁻ w, G w ∂(P.map Φ') := by rw [hm]
    _ = ∫⁻ ω, G (Φ' ω) ∂P := lintegral_map hG hΦ'

/-! ## The law of the stopped drift path -/

/-- **Law of the stopped drift path.** The stopped drift-`μ` path of `b` and the stopped drift-`μ`
path of the time-reversed Brownian motion `revBM b T` have the same law on `ℝ≥0 → ℝ`. -/
theorem map_dpath_min_eq (hb : GoodBM b P) (σ μ : ℝ) (T : ℝ≥0) :
    P.map (fun ω => fun t : ℝ≥0 => dpath σ μ b ω (min t T)) =
      P.map (fun ω => fun t : ℝ≥0 => dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T)) := by
  have hB : IsBrownianReal b P := ⟨hb.pre, Filter.Eventually.of_forall hb.cont⟩
  have hrev : IsPreBrownianReal (Thm14FromThm13.revBM b T) P :=
    (Thm14FromThm13.isBrownianReal_revBM hB T).toIsPreBrownianReal
  have hrevm : ∀ t, Measurable fun ω => Thm14FromThm13.revBM b T t ω := fun t => by
    simp only [Thm14FromThm13.revBM]
    exact (hb.meas (T - min t T)).sub (hb.meas (max t T))
  have hlaw := GermZeroOne.map_path_eq_of_isPreBrownianReal hb.pre hrev hb.meas hrevm
  have hbm : Measurable fun ω => (fun t : ℝ≥0 => b t ω) := measurable_pi_iff.2 hb.meas
  have hrvp : Measurable fun ω => (fun t : ℝ≥0 => Thm14FromThm13.revBM b T t ω) :=
    measurable_pi_iff.2 hrevm
  set Ψ : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) := fun w t => σ * w (min t T) + μ * (min t T) with hΨ
  have hΨm : Measurable Ψ := by
    refine measurable_pi_iff.2 fun t => ?_
    rw [hΨ]
    exact (measurable_const.mul (measurable_pi_apply (min t T))).add_const _
  calc P.map (fun ω => fun t : ℝ≥0 => dpath σ μ b ω (min t T))
      = P.map (Ψ ∘ fun ω => fun t : ℝ≥0 => b t ω) := rfl
    _ = (P.map (fun ω => fun t : ℝ≥0 => b t ω)).map Ψ := (Measure.map_map hΨm hbm).symm
    _ = (P.map (fun ω => fun t : ℝ≥0 => Thm14FromThm13.revBM b T t ω)).map Ψ := by rw [hlaw]
    _ = P.map (fun ω => fun t : ℝ≥0 => dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T)) := by
        rw [Measure.map_map hΨm hrvp]
        congr 1

/-! ## W2: Lebesgue duality -/

/-- **W2, Lebesgue duality.** Under `volume ⊗ P`, the stopped drift-`μ` path `x + dpath σ μ b (·∧T)`
and the reversed drift-`(-μ)` path `y + dpath σ (-μ) b (T − ·)` give the same integrals. -/
theorem lintegral_reversal (hb : GoodBM b P) (σ μ : ℝ) (T : ℝ≥0)
    {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, ∫⁻ ω, F (fun t => x + dpath σ μ b ω (min t T)) ∂P ∂volume =
      ∫⁻ y, ∫⁻ ω, F (fun t => y + dpath σ (-μ) b ω (T - t)) ∂P ∂volume := by
  have hprob : IsProbabilityMeasure P := hb.pre.isGaussianProcess.isProbabilityMeasure
  -- measurability of the drift paths, as functions of `ω` and of `(x, ω)`
  have hWd : ∀ s : ℝ≥0, Measurable fun ω : Ω => dpath σ μ b ω s := fun s => by
    simp only [dpath]
    exact ((hb.meas s).const_mul σ).add_const (μ * (s : ℝ))
  have hRd : ∀ s : ℝ≥0, Measurable fun ω : Ω =>
      dpath σ μ (Thm14FromThm13.revBM b T) ω s := fun s => by
    simp only [dpath, Thm14FromThm13.revBM]
    exact (((hb.meas (T - min s T)).sub (hb.meas (max s T))).const_mul σ).add_const (μ * (s : ℝ))
  have hWd' : ∀ s : ℝ≥0, Measurable fun p : ℝ × Ω => dpath σ μ b p.2 s := fun s =>
    (hWd s).comp measurable_snd
  have hRd' : ∀ s : ℝ≥0, Measurable fun p : Ω × ℝ =>
      dpath σ μ (Thm14FromThm13.revBM b T) p.1 s := fun s => (hRd s).comp measurable_fst
  have hGm : Measurable fun w : ℝ≥0 → ℝ => ∫⁻ y, F (fun t : ℝ≥0 => y + w t) ∂volume :=
    measurable_lintegral_path_add_val hF
  have hWm : Measurable fun ω : Ω => (fun t : ℝ≥0 => dpath σ μ b ω (min t T)) :=
    measurable_pi_iff.2 fun t => hWd (min t T)
  have hRm : Measurable fun ω : Ω =>
      (fun t : ℝ≥0 => dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T)) :=
    measurable_pi_iff.2 fun t => hRd (min t T)
  -- Step 1: Tonelli, left-hand side
  have step1 : ∫⁻ x, ∫⁻ ω, F (fun t => x + dpath σ μ b ω (min t T)) ∂P ∂volume
      = ∫⁻ ω, ∫⁻ x, F (fun t => x + dpath σ μ b ω (min t T)) ∂volume ∂P :=
    lintegral_lintegral_swap (μ := volume) (ν := P)
      (f := fun (x : ℝ) (ω : Ω) => F (fun t : ℝ≥0 => x + dpath σ μ b ω (min t T))) (by
        exact (hF.comp (measurable_pi_iff.2 fun t =>
          measurable_fst.add (hWd' (min t T)))).aemeasurable)
  -- Step 2: the law of the stopped path is that of the stopped reverse path
  have step2 : ∫⁻ ω, ∫⁻ x, F (fun t => x + dpath σ μ b ω (min t T)) ∂volume ∂P
      = ∫⁻ ω, ∫⁻ x, F (fun t => x + dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T)) ∂volume ∂P :=
    lintegral_of_map_eq (map_dpath_min_eq hb σ μ T) hGm hWm hRm
  -- Step 3: per-`ω` translation of the outer integral by `-Ŵ(T)`
  have step3 : ∫⁻ ω, ∫⁻ x, F (fun t => x + dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T))
        ∂volume ∂P
      = ∫⁻ ω, ∫⁻ x,
          F (fun t => (x - dpath σ μ (Thm14FromThm13.revBM b T) ω T)
            + dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T)) ∂volume ∂P := by
    refine lintegral_congr fun ω => (lintegral_path_add_const_eq
      (-(dpath σ μ (Thm14FromThm13.revBM b T) ω T))
      (fun t => dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T)) F hF).symm
  -- Step 4: Tonelli, right-hand side
  have step4 : ∫⁻ ω, ∫⁻ x,
        F (fun t => (x - dpath σ μ (Thm14FromThm13.revBM b T) ω T)
          + dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T)) ∂volume ∂P
      = ∫⁻ x, ∫⁻ ω,
        F (fun t => (x - dpath σ μ (Thm14FromThm13.revBM b T) ω T)
          + dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T)) ∂P ∂volume := by
    refine lintegral_lintegral_swap (μ := P) (ν := volume)
      (f := fun (ω : Ω) (x : ℝ) =>
        F (fun t : ℝ≥0 => (x - dpath σ μ (Thm14FromThm13.revBM b T) ω T)
          + dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T))) (by
      exact (hF.comp (measurable_pi_iff.2 fun t =>
        (measurable_snd.sub (hRd' T)).add (hRd' (min t T)))).aemeasurable)
  -- Step 5: the deterministic reversal identity
  have step5 : ∫⁻ x, ∫⁻ ω,
        F (fun t => (x - dpath σ μ (Thm14FromThm13.revBM b T) ω T)
          + dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T)) ∂P ∂volume
      = ∫⁻ x, ∫⁻ ω, F (fun t => x + dpath σ (-μ) b ω (T - t)) ∂P ∂volume := by
    refine lintegral_congr fun x => lintegral_congr fun ω => ?_
    rw [← add_dpath_tsub_eq hb σ μ T ω x]
  calc ∫⁻ x, ∫⁻ ω, F (fun t => x + dpath σ μ b ω (min t T)) ∂P ∂volume
      = ∫⁻ ω, ∫⁻ x, F (fun t => x + dpath σ μ b ω (min t T)) ∂volume ∂P := step1
    _ = ∫⁻ ω, ∫⁻ x, F (fun t => x + dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T))
          ∂volume ∂P := step2
    _ = ∫⁻ ω, ∫⁻ x,
          F (fun t => (x - dpath σ μ (Thm14FromThm13.revBM b T) ω T)
            + dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T)) ∂volume ∂P := step3
    _ = ∫⁻ x, ∫⁻ ω,
          F (fun t => (x - dpath σ μ (Thm14FromThm13.revBM b T) ω T)
            + dpath σ μ (Thm14FromThm13.revBM b T) ω (min t T)) ∂P ∂volume := step4
    _ = ∫⁻ y, ∫⁻ ω, F (fun t => y + dpath σ (-μ) b ω (T - t)) ∂P ∂volume := step5

end QuantumZipper.Williams
