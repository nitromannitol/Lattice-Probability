/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W6Meas at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Fin4
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.Glue
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W0

/-!
# W6 (part 1): killed functionals and their measurability

Node W6 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1). This file sets up the four *killed
finite-dimensional functionals* used in the assembly of `WilliamsDriftDecomposition`:

* `hatKill a u U g y = 1{U < λ_a(ŷ)} g(ŷ(uᵢ))` with `ŷ = postLast y 0`;
* `revKill a u U g x = 1{U < T_a(x)} g((revHit x a).2 (uᵢ))`;
* `phiZ c d u U g x y = 1{U < T_c(x) + λ_d(ŷ)} g(glued c x y (uᵢ))` (the path `Z_c` killed at its
  last passage at `c + d`);
* `phiR c d u U g x x' = 1{U < T_c(x) + T_d(x')} g(concatPre c (revHit x c) (revHit x' d) (uᵢ))`.

They are measurable along any family of continuous paths with measurable evaluations
(`measurable_hitLevel_gen` etc.; for continuous paths the hitting time is measurable through the
countable description `zeroSet`), in particular on the space `CPath` of continuous paths, where
laws can be transported. `lintegral_hatKill_eq_revKill` restates W5(ii)
(`killed_fd_measure_eq`) for these functionals.

Sources: Williams (1974); Rogers–Pitman (1981), Thm 1; the bookkeeping is own elementary work.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

/-! ## The functionals -/

/-- `1{U < λ_a(ŷ)} g(ŷ(uᵢ))`, `ŷ = postLast y 0`. -/
def hatKill (a : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (g : (Fin n → ℝ) → ℝ≥0∞)
    (y : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  if U < lastPass (postLast y 0) a then g (fun i => postLast y 0 (u i)) else 0

/-- `1{U < T_a(x)} g((revHit x a).2 (uᵢ))`. -/
def revKill (a : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (g : (Fin n → ℝ) → ℝ≥0∞)
    (x : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  if U < hitLevel x (-a) then g (fun i => (revHit x a).2 (u i)) else 0

/-- The glued path `Z_c`, killed at its last passage at `c + d`. -/
def phiZ (c d : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (g : (Fin n → ℝ) → ℝ≥0∞)
    (x y : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  if U < hitLevel x (-c) + lastPass (postLast y 0) d then g (fun i => glued c x y (u i)) else 0

/-- The concatenated reversed path, killed at its lifetime. -/
def phiR (c d : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (g : (Fin n → ℝ) → ℝ≥0∞)
    (x x' : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  if U < hitLevel x (-c) + hitLevel x' (-d) then
    g (fun i => (concatPre c (revHit x c) (revHit x' d)).2 (u i)) else 0

/-! ## Measurability along families of continuous paths -/

section Gen

variable {α : Type*} [MeasurableSpace α] {f : α → ℝ≥0 → ℝ}

/-- Hitting times of continuous path families are measurable (junk value `0` off the hitting
event). Same proof as `measurable_hitLevel_dpath`. -/
theorem measurable_hitLevel_gen (hc : ∀ x, Continuous (f x)) (hm : ∀ t, Measurable fun x => f x t)
    (a : ℝ) : Measurable fun x => hitLevel (f x) a := by
  have hex : MeasurableSet {x | ∃ t : ℝ≥0, f x t = a} := by
    have e : {x | ∃ t : ℝ≥0, f x t = a} = (fun x => fun t => f x t - a) ⁻¹' zeroSet := by
      ext x
      simp only [mem_setOf_eq, mem_preimage]
      rw [mem_zeroSet_iff (show Continuous fun t => f x t - a from (hc x).sub continuous_const)]
      simp only [sub_eq_zero]
    rw [e]
    exact measurableSet_zeroSet.preimage (measurable_pi_iff.2 fun t => (hm t).sub_const a)
  refine measurable_of_Iic fun m => ?_
  have hS : (fun x => hitLevel (f x) a) ⁻¹' Iic m
      = (fun x => fun t => f x (min t m) - a) ⁻¹' zeroSet ∪ {x | ∃ t : ℝ≥0, f x t = a}ᶜ := by
    ext x
    have hw := hc x
    have hcm : Continuous fun t => f x (min t m) - a :=
      (hw.comp (continuous_id.min continuous_const)).sub continuous_const
    simp only [mem_preimage, mem_Iic, mem_union, mem_compl_iff, mem_setOf_eq]
    rw [mem_zeroSet_iff hcm]
    constructor
    · intro h
      by_cases hh : ∃ t, f x t = a
      · left
        exact ⟨hitLevel (f x) a, by rw [min_eq_left h, hitLevel_mem hw hh, sub_self]⟩
      · exact Or.inr hh
    · rintro (⟨t, ht⟩ | hh)
      · have h1 : hitLevel (f x) a ≤ min t m :=
          csInf_le (OrderBot.bddBelow _) (show f x (min t m) = a from sub_eq_zero.1 ht)
        exact h1.trans (min_le_right _ _)
      · have he : {t | f x t = a} = ∅ :=
          eq_empty_iff_forall_notMem.2 fun t ht => hh ⟨t, ht⟩
        simp [hitLevel, he]
  rw [hS]
  exact (measurableSet_zeroSet.preimage (measurable_pi_iff.2 fun t =>
    (hm _).sub_const a)).union hex.compl

theorem measurable_eval_gen (hc : ∀ x, Continuous (f x)) (hm : ∀ t, Measurable fun x => f x t)
    {s : α → ℝ≥0} (hs : Measurable s) : Measurable fun x => f x (s x) :=
  StrongMarkov.measurable_randomTime_eval (B := fun t x => f x t) hc hm hs

theorem measurable_postLast_gen (hc : ∀ x, Continuous (f x)) (hm : ∀ t, Measurable fun x => f x t)
    {s : α → ℝ≥0} (hs : Measurable s) : Measurable fun x => postLast (f x) 0 (s x) :=
  (measurable_eval_gen hc hm ((measurable_lastPass hc hm).add hs)).sub_const 0

omit [MeasurableSpace α] in
theorem continuous_postLast_gen (hc : ∀ x, Continuous (f x)) (x : α) :
    Continuous (postLast (f x) 0) :=
  ((hc x).comp (continuous_const.add continuous_id)).sub continuous_const

theorem measurable_lastPass_postLast_gen (hc : ∀ x, Continuous (f x))
    (hm : ∀ t, Measurable fun x => f x t) (a : ℝ) :
    Measurable fun x => lastPass (postLast (f x) 0) a := by
  have h := measurable_lastPass (f := fun x t => postLast (f x) 0 t - a)
    (fun x => (continuous_postLast_gen hc x).sub continuous_const)
    (fun t => (measurable_postLast_gen hc hm measurable_const).sub_const a)
  have e : ∀ w : ℝ≥0 → ℝ, lastPass (fun t => w t - a) 0 = lastPass w a := fun w => by
    simp only [lastPass, sub_eq_zero]
  simpa only [e] using h

theorem measurable_revHit_gen (hc : ∀ x, Continuous (f x)) (hm : ∀ t, Measurable fun x => f x t)
    (a : ℝ) {s : α → ℝ≥0} (hs : Measurable s) : Measurable fun x => (revHit (f x) a).2 (s x) :=
  (measurable_eval_gen hc hm ((measurable_hitLevel_gen hc hm (-a)).sub hs)).add_const a

variable {f₁ f₂ : α → ℝ≥0 → ℝ}

theorem measurable_hatKill_gen (hc : ∀ x, Continuous (f x)) (hm : ∀ t, Measurable fun x => f x t)
    (a : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun x => hatKill a u U g (f x) :=
  Measurable.ite (measurableSet_lt measurable_const (measurable_lastPass_postLast_gen hc hm a))
    (hg.comp (measurable_pi_iff.2 fun i => measurable_postLast_gen hc hm measurable_const))
    measurable_const

theorem measurable_revKill_gen (hc : ∀ x, Continuous (f x)) (hm : ∀ t, Measurable fun x => f x t)
    (a : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun x => revKill a u U g (f x) :=
  Measurable.ite (measurableSet_lt measurable_const (measurable_hitLevel_gen hc hm (-a)))
    (hg.comp (measurable_pi_iff.2 fun i => measurable_revHit_gen hc hm a measurable_const))
    measurable_const

theorem measurable_phiZ_gen (hc₁ : ∀ x, Continuous (f₁ x)) (hm₁ : ∀ t, Measurable fun x => f₁ x t)
    (hc₂ : ∀ x, Continuous (f₂ x)) (hm₂ : ∀ t, Measurable fun x => f₂ x t)
    (c d : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun x => phiZ c d u U g (f₁ x) (f₂ x) := by
  have hT := measurable_hitLevel_gen hc₁ hm₁ (-c)
  have hgl : ∀ v : ℝ≥0, Measurable fun x => glued c (f₁ x) (f₂ x) v := fun v =>
    Measurable.ite (measurableSet_le measurable_const hT)
      (measurable_revHit_gen hc₁ hm₁ c measurable_const)
      (measurable_const.add (measurable_postLast_gen hc₂ hm₂ (measurable_const.sub hT)))
  exact Measurable.ite
    (measurableSet_lt measurable_const (hT.add (measurable_lastPass_postLast_gen hc₂ hm₂ d)))
    (hg.comp (measurable_pi_iff.2 fun i => hgl (u i))) measurable_const

theorem measurable_phiR_gen (hc₁ : ∀ x, Continuous (f₁ x)) (hm₁ : ∀ t, Measurable fun x => f₁ x t)
    (hc₂ : ∀ x, Continuous (f₂ x)) (hm₂ : ∀ t, Measurable fun x => f₂ x t)
    (c d : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun x => phiR c d u U g (f₁ x) (f₂ x) := by
  have hT := measurable_hitLevel_gen hc₁ hm₁ (-c)
  have hT' := measurable_hitLevel_gen hc₂ hm₂ (-d)
  have hcat : ∀ v : ℝ≥0, Measurable fun x =>
      (concatPre c (revHit (f₁ x) c) (revHit (f₂ x) d)).2 v := fun v =>
    Measurable.ite (measurableSet_le measurable_const hT)
      (measurable_revHit_gen hc₁ hm₁ c measurable_const)
      (measurable_const.add (measurable_revHit_gen hc₂ hm₂ d (measurable_const.sub hT)))
  exact Measurable.ite (measurableSet_lt measurable_const (hT.add hT'))
    (hg.comp (measurable_pi_iff.2 fun i => hcat (u i))) measurable_const

end Gen

/-! ## On the space of continuous paths -/

theorem cPath_cont (x : CPath) : Continuous (x : ℝ≥0 → ℝ) := x.2

theorem cPath_meas (t : ℝ≥0) : Measurable fun x : CPath => (x : ℝ≥0 → ℝ) t :=
  (measurable_pi_apply t).comp measurable_subtype_coe

theorem cPath_fst_meas (t : ℝ≥0) : Measurable fun p : CPath × CPath => (p.1 : ℝ≥0 → ℝ) t :=
  (cPath_meas t).comp measurable_fst

theorem cPath_snd_meas (t : ℝ≥0) : Measurable fun p : CPath × CPath => (p.2 : ℝ≥0 → ℝ) t :=
  (cPath_meas t).comp measurable_snd

/-! ## W5(ii) for the killed functionals -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- **W5(ii)** in functional form: the killed finite-dimensional functionals of `Ŷ` (killed at
`λ_a(Ŷ)`) and of the reversed path `revHit X a` (killed at `T_a`) have equal expectations. -/
theorem lintegral_hatKill_eq_revKill (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) {a : ℝ}
    (ha : 0 < a) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (hu : ∀ i, u i ≤ U)
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, hatKill a u U g (dpath σ μ b ω) ∂P = ∫⁻ ω, revKill a u U g (dpath σ (-μ) b ω) ∂P := by
  have h := congrArg (fun m : Measure (Fin n → ℝ) => ∫⁻ x, g x ∂m)
    (killed_fd_measure_eq hb hσ hμ ha u U hu)
  have hS₁ : MeasurableSet {ω | U < lastPass (postLast (dpath σ μ b ω) 0) a} :=
    measurableSet_lt measurable_const (measurable_lastPass_postLast hb σ μ a)
  have hS₂ : MeasurableSet {ω | U < (revHit (dpath σ (-μ) b ω) a).1} :=
    measurableSet_lt measurable_const (measurable_hitLevel_dpath hb σ (-μ) (-a))
  have hφ₁ : Measurable fun ω (i : Fin n) => postLast (dpath σ μ b ω) 0 (u i) :=
    measurable_pi_iff.2 fun i => measurable_postLast_eval hb σ μ (u i)
  have hφ₂ : Measurable fun ω (i : Fin n) => (revHit (dpath σ (-μ) b ω) a).2 (u i) :=
    measurable_pi_iff.2 fun i => measurable_revHit_eval hb σ (-μ) a (u i)
  rw [lintegral_map hg hφ₁, lintegral_map hg hφ₂, ← lintegral_indicator hS₁,
    ← lintegral_indicator hS₂] at h
  convert h using 2 with ω ω
  · simp only [hatKill, indicator, mem_setOf_eq]
  · simp only [revKill, revHit, indicator, mem_setOf_eq]

end QuantumZipper.Williams
