import Mathlib

/-!
# Covariances on product and finite power spaces

Covariance computations for random variables built from independent factors:

* `LatticeProb.covariance_comp_measurePreserving`, `LatticeProb.integral_comp_measurePreserving`:
  covariances and expectations are invariant under a measure-preserving change of variables.
* `LatticeProb.covariance_prod_add`: on a product of probability spaces, the covariance of two sums
  `F x.1 + G x.2` and `F' x.1 + G' x.2` of square-integrable functions of the two factors is the sum of
  the covariances of the two parts.
* `LatticeProb.covariance_pi_eval_comp`: on a finite power `Measure.pi (fun _ => P)`, the covariance of
  `f (w p)` and `g (w q)` is `Cov(f, g)` if `p = q` and `0` otherwise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LatticeProb

section Comp

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- The expectation of a function of a measure-preserving map. -/
theorem integral_comp_measurePreserving {f : α → β} (hf : MeasurePreserving f μ ν) {X : β → ℝ}
    (hX : AEStronglyMeasurable X ν) : ∫ a, X (f a) ∂μ = ∫ b, X b ∂ν := by
  rw [← hf.map_eq] at hX ⊢
  exact (integral_map hf.measurable.aemeasurable hX).symm

/-- Covariance is invariant under a measure-preserving change of variables. -/
theorem covariance_comp_measurePreserving {f : α → β} (hf : MeasurePreserving f μ ν) {X Y : β → ℝ}
    (hX : AEStronglyMeasurable X ν) (hY : AEStronglyMeasurable Y ν) :
    cov[fun a => X (f a), fun a => Y (f a); μ] = cov[X, Y; ν] := by
  have h := covariance_map (μ := μ) (Z := f) (X := X) (Y := Y) (by rwa [hf.map_eq])
    (by rwa [hf.map_eq]) hf.measurable.aemeasurable
  rw [hf.map_eq] at h
  exact h.symm

end Comp

section Prod

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Covariance of independent sums on a product space.** -/
theorem covariance_prod_add {F F' : α → ℝ} {G G' : β → ℝ} (hF : MemLp F 2 μ) (hF' : MemLp F' 2 μ)
    (hG : MemLp G 2 ν) (hG' : MemLp G' 2 ν) :
    cov[fun x : α × β => F x.1 + G x.2, fun x : α × β => F' x.1 + G' x.2; μ.prod ν] =
      cov[F, F'; μ] + cov[G, G'; ν] := by
  have h1 : ∀ {A : α → ℝ}, MemLp A 2 μ → MemLp (fun x : α × β => A x.1) 2 (μ.prod ν) :=
    fun h => h.comp_measurePreserving measurePreserving_fst
  have h2 : ∀ {B : β → ℝ}, MemLp B 2 ν → MemLp (fun x : α × β => B x.2) 2 (μ.prod ν) :=
    fun h => h.comp_measurePreserving measurePreserving_snd
  change cov[(fun x : α × β => F x.1) + (fun x : α × β => G x.2),
    (fun x : α × β => F' x.1) + (fun x : α × β => G' x.2); μ.prod ν] = _
  rw [covariance_add_left (h1 hF) (h2 hG) ((h1 hF').add (h2 hG')),
    covariance_add_right (h1 hF) (h1 hF') (h2 hG'),
    covariance_add_right (h2 hG) (h1 hF') (h2 hG'),
    (indepFun_prod₀ hF.aemeasurable hG'.aemeasurable).covariance_eq_zero (h1 hF) (h2 hG'),
    covariance_comm (fun x : α × β => G x.2),
    (indepFun_prod₀ hF'.aemeasurable hG.aemeasurable).covariance_eq_zero (h1 hF') (h2 hG),
    covariance_comp_measurePreserving measurePreserving_fst hF.aestronglyMeasurable
      hF'.aestronglyMeasurable,
    covariance_comp_measurePreserving measurePreserving_snd hG.aestronglyMeasurable
      hG'.aestronglyMeasurable]
  ring

end Prod

section Pi

variable {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- Functions of two different coordinates of a finite power probability space are independent. -/
theorem indepFun_pi_eval_comp {p q : κ} (hpq : p ≠ q) {f g : Ω → ℝ} (hf : AEMeasurable f P)
    (hg : AEMeasurable g P) :
    IndepFun (fun w : κ → Ω => f (w p)) (fun w : κ → Ω => g (w q)) (Measure.pi fun _ => P) := by
  have h := (iIndepFun_pi (μ := fun _ : κ => P) (X := fun r => if r = p then f else g)
    (fun r => by split_ifs <;> assumption)).indepFun hpq
  simpa [hpq.symm] using h

/-- **Covariance of functions of the coordinates of a finite power.** -/
theorem covariance_pi_eval_comp (p q : κ) {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    cov[fun w : κ → Ω => f (w p), fun w : κ → Ω => g (w q); Measure.pi fun _ => P] =
      if p = q then cov[f, g; P] else 0 := by
  split_ifs with h
  · subst h
    exact covariance_comp_measurePreserving (measurePreserving_eval (fun _ : κ => P) p)
      hf.aestronglyMeasurable hg.aestronglyMeasurable
  · exact (indepFun_pi_eval_comp h hf.aemeasurable hg.aemeasurable).covariance_eq_zero
      (hf.comp_measurePreserving (measurePreserving_eval (fun _ : κ => P) p))
      (hg.comp_measurePreserving (measurePreserving_eval (fun _ : κ => P) q))

end Pi

end LatticeProb
