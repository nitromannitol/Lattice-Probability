/-
The law of a Brownian motion on path space, and its invariance under restarting.

A pre-Brownian motion on the real line has, by definition, the canonical
finite-dimensional distributions, so any two of them induce the same measure on
the path space `ℝ≥0 → ℝ`: the measurable cylinders are a π-system generating the
product σ-algebra, and on a cylinder over a finite set of times both laws are the
same projective family.  That is `map_path_eq_of_isPreBrownianReal`, and it needs
the values of the process at each time to be measurable, since otherwise the path
map has no law at all.

For a motion on `ℝ ^ d` the increments after a time `s` are, coordinate by
coordinate, a pre-Brownian motion, and the coordinates are independent, so the
law of the increment path is the product of the coordinate laws and therefore
does not depend on `s`.  That is `IsBrownianSpace.map_shift_eq`, and it is what
lets the strong Markov property be stated with the law of the motion itself on
the right-hand side rather than the law of the increments after the stopping
time.  The rescaling by `√d` that relates a coordinate of the motion to a
standard pre-Brownian motion is undone by a measurable map on path space, which
is the identity when `d = 0` because there are then no coordinates at all.
-/
import Mathlib
import LatticeProb.Prob.BrownianMarkov

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}

theorem map_path_eq_of_isPreBrownianReal
    {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
    (hX : IsPreBrownianReal X P) (hY : IsPreBrownianReal Y Q)
    (hXm : ∀ t, Measurable (X t)) (hYm : ∀ t, Measurable (Y t)) :
    P.map (fun ω t => X t ω) = Q.map (fun ω t => Y t ω) := by
  have hmX : Measurable fun ω (t : ℝ≥0) => X t ω := measurable_pi_lambda _ hXm
  have hmY : Measurable fun ω (t : ℝ≥0) => Y t ω := measurable_pi_lambda _ hYm
  haveI : IsProbabilityMeasure (P.map fun ω (t : ℝ≥0) => X t ω) :=
    Measure.isProbabilityMeasure_map hmX.aemeasurable
  refine ext_of_generate_finite (measurableCylinders fun _ : ℝ≥0 => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · rintro s hs
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).mp hs
    rw [Measure.map_apply hmX hS.cylinder, Measure.map_apply hmY hS.cylinder]
    exact ((hX.hasLaw I).measure_eq (p := fun f => f ∈ S) hS).trans
      ((hY.hasLaw I).measure_eq (p := fun f => f ∈ S) hS).symm
  · rw [Measure.map_apply hmX MeasurableSet.univ, Measure.map_apply hmY MeasurableSet.univ]
    simp

theorem IsBrownianSpace.map_coord_shift_eq {d : ℕ} {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, Measurable (B t)) (s : ℝ≥0) (i : Fin d) :
    P.map (fun ω (t : ℝ≥0) => Real.sqrt d * (B (s + t) ω i - B s ω i))
      = P.map (fun ω (t : ℝ≥0) => Real.sqrt d * (B (0 + t) ω i - B 0 ω i)) := by
  haveI := hB.isProbabilityMeasure
  have hev : Measurable fun v : EuclideanSpace ℝ (Fin d) => v i := by fun_prop
  have hcoord : ∀ t : ℝ≥0, Measurable fun ω => B t ω i := fun t => hev.comp (hm t)
  have h1 : IsPreBrownianReal (fun t ω => Real.sqrt d * (B (s + t) ω i - B s ω i)) P := by
    have h := ((hB.shift s).coord i).toIsPreBrownianReal
    simpa only [PiLp.sub_apply, PiLp.zero_apply, sub_zero] using h
  have h2 : IsPreBrownianReal (fun t ω => Real.sqrt d * (B (0 + t) ω i - B 0 ω i)) P := by
    have h := ((hB.shift 0).coord i).toIsPreBrownianReal
    simpa only [PiLp.sub_apply, PiLp.zero_apply, sub_zero] using h
  exact map_path_eq_of_isPreBrownianReal h1 h2
    (fun t => ((hcoord (s + t)).sub (hcoord s)).const_mul _)
    (fun t => ((hcoord (0 + t)).sub (hcoord 0)).const_mul _)

theorem IsBrownianSpace.map_shift_eq {d : ℕ} {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, Measurable (B t)) (t₀ : ℝ≥0) :
    P.map (fun ω (t : ℝ≥0) => B (t₀ + t) ω - B t₀ ω)
      = P.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) := by
  haveI := hB.isProbabilityMeasure
  set c : ℝ := Real.sqrt d with hc
  have hev : ∀ i : Fin d, Measurable fun v : EuclideanSpace ℝ (Fin d) => v i := fun i => by fun_prop
  have hcoord : ∀ (t : ℝ≥0) (i : Fin d), Measurable fun ω => B t ω i :=
    fun t i => (hev i).comp (hm t)
  have hmT : ∀ s : ℝ≥0, Measurable
      (fun ω (i : Fin d) => (fun t : ℝ≥0 => c * (B (s + t) ω i - B s ω i))) := by
    intro s
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun t => ?_
    exact ((hcoord (s + t) i).sub (hcoord s i)).const_mul c
  have hindepT : ∀ s : ℝ≥0,
      iIndepFun (fun (i : Fin d) ω => (fun t : ℝ≥0 => c * (B (s + t) ω i - B s ω i))) P := by
    intro s
    refine (hB.shift s).indep.comp (fun _ (h : ℝ≥0 → ℝ) => fun t : ℝ≥0 => c * h t) (fun _ => ?_)
    refine measurable_pi_lambda _ fun t => ?_
    exact ((measurable_pi_apply t : Measurable fun h : ℝ≥0 → ℝ => h t)).const_mul c
  have hpi : ∀ s : ℝ≥0,
      P.map (fun ω (i : Fin d) => (fun t : ℝ≥0 => c * (B (s + t) ω i - B s ω i)))
        = Measure.pi (fun i : Fin d =>
            P.map (fun ω (t : ℝ≥0) => c * (B (s + t) ω i - B s ω i))) := by
    intro s
    refine (hindepT s).map_fun_eq_pi_map (fun i => ?_)
    exact (measurable_pi_lambda _ fun t =>
      ((hcoord (s + t) i).sub (hcoord s i)).const_mul c).aemeasurable
  have hT : P.map (fun ω (i : Fin d) => (fun t : ℝ≥0 => c * (B (t₀ + t) ω i - B t₀ ω i)))
      = P.map (fun ω (i : Fin d) => (fun t : ℝ≥0 => c * (B (0 + t) ω i - B 0 ω i))) := by
    rw [hpi t₀, hpi 0]
    exact congrArg Measure.pi (funext fun i => hB.map_coord_shift_eq hm t₀ i)
  have hφ : Measurable fun u : Fin d → (ℝ≥0 → ℝ) => (fun t : ℝ≥0 =>
      ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => c⁻¹ * u i t) :
        EuclideanSpace ℝ (Fin d))) := by
    refine measurable_pi_lambda _ fun t => ?_
    refine ((EuclideanSpace.equiv (Fin d) ℝ).symm.continuous).measurable.comp ?_
    refine measurable_pi_lambda _ fun i => ?_
    exact (((measurable_pi_apply t : Measurable fun h : ℝ≥0 → ℝ => h t)).comp
      ((measurable_pi_apply i : Measurable fun u : Fin d → (ℝ≥0 → ℝ) => u i))).const_mul c⁻¹
  have hsymm : ∀ (u : Fin d → ℝ) (i : Fin d),
      ((EuclideanSpace.equiv (Fin d) ℝ).symm u) i = u i := fun _ _ => rfl
  have hcne : ∀ i : Fin d, c ≠ 0 := by
    intro i
    have hd : (0 : ℝ) < d := by exact_mod_cast Fin.pos i
    rw [hc]
    exact (Real.sqrt_pos.2 hd).ne'
  have hcomp : ∀ s : ℝ≥0,
      (fun u : Fin d → (ℝ≥0 → ℝ) => (fun t : ℝ≥0 =>
        ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => c⁻¹ * u i t) :
          EuclideanSpace ℝ (Fin d))))
        ∘ (fun ω (i : Fin d) => (fun t : ℝ≥0 => c * (B (s + t) ω i - B s ω i)))
      = fun ω (t : ℝ≥0) => B (s + t) ω - B s ω := by
    intro s
    funext ω t
    ext i
    simp only [Function.comp_apply, PiLp.sub_apply, hsymm]
    rw [inv_mul_cancel_left₀ (hcne i)]
  have step : P.map (fun ω (t : ℝ≥0) => B (t₀ + t) ω - B t₀ ω)
      = P.map (fun ω (t : ℝ≥0) => B (0 + t) ω - B 0 ω) := by
    rw [← hcomp t₀, ← hcomp 0, ← Measure.map_map hφ (hmT t₀), ← Measure.map_map hφ (hmT 0), hT]
  simpa only [zero_add] using step

end LatticeProb

end
