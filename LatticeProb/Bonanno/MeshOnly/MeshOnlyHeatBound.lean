/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MeshOnly.MeshOnlyHeatBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MeshOnly.MeshOnlyHeatLaw
import LatticeProb.Bonanno.MeshOnly.MeshOnlyHeatSurvivalScale
import LatticeProb.Bonanno.MeshOnly.MeshOnlyNashKernelBound

/-! Apply the scalar Nash decay theorem to the actual killed heat density.
The only input to this generic finite-network helper is the defective Nash
inequality; its geometric proof for tile volumes is kept separate. -/

open MeasureTheory
open scoped BigOperators NNReal

namespace BouRabeeGwynne.MeshOnlyHeat

universe u

/-- The constant is chosen before the finite state space, conductances, masses,
active set, mesh, initial vertex, and time. -/
theorem heat_bound_from_defective_nash {d : ℕ} (hd : 1 ≤ d) {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (N : FiniteConductanceNetwork V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
      (S : Set V) (ε : ℝ), 0 < ε →
      (∀ f : V → ℝ, S.indicator f = f →
        (∑ v, m v * (f v)^2) ^ (2 + 2 / (d : ℝ)) ≤
          C * (∑ v, m v * |f v|) ^ (4 / (d : ℝ)) * N.energy f *
            ((∑ v, m v * (f v)^2) + ε^2 * N.energy f)) →
      ∀ x ∈ S, ∀ t : ℝ, 0 < t →
        N.killedHeatDensity m S x (2*t) x ≤
          K * (t^(-(d : ℝ)/2) + ε^d * t^(-(d : ℝ))) := by
  obtain ⟨K, hK, hdecay⟩ := on_diagonal_decay_of_defective_nash hd hC
  refine ⟨K, hK, ?_⟩
  intro V _ _ N m hm S ε hε hnash x hx t ht
  let u : ℝ → V → ℝ := N.killedHeatDensity m S x
  let X : ℝ → ℝ := fun s => ∑ v, m v * (u s v)^2
  let Q : ℝ → ℝ := fun s => N.energy (u s)
  have hX (s : ℝ) (hs : 0 ≤ s) : 0 < X s :=
    N.killedHeatDensity_weighted_sq_pos m hm S hx hs
  have hQ (s : ℝ) : 0 ≤ Q s := N.energy_nonneg _
  have hderiv (s : ℝ) (_hs : 0 ≤ s) : HasDerivAt X (-2 * Q s) s :=
    N.hasDerivAt_killedHeatDensity_weighted_sq m (fun v => (hm v).ne') S x s
  have hNash (s : ℝ) (hs : 0 ≤ s) :
      X s ^ (2 + 2 / (d : ℝ)) ≤ C * Q s * (X s + ε^2 * Q s) := by
    have hu : S.indicator (u s) = u s :=
      N.indicator_killedHeatFlow m S (Pi.single x (m x)⁻¹) s
    have hnf := hnash (u s) hu
    have hL1 : (∑ v, m v * |u s v|) ≤ 1 :=
      N.killedHeatDensity_weighted_L1_le_one m hm S hx hs
    have hL0 : 0 ≤ ∑ v, m v * |u s v| :=
      Finset.sum_nonneg fun v _ => mul_nonneg (hm v).le (abs_nonneg _)
    have hLp : (∑ v, m v * |u s v|) ^ (4 / (d : ℝ)) ≤ 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow hL0 hL1 (show 0 ≤ 4 / (d : ℝ) by positivity)
    have hfactor : C * (∑ v, m v * |u s v|) ^ (4 / (d : ℝ)) * Q s ≤ C * Q s := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLp hC) (hQ s)
    exact hnf.trans (mul_le_mul_of_nonneg_right hfactor
      (add_nonneg (hX s hs).le (mul_nonneg (sq_nonneg ε) (hQ s))))
  have hb := hdecay ε hε X Q hX (fun s _ => hQ s) hderiv hNash t ht
  simpa only [X, u,
    N.killedHeatDensity_weighted_sq_eq_double m (fun v => (hm v).ne') S hx] using hb


/-- Both estimates in Proposition 3.1, with a single constant independent of
the finite network data. The geometric Nash inequality is the sole input of
this assembly helper. -/
theorem heat_and_survival_bounds_from_defective_nash {d : ℕ} (hd : 1 ≤ d)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ {V : Type u} [Fintype V] [DecidableEq V]
      [MeasurableSpace V] [MeasurableSingletonClass V]
      (N : FiniteConductanceNetwork V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
      (S : Set V) (ε : ℝ), 0 < ε →
      (∀ f : V → ℝ, S.indicator f = f →
        (∑ v, m v * (f v)^2) ^ (2 + 2 / (d : ℝ)) ≤
          C * (∑ v, m v * |f v|) ^ (4 / (d : ℝ)) * N.energy f *
            ((∑ v, m v * (f v)^2) + ε^2 * N.energy f)) →
      ∀ x ∈ S,
        (∀ t : ℝ, 0 < t → N.killedHeatDensity m S x (2*t) x ≤
          K * (t^(-(d : ℝ)/2) + ε^d * t^(-(d : ℝ)))) ∧
        (∀ t : ℝ≥0, 0 < (t : ℝ) → ε^2 ≤ (t : ℝ) →
          (N.poissonizedUniformizedLaw m hm S x t S).toReal ≤
            K * Real.sqrt (∑ v, S.indicator m v) * (t : ℝ)^(-(d : ℝ)/4)) := by
  obtain ⟨A, hA, hdiag⟩ := heat_bound_from_defective_nash.{u} hd hC
  let K : ℝ := A + Real.sqrt (2*A)
  have hAK : A ≤ K := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hsqrtK : Real.sqrt (2*A) ≤ K := le_add_of_nonneg_left hA.le
  refine ⟨K, lt_of_lt_of_le hA hAK, ?_⟩
  intro V _ _ _ _ N m hm S ε hε hnash x hx
  have hD := hdiag N m hm S ε hε hnash x hx
  have hM : 0 ≤ ∑ v, S.indicator m v := by
    apply Finset.sum_nonneg
    intro v _
    by_cases hv : v ∈ S <;> simp [hv, (hm v).le]
  constructor
  · intro t ht
    exact (hD t ht).trans (mul_le_mul_of_nonneg_right hAK (by positivity))
  · intro t ht hscale
    have hsq : (N.poissonizedUniformizedLaw m hm S x t S).toReal ^ 2 ≤
        (∑ v, S.indicator m v) *
          (A * ((t : ℝ)^(-(d : ℝ)/2) + ε^d*(t : ℝ)^(-(d : ℝ)))) :=
      (N.poissonizedUniformizedLaw_survival_sq_le m hm S hx t).trans
        (mul_le_mul_of_nonneg_left (hD t ht) hM)
    have hs := survival_bound_of_sq hε.le ht hscale hA.le hM hsq
    exact hs.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsqrtK (Real.sqrt_nonneg _))
      (Real.rpow_nonneg t.coe_nonneg _))

end BouRabeeGwynne.MeshOnlyHeat
