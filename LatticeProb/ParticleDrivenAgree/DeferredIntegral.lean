/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.DeferredIntegral at commit 66d817d. The module paths and the namespace `Parking`
   are renamed (to `LatticeProb.ParticleDrivenAgree`), and proofs are adapted to the Lean and Mathlib
   versions of this repository where needed. -/
import LatticeProb.ParticleDrivenAgree.Measurability
import LatticeProb.ParticleDrivenAgree.Deferred
import LatticeProb.Prob.Coordinate
import LatticeProb.Invariance

/-!
# The second clause of `lem:deferred`

The second clause of `lem:deferred` (`parking.tex:659-667`): averaging over the
instructions with the configuration held fixed,

  `E[1{U_n(y) ≥ j+1} 1{ρ_j(y)=x} | η] = P(y,x) P(U_n(y) ≥ j+1 | η)`.

The event does not read the instruction of index `j` at `y`, which is the first
clause, so `LatticeProb.integral_mul_indicator_eval_prod` factors the integral:
one coordinate of an infinite product is independent of the rest, and the
stacks and the uniform variables sit in exactly that shape.

The first clause holds only for realizations whose instructions are neighbours
of the site carrying them, while the library's factorization wants invariance
under overwriting the coordinate for every realization.  `nbrProj` bridges the
two: it replaces every instruction that is not a neighbour by one that is, it
commutes with overwriting one coordinate by a neighbour, and it is the identity
almost surely.

The transition probability is read off the one-step law: the `2d` neighbours of
a site are distinct, so the law gives each of them mass `1/(2d)`.
-/

open LatticeProb (instructionLaw_isProbability rankLaw_isProbability)

noncomputable section

namespace LatticeProb.ParticleDrivenAgree

open LatticeProb Finset MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- Adding a unit vector to `y` is injective in the coordinate. -/
theorem unit_add_left_inj {y : Site d} {i j : Fin d} (h : y + unit i = y + unit j) : i = j := by
  by_contra hne
  have := congrFun h i
  simp [unit, Pi.single_eq_same,  Pi.single_eq_of_ne hne] at this

/-- Subtracting a unit vector from `y` is injective in the coordinate. -/
theorem unit_sub_left_inj {y : Site d} {i j : Fin d} (h : y - unit i = y - unit j) : i = j := by
  by_contra hne
  have := congrFun h i
  simp [unit, Pi.single_eq_same,  Pi.single_eq_of_ne hne] at this

/-- Adding a unit vector to `y` never lands where subtracting a unit vector
does. -/
theorem unit_add_ne_sub (y : Site d) (i j : Fin d) : y + unit i ≠ y - unit j := by
  intro h
  have := congrFun h i
  by_cases hij : i = j
  · subst hij; simp [unit, Pi.single_eq_same] at this; omega
  · simp [unit, Pi.single_eq_same,  Pi.single_eq_of_ne hij] at this

/-- Summing the two Dirac masses `dirac (y + unit i)` and `dirac (y - unit i)`
over all coordinates `i` gives `1` at each of the `2d` neighbours of `y` (using
`unit_add_left_inj`, `unit_sub_left_inj` and `unit_add_ne_sub` to see the sum has
no repeated mass) and `0` elsewhere. -/
theorem sum_dirac_nbr (y x : Site d) :
    (∑ i : Fin d, ((Measure.dirac (y + unit i) + Measure.dirac (y - unit i))
        ({x} : Set (Site d))))
      = if x ∈ nbrFinset y then 1 else 0 := by
  classical
  simp only [Measure.coe_add, Pi.add_apply, Measure.dirac_apply]
  by_cases hx : x ∈ nbrFinset y
  · rw [if_pos hx]
    obtain ⟨i, hi | hi⟩ := mem_nbrFinset_iff.mp hx
    · rw [Finset.sum_eq_single i]
      · rw [Set.indicator_of_mem (by simp [hi]), Set.indicator_of_notMem
          (by simpa using fun hc => unit_add_ne_sub y i i ((hc.trans hi).symm))]
        simp
      · intro j _ hj
        rw [Set.indicator_of_notMem (by
            simpa using fun hc => hj (unit_add_left_inj (hc.trans hi))),
          Set.indicator_of_notMem (by
            simpa using fun hc => unit_add_ne_sub y i j ((hc.trans hi).symm))]
        simp
      · intro hc; exact absurd (Finset.mem_univ i) hc
    · rw [Finset.sum_eq_single i]
      · rw [Set.indicator_of_notMem (by
            simpa using fun hc => unit_add_ne_sub y i i (hc.trans hi)),
          Set.indicator_of_mem (by simp [hi])]
        simp
      · intro j _ hj
        rw [Set.indicator_of_notMem (by
            simpa using fun hc => unit_add_ne_sub y j i (hc.trans hi)),
          Set.indicator_of_notMem (by
            simpa using fun hc => hj (unit_sub_left_inj (hc.trans hi)))]
        simp
      · intro hc; exact absurd (Finset.mem_univ i) hc
  · rw [if_neg hx]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Set.indicator_of_notMem (by
        simpa using fun hc : y + unit i = x => hx (hc ▸ mem_nbrFinset_add y i)),
      Set.indicator_of_notMem (by
        simpa using fun hc : y - unit i = x => hx (hc ▸ mem_nbrFinset_sub y i))]
    simp

/-- The one-step transition probability `instructionLaw y {x}` equals `kern d y x`:
the `2d` neighbours of `y` are distinct by `sum_dirac_nbr`, so the uniform law over
them gives each mass `1/(2d)`. -/
theorem instructionLaw_singleton (hd : 1 ≤ d) (y x : Site d) :
    (instructionLaw y ({x} : Set (Site d))).toReal = kern d y x := by
  have h2d : (2 * (d : ℝ≥0∞)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
    exact ⟨two_ne_zero, by omega⟩
  have h2d' : (2 * (d : ℝ≥0∞)) ≠ ⊤ := by simp [ENNReal.mul_eq_top]
  have hval : instructionLaw y ({x} : Set (Site d))
      = (2 * (d : ℝ≥0∞))⁻¹ * (if x ∈ nbrFinset y then 1 else 0) := by
    simp only [instructionLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      smul_eq_mul]
    rw [← sum_dirac_nbr y x]
  rw [hval, kern]
  by_cases hx : x ∈ nbrFinset y
  · rw [if_pos hx, if_pos hx, mul_one, ENNReal.toReal_inv, ENNReal.toReal_mul,
      ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  · rw [if_neg hx, if_neg hx, mul_zero, ENNReal.toReal_zero]

/-! ### Projecting a stack onto the neighbour stacks -/

/-- Replace every instruction that is not a neighbour of its site by one that
is.  The law of the stacks does not see the change. -/
def nbrProj (i₀ : Fin d) (σ : Site d × ℕ → Site d) : Site d × ℕ → Site d :=
  fun q => if σ q ∈ nbrFinset q.1 then σ q else q.1 + unit i₀

/-- `nbrProj i₀ σ` always outputs a neighbour of the site it is read at. -/
theorem nbrProj_mem (i₀ : Fin d) (σ : Site d × ℕ → Site d) (q : Site d × ℕ) :
    nbrProj i₀ σ q ∈ nbrFinset q.1 := by
  unfold nbrProj
  split
  · assumption
  · exact mem_nbrFinset_add q.1 i₀

/-- `nbrProj` is the identity on a stack all of whose instructions already point
to a neighbour of their site. -/
theorem nbrProj_eq_self {i₀ : Fin d} {σ : Site d × ℕ → Site d}
    (h : ∀ q, σ q ∈ nbrFinset q.1) : nbrProj i₀ σ = σ := by
  funext q; unfold nbrProj; rw [if_pos (h q)]

/-- `nbrProj` commutes with overwriting one coordinate `q₀` by a neighbour `c`
of `q₀.1`. -/
theorem nbrProj_update (i₀ : Fin d) (σ : Site d × ℕ → Site d) (q₀ : Site d × ℕ)
    {c : Site d} (hc : c ∈ nbrFinset q₀.1) :
    nbrProj i₀ (Function.update σ q₀ c) = Function.update (nbrProj i₀ σ) q₀ c := by
  funext q
  by_cases hq : q = q₀
  · subst hq; simp [nbrProj, hc]
  · simp [nbrProj, Function.update_of_ne hq]

/-- `nbrProj i₀` is measurable. -/
theorem measurable_nbrProj (i₀ : Fin d) :
    Measurable fun σ : Site d × ℕ → Site d => nbrProj i₀ σ := by
  refine Measurable.of_eval fun q => ?_
  refine Measurable.ite ?_ (measurable_pi_apply q) measurable_const
  exact (measurable_pi_apply q) (Finset.measurableSet _)

/-! ### The deferred instruction -/

/-- **The second clause of `lem:deferred`.**  Conditionally on the configuration
`η`, the event that the odometer at `y` has reached `j + 1` and the instruction of
index `j` at `y` sends the particle to `x` factors as `kern d y x` times the
probability of the odometer event alone: `nbrProj` replaces every instruction by a
neighbour without changing the odometer event (`odometer_ge_congr` via
`stepsToNeighbour_of_mem`), which is almost surely the identity
(`stackLaw_ae_nbr`), and then `LatticeProb.integral_mul_indicator_eval_prod`
factors the resulting integral over the independent coordinate `(y, j)`. -/
theorem deferred_factorization (hd : 1 ≤ d) (n : ℕ) (y x : Site d) (j : ℕ)
    (η : Site d → ℤ) :
    probGiven d η {ω | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x}
      = kern d y x * probGiven d η {ω | j + 1 ≤ U ω n y} := by
  classical
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
    fun q => instructionLaw_isProbability hd q.1
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (stackRankLaw d) := by
    unfold stackRankLaw stackLaw
    infer_instance
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  set c : Site d := y + unit i₀ with hc
  have hcmem : c ∈ nbrFinset y := mem_nbrFinset_add y i₀
  set A : Set (Data d) := {ω | j + 1 ≤ U ω n y} with hA
  have hAmeas : MeasurableSet A := by
    have : A = (fun ω : Data d => U ω n y) ⁻¹' {m : ℕ | j + 1 ≤ m} := rfl
    rw [this]
    exact (measurable_U n y) (Set.to_countable _).measurableSet
  have hemb : Measurable fun s : Randomness d => ((η, s) : Data d) :=
    measurable_const.prodMk measurable_id
  have hembP : Measurable fun s : Randomness d => ((η, nbrProj i₀ s.1, s.2) : Data d) :=
    measurable_const.prodMk
      (((measurable_nbrProj i₀).comp measurable_fst).prodMk measurable_snd)
  set F : Randomness d → ℝ := fun s => Set.indicator A (fun _ => (1 : ℝ)) ((η, s) : Data d)
    with hF
  set G : Randomness d → ℝ :=
    fun s => Set.indicator A (fun _ => (1 : ℝ)) ((η, nbrProj i₀ s.1, s.2) : Data d) with hG
  have hFmeas : Measurable F := (measurable_one.indicator hAmeas).comp hemb
  have hGmeas : Measurable G := (measurable_one.indicator hAmeas).comp hembP
  have hGbdd : ∀ s, ‖G s‖ ≤ 1 := by
    intro s
    rw [hG]
    by_cases hs : ((η, nbrProj i₀ s.1, s.2) : Data d) ∈ A
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  have hGint : Integrable G (stackRankLaw d) :=
    (integrable_const (1 : ℝ)).mono' hGmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by simpa using hGbdd s)
  have hae : ∀ᵐ s ∂(stackRankLaw d), nbrProj i₀ s.1 = s.1 := by
    have h1 : ∀ᵐ σ ∂(stackLaw d), nbrProj i₀ σ = σ :=
      (stackLaw_ae_nbr hd).mono fun σ hσ => nbrProj_eq_self hσ
    exact (Measure.quasiMeasurePreserving_fst).ae h1
  have hFG : G =ᵐ[stackRankLaw d] F := hae.mono fun s hs => by
    show Set.indicator A (fun _ => (1 : ℝ)) ((η, nbrProj i₀ s.1, s.2) : Data d)
      = Set.indicator A (fun _ => (1 : ℝ)) ((η, s) : Data d)
    rw [hs]
  have hinv : ∀ (σ : Site d × ℕ → Site d) (r : Label d × ℕ → ℝ),
      G (Function.update σ (y, j) c, r) = G (σ, r) := by
    intro σ r
    have hstep1 : ∀ q : Site d × ℕ, nbrProj i₀ σ q ∈ nbrFinset q.1 := nbrProj_mem i₀ σ
    have hstep2 : ∀ q : Site d × ℕ,
        Function.update (nbrProj i₀ σ) (y, j) c q ∈ nbrFinset q.1 := by
      intro q
      by_cases hq : q = (y, j)
      · subst hq; simpa using hcmem
      · rw [Function.update_of_ne hq]; exact hstep1 q
    have hne : ∀ q : Site d × ℕ, q ≠ (y, j) →
        Function.update (nbrProj i₀ σ) (y, j) c q = nbrProj i₀ σ q := fun q hq =>
      Function.update_of_ne hq _ _
    have hiff := odometer_ge_congr
      (D := toDriver ((η, Function.update (nbrProj i₀ σ) (y, j) c, r) : Data d))
      (D' := toDriver ((η, nbrProj i₀ σ, r) : Data d))
      (stepsToNeighbour_of_mem hstep2) (stepsToNeighbour_of_mem hstep1) rfl rfl y j n hne
    show Set.indicator A (fun _ => (1 : ℝ))
        ((η, nbrProj i₀ (Function.update σ (y, j) c), r) : Data d)
      = Set.indicator A (fun _ => (1 : ℝ)) ((η, nbrProj i₀ σ, r) : Data d)
    rw [nbrProj_update i₀ σ (y, j) hcmem]
    by_cases h1 : ((η, Function.update (nbrProj i₀ σ) (y, j) c, r) : Data d) ∈ A
    · rw [Set.indicator_of_mem h1,
        Set.indicator_of_mem (show ((η, nbrProj i₀ σ, r) : Data d) ∈ A from hiff.mp h1)]
    · rw [Set.indicator_of_notMem h1,
        Set.indicator_of_notMem
          (show ((η, nbrProj i₀ σ, r) : Data d) ∉ A from fun hcon => h1 (hiff.mpr hcon))]
  have hsplit : ∀ s : Randomness d,
      Set.indicator {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x} (fun _ => (1 : ℝ))
          ((η, s) : Data d)
        = F s * Set.indicator ({x} : Set (Site d)) (fun _ => (1 : ℝ)) (s.1 (y, j)) := by
    intro s
    show Set.indicator {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x} (fun _ => (1 : ℝ))
          ((η, s) : Data d)
        = Set.indicator A (fun _ => (1 : ℝ)) ((η, s) : Data d)
          * Set.indicator ({x} : Set (Site d)) (fun _ => (1 : ℝ)) (s.1 (y, j))
    by_cases h1 : ((η, s) : Data d) ∈ A <;> by_cases h2 : s.1 (y, j) = x
    · rw [Set.indicator_of_mem (show ((η, s) : Data d)
          ∈ {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x} from ⟨h1, h2⟩),
        Set.indicator_of_mem h1,
        Set.indicator_of_mem (show s.1 (y, j) ∈ ({x} : Set (Site d)) from h2)]
      simp
    · rw [Set.indicator_of_notMem (show ((η, s) : Data d)
          ∉ {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x} from fun hcon => h2 hcon.2),
        Set.indicator_of_notMem (show s.1 (y, j) ∉ ({x} : Set (Site d)) from h2)]
      simp
    · rw [Set.indicator_of_notMem (show ((η, s) : Data d)
          ∉ {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x} from fun hcon => h1 hcon.1),
        Set.indicator_of_notMem h1]
      simp
    · rw [Set.indicator_of_notMem (show ((η, s) : Data d)
          ∉ {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x} from fun hcon => h1 hcon.1),
        Set.indicator_of_notMem h1]
      simp
  have hlib := LatticeProb.integral_mul_indicator_eval_prod
    (μ := fun q : Site d × ℕ => instructionLaw (d := d) q.1) (ν := rankLaw d)
    (y, j) c G hGmeas hGint hinv (measurableSet_singleton x)
  show ∫ s, Set.indicator {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x}
      (fun _ => (1 : ℝ)) ((η, s) : Data d) ∂(stackRankLaw d) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)]
  have hstep : ∫ s : Randomness d, F s *
        Set.indicator ({x} : Set (Site d)) (fun _ => (1 : ℝ)) (s.1 (y, j)) ∂(stackRankLaw d)
      = ∫ s : Randomness d, G s *
        Set.indicator ({x} : Set (Site d)) (fun _ => (1 : ℝ)) (s.1 (y, j)) ∂(stackRankLaw d) :=
    integral_congr_ae (hFG.symm.mono fun s hs => by
      show F s * Set.indicator ({x} : Set (Site d)) (fun _ => (1 : ℝ)) (s.1 (y, j))
        = G s * Set.indicator ({x} : Set (Site d)) (fun _ => (1 : ℝ)) (s.1 (y, j))
      rw [hs])
  rw [hstep]
  have hgoal : ∫ s : Randomness d, G s *
        Set.indicator ({x} : Set (Site d)) (fun _ => (1 : ℝ)) (s.1 (y, j)) ∂(stackRankLaw d)
      = (instructionLaw (d := d) y ({x} : Set (Site d))).toReal
        * ∫ s : Randomness d, G s ∂(stackRankLaw d) := hlib
  rw [hgoal, instructionLaw_singleton hd y x]
  show _ = kern d y x * ∫ s, F s ∂(stackRankLaw d)
  rw [integral_congr_ae hFG]

end LatticeProb.ParticleDrivenAgree

end
