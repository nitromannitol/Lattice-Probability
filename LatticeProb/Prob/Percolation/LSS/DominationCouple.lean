import LatticeProb.Prob.Percolation.LSS.Domination

/-!
# Finite-coordinate domination from the thinning and the coupling family

Finishing the bounded-degree domination: the finite-coordinate product expansion,
finite-coordinate domination from the thinning, and the consistent projective family of
couplings giving the unconditional bounded-degree theorem.

Ported from the Exploding-Sandpiles formalization, `Support/ExtLSSProofFinal.lean` and
`Support/ExtLSSProofCouple.lean`.
-/

namespace LatticeProb.Percolation.LSS

section

open MeasureTheory Set Filter
open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

variable {S : Type}


/-- The one-site Bernoulli law is a probability measure. -/
theorem xlss6_bitLaw_isProb {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    IsProbabilityMeasure (bitLaw q) := by
  refine ⟨?_⟩
  unfold bitLaw
  simp only [Measure.add_apply, Measure.smul_apply, MeasureTheory.measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  norm_num

/-- The product law of a `T`-determined set, expanded over the subsets of `T`. -/
theorem xlss6_bernoulli_powerset [DecidableEq S] (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (T : Finset S) (A : Set (S → Bool))
    (hA : MeasurableSet A)
    (hdet : ∀ x y, (∀ t ∈ T, x t = y t) → (x ∈ A ↔ y ∈ A)) :
    bernoulliProduct S ρ A =
      ∑ V ∈ T.powerset, (if (fun s => decide (s ∈ V)) ∈ A then
        ENNReal.ofReal (ρ ^ V.card * (1 - ρ) ^ (T.card - V.card)) else 0) := by
  classical
  have : IsProbabilityMeasure (bitLaw ρ) := xlss6_bitLaw_isProb hρ0 hρ1
  set B : Set (T → Bool) := T.restrict '' A with hB
  have hBmeas : MeasurableSet B := by
    have hpre : B = (fun v : T → Bool => fun s : S => decide (s ∈ xlss_Vof T v)) ⁻¹' A := by
      ext v
      rw [hB, Set.mem_preimage]
      exact xlss_mem_proj T A hdet v
    rw [hpre]
    exact (xlss_meas_Phi T) hA
  have hpre : T.restrict ⁻¹' B = A := by
    ext x
    rw [hB, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (hdet y x (fun t ht => congrFun hyx ⟨t, ht⟩)).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hν : bernoulliProduct S ρ A = Measure.pi (fun _ : T => bitLaw ρ) B := by
    have hmap : (bernoulliProduct S ρ).map T.restrict = Measure.pi (fun _ : T => bitLaw ρ) := by
      change (Measure.infinitePi (fun _ : S => bitLaw ρ)).map T.restrict = _
      rw [Measure.infinitePi_map_restrict]
    have hmeas : Measurable (Finset.restrict T : (S → Bool) → (T → Bool)) :=
      Measurable.of_eval fun t => measurable_pi_apply (t : S)
    rw [← hpre, ← hmap, Measure.map_apply hmeas hBmeas]
  calc bernoulliProduct S ρ A
      = Measure.pi (fun _ : T => bitLaw ρ) B := hν
    _ = ∑ v ∈ B.toFinset, ∏ t : T, bitLaw ρ {v t} := by
          conv_lhs => rw [← Set.coe_toFinset B]
          exact xlss_pi_eq_sum (fun _ : T => bitLaw ρ) B.toFinset
    _ = ∑ v : T → Bool, (if v ∈ B then ∏ t : T, bitLaw ρ {v t} else 0) := by
          rw [show B.toFinset = Finset.univ.filter (fun v : T → Bool => v ∈ B) from by
            ext v
            simp, Finset.sum_filter]
    _ = ∑ v : T → Bool, (fun V : Finset S =>
          if (fun s : S => decide (s ∈ V)) ∈ A then
            ENNReal.ofReal (ρ ^ V.card * (1 - ρ) ^ (T.card - V.card)) else 0) (xlss_Vof T v) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [xlss_mem_proj T A hdet v, xlss_bitLaw_prod ρ hρ0 hρ1 T v]
    _ = ∑ V ∈ T.powerset, (if (fun s : S => decide (s ∈ V)) ∈ A then
          ENNReal.ofReal (ρ ^ V.card * (1 - ρ) ^ (T.card - V.card)) else 0) :=
          xlss_sum_Vof T (fun V : Finset S =>
            if (fun s : S => decide (s ∈ V)) ∈ A then
              ENNReal.ofReal (ρ ^ V.card * (1 - ρ) ^ (T.card - V.card)) else 0)

end

section

open MeasureTheory Set Filter
open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

variable {S : Type}


/-- The pointwise thinning bound: the weighted indicators of the subsets lying in `A` never
exceed the indicator of `A`. -/
theorem xlss7_pointwise [DecidableEq S] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (ρ γ : ℝ) (T : Finset S) (w : S → Bool → Finset S → ℝ) (hw : XlssThin μ ρ γ T w)
    (A : Set (S → Bool)) (hinc : IsIncreasingSet A) (x : S → Bool) :
    ∑ V ∈ T.powerset, (if (fun s => decide (s ∈ V)) ∈ A then 1 else 0) *
      ENNReal.ofReal (∏ l ∈ T, w l (x l) V) ≤ Set.indicator A (fun _ => 1) x := by
  classical
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
    calc ∑ V ∈ T.powerset, (if (fun s => decide (s ∈ V)) ∈ A then 1 else 0) *
          ENNReal.ofReal (∏ l ∈ T, w l (x l) V)
        ≤ ∑ V ∈ T.powerset, ENNReal.ofReal (∏ l ∈ T, w l (x l) V) := by
          refine Finset.sum_le_sum fun V _ => ?_
          by_cases hVA : (fun s => decide (s ∈ V)) ∈ A
          · rw [ite_eq_left hVA, one_mul]
          · rw [ite_eq_right hVA, zero_mul]
            positivity
      _ = 1 := xlss_thin_norm_ofReal μ ρ γ T w hw x
  · rw [Set.indicator_of_notMem hx]
    refine le_of_eq (Finset.sum_eq_zero fun V hVT => ?_)
    by_cases hVA : (fun s => decide (s ∈ V)) ∈ A
    · rw [ite_eq_left hVA]
      have hVsub : V ⊆ T := Finset.mem_powerset.mp hVT
      have hex : ∃ l ∈ V, x l = false := by
        by_contra hcon
        push Not at hcon
        exact hx (hinc (fun s => decide (s ∈ V)) x hVA fun s hs => by
          have hsV : s ∈ V := by simpa using hs
          cases h : x s <;> simp_all [hcon s hsV])
      obtain ⟨l, hlV, hxl⟩ := hex
      rw [Finset.prod_eq_zero (hVsub hlV)
        (by rw [hxl, (hw.pos l (hVsub hlV) V hVsub hlV).1]), ENNReal.ofReal_zero, mul_zero]
    · rw [ite_eq_right hVA, zero_mul]

/-- Finite-coordinate domination: the thinning on `T` bounds the product law of a
`T`-determined increasing set by the given law. -/
theorem xlss7_dom_fin [DecidableEq S] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (ρ γ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (T : Finset S) (w : S → Bool → Finset S → ℝ)
    (hw : XlssThin μ ρ γ T w) (A : Set (S → Bool)) (hA : MeasurableSet A)
    (hinc : IsIncreasingSet A)
    (hdet : ∀ x y, (∀ t ∈ T, x t = y t) → (x ∈ A ↔ y ∈ A)) :
    bernoulliProduct S ρ A ≤ μ A := by
  classical
  rw [xlss6_bernoulli_powerset ρ hρ0 hρ1 T A hA hdet]
  calc ∑ V ∈ T.powerset, (if (fun s : S => decide (s ∈ V)) ∈ A then
          ENNReal.ofReal (ρ ^ V.card * (1 - ρ) ^ (T.card - V.card)) else 0)
      = ∑ V ∈ T.powerset, (if (fun s : S => decide (s ∈ V)) ∈ A then
          ∫⁻ x, ENNReal.ofReal (∏ l ∈ T, w l (x l) V) ∂μ else 0) := by
          refine Finset.sum_congr rfl fun V hV => ?_
          rw [xlss_thin_marg_ofReal μ ρ γ T w hw V (Finset.mem_powerset.mp hV)]
    _ = ∑ V ∈ T.powerset, (if (fun s : S => decide (s ∈ V)) ∈ A then 1 else 0) *
          ∫⁻ x, ENNReal.ofReal (∏ l ∈ T, w l (x l) V) ∂μ := by
          refine Finset.sum_congr rfl fun V _ => ?_
          by_cases hV : (fun s : S => decide (s ∈ V)) ∈ A <;> simp [hV]
    _ = ∫⁻ x, ∑ V ∈ T.powerset, (if (fun s : S => decide (s ∈ V)) ∈ A then 1 else 0) *
          ENNReal.ofReal (∏ l ∈ T, w l (x l) V) ∂μ := by
          rw [lintegral_finsetSum]
          case hf =>
            intro V _
            exact measurable_const.mul
              ((xlss_meas_prod T (fun l b => w l b V)).ennreal_ofReal)
          refine Finset.sum_congr rfl fun V _ => ?_
          rw [lintegral_const_mul]
          exact (xlss_meas_prod T (fun l b => w l b V)).ennreal_ofReal
    _ ≤ ∫⁻ x, Set.indicator A (fun _ => 1) x ∂μ :=
          lintegral_mono fun x => xlss7_pointwise μ ρ γ T w hw A hinc x
    _ = μ A := by
          rw [show (fun x : S → Bool => (1 : ENNReal)) = 1 from rfl,
            lintegral_indicator_one hA]

end

end LatticeProb.Percolation.LSS
