/-
The Efron-Stein inequality over a countable index set.

`LatticeProb/Prob/EfronSteinCov.lean` proves the inequality with the classical
constant `1/2` for a function of finitely many independent coordinates.  What a
lattice application needs is the same bound for a functional of the whole
field, indexed by a countable set of sites, under `Measure.infinitePi`.

The passage is the partial integral of `LatticeProb/Prob/Splice.lean`: average
the functional over the coordinates outside a finite set `S`.  The result reads
only the coordinates in `S`, so the finite inequality applies to it; its
resampling energies are Jensen against those of the functional; its mean is the
mean of the functional; and along an increasing exhaustion of the index set it
converges almost everywhere to the functional, because it IS the conditional
expectation on the coordinates in `S` and Levy's upward theorem applies.  Fatou
then transfers the variance.
-/
import Mathlib
import LatticeProb.Prob.Splice
import LatticeProb.Prob.EfronSteinCov
import LatticeProb.Prob.FiniteMarginal

noncomputable section

namespace LatticeProb

open MeasureTheory

variable {V : Type*}

/-- The configuration `ω` read on `S` and set to zero off `S`. -/
def truncate (S : Set V) [DecidablePred (· ∈ S)] (ω : V → ℝ) : V → ℝ :=
  comb S ω 0

theorem truncate_apply_of_mem {S : Set V} [DecidablePred (· ∈ S)] {ω : V → ℝ} {i : V}
    (hi : i ∈ S) : truncate S ω i = ω i := comb_apply_of_mem hi

theorem measurable_truncate (S : Set V) [DecidablePred (· ∈ S)] :
    Measurable (truncate S : (V → ℝ) → V → ℝ) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : i ∈ S
  · simp only [truncate, comb, hi, if_pos]
    exact measurable_pi_apply i
  · simp only [truncate, comb, hi, if_neg, not_false_iff]
    exact measurable_const

/-- The sigma-algebra of the coordinates in `S`. -/
@[reducible] def coordAlg (S : Set V) [DecidablePred (· ∈ S)] : MeasurableSpace (V → ℝ) :=
  MeasurableSpace.comap (truncate S) inferInstance

theorem coordAlg_le (S : Set V) [DecidablePred (· ∈ S)] :
    coordAlg S ≤ (inferInstance : MeasurableSpace (V → ℝ)) :=
  (measurable_truncate S).comap_le

/-- A functional that reads only the coordinates in `S` is measurable for
`coordAlg S`. -/
theorem measurable_coordAlg_of_local {S : Set V} [DecidablePred (· ∈ S)] {f : (V → ℝ) → ℝ}
    (hf : Measurable f) (hloc : ∀ ω : V → ℝ, f (truncate S ω) = f ω) :
    Measurable[coordAlg S] f := by
  have h : Measurable[coordAlg S] (truncate S : (V → ℝ) → V → ℝ) :=
    Measurable.of_comap_le le_rfl
  have h2 : Measurable[coordAlg S] (fun ω : V → ℝ => f (truncate S ω)) := hf.comp h
  have hEq : (fun ω : V → ℝ => f (truncate S ω)) = f := funext hloc
  rwa [hEq] at h2

theorem comap_eval_le_coordAlg {S : Set V} [DecidablePred (· ∈ S)] {i : V} (hi : i ∈ S) :
    MeasurableSpace.comap (fun ω : V → ℝ => ω i) inferInstance ≤ coordAlg S := by
  have hcomp : (fun ω : V → ℝ => ω i) = (fun ω : V → ℝ => ω i) ∘ (truncate S) := by
    funext ω
    exact (truncate_apply_of_mem hi).symm
  calc MeasurableSpace.comap (fun ω : V → ℝ => ω i) inferInstance
      = MeasurableSpace.comap ((fun ω : V → ℝ => ω i) ∘ (truncate S)) inferInstance := by
        rw [← hcomp]
    _ = (MeasurableSpace.comap (fun ω : V → ℝ => ω i) inferInstance).comap (truncate S) :=
        (MeasurableSpace.comap_comp).symm
    _ ≤ coordAlg S := MeasurableSpace.comap_mono (measurable_pi_apply i).comap_le

theorem coordAlg_mono {S T : Set V} [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h : S ⊆ T) : coordAlg S ≤ coordAlg T := by
  have hcomp : (truncate S : (V → ℝ) → V → ℝ) = (truncate S) ∘ (truncate T) := by
    funext ω i
    by_cases hi : i ∈ S
    · rw [Function.comp_apply, truncate_apply_of_mem hi, truncate_apply_of_mem hi,
        truncate_apply_of_mem (h hi)]
    · simp [truncate, comb, hi]
  calc coordAlg S = MeasurableSpace.comap ((truncate S) ∘ (truncate T)) inferInstance := by
        rw [coordAlg, ← hcomp]
    _ = (MeasurableSpace.comap (truncate S) inferInstance).comap (truncate T) :=
        (MeasurableSpace.comap_comp).symm
    _ ≤ coordAlg T := MeasurableSpace.comap_mono (coordAlg_le S)

/-- An exhaustion of the index set by sets of coordinates generates everything. -/
theorem iSup_coordAlg_eq_top {S : ℕ → Set V} [∀ n, DecidablePred (· ∈ S n)]
    (hS : ∀ v : V, ∃ n, v ∈ S n) :
    (⨆ n, coordAlg (S n)) = (inferInstance : MeasurableSpace (V → ℝ)) := by
  refine le_antisymm (iSup_le fun n => coordAlg_le (S n)) ?_
  show (MeasurableSpace.pi : MeasurableSpace (V → ℝ)) ≤ _
  refine iSup_le fun i => ?_
  obtain ⟨n, hn⟩ := hS i
  exact le_trans (comap_eval_le_coordAlg hn) (le_iSup (fun n => coordAlg (S n)) n)

/-! ### The partial integral is the conditional expectation on the coordinates -/

section Cond

variable {S : Set V} [DecidablePred (· ∈ S)] (ν : Measure ℝ) [IsProbabilityMeasure ν]

theorem truncate_comb (ω η : V → ℝ) : truncate S (comb S ω η) = truncate S ω := by
  funext i
  by_cases hi : i ∈ S
  · rw [truncate_apply_of_mem hi, comb_apply_of_mem hi, truncate_apply_of_mem hi]
  · simp [truncate, comb, hi]

omit [IsProbabilityMeasure ν] in
theorem mem_of_coordAlg {s : Set (V → ℝ)} (hs : MeasurableSet[coordAlg S] s) (ω η : V → ℝ) :
    comb S ω η ∈ s ↔ ω ∈ s := by
  obtain ⟨B, _, rfl⟩ := hs
  simp only [Set.mem_preimage, truncate_comb]

omit [IsProbabilityMeasure ν] in
theorem partialInt_truncate {F : (V → ℝ) → ℝ} (ω : V → ℝ) :
    partialInt (fun _ : V => ν) S F (truncate S ω) = partialInt (fun _ : V => ν) S F ω :=
  partialInt_congr _ S F fun _ hi => truncate_apply_of_mem hi

/-- **The partial integral is the conditional expectation on the coordinates in
`S`.**  Averaging out the coordinates off `S` is exactly conditioning on the
coordinates in `S`; nothing about `S` is used but that a set of the
sigma-algebra is unchanged by resetting the coordinates off it. -/
theorem partialInt_ae_eq_condExp {F : (V → ℝ) → ℝ} (hFm : Measurable F)
    (hF : Integrable F (Measure.infinitePi fun _ : V => ν)) :
    partialInt (fun _ : V => ν) S F
      =ᵐ[Measure.infinitePi fun _ : V => ν]
        (Measure.infinitePi fun _ : V => ν)[F | coordAlg S] := by
  have hm : coordAlg S ≤ (inferInstance : MeasurableSpace (V → ℝ)) := coordAlg_le S
  have hPI : Integrable (partialInt (fun _ : V => ν) S F)
      (Measure.infinitePi fun _ : V => ν) := integrable_partialInt _ S hF
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hF (fun s _ _ => hPI.integrableOn)
    (fun s hs _ => ?_) ?_
  · have hsm : MeasurableSet s := hm s hs
    set χ : (V → ℝ) → ℝ := s.indicator (fun _ => (1 : ℝ)) with hχdef
    have hmul : ∀ (g : (V → ℝ) → ℝ) (x : V → ℝ), χ x * g x = s.indicator g x := by
      intro g x
      by_cases hx : x ∈ s <;> simp [hχdef, hx]
    have hloc : ∀ ω η : V → ℝ, χ (comb S ω η) = χ ω := by
      intro ω η
      by_cases hx : ω ∈ s
      · have : comb S ω η ∈ s := (mem_of_coordAlg hs ω η).mpr hx
        simp [hχdef, hx, this]
      · have : comb S ω η ∉ s := fun h => hx ((mem_of_coordAlg hs ω η).mp h)
        simp [hχdef, hx, this]
    have hint : Integrable (fun ω => χ ω * F ω) (Measure.infinitePi fun _ : V => ν) := by
      have : (fun ω => χ ω * F ω) = s.indicator F := funext fun x => hmul F x
      rw [this]
      exact hF.indicator hsm
    have hkey := integral_mul_partialInt (μ := fun _ : V => ν) (F := F) (g := χ) S hloc hint
    rw [← integral_indicator hsm, ← integral_indicator hsm]
    calc ∫ x, s.indicator (partialInt (fun _ : V => ν) S F) x
            ∂(Measure.infinitePi fun _ : V => ν)
        = ∫ x, χ x * partialInt (fun _ : V => ν) S F x
            ∂(Measure.infinitePi fun _ : V => ν) := by
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hmul _ x).symm)
      _ = ∫ x, χ x * F x ∂(Measure.infinitePi fun _ : V => ν) := hkey
      _ = ∫ x, s.indicator F x ∂(Measure.infinitePi fun _ : V => ν) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => hmul F x)
  · exact (measurable_coordAlg_of_local (measurable_partialInt _ S hFm)
      (partialInt_truncate ν)).stronglyMeasurable.aestronglyMeasurable

end Cond

/-! ### Almost sure convergence along an exhaustion -/

section Converge

variable {S : ℕ → Set V} [∀ n, DecidablePred (· ∈ S n)]
  (ν : Measure ℝ) [IsProbabilityMeasure ν]

/-- **The partial integrals converge to the functional.**  Along an increasing
exhaustion of the index set the conditional expectations on the coordinates
revealed so far converge almost everywhere, by Levy's upward theorem, and each
of them is the partial integral. -/
theorem tendsto_partialInt (hmono : Monotone S) (hcov : ∀ v : V, ∃ n, v ∈ S n)
    {F : (V → ℝ) → ℝ} (hFm : Measurable F)
    (hF : Integrable F (Measure.infinitePi fun _ : V => ν)) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : V => ν),
      Filter.Tendsto (fun n => partialInt (fun _ : V => ν) (S n) F ω) Filter.atTop
        (nhds (F ω)) := by
  set ℱ : Filtration ℕ (inferInstance : MeasurableSpace (V → ℝ)) :=
    { seq := fun n => coordAlg (S n)
      mono' := fun _ _ h => coordAlg_mono (hmono h)
      le' := fun n => coordAlg_le (S n) } with hℱ
  have hsup : (⨆ n, ℱ n) = (inferInstance : MeasurableSpace (V → ℝ)) :=
    iSup_coordAlg_eq_top hcov
  have hgmeas : StronglyMeasurable[⨆ n, ℱ n] F := by
    rw [hsup]; exact hFm.stronglyMeasurable
  have hlim := hF.tendsto_ae_condExp (ℱ := ℱ) hgmeas
  have heq : ∀ n, partialInt (fun _ : V => ν) (S n) F
      =ᵐ[Measure.infinitePi fun _ : V => ν]
        (Measure.infinitePi fun _ : V => ν)[F | ℱ n] :=
    fun n => partialInt_ae_eq_condExp ν hFm hF
  have heq' : ∀ᵐ ω ∂(Measure.infinitePi fun _ : V => ν), ∀ n,
      partialInt (fun _ : V => ν) (S n) F ω
        = ((Measure.infinitePi fun _ : V => ν)[F | ℱ n]) ω := ae_all_iff.2 heq
  filter_upwards [hlim, heq'] with ω hω hωeq
  exact hω.congr fun n => (hωeq n).symm

end Converge

end LatticeProb

end
