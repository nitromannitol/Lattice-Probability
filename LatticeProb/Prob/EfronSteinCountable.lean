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

open scoped ENNReal

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

/-! ### The resampling energy of a site -/

section Energy

variable [DecidableEq V] (ν : Measure ℝ) [IsProbabilityMeasure ν]

/-- The resampling energy of the field at the site `v`, in `ℝ≥0∞` so that no
integrability hypothesis is needed and no junk value can make it small. -/
def siteEnergy (F : (V → ℝ) → ℝ) (v : V) : ℝ≥0∞ :=
  ∫⁻ ξ, ∫⁻ t, ENNReal.ofReal ((F ξ - F (Function.update ξ v t)) ^ 2) ∂ν
    ∂(Measure.infinitePi fun _ : V => ν)

theorem measurable_updateAt (v : V) :
    Measurable (fun q : (V → ℝ) × ℝ => Function.update q.1 v q.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : i = v
  · subst hi
    simp only [Function.update_self]
    fun_prop
  · simp only [Function.update_of_ne hi]
    fun_prop

theorem measurable_resampleSq {F : (V → ℝ) → ℝ} (hFm : Measurable F) (v : V) :
    Measurable (fun q : (V → ℝ) × ℝ => (F q.1 - F (Function.update q.1 v q.2)) ^ 2) :=
  ((hFm.comp measurable_fst).sub (hFm.comp (measurable_updateAt v))).pow_const 2

theorem measurable_resampleDiff {F : (V → ℝ) → ℝ} (hFm : Measurable F) (v : V) :
    Measurable (fun q : (V → ℝ) × ℝ =>
      ENNReal.ofReal ((F q.1 - F (Function.update q.1 v q.2)) ^ 2)) :=
  (measurable_resampleSq hFm v).ennreal_ofReal

theorem siteEnergy_eq_lintegral_prod {F : (V → ℝ) → ℝ} (hFm : Measurable F) (v : V) :
    siteEnergy ν F v
      = ∫⁻ q : (V → ℝ) × ℝ, ENNReal.ofReal ((F q.1 - F (Function.update q.1 v q.2)) ^ 2)
          ∂((Measure.infinitePi fun _ : V => ν).prod ν) :=
  (lintegral_prod _ (measurable_resampleDiff hFm v).aemeasurable).symm

/-- Resampling a coordinate of `S` commutes with splicing along `S`. -/
theorem comb_update {S : Set V} [DecidablePred (· ∈ S)] {v : V} (hv : v ∈ S)
    (ω η : V → ℝ) (t : ℝ) :
    comb S (Function.update ω v t) η = Function.update (comb S ω η) v t := by
  funext i
  by_cases hi : i = v
  · subst hi
    simp [comb, hv]
  · by_cases hS : i ∈ S
    · simp [comb, hS, Function.update_of_ne hi]
    · have : i ≠ v := hi
      simp [comb, hS, Function.update_of_ne hi]

/-- **The resampling energies of the partial integral are Jensen against those
of the functional.**  Averaging out the coordinates off `S` can only decrease
the energy at a coordinate of `S`. -/
theorem siteEnergy_partialInt_le {S : Set V} [DecidablePred (· ∈ S)] {v : V} (hv : v ∈ S)
    {F : (V → ℝ) → ℝ} (hFm : Measurable F)
    (hF : Integrable F (Measure.infinitePi fun _ : V => ν)) :
    siteEnergy ν (partialInt (fun _ : V => ν) S F) v ≤ siteEnergy ν F v := by
  set P := Measure.infinitePi (fun _ : V => ν) with hP
  set Φ := partialInt (fun _ : V => ν) S F with hΦ
  set D : (V → ℝ) × ℝ → ℝ := fun q => F q.1 - F (Function.update q.1 v q.2) with hD
  -- the two almost sure integrabilities
  have h1 : ∀ᵐ ω ∂P, Integrable (fun η => F (comb S ω η)) P :=
    (integrable_comp_comb (fun _ : V => ν) S hF).prod_right_ae
  have hupdmp := measurePreserving_update_infinitePi (fun _ : V => ν) v
  have h1' : ∀ᵐ q ∂(P.prod ν), Integrable (fun η => F (comb S q.1 η)) P :=
    Measure.quasiMeasurePreserving_fst.ae h1
  have h2 : ∀ᵐ q ∂(P.prod ν),
      Integrable (fun η => F (comb S (Function.update q.1 v q.2) η)) P :=
    hupdmp.quasiMeasurePreserving.ae h1
  -- the identity for the difference of partial integrals
  have hae : ∀ᵐ q ∂(P.prod ν),
      Φ q.1 - Φ (Function.update q.1 v q.2) = ∫ η, D (comb S q.1 η, q.2) ∂P := by
    filter_upwards [h1', h2] with q hq1 hq2
    have : Φ q.1 - Φ (Function.update q.1 v q.2)
        = ∫ η, (F (comb S q.1 η) - F (comb S (Function.update q.1 v q.2) η)) ∂P :=
      (integral_sub hq1 hq2).symm
    rw [this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    rw [hD]
    simp only []
    rw [comb_update hv]
  -- Jensen, coordinate by coordinate
  have hjensen : ∀ q : (V → ℝ) × ℝ,
      ENNReal.ofReal ((∫ η, D (comb S q.1 η, q.2) ∂P) ^ 2)
        ≤ ∫⁻ η, ENNReal.ofReal ((D (comb S q.1 η, q.2)) ^ 2) ∂P := by
    intro q
    refine ofReal_sq_integral_le_lintegral P ?_
    have hupd : Measurable (fun ζ : V → ℝ => Function.update ζ v q.2) := by
      refine measurable_pi_lambda _ fun i => ?_
      by_cases hi : i = v
      · subst hi
        simp only [Function.update_self]
        fun_prop
      · simp only [Function.update_of_ne hi]
        fun_prop
    have : Measurable (fun η : V → ℝ => D (comb S q.1 η, q.2)) := by
      rw [hD]
      exact (hFm.comp ((measurable_comb S).comp (measurable_const.prodMk measurable_id))).sub
        (hFm.comp (hupd.comp
          ((measurable_comb S).comp (measurable_const.prodMk measurable_id))))
    exact this.aestronglyMeasurable
  calc siteEnergy ν Φ v
      = ∫⁻ q : (V → ℝ) × ℝ,
          ENNReal.ofReal ((Φ q.1 - Φ (Function.update q.1 v q.2)) ^ 2) ∂(P.prod ν) :=
        siteEnergy_eq_lintegral_prod ν (measurable_partialInt _ S hFm) v
    _ = ∫⁻ q : (V → ℝ) × ℝ,
          ENNReal.ofReal ((∫ η, D (comb S q.1 η, q.2) ∂P) ^ 2) ∂(P.prod ν) :=
        lintegral_congr_ae (by filter_upwards [hae] with q hq; rw [hq])
    _ ≤ ∫⁻ q : (V → ℝ) × ℝ, (∫⁻ η, ENNReal.ofReal ((D (comb S q.1 η, q.2)) ^ 2) ∂P)
          ∂(P.prod ν) := lintegral_mono hjensen
    _ = siteEnergy ν F v := by
        have hR : Measurable (fun r : (V → ℝ) × ℝ =>
            ENNReal.ofReal ((F r.1 - F (Function.update r.1 v r.2)) ^ 2)) :=
          measurable_resampleDiff hFm v
        set G : (V → ℝ) → ℝ≥0∞ := fun ζ =>
          ∫⁻ t, ENNReal.ofReal ((F ζ - F (Function.update ζ v t)) ^ 2) ∂ν with hG
        have hGmeas : Measurable G := hR.lintegral_prod_right'
        have hHmeas : Measurable (fun p : ((V → ℝ) × ℝ) × (V → ℝ) =>
            ENNReal.ofReal ((D (comb S p.1.1 p.2, p.1.2)) ^ 2)) :=
          hR.comp (((measurable_comb S).comp
            ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
              (measurable_snd.comp measurable_fst))
        have hstep1 : ∫⁻ q : (V → ℝ) × ℝ,
              (∫⁻ η, ENNReal.ofReal ((D (comb S q.1 η, q.2)) ^ 2) ∂P) ∂(P.prod ν)
            = ∫⁻ ω, ∫⁻ t, (∫⁻ η, ENNReal.ofReal ((D (comb S ω η, t)) ^ 2) ∂P) ∂ν ∂P :=
          lintegral_prod _ (hHmeas.lintegral_prod_right').aemeasurable
        have hstep2 : ∀ ω : V → ℝ,
            ∫⁻ t, (∫⁻ η, ENNReal.ofReal ((D (comb S ω η, t)) ^ 2) ∂P) ∂ν
              = ∫⁻ η, G (comb S ω η) ∂P := by
          intro ω
          have hswap : AEMeasurable (Function.uncurry
              (fun (t : ℝ) (η : V → ℝ) => ENNReal.ofReal ((D (comb S ω η, t)) ^ 2)))
              (ν.prod P) :=
            (hR.comp (((measurable_comb S).comp
              (measurable_const.prodMk measurable_snd)).prodMk measurable_fst)).aemeasurable
          exact lintegral_lintegral_swap hswap
        have hstep3 : ∫⁻ ω, (∫⁻ η, G (comb S ω η) ∂P) ∂P
            = ∫⁻ p : (V → ℝ) × (V → ℝ), G (comb S p.1 p.2) ∂(P.prod P) :=
          (lintegral_prod _ (hGmeas.comp (measurable_comb S)).aemeasurable).symm
        have hstep4 : ∫⁻ p : (V → ℝ) × (V → ℝ), G (comb S p.1 p.2) ∂(P.prod P)
            = ∫⁻ ζ, G ζ ∂P :=
          (measurePreserving_comb (fun _ : V => ν) S).lintegral_comp hGmeas
        rw [hstep1]
        rw [lintegral_congr fun ω => hstep2 ω, hstep3, hstep4]
        rfl

theorem enorm_sq_eq_ofReal_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

/-- A site whose resampling energy is finite has an integrable resampling
increment. -/
theorem integrable_resample_of_ne_top {F : (V → ℝ) → ℝ} (hFm : Measurable F) (v : V)
    (h : siteEnergy ν F v ≠ ⊤) :
    Integrable (fun q : (V → ℝ) × ℝ => (F q.1 - F (Function.update q.1 v q.2)) ^ 2)
      ((Measure.infinitePi fun _ : V => ν).prod ν) := by
  refine ⟨(measurable_resampleSq hFm v).aestronglyMeasurable, ?_⟩
  have hen : ∀ q : (V → ℝ) × ℝ,
      ‖(F q.1 - F (Function.update q.1 v q.2)) ^ 2‖ₑ
        = ENNReal.ofReal ((F q.1 - F (Function.update q.1 v q.2)) ^ 2) :=
    fun q => Real.enorm_eq_ofReal (sq_nonneg _)
  unfold HasFiniteIntegral
  simp only [hen]
  rw [← siteEnergy_eq_lintegral_prod ν hFm v]
  exact lt_of_le_of_ne le_top h

/-! ### The finite inequality, read on the field -/

/-- The resampling energy of the site `v`, as a real integral. -/
def siteEnergyReal (F : (V → ℝ) → ℝ) (v : V) : ℝ :=
  ∫ q : (V → ℝ) × ℝ, (F q.1 - F (Function.update q.1 v q.2)) ^ 2
    ∂((Measure.infinitePi fun _ : V => ν).prod ν)

/-- On a site whose resampling increment is integrable the two forms of the
energy agree. -/
theorem ofReal_siteEnergyReal {F : (V → ℝ) → ℝ} (hFm : Measurable F) (v : V)
    (h : Integrable (fun q : (V → ℝ) × ℝ => (F q.1 - F (Function.update q.1 v q.2)) ^ 2)
      ((Measure.infinitePi fun _ : V => ν).prod ν)) :
    ENNReal.ofReal (siteEnergyReal ν F v) = siteEnergy ν F v := by
  rw [siteEnergyReal,
    ofReal_integral_eq_lintegral_ofReal h (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    siteEnergy_eq_lintegral_prod ν hFm v]

/-- **The Efron-Stein inequality for a functional of finitely many
coordinates, read on the field.**  A functional that reads only the sites of a
finite set has variance at most half the total resampling energy of those
sites.  This is the finite inequality of `LatticeProb.efron_stein_var`,
transported along the reading of the field at those sites. -/
theorem variance_le_half_sum_of_local (S : Finset V) {Φ : (V → ℝ) → ℝ}
    (hΦm : Measurable Φ)
    (hloc : ∀ ω ω' : V → ℝ, (∀ v ∈ S, ω v = ω' v) → Φ ω = Φ ω')
    (hΦ2 : Integrable (fun ω => Φ ω ^ 2) (Measure.infinitePi fun _ : V => ν))
    (hE : ∀ v ∈ S, Integrable
      (fun q : (V → ℝ) × ℝ => (Φ q.1 - Φ (Function.update q.1 v q.2)) ^ 2)
      ((Measure.infinitePi fun _ : V => ν).prod ν)) :
    ∫ ω, (Φ ω - ∫ ω', Φ ω' ∂(Measure.infinitePi fun _ : V => ν)) ^ 2
        ∂(Measure.infinitePi fun _ : V => ν)
      ≤ (1 / 2) * ∑ v ∈ S, siteEnergyReal ν Φ v := by
  classical
  set P := Measure.infinitePi (fun _ : V => ν) with hP
  set k := S.card with hk
  set e : Fin k → V := fun j => ((S.equivFin.symm j : S) : V) with he
  have hein : ∀ j, e j ∈ S := fun j => (S.equivFin.symm j).2
  have heinj : Function.Injective e := by
    intro a b hab
    have : (S.equivFin.symm a) = (S.equivFin.symm b) := Subtype.ext hab
    exact S.equivFin.symm.injective this
  set T : (V → ℝ) → (Fin k → ℝ) := fun ω j => ω (e j) with hT
  have hTmeas : Measurable T := measurable_pi_lambda _ fun j => measurable_pi_apply (e j)
  have hTmap : P.map T = Measure.pi (fun _ : Fin k => ν) := infinitePi_map_comp ν e heinj
  have hTmp : MeasurePreserving T P (Measure.pi fun _ : Fin k => ν) := ⟨hTmeas, hTmap⟩
  set sp : (Fin k → ℝ) → (V → ℝ) :=
    fun x v => if h : v ∈ S then x (S.equivFin ⟨v, h⟩) else 0 with hsp
  have hspmeas : Measurable sp := by
    refine measurable_pi_lambda _ fun v => ?_
    by_cases hv : v ∈ S
    · simp only [hsp, hv, dif_pos]
      exact measurable_pi_apply _
    · simp only [hsp, hv, dif_neg, not_false_iff]
      exact measurable_const
  set G : (Fin k → ℝ) → ℝ := fun x => Φ (sp x) with hG
  have hGm : Measurable G := hΦm.comp hspmeas
  have hGT : ∀ ω : V → ℝ, G (T ω) = Φ ω := by
    intro ω
    refine hloc _ _ ?_
    intro v hv
    simp only [hsp, hv, dif_pos, hT]
    congr 1
    exact congrArg Subtype.val (S.equivFin.symm_apply_apply ⟨v, hv⟩)
  have hTupd : ∀ (ω : V → ℝ) (j : Fin k) (t : ℝ),
      T (Function.update ω (e j) t) = Function.update (T ω) j t := by
    intro ω j t
    funext j'
    simp only [hT, Function.update_apply]
    by_cases hj : j' = j
    · subst hj; simp
    · rw [if_neg hj, if_neg (fun h => hj (heinj h))]
  -- transporting integrals
  have hint : ∀ f : (Fin k → ℝ) → ℝ, AEStronglyMeasurable f (Measure.pi fun _ : Fin k => ν) →
      ∫ x, f x ∂(Measure.pi fun _ : Fin k => ν) = ∫ ω, f (T ω) ∂P := by
    intro f hf
    rw [← hTmap, integral_map hTmeas.aemeasurable (by rwa [hTmap])]
  have hintable : ∀ f : (Fin k → ℝ) → ℝ, AEStronglyMeasurable f (Measure.pi fun _ : Fin k => ν) →
      (Integrable f (Measure.pi fun _ : Fin k => ν) ↔ Integrable (fun ω => f (T ω)) P) := by
    intro f hf
    rw [← hTmap] at hf ⊢
    exact integrable_map_measure hf hTmeas.aemeasurable
  have hG2 : Integrable (fun x => G x ^ 2) (Measure.pi fun _ : Fin k => ν) := by
    refine (hintable (fun x => G x ^ 2) ((hGm.pow_const 2).aestronglyMeasurable)).mpr ?_
    simpa only [hGT] using hΦ2
  have hGmean : ∫ x, G x ∂(Measure.pi fun _ : Fin k => ν) = ∫ ω, Φ ω ∂P := by
    rw [hint G hGm.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hGT ω)
  -- transporting the energies
  set T' : (V → ℝ) × ℝ → (Fin k → ℝ) × ℝ := fun q => (T q.1, q.2) with hT'
  have hT'mp : MeasurePreserving T' (P.prod ν) ((Measure.pi fun _ : Fin k => ν).prod ν) :=
    hTmp.prod (MeasurePreserving.id ν)
  have hT'meas : Measurable T' := hT'mp.measurable
  have hupdG : ∀ (q : (V → ℝ) × ℝ) (j : Fin k),
      (G (T' q).1 - G (Function.update (T' q).1 j (T' q).2)) ^ 2
        = (Φ q.1 - Φ (Function.update q.1 (e j) q.2)) ^ 2 := by
    intro q j
    simp only [hT']
    rw [hGT, ← hTupd, hGT]
  have hEmeas : ∀ j : Fin k, Measurable
      (fun r : (Fin k → ℝ) × ℝ => (G r.1 - G (Function.update r.1 j r.2)) ^ 2) := by
    intro j
    have hupd : Measurable (fun r : (Fin k → ℝ) × ℝ => Function.update r.1 j r.2) := by
      refine measurable_pi_lambda _ fun i => ?_
      by_cases hi : i = j
      · subst hi
        simp only [Function.update_self]
        fun_prop
      · simp only [Function.update_of_ne hi]
        fun_prop
    exact ((hGm.comp measurable_fst).sub (hGm.comp hupd)).pow_const 2
  have hEint : ∀ j : Fin k, ∫ r : (Fin k → ℝ) × ℝ,
      (G r.1 - G (Function.update r.1 j r.2)) ^ 2
        ∂((Measure.pi fun _ : Fin k => ν).prod ν) = siteEnergyReal ν Φ (e j) := by
    intro j
    rw [← hT'mp.map_eq, integral_map hT'meas.aemeasurable
      ((hEmeas j).aestronglyMeasurable.mono_measure (by rw [hT'mp.map_eq]))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun q => hupdG q j)
  have hEtr : ∀ j : Fin k, Integrable
      (fun r : (Fin k → ℝ) × ℝ => (G r.1 - G (Function.update r.1 j r.2)) ^ 2)
      ((Measure.pi fun _ : Fin k => ν).prod ν) := by
    intro j
    rw [← hT'mp.map_eq]
    refine (integrable_map_measure ?_ hT'meas.aemeasurable).mpr ?_
    · exact (hEmeas j).aestronglyMeasurable.mono_measure (by rw [hT'mp.map_eq])
    · have := hE (e j) (hein j)
      refine this.congr ?_
      exact Filter.Eventually.of_forall fun q => (hupdG q j).symm
  have hmain := efron_stein_var k (fun _ : Fin k => ν) (fun _ => inferInstance) G hGm hG2 hEtr
  have hres : ∀ j : Fin k, resampleEnergy (fun _ : Fin k => ν) G j = siteEnergyReal ν Φ (e j) :=
    fun j => hEint j
  rw [Finset.sum_congr rfl fun j _ => hres j] at hmain
  have hlhs : ∫ x, (G x - ∫ y, G y ∂(Measure.pi fun _ : Fin k => ν)) ^ 2
        ∂(Measure.pi fun _ : Fin k => ν)
      = ∫ ω, (Φ ω - ∫ ω', Φ ω' ∂P) ^ 2 ∂P := by
    rw [hGmean, hint (fun x => (G x - ∫ ω', Φ ω' ∂P) ^ 2)
      (((hGm.sub measurable_const).pow_const 2).aestronglyMeasurable)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only []
      rw [hGT])
  rw [hlhs] at hmain
  have hsum : ∑ j : Fin k, siteEnergyReal ν Φ (e j) = ∑ v ∈ S, siteEnergyReal ν Φ v := by
    rw [← Finset.sum_coe_sort S (fun v => siteEnergyReal ν Φ v)]
    exact Fintype.sum_equiv S.equivFin.symm _ _ (fun j => rfl)
  rwa [hsum] at hmain

/-! ### The countable inequality -/

/-- **The Efron-Stein inequality over a countable index set.**  The variance of
a square-integrable functional of an independent field indexed by a countable
set is at most half the total resampling energy of the sites, with the classical
constant and no Lipschitz hypothesis.  The energies are read in `ℝ≥0∞`, so no
junk value can make the right-hand side small.

The proof is the finite inequality applied to the partial integral over an
increasing exhaustion of the index set: the partial integral reads only the
sites revealed so far, its resampling energies are Jensen against those of the
functional, its mean is the mean of the functional, and it converges to the
functional almost everywhere, being the conditional expectation on those sites.
Fatou transfers the variance. -/
theorem evariance_le_half_tsum_siteEnergy [Countable V] {F : (V → ℝ) → ℝ}
    (hFm : Measurable F)
    (hF2 : Integrable (fun ω => F ω ^ 2) (Measure.infinitePi fun _ : V => ν)) :
    ProbabilityTheory.evariance F (Measure.infinitePi fun _ : V => ν)
      ≤ (∑' v : V, siteEnergy ν F v) / 2 := by
  classical
  by_cases htop : (∑' v : V, siteEnergy ν F v) = ⊤
  · rw [htop, ENNReal.top_div_of_ne_top (by norm_num)]
    exact le_top
  have hfin : ∀ v : V, siteEnergy ν F v ≠ ⊤ := fun v =>
    ne_top_of_le_ne_top htop (ENNReal.le_tsum v)
  set P := Measure.infinitePi (fun _ : V => ν) with hP
  have hFint : Integrable F P := integrable_of_integrable_sq P hFm.aestronglyMeasurable hF2
  set m : ℝ := ∫ ω, F ω ∂P with hm
  obtain ⟨g, hg⟩ := exists_injective_nat V
  set Sset : ℕ → Set V := fun n => {v | g v < n} with hSset
  have hSfinite : ∀ n, (Sset n).Finite := by
    intro n
    have hsub : Sset n ⊆ g ⁻¹' (Set.Iio n) := fun v hv => hv
    exact Set.Finite.subset (Set.Finite.preimage hg.injOn (Set.finite_Iio n)) hsub
  set Sf : ℕ → Finset V := fun n => (hSfinite n).toFinset with hSf
  have hmemSf : ∀ (n : ℕ) (v : V), v ∈ Sf n ↔ v ∈ Sset n := fun n v =>
    Set.Finite.mem_toFinset _
  have hmono : Monotone Sset := fun a b hab v hv => lt_of_lt_of_le hv hab
  have hcov : ∀ v : V, ∃ n, v ∈ Sset n := fun v => ⟨g v + 1, Nat.lt_succ_self _⟩
  set Φ : ℕ → (V → ℝ) → ℝ := fun n => partialInt (fun _ : V => ν) (Sset n) F with hΦ
  have hΦm : ∀ n, Measurable (Φ n) := fun n => measurable_partialInt _ _ hFm
  have hΦmean : ∀ n, ∫ ω, Φ n ω ∂P = m := fun n => integral_partialInt _ _ hFint
  have hΦ2 : ∀ n, Integrable (fun ω => Φ n ω ^ 2) P :=
    fun n => integrable_sq_partialInt _ _ hFm hFint hF2
  have hΦloc : ∀ (n : ℕ) (ω ω' : V → ℝ), (∀ v ∈ Sf n, ω v = ω' v) → Φ n ω = Φ n ω' :=
    fun n ω ω' h => partialInt_congr _ _ F fun v hv => h v ((hmemSf n v).mpr hv)
  have hΦE : ∀ (n : ℕ), ∀ v ∈ Sf n, siteEnergy ν (Φ n) v ≤ siteEnergy ν F v :=
    fun n v hv => siteEnergy_partialInt_le ν ((hmemSf n v).mp hv) hFm hFint
  have hΦEint : ∀ (n : ℕ), ∀ v ∈ Sf n, Integrable (fun q : (V → ℝ) × ℝ =>
      (Φ n q.1 - Φ n (Function.update q.1 v q.2)) ^ 2) (P.prod ν) :=
    fun n v hv => integrable_resample_of_ne_top ν (hΦm n) v
      (ne_top_of_le_ne_top (hfin v) (hΦE n v hv))
  have hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal ((Φ n ω - m) ^ 2) ∂P
      ≤ (∑' v : V, siteEnergy ν F v) / 2 := by
    intro n
    have hint : Integrable (fun ω => (Φ n ω - m) ^ 2) P :=
      integrable_sub_const_sq (hΦm n) (hΦ2 n) m
    have h1 : ∫⁻ ω, ENNReal.ofReal ((Φ n ω - m) ^ 2) ∂P
        = ENNReal.ofReal (∫ ω, (Φ n ω - m) ^ 2 ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    have h2 : ∫ ω, (Φ n ω - m) ^ 2 ∂P ≤ 1 / 2 * ∑ v ∈ Sf n, siteEnergyReal ν (Φ n) v := by
      have hv := variance_le_half_sum_of_local ν (Sf n) (hΦm n) (hΦloc n) (hΦ2 n) (hΦEint n)
      rwa [hΦmean n] at hv
    have hnn : ∀ v ∈ Sf n, 0 ≤ siteEnergyReal ν (Φ n) v :=
      fun v _ => integral_nonneg fun _ => sq_nonneg _
    have h3 : ENNReal.ofReal (1 / 2 * ∑ v ∈ Sf n, siteEnergyReal ν (Φ n) v)
        ≤ (∑' v : V, siteEnergy ν F v) / 2 := by
      rw [show (1 : ℝ) / 2 * (∑ v ∈ Sf n, siteEnergyReal ν (Φ n) v)
            = (∑ v ∈ Sf n, siteEnergyReal ν (Φ n) v) / 2 by ring,
        ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_sum_of_nonneg hnn,
        show ENNReal.ofReal (2 : ℝ) = 2 by simp]
      refine ENNReal.div_le_div_right ?_ 2
      calc ∑ v ∈ Sf n, ENNReal.ofReal (siteEnergyReal ν (Φ n) v)
          = ∑ v ∈ Sf n, siteEnergy ν (Φ n) v :=
            Finset.sum_congr rfl fun v hv => ofReal_siteEnergyReal ν (hΦm n) v (hΦEint n v hv)
        _ ≤ ∑ v ∈ Sf n, siteEnergy ν F v := Finset.sum_le_sum (hΦE n)
        _ ≤ ∑' v : V, siteEnergy ν F v := ENNReal.sum_le_tsum _
    exact h1.trans_le ((ENNReal.ofReal_le_ofReal h2).trans h3)
  have hconv : ∀ᵐ ω ∂P, Filter.Tendsto (fun n => Φ n ω) Filter.atTop (nhds (F ω)) :=
    tendsto_partialInt ν hmono hcov hFm hFint
  have hlim : ∀ᵐ ω ∂P, ENNReal.ofReal ((F ω - m) ^ 2)
      = Filter.liminf (fun n => ENNReal.ofReal ((Φ n ω - m) ^ 2)) Filter.atTop := by
    filter_upwards [hconv] with ω hω
    have : Filter.Tendsto (fun n => ENNReal.ofReal ((Φ n ω - m) ^ 2)) Filter.atTop
        (nhds (ENNReal.ofReal ((F ω - m) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((hω.sub_const m).pow 2)
    exact this.liminf_eq.symm
  calc ProbabilityTheory.evariance F P
      = ∫⁻ ω, ENNReal.ofReal ((F ω - m) ^ 2) ∂P := by
        rw [ProbabilityTheory.evariance]
        exact lintegral_congr fun ω => enorm_sq_eq_ofReal_sq _
    _ = ∫⁻ ω, Filter.liminf (fun n => ENNReal.ofReal ((Φ n ω - m) ^ 2)) Filter.atTop ∂P :=
        lintegral_congr_ae hlim
    _ ≤ Filter.liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((Φ n ω - m) ^ 2) ∂P) Filter.atTop :=
        lintegral_liminf_le fun n => (((hΦm n).sub measurable_const).pow_const 2).ennreal_ofReal
    _ ≤ Filter.liminf (fun _ : ℕ => (∑' v : V, siteEnergy ν F v) / 2) Filter.atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound)
    _ = (∑' v : V, siteEnergy ν F v) / 2 := Filter.liminf_const _

/-- The countable Efron-Stein inequality with the energies written out, in the
form the random-walk-in-random-scenery formalization asks for.  The only
hypothesis beyond measurability is that the functional is square integrable,
which is what `F ∈ L²` means; without it the left-hand side reads the junk value
of the mean. -/
theorem evariance_le_half_sum_resample [Countable V] (F : (V → ℝ) → ℝ)
    (hF : Measurable F)
    (hF2 : Integrable (fun ω => F ω ^ 2) (Measure.infinitePi fun _ : V => ν)) :
    ProbabilityTheory.evariance F (Measure.infinitePi fun _ : V => ν)
      ≤ (∑' v : V, ∫⁻ ξ, ∫⁻ t, ENNReal.ofReal ((F ξ - F (Function.update ξ v t)) ^ 2) ∂ν
          ∂(Measure.infinitePi fun _ : V => ν)) / 2 :=
  evariance_le_half_tsum_siteEnergy ν hF hF2

end Energy

end LatticeProb

end
