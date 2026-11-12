/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L47MeasA at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Sel2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD5
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE5
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Conditional
import LatticeProb.Bonanno.LQGMetric.Field.MarkovZBIndep
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas4
import LatticeProb.Bonanno.LQGMetric.Meas.Geod
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs

/-!
# GM Lemma 4.7: measurability inputs on a complete probability space (D70, `decisions/DEC-47.md`)

GM, arXiv:1905.00383, `uniqueness-final.tex`, §4.2: (4.8) (l. 1640–1650) defines
`𝓕_k = σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}}, P|_{[0,s_k]})`, and the proof of Lemma 4.7 (l. 1890–1912)
conditions on it. GM do not discuss measurability. Decision D70: GM §4's conditional arguments run
on a complete probability space (`[P.IsComplete]`; T4.2 is recovered by completion).

* `gm_measurableSet_of_ae_eq_um`: an event a.s. equal to the preimage of a universally measurable
  set under a random variable is measurable (complete space).
* `gm_measurable_geod_of_complete`: the a.s. unique geodesic `η` is measurable — for Borel `B`,
  `{η ∈ B}` is a.s. `{∃ geodesic in B}`, universally measurable (`uMeasurableSet_exists_geod`).
  No measurability hypothesis on `η` (T4.2's selector `sel` is arbitrary).
* `gm_measurable_tauD`, `gm_measurable_s4S`, `gm_measurable_s4T`: `τ_{ℓ𝕣}`, `s_k`, `t_k`.
* `gm_measurableSet_hitOpen`, `gm_measurableSet_hitBall` (`hHit`).
* `gm_measurableSet_stabEv` (`hStab`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-- on a complete space, an event a.s. equal to `X ⁻¹' S`, `S` universally measurable, is
measurable -/
theorem gm_measurableSet_of_ae_eq_um {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} [IsFiniteMeasure P] [P.IsComplete] {X : Ω → α} (hX : Measurable X)
    {S : Set α} (hS : UMeasurableSet S) {E : Set Ω} (hE : E =ᵐ[P] X ⁻¹' S) :
    MeasurableSet E :=
  ((UMeasurableSet.nullMeasurableSet_preimage hS hX.aemeasurable).congr hE.symm).measurable_of_complete

section
variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **the a.s. unique geodesic is measurable** on a complete space -/
theorem gm_measurable_geod_of_complete [P.IsComplete] (hD : IsWeakLQGMetric γ D c')
    (hh : IsWholePlaneGFF h P) {𝕫 𝕨 : ℂ} {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨) :
    Measurable η := by
  intro B hB
  have hS := uMeasurableSet_exists_geod D hD.measurable 𝕫 𝕨
    (Q := (Prod.snd ⁻¹' B : Set (DistC × C(unitInterval, ℂ)))) (measurable_snd hB)
  refine gm_measurableSet_of_ae_eq_um (P := P) hh.measurable hS ?_
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [hη] with ω ⟨hg, hu⟩
  simp only [mem_preimage, mem_ofPred_eq]
  constructor
  · intro hb
    exact ⟨η ω, hg, hb⟩
  · rintro ⟨p, hp, hpB⟩
    have : p = η ω := hu.unique hp hg
    exact this ▸ hpB

/-- `τ_R(𝕫)` of `D_h` is measurable on a complete space (`tauD = gmTauB` on `lenSet`) -/
theorem gm_measurable_tauD [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) (R : ℝ) :
    Measurable fun ω => tauD (D (h ω)) 𝕫 R := by
  refine Measurable.congr_ae (μ := P)
    ((gm_measurable_tauB 𝕫 R).comp (hD.measurable.comp hh.measurable)) ?_
  filter_upwards [ae_mem_lenSet h38 hγ hγ2 hD P h hh] with ω hω
  exact (gm_tauD_eq_tauB hω 𝕫 R).symm

theorem gm_measurable_s4S [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) (ℓ 𝕣 ε β : ℝ) (k : ℕ) :
    Measurable (s4S D h 𝕫 ℓ 𝕣 ε β k) := by
  have e : s4S D h 𝕫 ℓ 𝕣 ε β k = fun ω => tauD (D (h ω)) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β) :=
    funext (gm_s4S_eq D h 𝕫 ℓ 𝕣 ε β k)
  rw [e]
  exact (gm_measurable_tauD h38 hγ hγ2 hD hh 𝕫 _).mul_const _

theorem gm_measurable_s4T [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) (ℓ 𝕣 ε β : ℝ) (k : ℕ) :
    Measurable (s4T D h 𝕫 ℓ 𝕣 ε β k) := by
  have e : s4T D h 𝕫 ℓ 𝕣 ε β k =
      fun ω => tauD (D (h ω)) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β + ε ^ (2 * β)) :=
    funext (gm_s4T_eq D h 𝕫 ℓ 𝕣 ε β k)
  rw [e]
  exact (gm_measurable_tauD h38 hγ hγ2 hD hh 𝕫 _).mul_const _

/-- **`Stab_{k,r}(z)` is an event** on a complete space -/
theorem gm_measurableSet_stabEv [P.IsComplete] (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4)
    (hC27 : CONFLem2_7) (hC14 : CONFThm1_4) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P)
    {𝕫 z : ℂ} {ℓ 𝕣 ε β lam1 lam4 ν r : ℝ} {k : ℕ} {Rads : Set ℝ} (hAvAn : GMAvoidRelAn 𝕫 z r)
    (hε : 0 < ε) (ha : 0 < lam4 * ε * 𝕣) :
    MeasurableSet (gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r) := by
  refine gm_measurableSet_of_ae_eq_um (P := P) (hD.measurable.comp hh.measurable)
    (gm_uMeasurableSet_stabSetN (gm_arcRelAn 𝕫) hAvAn (ℓ * 𝕣) (1 + k * ε ^ β)
      (1 + k * ε ^ β + ε ^ (2 * β)) lam1 lam4 ε ν 𝕣 Rads) ?_
  have h1 := gm_stab_ae_eq_stabSetN h38 hC24 hC27 hC14 hγ hγ2 hD hh (𝕫 := 𝕫) (z := z) (ℓ := ℓ)
    (𝕣 := 𝕣) (β := β) (k := k) (lam1 := lam1) (ν := ν) (Rads := Rads) (r := r) hε ha
  rw [Filter.eventuallyEqSet_iff] at h1 ⊢
  filter_upwards [h1, ae_mem_lenSet h38 hγ hγ2 hD P h hh] with ω h1 hl
  simp only [mem_preimage, mem_inter_iff, Function.comp_apply]
  exact h1.trans ⟨fun hx => ⟨hl, hx⟩, fun hx => hx.2⟩

end

section Hit
variable {Ω : Type} [MeasurableSpace Ω]

/-- hit events of a measurable random path with open sets are events -/
theorem gm_measurableSet_hitOpen {η : Ω → C(unitInterval, ℂ)} (hηm : Measurable η) {U : Set ℂ}
    (hU : IsOpen U) : MeasurableSet {ω | (range (η ω) ∩ U).Nonempty} := by
  have ho : IsOpen {p : C(unitInterval, ℂ) | (range p ∩ U).Nonempty} := by
    have e : {p : C(unitInterval, ℂ) | (range p ∩ U).Nonempty} =
        ⋃ s : unitInterval, (fun p : C(unitInterval, ℂ) => p s) ⁻¹' U := by
      ext p
      simp only [mem_ofPred_eq, mem_iUnion, mem_preimage]
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, hs⟩
        exact ⟨s, hs⟩
      · rintro ⟨s, hs⟩
        exact ⟨_, ⟨s, rfl⟩, hs⟩
    rw [e]
    exact isOpen_iUnion fun s => hU.preimage (continuous_eval_const s)
  exact hηm ho.measurableSet

omit [MeasurableSpace Ω] in
/-- `gmHitBall` is the hit event of the path `η` (`𝕫 ≠ 𝕨`) -/
theorem gm_hitBall_eq (D : DistC → ContMetric) (h : Ω → DistC) {𝕫 𝕨 : ℂ} (h𝕫𝕨 : 𝕫 ≠ 𝕨)
    (η : Ω → C(unitInterval, ℂ)) (z : ℂ) (r : ℝ) :
    gmHitBall D h 𝕫 𝕨 η z r = {ω | (range (η ω) ∩ ball z r).Nonempty} := by
  ext ω
  set d := D (h ω)
  have hL : 0 < d.1 (𝕫, 𝕨) :=
    lt_of_le_of_ne (gm_D_nonneg d 𝕫 𝕨) (fun h0 => h𝕫𝕨 (d.2.eq_of_eq_zero 𝕫 𝕨 h0.symm))
  simp only [gmHitBall, geodL, mem_ofPred_eq]
  constructor
  · rintro ⟨u, -, hu⟩
    exact ⟨_, ⟨_, rfl⟩, hu⟩
  · rintro ⟨_, ⟨s, rfl⟩, hs⟩
    refine ⟨(s : ℝ) * d.1 (𝕫, 𝕨), ⟨mul_nonneg s.2.1 hL.le, ?_⟩, ?_⟩
    · exact mul_le_of_le_one_left hL.le s.2.2
    · rw [mul_div_cancel_right₀ _ hL.ne', projIcc_val]
      exact hs

/-- **`{P ∩ B_r(z) ≠ ∅}` is an event** (`hHit`) -/
theorem gm_measurableSet_hitBall (D : DistC → ContMetric) (h : Ω → DistC) {𝕫 𝕨 : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) {η : Ω → C(unitInterval, ℂ)} (hηm : Measurable η) (z : ℂ) (r : ℝ) :
    MeasurableSet (gmHitBall D h 𝕫 𝕨 η z r) := by
  rw [gm_hitBall_eq D h h𝕫𝕨 η z r]
  exact gm_measurableSet_hitOpen hηm isOpen_ball

end Hit

end LQGMetric.GM
