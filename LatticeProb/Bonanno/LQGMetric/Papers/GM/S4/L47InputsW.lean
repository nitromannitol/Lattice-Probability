/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L47InputsW at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD5

/-!
# GM Lemma 4.6 (c) without the global hypothesis `𝕨 ∉ 𝓑^•_{t_k}` (task P2-L47)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 4.6, l. 1709–1716, and proof of Lemma 4.7, l. 1900–1902: GM only use the event
`{𝕨 ∉ 𝓑^•_{t_k}}` on `G = {(z,r) ∈ 𝒵_k} ∩ {𝕨 ∉ B_{3λ₄ε𝕣}(𝓑^•_{t_k})}`; it is not an a.s. fact.
P2-E3c's `gm_arcHit_ae_eq_hitU`, `gm_L4_6_hArc`, `gm_L4_6c` (`L46MeasD5.lean`) take it as the
a.s. hypothesis `hw`. Here it is removed: on `Stab ∩ Hit` it holds surely, since

* `gm_geod_mem_filledBall_of_end`: a geodesic from `𝕫` to a point `𝕨 ∈ 𝓑^•_t(𝕫)` stays in
  `𝓑^•_t(𝕫)` (its part after time `t` is a connected subset of `ℂ ∖ cl 𝓑_t` ending in the bounded
  component of `𝕨`; own elementary argument),

and on `Stab`, `B̄_r(z)` is disjoint from `𝓑^•_{t_k}` while on `Hit` the geodesic meets `B_r(z)`.
The proofs of `gm_arcHit_ae_eq_hitU_nw`, `gm_L4_6_hArc_nw`, `gm_L4_6c_nw` are those of
`L46MeasD5.lean` (P2-E3c) with this one step added.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric MeasurableSpace
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-- a geodesic from `z` to `w ∈ 𝓑^•_t(z)` stays in `𝓑^•_t(z)` -/
theorem gm_geod_mem_filledBall_of_end {D : ContMetric} {z w : ℂ} {P : ℝ → ℂ} {L t u : ℝ}
    (hP : IsGeodesicL D P L z w) (hw : w ∈ filledBall D z t) (hu : u ∈ Icc 0 L) :
    P u ∈ filledBall D z t := by
  by_contra hPu
  have hcl : closure (ballM D z t) ⊆ {x | D.1 (z, x) ≤ t} :=
    closure_minimal (fun x hx => by show D.1 (z, x) ≤ t; exact le_of_lt hx)
      (isClosed_le (D.1.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const)
  have hPucl : P u ∉ closure (ballM D z t) := fun h => hPu (Or.inl h)
  have hut : t ≤ u := by
    by_contra hlt
    refine hPucl (subset_closure ?_)
    show D.1 (z, P u) < t
    rw [gm_geodL_dist hP hu]
    exact lt_of_not_ge hlt
  have hS : P '' Icc u L ⊆ (closure (ballM D z t))ᶜ := by
    rintro _ ⟨v, hv, rfl⟩
    rcases eq_or_lt_of_le hv.1 with e | hlt
    · rw [← e]; exact hPucl
    · intro hvc
      have h1 := hcl hvc
      simp only [mem_ofPred_eq] at h1
      rw [gm_geodL_dist hP ⟨hu.1.trans hv.1, hv.2⟩] at h1
      linarith
  have hconn : IsPreconnected (P '' Icc u L) :=
    isPreconnected_Icc.image _ ((gm_geodL_continuousOn hP).mono (Icc_subset_Icc hu.1 le_rfl))
  have hsub := hconn.subset_connectedComponentIn ⟨u, ⟨le_rfl, hu.2⟩, rfl⟩ hS
  have hwS : w ∈ P '' Icc u L := ⟨L, ⟨hu.2, le_rfl⟩, hP.2.2.1⟩
  have hwcl : w ∉ closure (ballM D z t) := hS hwS
  rcases hw with hw | ⟨-, hb⟩
  · exact hwcl hw
  · rw [← connectedComponentIn_eq (hsub hwS)] at hb
    exact hPu (Or.inr ⟨hPucl, hb⟩)

variable {Ω : Type} [MeasurableSpace Ω]

/-- on `Stab ∩ Hit`, a.s., the hit events of the arc containing `P(t_k)` are metric events -/
theorem gm_arcHit_ae_eq_hitU_nw (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {𝕫 𝕨 z : ℂ} (h𝕫𝕨 : 𝕫 ≠ 𝕨) {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {ℓ 𝕣 ε β lam1 lam4 ν r : ℝ} {k : ℕ} {Rads : Set ℝ}
    (hε : 0 < ε) (ha : 0 < lam4 * ε * 𝕣) (hr : r < lam4 * ε * 𝕣) (U : Set ℂ) :
    gmArcHit D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k) U ∩
        (gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r) =ᵐ[P]
      h ⁻¹' (D ⁻¹' gmHitUSet 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β) (1 + k * ε ^ β + ε ^ (2 * β)) lam1 lam4
        ε ν 𝕣 Rads z r U) ∩
        (gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r) := by
  set c₁ := 1 + k * ε ^ β
  set cc := 1 + k * ε ^ β + ε ^ (2 * β)
  have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hc₁ : 1 ≤ c₁ := by
    have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
    simp only [c₁]
    linarith
  have hc₁c : c₁ < cc := by simp only [c₁, cc]; linarith
  have hc : 1 < cc := by linarith
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [hη, gm_S4_1 hC24 hC27 hC14 hγ hγ2 hD P h hh 𝕫,
    hC24 γ hγ hγ2 D c hD P h hh 𝕫, ae_mem_lenSet h38 hγ hγ2 hD P h hh] with ω hηω h41 h24 hlen
  set d := D (h ω)
  have hl : d.IsLength := isLength_of_mem_lenSet hlen
  suffices H : ω ∈ gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r →
      ω ∈ gmHitBall D h 𝕫 𝕨 η z r →
      (ω ∈ gmArcHit D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k) U ↔
        ω ∈ h ⁻¹' (D ⁻¹' gmHitUSet 𝕫 (ℓ * 𝕣) c₁ cc lam1 lam4 ε ν 𝕣 Rads z r U)) by
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨(H h2 h3).1 h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨(H h2 h3).2 h1, h2, h3⟩
  intro hS hH
  simp only [gmStabEv, gmArcHit, gmHitUSet, mem_ofPred_eq, mem_preimage, gm_s4T_eq,
    gm_s4S_eq] at hS ⊢
  change candEvD d 𝕫 (ℓ * 𝕣) cc lam1 lam4 ε ν 𝕣 Rads z r ∧
    stabCond d 𝕫 (tauD d 𝕫 (ℓ * 𝕣) * c₁) (tauD d 𝕫 (ℓ * 𝕣) * cc) z r at hS
  change _ ↔ candEvD d 𝕫 (ℓ * 𝕣) cc lam1 lam4 ε ν 𝕣 Rads z r ∧ _
  obtain ⟨hcand, hstab⟩ := hS
  set τ := tauD d 𝕫 (ℓ * 𝕣)
  have hpos := (gm_agree_of_candEvD (d₂ := d) hl hl hc ha le_rfl isOpen_univ (subset_univ _)
    (fun _ _ _ _ => rfl) hcand).1.pos
  have hτ : 0 < τ := pos_of_mul_pos_left hpos (by linarith)
  have hs : 0 < τ * c₁ := mul_pos hτ (by linarith)
  have hst : τ * c₁ < τ * cc := mul_lt_mul_of_pos_left hc₁c hτ
  obtain ⟨-, -, hdisj, -⟩ := h41 _ _ hs hst
  have hball : Disjoint (closedBall z r) (filledBall d 𝕫 (τ * cc)) := by
    refine Set.disjoint_left.2 fun x hx hxK => ?_
    have h1 := gm_infDist_frontier_le_dist hcand.2.1 hxK
    have h3 := hcand.2.2.2.1
    rw [mem_closedBall, dist_comm] at hx
    linarith
  have hwω : 𝕨 ∉ filledBall d 𝕫 (τ * cc) := by
    intro hwK
    obtain ⟨u, hu, hPu⟩ := hH
    exact Set.disjoint_left.1 hball (ball_subset_closedBall hPu)
      (gm_geod_mem_filledBall_of_end (gm_geodL_isGeodesicL hηω.1 h𝕫𝕨) hwK hu)
  rw [gm_arcHit_iff_hitU hηω.2 (gm_geodL_isGeodesicL hηω.1 h𝕫𝕨) hs hst hwω
    (fun y hy => (h24 _ (hs.trans hst) y hy true).1) hdisj hball hH hstab U]
  exact ⟨fun h' => ⟨hcand, h'⟩, fun h' => h'.2⟩


/-- **GM Lemma 4.6, second claim, arc part** (l. 1709–1714): input `hArc` of `gm_L4_6c_of` -/
theorem gm_L4_6_hArc_nw (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {𝕫 𝕨 z : ℂ} (h𝕫𝕨 : 𝕫 ≠ 𝕨) {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {ℓ 𝕣 ε β lam1 lam4 ν r ρ : ℝ} {k : ℕ} {Rads : Set ℝ}
    (hε : 0 < ε) (ha : 0 < lam4 * ε * 𝕣) (hρ : ρ ≤ lam4 * ε * 𝕣) (hρr : ρ ≤ r)
    (hr : r < lam4 * ε * 𝕣) (hArcAn : GMArcRelAn 𝕫) (hAvAn : GMAvoidRelAn 𝕫 z r) :
    ∀ U : Set ℂ, IsOpen U → ∃ t, MeasurableSet[fieldSigmaClosed h (Metric.ball z ρ)ᶜ ⊔
        generateFrom {gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r}] t ∧
      gmArcHit D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k) U ∩
        (gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r) =ᵐ[P] t := by
  intro U hU
  set cc := 1 + k * ε ^ β + ε ^ (2 * β)
  have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hc : 1 < cc := by
    have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
    simp only [cc]
    linarith
  have hc₁ : 1 + k * ε ^ β ≤ cc := by simp only [cc]; linarith
  obtain ⟨F, hF, hEF⟩ := gm_aeEventIn_of_local hD (Tight.isGFFPlusCont_of_wp hh) lenSet
    measurableSet_lenSet (fun d hd => isLength_of_mem_lenSet hd)
    (ae_mem_lenSet h38 hγ hγ2 hD P h hh) z ρ _
    (gm_uMeasurableSet_hitUSet hArcAn hAvAn (ℓ * 𝕣) (1 + k * ε ^ β) cc lam1 lam4 ε ν 𝕣 Rads
      hU.measurableSet)
    (fun d₁ hd₁ d₂ hd₂ U' hU' hUρ heq hB => gm_hitUSet_of_internal_eq
      (isLength_of_mem_lenSet hd₁) (isLength_of_mem_lenSet hd₂) hc hc₁ ha hρ hρr hU' hUρ heq hB)
  set E := gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r
  refine ⟨F ∩ E, ?_, ?_⟩
  · exact (le_sup_left (α := MeasurableSpace Ω) _ hF).inter
      (le_sup_right (α := MeasurableSpace Ω) _ (measurableSet_generateFrom rfl))
  · exact (gm_arcHit_ae_eq_hitU_nw (ℓ := ℓ) (β := β) (k := k) (lam1 := lam1) (ν := ν)
      (Rads := Rads) (z := z) h38 hC24 hC27 hC14 hγ hγ2 hD hh h𝕫𝕨 hη hε ha hr U).trans
      (hEF.inter (EventuallyEq.refl _ E))


/-- **GM Lemma 4.6 (c)** (l. 1710–1716) in the `hL46` form of `gm_L4_7_pair`: every
`𝓕_k`-event, traced on `Stab ∩ Hit`, is a.s. an event of `σ(h|_{ℂ∖B_ρ(z)}) ∨ σ(1_{Stab ∩ Hit})`.
Inputs: GM Lemma 4.5 (`hE2b`, from `gm_L4_5_E2b`) and the traces of `σ(𝓑^•_{t_k}, h|)` (`hA`). -/
theorem gm_L4_6c_nw (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {𝕫 𝕨 z : ℂ} (h𝕫𝕨 : 𝕫 ≠ 𝕨) {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {ℓ 𝕣 ε β lam1 lam4 ν r ρ : ℝ} {k : ℕ} {Rads : Set ℝ}
    (hε : 0 < ε) (ha : 0 < lam4 * ε * 𝕣) (hρ : ρ ≤ lam4 * ε * 𝕣) (hρr : ρ ≤ r)
    (hr : r < lam4 * ε * 𝕣) (hArcAn : GMArcRelAn 𝕫) (hAvAn : GMAvoidRelAn 𝕫 z r)
    (hE2b : AEDeterminedSigma (gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k))
      (gmSigF' D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)) P)
    (hA : ∀ a, MeasurableSet[gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k)] a →
      ∃ t, MeasurableSet[fieldSigmaClosed h (Metric.ball z ρ)ᶜ ⊔
        generateFrom {gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r}] t ∧
      a ∩ (gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r) =ᵐ[P] t) :
    ∀ F', MeasurableSet[gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)] F' →
      ∃ t, MeasurableSet[fieldSigmaClosed h (Metric.ball z ρ)ᶜ ⊔
        generateFrom {gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r}] t ∧
      F' ∩ (gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r) =ᵐ[P] t :=
  gm_L4_6c_of hE2b hA (gm_L4_6_hArc_nw h38 hC24 hC27 hC14 hγ hγ2 hD hh h𝕫𝕨 hη hε ha hρ hρr hr
    hArcAn hAvAn)

end LQGMetric.GM
