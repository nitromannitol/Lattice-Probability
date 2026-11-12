/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasD6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD5

/-!
# GM Lemma 4.6 (c), input `hA`: hit events of `𝓑^•_{t_k}` traced on `Stab ∩ Hit` (task P2-E3c)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 4.6, l. 1701–1706 ("`(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})` … is determined by
`h|_{ℂ∖B_r(z)}` on the event `{(z,r) ∈ 𝒵_k}`"), first half: the random set `𝓑^•_{t_k}` itself.

* `gm_filledBall_inter_open_iff`: for `V` open, `𝓑^•_t ∩ V ≠ ∅` iff a point of a fixed dense
  sequence in `V` lies in `𝓑^•_t` (the bounded components of `ℂ ∖ cl 𝓑_t` are open);
* `gm_trace_hitK`: the generators `{𝓑^•_{t_k} ∩ V ≠ ∅}` of `setSigma` (Effros) traced on
  `Stab ∩ Hit` are a.s. events of `σ(h|_{ℂ∖B_ρ(z)}) ∨ σ(1_{Stab ∩ Hit})`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric MeasurableSpace TopologicalSpace
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-- `𝓑^•_t ∩ V ≠ ∅` is read off a dense sequence (`V` open) -/
theorem gm_filledBall_inter_open_iff (d : ContMetric) (𝕫 : ℂ) (t : ℝ) {V : Set ℂ}
    (hV : IsOpen V) : (filledBall d 𝕫 t ∩ V).Nonempty ↔
      ∃ i, denseSeq ℂ i ∈ V ∧ denseSeq ℂ i ∈ filledBall d 𝕫 t := by
  constructor
  · rintro ⟨x, hxK, hxV⟩
    rcases hxK with hx | ⟨hx, hb⟩
    · have hBo : IsOpen (ballM d 𝕫 t) :=
        isOpen_lt (d.1.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const
      obtain ⟨y, hyB, hyV⟩ := mem_closure_iff.1 hx V hV hxV
      obtain ⟨i, hi⟩ := (denseRange_denseSeq ℂ).exists_mem_open (hBo.inter hV) ⟨y, hyV, hyB⟩
      exact ⟨i, hi.2, Or.inl (subset_closure hi.1)⟩
    · set C := connectedComponentIn (closure (ballM d 𝕫 t))ᶜ x
      have hCo : IsOpen C := isClosed_closure.isOpen_compl.connectedComponentIn
      obtain ⟨i, hiC, hiV⟩ := (denseRange_denseSeq ℂ).exists_mem_open (hCo.inter hV)
        ⟨x, mem_connectedComponentIn hx, hxV⟩
      refine ⟨i, hiV, Or.inr ⟨connectedComponentIn_subset _ _ hiC, ?_⟩⟩
      rw [← connectedComponentIn_eq hiC]
      exact hb
  · rintro ⟨i, hiV, hiK⟩
    exact ⟨_, hiK, hiV⟩

/-- the metric event `{(z,r) ∈ 𝒵_k} ∩ {𝓑^•_{t} ∩ V ≠ ∅}`, `t = τ c` -/
def gmHitKSet (𝕫 : ℂ) (R c lam1 lam4 ε ν 𝕣 : ℝ) (Rads : Set ℝ) (z : ℂ) (r : ℝ) (V : Set ℂ) :
    Set ContMetric :=
  {d | candEvD d 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r ∧
    (filledBall d 𝕫 (tauD d 𝕫 R * c) ∩ V).Nonempty}

theorem gm_uMeasurableSet_hitKSet (𝕫 : ℂ) (R c lam1 lam4 ε ν 𝕣 : ℝ) (Rads : Set ℝ) (z : ℂ)
    (r : ℝ) {V : Set ℂ} (hV : IsOpen V) :
    UMeasurableSet (lenSet ∩ gmHitKSet 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r V) := by
  have hg : Measurable fun d : ContMetric => (d, gmTauB 𝕫 R d * c) :=
    measurable_id.prodMk ((gm_measurable_tauB 𝕫 R).mul_const c)
  have e : lenSet ∩ gmHitKSet 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r V =
      (lenSet ∩ {d | candEvD d 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r}) ∩
        (lenSet ∩ ⋃ i, ({_d : ContMetric | denseSeq ℂ i ∈ V} ∩
          (fun d : ContMetric => (d, gmTauB 𝕫 R d * c)) ⁻¹'
            {p : ContMetric × ℝ | denseSeq ℂ i ∉ filledBall p.1 𝕫 p.2}ᶜ)) := by
    ext d
    simp only [gmHitKSet, mem_inter_iff, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_compl_iff,
      not_not]
    constructor
    · rintro ⟨hd, hc, hK⟩
      rw [gm_filledBall_inter_open_iff _ _ _ hV, gm_tauD_eq_tauB hd] at hK
      exact ⟨⟨hd, hc⟩, hd, hK⟩
    · rintro ⟨⟨hd, hc⟩, -, hK⟩
      refine ⟨hd, hc, ?_⟩
      rw [gm_filledBall_inter_open_iff _ _ _ hV, gm_tauD_eq_tauB hd]
      exact hK
  rw [e]
  refine (gm_uMeasurableSet_candEvD 𝕫 _ _ _ _ _ _ _ _ z r).inter
    ((UMeasurableSet.of_measurableSet measurableSet_lenSet).inter
      (UMeasurableSet.iUnion fun i => ?_))
  exact (UMeasurableSet.of_measurableSet (MeasurableSet.const _)).inter
    ((gm_uMeasurableSet_notMem_filledBall 𝕫 (denseSeq ℂ i)).compl.preimage hg)

theorem gm_hitKSet_of_internal_eq {d₁ d₂ : ContMetric} (h₁ : d₁.IsLength) (h₂ : d₂.IsLength)
    {𝕫 : ℂ} {R c lam1 lam4 ε ν 𝕣 : ℝ} {Rads : Set ℝ} {z : ℂ} {r ρ : ℝ} {V : Set ℂ}
    (hc : 1 < c) (ha : 0 < lam4 * ε * 𝕣) (hρ : ρ ≤ lam4 * ε * 𝕣)
    {U : Set ℂ} (hU : IsOpen U) (hUρ : (Metric.ball z ρ)ᶜ ⊆ U)
    (heq : ∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y)
    (H : d₁ ∈ gmHitKSet 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r V) :
    d₂ ∈ gmHitKSet 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r V := by
  obtain ⟨hA, hτ⟩ := gm_agree_of_candEvD h₁ h₂ hc ha hρ hU hUρ heq H.1
  refine ⟨gm_candEvD_of_internal_eq h₁ h₂ hc ha hρ hU hUρ heq H.1, ?_⟩
  rw [hτ, hA.fb le_rfl]
  exact H.2

variable {Ω : Type} [MeasurableSpace Ω]

/-- **traces of the hit events of `𝓑^•_{t_k}`** on `Stab ∩ Hit` (GM l. 1701–1706) -/
theorem gm_trace_hitK (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {𝕫 𝕨 z : ℂ} {η : Ω → C(unitInterval, ℂ)}
    {ℓ 𝕣 ε β lam1 lam4 ν r ρ : ℝ} {k : ℕ} {Rads : Set ℝ}
    (hε : 0 < ε) (ha : 0 < lam4 * ε * 𝕣) (hρ : ρ ≤ lam4 * ε * 𝕣) {V : Set ℂ} (hV : IsOpen V) :
    ∃ t, MeasurableSet[fieldSigmaClosed h (Metric.ball z ρ)ᶜ ⊔
        generateFrom {gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r}] t ∧
      {ω | (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ∩ V).Nonempty} ∩
        (gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r) =ᵐ[P] t := by
  set cc := 1 + k * ε ^ β + ε ^ (2 * β)
  have hc : 1 < cc := by
    have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
    have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
    simp only [cc]
    linarith
  obtain ⟨F, hF, hEF⟩ := gm_aeEventIn_of_local hD (Tight.isGFFPlusCont_of_wp hh) lenSet
    measurableSet_lenSet (fun d hd => isLength_of_mem_lenSet hd)
    (ae_mem_lenSet h38 hγ hγ2 hD P h hh) z ρ _
    (gm_uMeasurableSet_hitKSet 𝕫 (ℓ * 𝕣) cc lam1 lam4 ε ν 𝕣 Rads z r hV)
    (fun d₁ hd₁ d₂ hd₂ U' hU' hUρ heq hB => gm_hitKSet_of_internal_eq
      (isLength_of_mem_lenSet hd₁) (isLength_of_mem_lenSet hd₂) hc ha hρ hU' hUρ heq hB)
  set E := gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ gmHitBall D h 𝕫 𝕨 η z r
  refine ⟨F ∩ E, (le_sup_left (α := MeasurableSpace Ω) _ hF).inter
      (le_sup_right (α := MeasurableSpace Ω) _ (measurableSet_generateFrom rfl)), ?_⟩
  have e : {ω | (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ∩ V).Nonempty} ∩ E =
      h ⁻¹' (D ⁻¹' gmHitKSet 𝕫 (ℓ * 𝕣) cc lam1 lam4 ε ν 𝕣 Rads z r V) ∩ E := by
    ext ω
    simp only [E, gmStabEv, gmHitKSet, mem_inter_iff, mem_ofPred_eq, mem_preimage, gm_s4T_eq,
      cc]
    constructor
    · rintro ⟨hK, hS, hH⟩; exact ⟨⟨hS.1, hK⟩, hS, hH⟩
    · rintro ⟨⟨-, hK⟩, hS, hH⟩; exact ⟨hK, hS, hH⟩
  rw [e]
  exact hEF.inter (EventuallyEq.refl _ E)

end LQGMetric.GM
