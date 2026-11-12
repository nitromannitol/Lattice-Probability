/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate2L420H at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2L420
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGood

/-!
# GM Lemma 4.20: the hit part `{P ∩ B_{λ₂r}(z) ≠ ∅}`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.20, l. 2353–2354:
"since `P|_{[0,s_{k+1}]} ∈ 𝓕_{k+1}` and `P` does not re-enter `𝓑^•_{s_{k+1}}` after time `s_{k+1}`,
we have `F_k ∩ {P ∩ B_{λ₂r}(z) ≠ ∅} ∩ {(z,r) ∈ 𝒵_k} ∈ 𝓕_{k+1}`" (non-reentry: GM.S4.7,
`gm_S4_7_mem_iff`).

* `gm_hit_iff_pathK` (pathwise): for a geodesic `η` from `𝕫` to `𝕨 ∉ 𝓑^•_s` and `B ⊂ 𝓑^•_s`,
  `η` hits `B` iff `P|_{[0,s]}` does.
* `gm_measurableSet_pathK_hit`: `{P|_{[0,s]} hits B}` is a `σ(P|_{[0,s]})`-event (`B` open).
* `gm_hit_aeEventIn`: `{(z,r) ∈ 𝒵_k} ∩ {P ∩ B_{λ₂r}(z) ≠ ∅} ∩ F⁰_k ∩ {𝕨 ∉ 𝓑^•_{s_{k+1}}}` is a.s.
  an event of `𝓕_{k+1}` (`λ₂r ≤ 2λ₄ε𝕣` for the radii of `ℛ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **non-reentry, pathwise** (GM l. 2353–2354) -/
theorem gm_hit_iff_pathK {d : ContMetric} {𝕫 𝕨 : ℂ} {η : C(unitInterval, ℂ)}
    (hη : IsGeod01 d 𝕫 𝕨 η) (h𝕫𝕨 : 𝕫 ≠ 𝕨) {s : ℝ} (hs : 0 < s)
    (hw : 𝕨 ∉ filledBall d 𝕫 s) {B : Set ℂ} (hB : B ⊆ filledBall d 𝕫 s) :
    (range η ∩ B).Nonempty ↔ ∃ u : unitInterval, geodL d 𝕫 𝕨 η (s * u) ∈ B := by
  have hP := gm_geodL_isGeodesicL hη h𝕫𝕨
  set L := d.1 (𝕫, 𝕨)
  have hL : 0 < L := lt_of_le_of_ne (gm_D_nonneg d 𝕫 𝕨)
    (fun h0 => h𝕫𝕨 (d.2.eq_of_eq_zero 𝕫 𝕨 h0.symm))
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, hvB⟩
    have hPv : geodL d 𝕫 𝕨 η (v * L) = η v := by
      simp only [geodL, L]
      congr 1
      rw [mul_div_cancel_right₀ _ hL.ne']
      exact projIcc_val zero_le_one v
    have hvL : (v : ℝ) * L ∈ Icc 0 L :=
      ⟨mul_nonneg v.2.1 hL.le, mul_le_of_le_one_left hL.le v.2.2⟩
    have hle : (v : ℝ) * L ≤ s :=
      (gm_S4_7_mem_iff hP hs hw hvL).1 (by rw [hPv]; exact hB hvB)
    refine ⟨⟨v * L / s, div_nonneg hvL.1 hs.le, (div_le_one hs).2 hle⟩, ?_⟩
    show geodL d 𝕫 𝕨 η (s * (v * L / s)) ∈ B
    rw [mul_div_cancel₀ _ hs.ne', hPv]; exact hvB
  · rintro ⟨u, hu⟩
    exact ⟨_, ⟨_, rfl⟩, hu⟩

/-- `{P|_{[0,s]} hits B}` is a `σ(P|_{[0,s]})`-event for `B` open -/
theorem gm_measurableSet_pathK_hit {Ω : Type} (D : DistC → ContMetric) (h : Ω → DistC)
    (𝕫 𝕨 : ℂ) (η : Ω → C(unitInterval, ℂ)) (sk : Ω → ℝ) {B : Set ℂ} (hB : IsOpen B) :
    MeasurableSet[MeasurableSpace.comap (gmPathK D h 𝕫 𝕨 η sk) inferInstance]
      {ω | ∃ u : unitInterval, gmPathK D h 𝕫 𝕨 η sk ω u ∈ B} := by
  have hc : ∀ ω, Continuous (gmPathK D h 𝕫 𝕨 η sk ω) := fun ω =>
    (η ω).continuous.comp (continuous_projIcc.comp
      ((continuous_const.mul continuous_subtype_val).div_const _))
  have e : {ω | ∃ u : unitInterval, gmPathK D h 𝕫 𝕨 η sk ω u ∈ B} =
      gmPathK D h 𝕫 𝕨 η sk ⁻¹'
        ⋃ i : ℕ, {f : unitInterval → ℂ | f (TopologicalSpace.denseSeq unitInterval i) ∈ B} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_iUnion]
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨i, hi⟩ := (TopologicalSpace.denseRange_denseSeq unitInterval).exists_mem_open
        (hB.preimage (hc ω)) ⟨u, hu⟩
      exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨_, hi⟩
  rw [e]
  refine ⟨_, MeasurableSet.iUnion fun i => ?_, rfl⟩
  exact measurableSet_preimage (measurable_pi_apply _) hB.measurableSet

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **the hit part of GM Lemma 4.20** (l. 2353–2354) -/
theorem gm_hit_aeEventIn [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) {𝕫 𝕨 : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {𝕣 ε β : ℝ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε) (ha : 0 < R.lam 3 * ε * 𝕣) (k : ℕ)
    (z : ℂ) (r : ℝ) (hlr : r ∈ p4Rads R 𝕣 ε → R.lam 1 * r ≤ 2 * R.lam 3 * (ε * 𝕣)) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1))
      ({ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
          (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)} ∩
        {ω | (range (η ω) ∩ ball z (R.lam 1 * r)).Nonempty} ∩ gmF0 D h R 𝕫 𝕣 ε β k ∩
        {ω | 𝕨 ∉ filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω)}) := by
  set sk := s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1)
  set Cd : Set Ω := {ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω))
    (R.lam 0) (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)}
  set W : Set Ω := {ω | 𝕨 ∉ filledBall (D (h ω)) 𝕫 (sk ω)}
  have hCd := gm_cand_aeEventIn h38 hγ hγ2 hD hh R 𝕫 𝕨 η hℓ𝕣 hε ha k z r (β := β)
  have hF0 := gm_gmF0_aeEventIn h38 hγ hγ2 hD hh R 𝕫 𝕨 η hℓ𝕣 hε ha k (β := β)
  have hW : AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) W := by
    have hm := gm_setSigma_s_le_aeSigma h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε (k + 1) (β := β) _
      (gm_setSigma_hit_compact _ (fun ω => gm_filledBall_isClosed _ _ _)
        (isCompact_singleton (x := 𝕨))).compl
    obtain ⟨F, hF, hEF⟩ := gm_measurableSet_aeSigma hm
    refine ⟨F, (le_sup_left : _ ≤ gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) _ hF,
      EventuallyEq.trans (Eventually.of_forall fun ω => propext ?_) hEF⟩
    show _ ↔ ¬ ((_ : Set ℂ) ∩ {𝕨}).Nonempty
    rw [inter_singleton_nonempty]
    rfl
  have hH : AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1))
      {ω | ∃ u : unitInterval, gmPathK D h 𝕫 𝕨 η sk ω u ∈ ball z (R.lam 1 * r)} :=
    gm_aeEventIn_of_measurableSet ((le_sup_right : _ ≤ gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) _
      (gm_measurableSet_pathK_hit D h 𝕫 𝕨 η sk isOpen_ball))
  obtain ⟨F, hF, hEF⟩ := gm_aeEventIn_inter (gm_aeEventIn_inter (gm_aeEventIn_inter hCd hH) hF0) hW
  refine ⟨F, hF, EventuallyEq.trans ?_ hEF⟩
  filter_upwards [hη] with ω hω
  apply propext
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨⟨hc, hhit⟩, hf⟩, hw⟩
    have hs : 0 < sk ω := by
      simp only [sk]; rw [gm_s4S_eq]
      have := gm_tauD_pos (D (h ω)) 𝕫 hℓ𝕣
      have : 0 ≤ ((k + 1 : ℕ) : ℝ) * ε ^ β :=
        mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hε.le β)
      positivity
    have hB : ball z (R.lam 1 * r) ⊆ filledBall (D (h ω)) 𝕫 (sk ω) :=
      (ball_subset_ball (hlr hc.2.2.1)).trans (gm_gmF0_ball hf hc)
    exact ⟨⟨⟨hc, (gm_hit_iff_pathK hω.1 h𝕫𝕨 hs hw hB).1 hhit⟩, hf⟩, hw⟩
  · rintro ⟨⟨⟨hc, ⟨u, hu⟩⟩, hf⟩, hw⟩
    exact ⟨⟨⟨hc, ⟨_, ⟨_, rfl⟩, hu⟩⟩, hf⟩, hw⟩

end LQGMetric.GM
