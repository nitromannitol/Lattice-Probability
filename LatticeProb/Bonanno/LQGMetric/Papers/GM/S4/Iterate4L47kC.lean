/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate4L47kC at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4L47k
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4L47Fix
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4Meas
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodS46

/-!
# GM Lemma 4.7 at index `k` for `𝒵^E_k`, `𝒵^𝔈_k` (DEC-89, packet B, concrete form)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.7, l. 1890–1940,
and its use in Lemma 4.21 (l. 2380–2390). The candidate pairs `(z, r)` range over a finite set `S`
containing `𝒵_k` on the event `G` (GM l. 1925), (4.13) holds for each of them by Thm 4.2 (4)
(`gm_L4_7_pair_of_cond4`, conditioning radius `λ₃r ≤ r`, far normalization `h(ψ₀) = 0`), and
`gm_h47_of_pairs` gives (4.14) in the form of `gm_P4_17_ae`'s `h47`.

* `gm_h47_k_core`: (4.14) at index `k`, given the count bound (4.19) on `G` (hypothesis `hP`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **GM (4.14) at index `k`** (proof of Lemma 4.7, l. 1890–1940) for `ZE = {𝒵^E_k ≠ ∅}`,
`ZF = {𝒵^𝔈_k ≠ ∅}`, `ℱ_k = gmFilt k`, from Thm 4.2 (2), (4) and the count bound (4.19) -/
theorem gm_h47_k_core [P.IsComplete] (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4)
    (hC27 : CONFLem2_7) (hC14 : CONFThm1_4) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) {𝕫 𝕨 : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {𝕣 ε β : ℝ} (k : ℕ) (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε) (h𝕣 : 0 < 𝕣)
    (hlam3 : 1 < R.lam 3) (hlam1 : 0 ≤ R.lam 1) (hlam11 : R.lam 1 ≤ 1) (hlam2 : 0 ≤ R.lam 2)
    (hlam21 : R.lam 2 ≤ 1)
    (hRads : ∀ r ∈ p4Rads R 𝕣 ε, 0 < r ∧ r ≤ ε * 𝕣) (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC)
    {Λ : ℝ} (hΛ : 0 < Λ) {ψ₀ : TestC} (hψ₀ : ∫ x, ψ₀ x = 1) (h0 : ∀ ω, h ω ψ₀ = 0)
    (S : Finset (ℂ × ℝ))
    (hψS : ∀ i ∈ S, tsupport (ψ₀ : ℂ → ℝ) ⊆ (Metric.ball i.1 (R.lam 2 * i.2))ᶜ)
    (hE2 : ∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma
      (fun ω => addConst (h ω) (-circleAvg (h ω) (R.lam 4 * r) z))
      (annulus z (R.lam 0 * r) (R.lam 3 * r))) (h ⁻¹' R.E r z))
    (hEf2 : ∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma h (ballO z (R.lam 3 * r)) ⊔
      MeasurableSpace.comap (fun ω => stopLastExit (sel 𝕫 𝕨 (h ω)) (Metric.ball z (R.lam 3 * r)))
        inferInstance) (h ⁻¹' Ef r z 𝕫 𝕨))
    (h4 : ∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, 𝕫 ∉ Metric.ball z (R.lam 3 * r) →
      𝕨 ∉ Metric.ball z (R.lam 3 * r) →
      (fun ω => Λ⁻¹ * (P[(h ⁻¹' R.E r z ∩
          {ω | (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball z (R.lam 1 * r)).Nonempty}).indicator
          (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h (Metric.ball z (R.lam 2 * r))ᶜ]) ω) ≤ᵐ[P]
        P[(h ⁻¹' Ef r z 𝕫 𝕨 ∩
          {ω | (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball z (R.lam 1 * r)).Nonempty}).indicator
          (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h (Metric.ball z (R.lam 2 * r))ᶜ])
    {G : Set Ω}
    (hG : MeasurableSet[gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β k] G)
    (hS : ∀ ω ∈ G, ∀ p ∈ zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω, p ∈ S)
    {K Cp δ : ℝ} (hK : 0 < K) (hCp : (S.card : ℝ) ≤ Cp) (hδ : 0 < δ)
    (hP : P.real ({x | K < ∑ i ∈ S,
      {ω | i ∈ zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω}.indicator (fun _ => (1 : ℝ)) x} ∩ G) ≤ δ)
    {Reg : Set Ω}
    (hReg : ∀ᵐ ω ∂P, ω ∈ Reg → ω ∈ {ω | 𝕨 ∉ thickening (3 * R.lam 3 * ε * 𝕣)
      (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω))} ∩ G) :
    P.real {ω | ω ∈ Reg ∧
      P[{ω | (zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω).Nonempty}.indicator (fun _ => (1 : ℝ)) |
        gmFilt h38 hγ hγ2 hD hh hη R.ℓ 𝕣 ε β k] ω <
      (Λ * K)⁻¹ * P[{ω | (zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω).Nonempty}.indicator (fun _ => (1 : ℝ)) |
        gmFilt h38 hγ hγ2 hD hh hη R.ℓ 𝕣 ε β k] ω - Cp * Real.sqrt δ / K} ≤ Real.sqrt δ := by
  set η : Ω → C(unitInterval, ℂ) := fun ω => sel 𝕫 𝕨 (h ω) with hηdef
  set Kt : Ω → Set ℂ := fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)
  set R₀ : ℝ := 3 * R.lam 3 * ε * 𝕣
  have he : 0 < ε * 𝕣 := mul_pos hε h𝕣
  have ha : 0 < R.lam 3 * ε * 𝕣 := by rw [mul_assoc]; exact mul_pos (by linarith) he
  have hηm : Measurable η := gm_measurable_geod_of_complete hD hh hη
  have hF : gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β k ≤ ‹MeasurableSpace Ω› := gm_sigF_le h38 hγ hγ2 hD hh hη R.ℓ 𝕣 ε β k
  let Hit : ℂ → ℝ → Set Ω := fun z r => {ω | (range (η ω) ∩ Metric.ball z (R.lam 1 * r)).Nonempty}
  have hHitm : ∀ z r, MeasurableSet (Hit z r) := fun z r => gm_measurableSet_hit hηm isOpen_ball
  have hStabm : ∀ z r, MeasurableSet (gmStabEv D h 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν
      (p4Rads R 𝕣 ε) z r) := fun z r =>
    gm_measurableSet_stabEv h38 hC24 hC27 hC14 hγ hγ2 hD hh (gm_avoidRelAn 𝕫 z r) hε ha
  -- the pieces
  let A : ℂ × ℝ → Set Ω := fun i => {ω | i ∈ zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω}
  let B : ℂ × ℝ → Set Ω := fun i => {ω | i ∈ zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω}
  let Z : ℂ × ℝ → Set Ω := fun i => gmG0 D h 𝕫 𝕨 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν
    (p4Rads R 𝕣 ε) i.1 i.2 0
  let W : Set Ω := {ω | 𝕨 ∉ thickening R₀ (Kt ω)}
  have eA : ∀ i : ℂ × ℝ, A i = h ⁻¹' R.E i.2 i.1 ∩ gmStabEv D h 𝕫 R.ℓ 𝕣 ε β k (R.lam 0)
      (R.lam 3) R.ν (p4Rads R 𝕣 ε) i.1 i.2 ∩ Hit i.1 i.2 := fun i => by
    ext ω; simp only [A, Hit, zkE, gmStabEv, mem_inter_iff, mem_setOf_eq, mem_preimage]; tauto
  have eB : ∀ i : ℂ × ℝ, B i = h ⁻¹' Ef i.2 i.1 𝕫 𝕨 ∩ gmStabEv D h 𝕫 R.ℓ 𝕣 ε β k (R.lam 0)
      (R.lam 3) R.ν (p4Rads R 𝕣 ε) i.1 i.2 ∩ Hit i.1 i.2 := fun i => by
    ext ω; simp only [B, Hit, zkF, gmStabEv, mem_inter_iff, mem_setOf_eq, mem_preimage]; tauto
  have hA0 : ∀ i : ℂ × ℝ, i.2 ∉ p4Rads R 𝕣 ε → A i = ∅ := fun i hi => by
    ext ω; simp only [A, mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, -, hr, -⟩, -⟩; exact hi hr
  have hB0 : ∀ i : ℂ × ℝ, i.2 ∉ p4Rads R 𝕣 ε → B i = ∅ := fun i hi => by
    ext ω; simp only [B, mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, -, hr, -⟩, -⟩; exact hi hr
  have hAm : ∀ i, MeasurableSet (A i) := fun i => by
    by_cases hi : i.2 ∈ p4Rads R 𝕣 ε
    · rw [eA]
      exact ((gm_measurableSet_E_of_cond2 hh (hE2 i.1 i.2 hi)).inter (hStabm _ _)).inter
        (hHitm _ _)
    · rw [hA0 i hi]; exact MeasurableSet.empty
  have hBm : ∀ i, MeasurableSet (B i) := fun i => by
    by_cases hi : i.2 ∈ p4Rads R 𝕣 ε
    · rw [eB]
      exact ((gm_measurableSet_Ef_of_cond2 hD hh hη (hEf2 i.1 i.2 hi)).inter (hStabm _ _)).inter
        (hHitm _ _)
    · rw [hB0 i hi]; exact MeasurableSet.empty
  have hZm : ∀ i, MeasurableSet[gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β k] (Z i) := fun i =>
    (le_sup_left : gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k) ≤ gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β k) _
      (gm_setSigma_le_localSigma h _ _ (gm_G0_measurableSet_setSigma D h 𝕫 𝕨 R.ℓ 𝕣 ε β k _ _ _ _
        _ _ 0 ha))
  have hAZ : ∀ i, A i ⊆ Z i := fun i ω hω => by
    refine ⟨hω.1, ?_⟩
    rw [thickening_of_nonpos le_rfl]; exact notMem_empty _
  -- `ZE`, `ZF` are events
  have hZE : MeasurableSet {ω | (zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω).Nonempty} := by
    have e : {ω | (zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω).Nonempty} = ⋃ (ab : ℤ × ℤ) (n : ℕ),
        A (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab, R.rr 𝕣 ε n) := by
      ext ω
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨p, hp⟩
        obtain ⟨⟨a, b, hab⟩, n, hn⟩ := gm_zkE_pairs D sel h R 𝕫 𝕨 𝕣 ε β k ω p hp
        refine ⟨(a, b), n, ?_⟩
        have : p = (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) (a, b), R.rr 𝕣 ε n) :=
          Prod.ext hab hn.symm
        rw [← this]; exact hp
      · rintro ⟨ab, n, hm⟩; exact ⟨_, hm⟩
    rw [e]; exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => hAm _
  have hZF : MeasurableSet {ω | (zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω).Nonempty} := by
    have e : {ω | (zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω).Nonempty} = ⋃ (ab : ℤ × ℤ) (n : ℕ),
        B (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab, R.rr 𝕣 ε n) := by
      ext ω
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨p, hp⟩
        obtain ⟨⟨a, b, hab⟩, n, hn⟩ := gm_zkF_pairs D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω p hp
        refine ⟨(a, b), n, ?_⟩
        have : p = (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) (a, b), R.rr 𝕣 ε n) :=
          Prod.ext hab hn.symm
        rw [← this]; exact hp
      · rintro ⟨ab, n, hm⟩; exact ⟨_, hm⟩
    rw [e]; exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => hBm _
  -- `𝕫 ∈ 𝓑^•_{t_k}`, closed
  have hKc : ∀ x, IsClosed (Kt x) := fun x => gm_filledBall_isClosed _ _ _
  have hK𝕫 : ∀ x, 𝕫 ∈ Kt x := fun x => by
    have htk : 0 < s4T D h 𝕫 R.ℓ 𝕣 ε β k x := by
      rw [gm_s4T_eq]
      have hτ := gm_tauD_pos (D (h x)) 𝕫 hℓ𝕣
      have : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
      have : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
      positivity
    exact subset_closure.trans subset_union_left
      (show (D (h x)).1 (𝕫, 𝕫) < _ by rw [(D (h x)).2.self_eq_zero 𝕫]; exact htk)
  -- on `Z i ∩ W` the pair is admissible for (4)
  have hgoodOf : ∀ (z : ℂ) (r : ℝ) (x : Ω), x ∈ Z (z, r) ∩ W →
      r ∈ p4Rads R 𝕣 ε ∧ 𝕫 ∉ Metric.ball z (R.lam 3 * r) ∧ 𝕨 ∉ Metric.ball z (R.lam 3 * r) := by
    rintro z r x ⟨⟨⟨-, hzK, hr, hlo, hhi⟩, -⟩, hW⟩
    have hKne : (Kt x).Nonempty := ⟨𝕫, hK𝕫 x⟩
    have hfr := gm_infDist_frontier_eq (hKc x) hKne hzK
    dsimp only at hlo hhi
    rw [hfr] at hlo hhi
    obtain ⟨hr0, hre⟩ := hRads r hr
    have hlr4 : R.lam 3 * r ≤ R.lam 3 * ε * 𝕣 := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hre (by linarith)
    refine ⟨hr, fun hb => ?_, fun hb => ?_⟩
    · have h1 : infDist z (Kt x) ≤ dist z 𝕫 := infDist_le_dist_of_mem (hK𝕫 x)
      rw [mem_ball, dist_comm] at hb
      linarith
    · have h1 : R₀ ≤ infDist 𝕨 (Kt x) := by
        by_contra hlt
        exact hW ((mem_thickening_iff_infDist_lt hKne).2 (not_le.1 hlt))
      have h2 := infDist_le_infDist_add_dist (x := 𝕨) (y := z) (s := Kt x)
      rw [mem_ball] at hb
      simp only [R₀] at h1
      linarith
  refine gm_h47_of_pairs hF (gm_condExp_gmFilt h38 hγ hγ2 hD hh hη hℓ𝕣 hε k) S A B Z W G
    {ω | (zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω).Nonempty} {ω | (zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω).Nonempty}
    Reg hAm hBm hZm hAZ hG hZE hZF ?_ ?_ hΛ ?_ hK (le_trans (Nat.cast_nonneg _) hCp) hδ
    (N := fun x => ∑ i ∈ S, (B i).indicator (fun _ => (1 : ℝ)) x)
    (Finset.measurable_sum S fun i _ => measurable_const.indicator (hBm i))
    (integrable_finset_sum S fun i _ => (integrable_const (1 : ℝ)).indicator (hBm i))
    (fun x => le_rfl) ?_ hP hReg
  · rintro ω ⟨⟨p, hp⟩, hωG⟩
    exact mem_iUnion₂.2 ⟨p, hS ω hωG p hp, hp⟩
  · intro ω hω
    obtain ⟨i, -, hi⟩ := mem_iUnion₂.1 hω
    exact ⟨i, hi⟩
  · rintro ⟨z, r⟩ hiS
    by_cases hgood : r ∈ p4Rads R 𝕣 ε ∧ 𝕫 ∉ Metric.ball z (R.lam 3 * r) ∧
        𝕨 ∉ Metric.ball z (R.lam 3 * r)
    · obtain ⟨hr, hfz, hfw⟩ := hgood
      obtain ⟨hr0, hre⟩ := hRads r hr
      have eZW : Z (z, r) ∩ W = gmG0 D h 𝕫 𝕨 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν
          (p4Rads R 𝕣 ε) z r R₀ := by
        ext x
        simp only [Z, W, gmG0, mem_inter_iff, mem_setOf_eq, thickening_of_nonpos le_rfl,
          notMem_empty, not_false_eq_true, and_true]
        rfl
      have hsub : Hit z r ⊆ gmHitBall D h 𝕫 𝕨 η z r := by
        rintro ω ⟨_, ⟨v, rfl⟩, hv⟩
        have hL : 0 < (D (h ω)).1 (𝕫, 𝕨) := lt_of_le_of_ne (gm_D_nonneg _ 𝕫 𝕨)
          (fun h0 => h𝕫𝕨 ((D (h ω)).2.eq_of_eq_zero 𝕫 𝕨 h0.symm))
        refine ⟨v * (D (h ω)).1 (𝕫, 𝕨), ⟨mul_nonneg v.2.1 hL.le,
          mul_le_of_le_one_left hL.le v.2.2⟩, ?_⟩
        have hPv : geodL (D (h ω)) 𝕫 𝕨 (η ω) (v * (D (h ω)).1 (𝕫, 𝕨)) = η ω v := by
          simp only [geodL]
          congr 1
          rw [mul_div_cancel_right₀ _ hL.ne']
          exact projIcc_val zero_le_one v
        rw [hPv]
        exact ball_subset_ball (mul_le_of_le_one_left hr0.le hlam11) hv
      rw [eZW, eA, eB]
      exact gm_L4_7_pair_of_cond4 h38 hC24 hC27 hC14 hγ hγ2 hD hh h𝕫𝕨 hη hℓ𝕣 hε ha
        (mul_le_of_le_one_left hr0.le hlam21) (gm_lt_lam4_of_le he hre hlam3)
        (gm_measurableSet_E_of_cond2 hh (hE2 z r hr))
        (gm_measurableSet_Ef_of_cond2 hD hh hη (hEf2 z r hr)) (hHitm z r) hsub hΛ hψ₀ h0
        (hψS _ hiS) (h4 z r hr hfz hfw)
    · have hzero : ∀ x, (Z (z, r) ∩ W).indicator (fun _ => (1 : ℝ)) x = 0 := fun x =>
        indicator_of_notMem (fun hx => hgood (hgoodOf z r x hx)) _
      exact Eventually.of_forall fun x => by rw [hzero x]; simp
  · intro x _
    refine le_trans ?_ hCp
    calc ∑ i ∈ S, (B i).indicator (fun _ => (1 : ℝ)) x ≤ ∑ _i ∈ S, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by
            by_cases hx : x ∈ B i
            · rw [indicator_of_mem hx]
            · rw [indicator_of_notMem hx]; exact zero_le_one
      _ = S.card := by simp

end LQGMetric.GM
