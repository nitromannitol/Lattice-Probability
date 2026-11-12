/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate4L420F at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3L420
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4Stop

/-!
# GM Lemma 4.20 for `𝒵^𝔈_k` (DEC-89, packet A)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.20 (l. 2333–2356):
"`𝔈_r(z)` is determined by `h|_{B_{λ₄r}(z)}` and `P` stopped at its last exit from `B_{λ₄r}(z)`
… since `P` does not re-enter `𝓑^•_{s_{k+1}}` after time `s_{k+1}` … `{𝒵^𝔈_k ≠ ∅} ∩ F_k ∈
𝓕_{k+1}`" (l. 2356). Decision `decisions/DEC-89.md` (D89a): `stopLastExit` is the stopped path
reparametrized by its own length, hence a function of `P|_{[0,s_{k+1}]}` on
`{B_{λ₄r}(z) ⊆ 𝓑^•_{s_{k+1}}, 𝕨 ∉ 𝓑^•_{s_{k+1}}}` (non-reentry, `gm_S4_7_mem_iff`).

* `gm_stopLastExit_eq_of_pathK` (pathwise): `stopLastExit η K = stopLastExit Q K` for
  `Q(v) = P(s v)`;
* `gm_aeEventIn_inter_sup`: the events `E` with `A ∩ E` a.s. in `m` form a σ-algebra;
* `gm_comap_continuous_le`: `Q : Ω → C(I,ℂ)` is measurable for the evaluation σ-algebra;
* `gm_Ef_piece_Fk`, `gm_zkF_pair_aeEventIn`, `gm_L4_20F`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric TopologicalSpace
open LQGMetric.Blueprint LQGMetric.LocalEvent
open scoped Pointwise

namespace LQGMetric.GM

/-- **the stopped geodesic only sees `P|_{[0,s]}`** (GM l. 2356, non-reentry; D89a) -/
theorem gm_stopLastExit_eq_of_pathK {d : ContMetric} {𝕫 𝕨 : ℂ} {η : C(unitInterval, ℂ)}
    (hη : IsGeod01 d 𝕫 𝕨 η) (h𝕫𝕨 : 𝕫 ≠ 𝕨) {s : ℝ} (hs : 0 < s)
    (hw : 𝕨 ∉ filledBall d 𝕫 s) {K : Set ℂ} (hK : K ⊆ filledBall d 𝕫 s)
    (Q : C(unitInterval, ℂ)) (hQ : ∀ v : unitInterval, Q v = geodL d 𝕫 𝕨 η (s * v)) :
    stopLastExit η K = stopLastExit Q K := by
  have hP := gm_geodL_isGeodesicL hη h𝕫𝕨
  set L := d.1 (𝕫, 𝕨) with hLdef
  have hL : 0 < L := lt_of_le_of_ne (gm_D_nonneg d 𝕫 𝕨)
    (fun h0 => h𝕫𝕨 (d.2.eq_of_eq_zero 𝕫 𝕨 h0.symm))
  have hPv : ∀ v : unitInterval, geodL d 𝕫 𝕨 η (v * L) = η v := fun v => by
    simp only [geodL, L]
    congr 1
    rw [mul_div_cancel_right₀ _ hL.ne']
    exact projIcc_val zero_le_one v
  have hsL : s < L := by
    by_contra hle
    replace hle := not_lt.mp hle
    apply hw
    have := (gm_S4_7_mem_iff hP hs hw (u := L) ⟨hL.le, le_rfl⟩).2 hle
    rwa [hP.2.2.1] at this
  have hQ' : ∀ v : unitInterval, Q v = η (projIcc 0 1 zero_le_one (s * v / L)) := hQ
  -- the sets of times in `K`
  have hset : {t : ℝ | ∃ u : unitInterval, (u : ℝ) = t ∧ η u ∈ K} =
      (s / L) • {t : ℝ | ∃ u : unitInterval, (u : ℝ) = t ∧ Q u ∈ K} := by
    ext t
    simp only [Set.mem_smul_set, mem_setOf_eq, smul_eq_mul]
    constructor
    · rintro ⟨u, rfl, hu⟩
      have huL : (u : ℝ) * L ∈ Icc 0 L :=
        ⟨mul_nonneg u.2.1 hL.le, mul_le_of_le_one_left hL.le u.2.2⟩
      have hle : (u : ℝ) * L ≤ s :=
        (gm_S4_7_mem_iff hP hs hw huL).1 (by rw [hPv]; exact hK hu)
      refine ⟨u * L / s, ⟨⟨u * L / s, div_nonneg huL.1 hs.le, (div_le_one hs).2 hle⟩, rfl, ?_⟩,
        ?_⟩
      · rw [hQ]
        show geodL d 𝕫 𝕨 η (s * ((u : ℝ) * L / s)) ∈ K
        rw [mul_div_cancel₀ _ hs.ne', hPv]; exact hu
      · field_simp
    · rintro ⟨_, ⟨v, rfl, hv⟩, rfl⟩
      have h01 : s / L * v ∈ Icc (0 : ℝ) 1 :=
        ⟨mul_nonneg (div_nonneg hs.le hL.le) v.2.1,
          mul_le_one₀ ((div_le_one hL).2 hsL.le) v.2.1 v.2.2⟩
      refine ⟨⟨_, h01⟩, rfl, ?_⟩
      rw [hQ'] at hv
      convert hv using 2
      rw [projIcc_of_mem _ (by rwa [div_mul_eq_mul_div] at h01)]
      ext; simp only; ring
  have hT : lastExitTime η K = s / L * lastExitTime Q K := by
    unfold lastExitTime
    rw [hset, Real.sSup_smul_of_nonneg (div_nonneg hs.le hL.le), smul_eq_mul]
  funext u
  have hT0 : 0 ≤ lastExitTime Q K := gm_lastExitTime_nonneg Q K
  have hT1 : lastExitTime Q K ≤ 1 := gm_lastExitTime_le_one Q K
  have hm : (u : ℝ) * lastExitTime Q K ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg u.2.1 hT0, mul_le_one₀ u.2.2 hT0 hT1⟩
  rw [gm_stopLastExit_apply, gm_stopLastExit_apply, hQ', projIcc_of_mem _ hm, hT]
  congr 2
  simp only
  ring

section Gen
variable {Ω : Type} {m0 m m₁ m₂ : MeasurableSpace Ω} {P : Measure[m0] Ω}

/-- the events `E` with `A ∩ E` a.s. in `m` form a σ-algebra (for `A` a.s. in `m`) -/
theorem gm_aeEventIn_inter_sup {A : Set Ω} (hA : @AEEventIn Ω m0 P m A)
    (h₁ : ∀ E, MeasurableSet[m₁] E → @AEEventIn Ω m0 P m (A ∩ E))
    (h₂ : ∀ E, MeasurableSet[m₂] E → @AEEventIn Ω m0 P m (A ∩ E)) {E : Set Ω}
    (hE : MeasurableSet[m₁ ⊔ m₂] E) : @AEEventIn Ω m0 P m (A ∩ E) := by
  let M : MeasurableSpace Ω :=
    { MeasurableSet' := fun E => @AEEventIn Ω m0 P m (A ∩ E)
      measurableSet_empty := ⟨∅, @MeasurableSet.empty _ m, by rw [inter_empty]⟩
      measurableSet_compl := fun E hE => by
        obtain ⟨F, hF, hEF⟩ := hE
        obtain ⟨G, hG, hAG⟩ := hA
        refine ⟨G ∩ Fᶜ, MeasurableSet.inter (m := m) hG (MeasurableSet.compl (m := m) hF), ?_⟩
        have e : A ∩ Eᶜ = A ∩ (A ∩ E)ᶜ := by
          ext ω; simp only [mem_inter_iff, mem_compl_iff]; tauto
        rw [e]
        exact EventuallyEqSet.inter hAG (EventuallyEqSet.compl hEF)
      measurableSet_iUnion := fun f hf => by
        rw [inter_iUnion]
        exact gm_aeEventIn_iUnion hf }
  have hle : m₁ ⊔ m₂ ≤ M := sup_le (fun E hE => h₁ E hE) (fun E hE => h₂ E hE)
  exact hle E hE

lemma gm_aeEventIn_congr {E₁ E₂ : Set Ω} (he : E₁ =ᵐ[P] E₂) (h : @AEEventIn Ω m0 P m E₂) :
    @AEEventIn Ω m0 P m E₁ := by
  obtain ⟨F, hF, hEF⟩ := h
  exact ⟨F, hF, he.trans hEF⟩

end Gen

/-- a continuous path-valued map is measurable (Borel on `C(I,ℂ)`) for the σ-algebra of its
evaluations (`C(I,ℂ)` is standard Borel; evaluation on a dense sequence is injective) -/
theorem gm_measurable_contPath {Ω : Type} (Q : Ω → unitInterval → ℂ)
    (hQ : ∀ ω, Continuous (Q ω)) :
    Measurable[MeasurableSpace.comap Q inferInstance]
      (fun ω => (⟨Q ω, hQ ω⟩ : C(unitInterval, ℂ))) := by
  let _ : MeasurableSpace Ω := MeasurableSpace.comap Q inferInstance
  let ev : C(unitInterval, ℂ) → ℕ → ℂ := fun f k => f (denseSeq unitInterval k)
  have hevm : Measurable ev := measurable_pi_iff.2 fun k => (continuous_eval_const _).measurable
  have hinj : Function.Injective ev := fun f g hfg => ContinuousMap.ext fun x =>
    congrFun (Continuous.ext_on (denseRange_denseSeq unitInterval) f.continuous g.continuous
      (by rintro _ ⟨k, rfl⟩; exact congrFun hfg k)) x
  have hemb : MeasurableEmbedding ev := hevm.measurableEmbedding hinj
  refine hemb.measurable_comp_iff.1 ?_
  exact measurable_pi_iff.2 fun k => (measurable_pi_apply _).comp (comap_measurable Q)

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **the `𝔈`-piece of GM Lemma 4.20** (l. 2356, D89a): if `𝔈_r(z)` is a.s. in
`σ(h|_{B_{λ₄r}(z)}, P stopped at its last exit from B_{λ₄r}(z))` (Thm 4.2 (2)), then
`{(z,r) ∈ 𝒵_k} ∩ 𝔈_r(z) ∩ {P ∩ B_{λ₂r}(z) ≠ ∅} ∩ F_k` is a.s. an event of `𝓕_{k+1}` -/
theorem gm_Ef_piece_Fk [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) {𝕫 𝕨 : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {𝕣 ε β : ℝ} {k : ℕ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε) (h𝕣 : 0 < 𝕣)
    (ha : 0 < R.lam 3 * ε * 𝕣) (hlam5 : 0 ≤ R.lam 4) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hre : r ≤ ε * 𝕣) (hlr : R.lam 1 * r ≤ 2 * R.lam 3 * (ε * 𝕣)) {Es : Set DistC}
    (hEf : AEEventIn P (fieldSigma h (ballO z (R.lam 3 * r)) ⊔ MeasurableSpace.comap
      (fun ω => stopLastExit (sel 𝕫 𝕨 (h ω)) (Metric.ball z (R.lam 3 * r))) inferInstance)
      (h ⁻¹' Es)) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1))
      ({ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
          (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)} ∩ h ⁻¹' Es ∩
        {ω | (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball z (R.lam 1 * r)).Nonempty} ∩
        gmFk D h R 𝕫 𝕨 𝕣 ε β k) := by
  set sk := s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1)
  set K : Set ℂ := Metric.ball z (R.lam 3 * r) with hKdef
  set Cd : Set Ω := {ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω))
    (R.lam 0) (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)}
  set Ht : Set Ω := {ω | (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball z (R.lam 1 * r)).Nonempty}
  set A : Set Ω := Cd ∩ Ht ∩ gmFk D h R 𝕫 𝕨 𝕣 ε β k with hAdef
  have he : 0 < ε * 𝕣 := mul_pos hε h𝕣
  have hlam : 0 < R.lam 3 := by
    have : 0 < R.lam 3 * (ε * 𝕣) := by rw [← mul_assoc]; exact ha
    exact pos_of_mul_pos_left this he.le
  have hA : AEEventIn P (gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1)) A :=
    gm_hit_piece_Fk h38 hγ hγ2 hD hh R h𝕫𝕨 hη hℓ𝕣 hε ha hlam5 h𝕣 k z r (fun _ => hlr) (β := β)
  have hsub : ∀ ω ∈ A, K ⊆ filledBall (D (h ω)) 𝕫 (sk ω) := by
    rintro ω ⟨⟨hc, -⟩, hF⟩
    have hrad : R.lam 3 * r ≤ (2 * R.lam 3 + R.lam 4) * (ε * 𝕣) := by
      have : R.lam 3 * r ≤ R.lam 3 * (ε * 𝕣) := mul_le_mul_of_nonneg_left hre hlam.le
      have : 0 ≤ R.lam 4 * (ε * 𝕣) := mul_nonneg hlam5 he.le
      nlinarith
    exact (ball_subset_ball hrad).trans (gm_gmF0C_ball hF.1.1 hc)
  have hsk : ∀ ω, 0 < sk ω := fun ω => by
    simp only [sk]; rw [gm_s4S_eq]
    have := gm_tauD_pos (D (h ω)) 𝕫 hℓ𝕣
    have : 0 ≤ ((k + 1 : ℕ) : ℝ) * ε ^ β :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hε.le β)
    positivity
  -- the field part
  have h₁ : ∀ E, MeasurableSet[fieldSigma h (ballO z (R.lam 3 * r))] E → AEEventIn P (gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1)) (A ∩ E) := by
    intro E hE
    have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
    obtain ⟨G₁, hG₁, hEG₁⟩ := gm_aeEventIn_localSigma_of_field h
      (A := fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω))
      (fun ω => gm_filledBall_isClosed _ _ _)
      (by filter_upwards [hlen] with ω hω; exact gm_filledBall_isBounded_of_lenSet hω 𝕫 _)
      (isOpen_ball (x := z) (ε := R.lam 3 * r)) hE
    have hloc : AEEventIn P (gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1))
        ({ω | K ⊆ filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω)} ∩ E) :=
      ⟨G₁, (le_sup_left : gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1)) ≤ _) _ hG₁, hEG₁⟩
    have e : A ∩ E =
        A ∩ ({ω | K ⊆ filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω)} ∩ E) := by
      ext ω
      simp only [mem_inter_iff, mem_setOf_eq]
      constructor
      · rintro ⟨hω, hE⟩
        exact ⟨hω, (hsub ω hω).trans (gm_filledBall_mono _ _ (gm_s4S_le_s4T hε (k + 1) ω)), hE⟩
      · rintro ⟨hω, -, hE⟩; exact ⟨hω, hE⟩
    rw [e]
    exact gm_aeEventIn_inter hA hloc
  -- the path part
  have hQc : ∀ ω, Continuous (gmPathK D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) sk ω) := fun ω =>
    (sel 𝕫 𝕨 (h ω)).continuous.comp (continuous_projIcc.comp
      ((continuous_const.mul continuous_subtype_val).div_const _))
  have h₂ : ∀ E, MeasurableSet[MeasurableSpace.comap
      (fun ω => stopLastExit (sel 𝕫 𝕨 (h ω)) K) inferInstance] E → AEEventIn P (gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1)) (A ∩ E) := by
    rintro _ ⟨S, hS, rfl⟩
    set Qc : Ω → C(unitInterval, ℂ) := fun ω =>
      ⟨gmPathK D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) sk ω, hQc ω⟩
    have hstm : Measurable fun f : C(unitInterval, ℂ) => stopLastExit f K :=
      measurable_pi_iff.2 fun u => gm_measurable_stopLastExit_apply isOpen_ball u
    have hG : MeasurableSet[gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1)] (Qc ⁻¹' ((fun f : C(unitInterval, ℂ) => stopLastExit f K) ⁻¹' S)) :=
      (le_sup_right : _ ≤ gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1)) _
        ((gm_measurable_contPath _ hQc) (hstm hS))
    refine gm_aeEventIn_congr ?_ (gm_aeEventIn_inter hA (gm_aeEventIn_of_measurableSet hG))
    filter_upwards [hη] with ω hω
    apply propext
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hωA, hS'⟩
      refine ⟨hωA, ?_⟩
      rwa [gm_stopLastExit_eq_of_pathK hω.1 h𝕫𝕨 (hsk ω) hωA.2.2 (hsub ω hωA) (Qc ω)
        (fun v => rfl)] at hS'
    · rintro ⟨hωA, hS'⟩
      refine ⟨hωA, ?_⟩
      rwa [gm_stopLastExit_eq_of_pathK hω.1 h𝕫𝕨 (hsk ω) hωA.2.2 (hsub ω hωA) (Qc ω)
        (fun v => rfl)]
  obtain ⟨F, hF, hEF⟩ := hEf
  have H := gm_aeEventIn_inter_sup hA h₁ h₂ hF
  have e : {ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
          (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)} ∩ h ⁻¹' Es ∩
        {ω | (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball z (R.lam 1 * r)).Nonempty} ∩
        gmFk D h R 𝕫 𝕨 𝕣 ε β k = A ∩ h ⁻¹' Es := by
    ext ω; simp only [hAdef, Cd, Ht, mem_inter_iff]; tauto
  rw [e]
  exact gm_aeEventIn_congr (EventuallyEqSet.inter EventuallyEq.rfl hEF) H

/-- one pair `(z, r)` of `𝒵^𝔈_k ∩ F_k` (GM l. 2352–2356) -/
theorem gm_zkF_pair_aeEventIn [P.IsComplete] (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4)
    (hC27 : CONFLem2_7) (hC14 : CONFThm1_4) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) {𝕫 𝕨 : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC)
    {𝕣 ε β : ℝ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε) (h𝕣 : 0 < 𝕣) (hlam : 1 < R.lam 3)
    (hlam5 : 0 ≤ R.lam 4)
    (hRads : ∀ r ∈ p4Rads R 𝕣 ε, 0 < r ∧ r ≤ ε * 𝕣 ∧ R.lam 1 * r ≤ 2 * R.lam 3 * (ε * 𝕣))
    (hEf : ∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma h (ballO z (R.lam 3 * r)) ⊔
      MeasurableSpace.comap (fun ω => stopLastExit (sel 𝕫 𝕨 (h ω)) (Metric.ball z (R.lam 3 * r)))
        inferInstance) (h ⁻¹' Ef r z 𝕫 𝕨))
    (k : ℕ) (z : ℂ) (r : ℝ) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1))
      ({ω | (z, r) ∈ zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω} ∩ gmFk D h R 𝕫 𝕨 𝕣 ε β k) := by
  by_cases hr : r ∈ p4Rads R 𝕣 ε
  · obtain ⟨hr0, hre, hlr⟩ := hRads r hr
    have he : 0 < ε * 𝕣 := mul_pos hε h𝕣
    have ha : 0 < R.lam 3 * ε * 𝕣 := by rw [mul_assoc]; exact mul_pos (by linarith) he
    have hρe : ε * 𝕣 < 2 * R.lam 3 * (ε * 𝕣) := by nlinarith
    have H1 := gm_Ef_piece_Fk (k := k) (β := β) h38 hγ hγ2 hD hh R h𝕫𝕨 sel hη hℓ𝕣 hε h𝕣 ha
      hlam5 z hr0 hre hlr (hEf z r hr)
    have H2 := gm_stab_piece_Fk (k := k) h38 hC24 hC27 hC14 hγ hγ2 hD hh R 𝕫 𝕨
      (fun ω => sel 𝕫 𝕨 (h ω)) hℓ𝕣 hε ha hρe z hr0 hre (β := β)
    have e : {ω | (z, r) ∈ zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω} ∩ gmFk D h R 𝕫 𝕨 𝕣 ε β k =
        ({ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
          (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)} ∩ h ⁻¹' Ef r z 𝕫 𝕨 ∩
          {ω | (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball z (R.lam 1 * r)).Nonempty} ∩
          gmFk D h R 𝕫 𝕨 𝕣 ε β k) ∩
        (gmStabEv D h 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν (p4Rads R 𝕣 ε) z r ∩
          gmFk D h R 𝕫 𝕨 𝕣 ε β k) := by
      ext ω
      simp only [zkF, gmStabEv, mem_inter_iff, mem_setOf_eq, mem_preimage]
      tauto
    rw [e]
    exact gm_aeEventIn_inter H1 H2
  · have e : {ω | (z, r) ∈ zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω} ∩ gmFk D h R 𝕫 𝕨 𝕣 ε β k = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨⟨⟨-, -, hr', -⟩, -⟩, -⟩
      exact hr hr'
    rw [e]
    exact ⟨∅, @MeasurableSet.empty Ω (gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1)),
      EventuallyEq.rfl⟩

/-- **GM Lemma 4.20 for `𝒵^𝔈_k`** (l. 2356): `{𝒵^𝔈_k ≠ ∅} ∩ F_k` is a.s. in `𝓕_{k+1}` -/
theorem gm_L4_20F [P.IsComplete] (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4)
    (hC27 : CONFLem2_7) (hC14 : CONFThm1_4) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) {𝕫 𝕨 : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC)
    {𝕣 ε β : ℝ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε) (h𝕣 : 0 < 𝕣) (hlam : 1 < R.lam 3)
    (hlam5 : 0 ≤ R.lam 4)
    (hRads : ∀ r ∈ p4Rads R 𝕣 ε, 0 < r ∧ r ≤ ε * 𝕣 ∧ R.lam 1 * r ≤ 2 * R.lam 3 * (ε * 𝕣))
    (hEf : ∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma h (ballO z (R.lam 3 * r)) ⊔
      MeasurableSpace.comap (fun ω => stopLastExit (sel 𝕫 𝕨 (h ω)) (Metric.ball z (R.lam 3 * r)))
        inferInstance) (h ⁻¹' Ef r z 𝕫 𝕨)) (k : ℕ) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1))
      ({ω | (zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω).Nonempty} ∩ gmFk D h R 𝕫 𝕨 𝕣 ε β k) :=
  gm_L4_20_of_pairs (m0 := ‹MeasurableSpace Ω›) (P := P)
    (m := gmSigFk D h 𝕫 𝕨 (fun ω => sel 𝕫 𝕨 (h ω)) R.ℓ 𝕣 ε β (k + 1))
    (zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k) (gmFk D h R 𝕫 𝕨 𝕣 ε β k)
    (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) (R.rr 𝕣 ε)
    (gm_zkF_pairs D sel h R Ef 𝕫 𝕨 𝕣 ε β k) fun _ _ =>
      gm_zkF_pair_aeEventIn h38 hC24 hC27 hC14 hγ hγ2 hD hh R h𝕫𝕨 sel hη Ef hℓ𝕣 hε h𝕣 hlam
        hlam5 hRads hEf k _ _

end LQGMetric.GM
