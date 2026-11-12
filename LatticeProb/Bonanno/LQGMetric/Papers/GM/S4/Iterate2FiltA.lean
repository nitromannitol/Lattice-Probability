/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate2FiltA at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2Filt
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE9
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventRandom2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc

/-!
# GM (4.9): `σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})` is a.s. increasing in `k`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, (4.9) (l. 1650: "the increasing
filtration `𝓕_k`"), and GM l. 1654 ("by Axiom II (locality), `𝓘_k` is determined by
`𝓑^•_{t_k}` and `h|_{𝓑^•_{t_k}}`"), the same locality argument for `𝓑^•_{t_j}`, `j ≤ k`:
`t_j = τ_{ℓ𝕣} c_j ≤ t_k` and `τ_{ℓ𝕣}`, `𝓑^•_{t_j}` are determined by the internal metric of `D_h`
on any open set containing `𝓑^•_{t_k}` (`gm_tk_congr`).

* `gmPieceSig`: events which on the hull piece `{B^{(n)} = S}` a.s. agree with a
  `σ(h|_{int S})`-event (a σ-algebra).
* `gm_localSigma_le_aeSigma` (abstract): for random closed sets `A ⊆ B` (`B` a.s. bounded) whose
  hit events `{A ∩ U ≠ ∅}` are piecewise local for `B`, `σ(A, h|_A)` is a.s. contained in
  `σ(B, h|_B)`.
* **`gm_sigA_ae_mono`**: `σ(𝓑^•_{t_j}, h|) ≤ gmAESigma σ(𝓑^•_{t_k}, h|)` for `j ≤ k` on a complete
  space: the hypothesis `hA` of `gm_condExp_gmFilt_ae_eq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter TopologicalSpace
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

section Abs
variable {Ω : Type} [MeasurableSpace Ω]

/-- events which on `{B^{(n)} = S}` a.s. agree with a `σ(h|_{int S})`-event -/
def gmPieceSig (h : Ω → DistC) (B : Ω → Set ℂ) (n : ℕ) (S : Set ℂ) (P : Measure Ω) :
    MeasurableSpace Ω where
  MeasurableSet' E := ∃ F, MeasurableSet[fieldSigma h (toOpens (interior S) isOpen_interior)] F ∧
    ∀ᵐ ω ∂P, dyadicHull n (B ω) = S → (ω ∈ E ↔ ω ∈ F)
  measurableSet_empty := ⟨∅, @MeasurableSet.empty Ω (fieldSigma _ _),
    Eventually.of_forall fun _ _ => Iff.rfl⟩
  measurableSet_compl := fun E ⟨F, hF, hEF⟩ => ⟨Fᶜ, hF.compl, by
    filter_upwards [hEF] with ω hω hS
    exact not_congr (hω hS)⟩
  measurableSet_iUnion := fun E hE => by
    choose F hF hEF using hE
    refine ⟨⋃ i, F i, MeasurableSet.iUnion hF, ?_⟩
    filter_upwards [ae_all_iff.2 hEF] with ω hω hS
    simp only [mem_iUnion]
    exact exists_congr fun i => hω i hS

omit [MeasurableSpace Ω] in
theorem gm_dyadicHull_mono (n : ℕ) {A B : Set ℂ} (hAB : A ⊆ B) :
    dyadicHull n A ⊆ dyadicHull n B := by
  intro x hx
  simp only [dyadicHull, mem_iUnion] at hx ⊢
  obtain ⟨k, hk, hxk⟩ := hx
  exact ⟨k, hk.mono (inter_subset_inter_right _ hAB), hxk⟩

/-- one hull level of `σ(A, h|_A)` is piecewise local for `B ⊇ A` -/
theorem gm_hullSigma_le_pieceSig (h : Ω → DistC) {P : Measure Ω} {A B : Ω → Set ℂ}
    (hA : ∀ ω, IsClosed (A ω)) (hAB : ∀ ω, A ω ⊆ B ω) (n : ℕ) (S' : Set ℂ)
    (hhit : ∀ U : Set ℂ, IsOpen U →
      MeasurableSet[gmPieceSig h B n S' P] {ω | (A ω ∩ U).Nonempty}) :
    hullSigma h A n ≤ gmPieceSig h B n S' P := by
  have hset : setSigma A ≤ gmPieceSig h B n S' P :=
    generateFrom_le (by rintro _ ⟨U, hU, rfl⟩; exact hhit U hU)
  refine sup_le hset (generateFrom_le ?_)
  rintro _ ⟨S, F, hF, rfl⟩
  obtain ⟨F₁, hF₁, hE₁⟩ := hset _ (measurableSet_hull_eq hA n S)
  by_cases hSS : S ⊆ S'
  · refine ⟨F₁ ∩ F, hF₁.inter (fieldSigma_mono h (V := toOpens (interior S) isOpen_interior)
      (W := toOpens (interior S') isOpen_interior) (interior_mono hSS) _ hF), ?_⟩
    filter_upwards [hE₁] with ω hω hS
    simp only [mem_inter_iff, mem_ofPred_eq] at hω ⊢
    rw [hω hS]
  · refine ⟨∅, @MeasurableSet.empty Ω (fieldSigma _ _), Eventually.of_forall fun ω hS => ?_⟩
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro h1 _
    exact hSS (h1 ▸ hS ▸ gm_dyadicHull_mono n (hAB ω))

/-- **`σ(A, h|_A)` is a.s. contained in `σ(B, h|_B)`** for random closed sets `A ⊆ B`, `B` a.s.
bounded, when the hit events of `A` are piecewise local for `B` -/
theorem gm_localSigma_le_aeSigma (h : Ω → DistC) {P : Measure Ω} {A B : Ω → Set ℂ}
    (hA : ∀ ω, IsClosed (A ω)) (hB : ∀ ω, IsClosed (B ω))
    (hb : ∀ᵐ ω ∂P, Bornology.IsBounded (B ω)) (hAB : ∀ ω, A ω ⊆ B ω)
    (hAm : localSigma h A ≤ ‹MeasurableSpace Ω›)
    (hhit : ∀ (n : ℕ) (s : Finset (ℤ × ℤ)) (U : Set ℂ), IsOpen U →
      MeasurableSet[gmPieceSig h B n (hullFin n s) P] {ω | (A ω ∩ U).Nonempty}) :
    localSigma h A ≤ gmAESigma (localSigma h B) P := by
  intro E hE
  refine MeasurableSpace.measurableSet_inf.2 ⟨hAm E hE, ?_⟩
  obtain ⟨F, hF, hEF⟩ := aeEventIn_localSigma h hB (P := P) (E := E) fun n =>
    aeEventIn_hullSigma_of_pieces h B hb n fun s =>
      gm_hullSigma_le_pieceSig h hA hAB n _ (fun U hU => hhit n s U hU) E
        ((MeasurableSpace.measurableSet_iInf.1 hE) n)
  exact ⟨F, hF, by rwa [inter_univ]⟩

end Abs

/-! ## The filled balls `𝓑^•_{t_j} ⊆ 𝓑^•_{t_k}` -/

/-- the hit event of `𝓑^•_{τ_R c}` is Borel on `lenSet` -/
theorem gm_hitAn (𝕫 : ℂ) (R c : ℝ) {U : Set ℂ} (hU : IsOpen U) :
    GMAnalyticOn lenSet {d | (filledBall d 𝕫 (tauD d 𝕫 R * c) ∩ U).Nonempty} := by
  have hg : ∀ x : ℂ, Measurable fun d : ContMetric => (d, gmTauB 𝕫 R d * c, x) := fun x =>
    measurable_id.prodMk (((gm_measurable_tauB 𝕫 R).mul_const c).prodMk measurable_const)
  refine gmAn_congr (gmAn_of_measurableSet (A := ⋃ i : ℕ, {_d : ContMetric | denseSeq ℂ i ∈ U} ∩
    (fun d : ContMetric => (d, gmTauB 𝕫 R d * c, denseSeq ℂ i)) ⁻¹'
      {p : ContMetric × ℝ × ℂ | p.2.2 ∈ filledBall p.1 𝕫 p.2.1})
    (MeasurableSet.iUnion fun i => (MeasurableSet.const _).inter
      ((gmE_measurableSet_filledBall 𝕫).preimage (hg _)))) fun d hd => ?_
  simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_preimage]
  rw [gm_filledBall_inter_open_iff _ _ _ hU, gm_tauD_eq_tauB hd]

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **the hit events of `𝓑^•_{t_j}` are piecewise local for `𝓑^•_{t_k}`** (`j ≤ k`; locality of
`D_h`, GM l. 1654) -/
theorem gm_hit_pieceSig (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {R cj ck : ℝ}
    (hR : 0 < R) (hc : 1 < ck) (hjk : cj ≤ ck) (n : ℕ) (S' : Set ℂ) {U : Set ℂ}
    (hU : IsOpen U) :
    MeasurableSet[gmPieceSig h (fun ω => filledBall (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 R * ck)) n S' P]
      {ω | (filledBall (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 R * cj) ∩ U).Nonempty} := by
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  set Bs : Set DistC := D ⁻¹' ({d | dyadicHull n (filledBall d 𝕫 (tauD d 𝕫 R * ck)) = S'} ∩
    {d | (filledBall d 𝕫 (tauD d 𝕫 R * cj) ∩ U).Nonempty}) with hBs
  have hnull : NullMeasurableSet Bs (P.map h) :=
    gmE_nullMeas_of_an hD.measurable hh.measurable.aemeasurable hlen
      (gmAn_inter (gmE_hullAn 𝕫 R ck n S') (gm_hitAn 𝕫 R cj hU))
  obtain ⟨F, hF, hEF⟩ := exists_fieldSigma_piece hD P h (Tight.isGFFPlusCont_of_wp hh) hlen
    isOpen_interior hnull (by
      rintro g₁ g₂ h1 h2 heq ⟨hS, hhit⟩
      have l1 := isLength_of_mem_lenSet h1
      have l2 := isLength_of_mem_lenSet h2
      have hKU : filledBall (D g₁) 𝕫 (tauD (D g₁) 𝕫 R * ck) ⊆ interior S' :=
        hS ▸ subset_interior_dyadicHull n _
      obtain ⟨hτ, hball⟩ := gm_tk_congr l1 l2 hc isOpen_interior heq
        (gm_tauD_pos _ 𝕫 hR) hKU
      have hfb : ∀ s ≤ tauD (D g₁) 𝕫 R * ck, filledBall (D g₂) 𝕫 s = filledBall (D g₁) 𝕫 s :=
        fun s hs => gm_filledBall_congr (hball s hs)
      have hτpos := gm_tauD_pos (D g₁) 𝕫 hR
      refine ⟨?_, ?_⟩
      · show dyadicHull n (filledBall (D g₂) 𝕫 (tauD (D g₂) 𝕫 R * ck)) = S'
        rw [hτ, hfb _ le_rfl]; exact hS
      · show (filledBall (D g₂) 𝕫 (tauD (D g₂) 𝕫 R * cj) ∩ U).Nonempty
        rw [hτ, hfb _ (mul_le_mul_of_nonneg_left hjk hτpos.le)]; exact hhit)
  refine ⟨F, hF, ?_⟩
  filter_upwards [hEF] with ω hω hS
  have := Iff.of_eq hω
  simp only [hBs, mem_preimage, mem_inter_iff, mem_ofPred_eq, hS, true_and] at this
  exact this

/-- **`σ(𝓑^•_{t_j}, h|_{𝓑^•_{t_j}})` is a.s. contained in `σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})`** for
`j ≤ k`, on a complete space (GM (4.9) "increasing", via locality) -/
theorem gm_sigA_ae_mono [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {ℓ 𝕣 ε β : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) {j k : ℕ} (hjk : j ≤ k) :
    gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β j) ≤
      gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k)) P := by
  have hc : ∀ i : ℕ, s4T D h 𝕫 ℓ 𝕣 ε β i =
      fun ω => tauD (D (h ω)) 𝕫 (ℓ * 𝕣) * (1 + i * ε ^ β + ε ^ (2 * β)) :=
    fun i => funext (gm_s4T_eq D h 𝕫 ℓ 𝕣 ε β i)
  have hβ : 0 ≤ ε ^ β := Real.rpow_nonneg hε.le β
  have hβ2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hjk' : 1 + j * ε ^ β + ε ^ (2 * β) ≤ 1 + k * ε ^ β + ε ^ (2 * β) := by
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    nlinarith
  have hck : 1 < 1 + k * ε ^ β + ε ^ (2 * β) := by
    have : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) hβ
    linarith
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  have hM : Measurable fun ω => D (h ω) := hD.measurable.comp hh.measurable
  have hAm : gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β j) ≤ ‹MeasurableSpace Ω› :=
    (iInf_le _ 0).trans (gm_hullSigma_filledBall_le (P := P) hh hM
      (gm_measurable_s4T h38 hγ hγ2 hD hh 𝕫 ℓ 𝕣 ε β j) 𝕫 0)
  simp only [gmSigA, hc] at hAm ⊢
  refine gm_localSigma_le_aeSigma h (fun ω => gm_filledBall_isClosed _ _ _)
    (fun ω => gm_filledBall_isClosed _ _ _) ?_
    (fun ω => gm_filledBall_mono _ _ (mul_le_mul_of_nonneg_left hjk' (gm_tauD_pos _ 𝕫 hℓ𝕣).le))
    hAm fun n s U hU => gm_hit_pieceSig h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hck hjk' n _ hU
  filter_upwards [hlen] with ω hω
  exact gm_filledBall_isBounded_of_lenSet hω 𝕫 _

/-- **GM (4.9) filtration, final form**: on a complete space, `P[f | gmFilt k] = P[f | 𝓕_k]` a.s.
for GM's `𝓕_k = σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}}, P|_{[0,s_k]})` (`gmSigF`) -/
theorem gm_condExp_gmFilt [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) {𝕫 𝕨 : ℂ}
    {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {ℓ 𝕣 ε β : ℝ} (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (k : ℕ) (f : Ω → ℝ) :
    P[f | gmSigFk D h 𝕫 𝕨 η ℓ 𝕣 ε β k] =ᵐ[P]
      P[f | gmFilt h38 hγ hγ2 hD hh hη ℓ 𝕣 ε β k] :=
  gm_condExp_gmFilt_ae_eq h38 hγ hγ2 hD hh hη ℓ 𝕣 ε β (Real.rpow_nonneg hε.le β)
    (fun _ hj => gm_sigA_ae_mono h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε hj) f

/-! ## Field events on open sets inside a random closed set (input of GM Lemma 4.20) -/

section FieldEv
variable {Ω : Type} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- `{V ⊂ A}` is a `σ(A)`-event for `V` open and `A` a random closed set -/
theorem gm_setSigma_subset_open (A : Ω → Set ℂ) (hA : ∀ ω, IsClosed (A ω)) {V : Set ℂ}
    (hV : IsOpen V) : MeasurableSet[setSigma A] {ω | V ⊆ A ω} := by
  have e : {ω | V ⊆ A ω} = ⋂ i : ℕ, {ω | denseSeq ℂ i ∈ V → (A ω ∩ {denseSeq ℂ i}).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, inter_singleton_nonempty]
    refine ⟨fun h i hi => h hi, fun h y hy => ?_⟩
    by_contra hyA
    obtain ⟨i, hi⟩ := (denseRange_denseSeq ℂ).exists_mem_open (hV.inter (hA ω).isOpen_compl)
      ⟨y, hy, hyA⟩
    exact hi.2 (h i hi.1)
  rw [e]
  refine MeasurableSet.iInter fun i => ?_
  by_cases hi : denseSeq ℂ i ∈ V
  · simpa only [hi, true_imp_iff] using gm_setSigma_hit_compact A hA isCompact_singleton
  · simp only [hi, false_imp_iff, ofPred_true]
    exact @MeasurableSet.univ Ω (setSigma A)

/-- **an event of `σ(h|_V)`, on `{V ⊂ A}`, is a.s. an event of `σ(A, h|_A)`** (`V` open, `A` an
a.s. bounded random closed set; GM l. 2351–2352: "since `E_r(z)` is determined by `h|_{B_{λ₄r}(z)}`
… `F_k ∩ E_r(z) ∩ {(z,r) ∈ 𝒵_k} ∈ 𝓕_{k+1}`") -/
theorem gm_aeEventIn_localSigma_of_field (h : Ω → DistC) {P : Measure Ω} {A : Ω → Set ℂ}
    (hA : ∀ ω, IsClosed (A ω)) (hb : ∀ᵐ ω ∂P, Bornology.IsBounded (A ω)) {V : Set ℂ}
    (hV : IsOpen V) {E : Set Ω} (hE : MeasurableSet[fieldSigma h (toOpens V hV)] E) :
    AEEventIn P (localSigma h A) ({ω | V ⊆ A ω} ∩ E) := by
  classical
  refine aeEventIn_localSigma h hA fun n => ?_
  set T : Set (Finset (ℤ × ℤ)) := {s | V ⊆ interior (hullFin n s)}
  refine ⟨⋃ s : T, {ω | dyadicHull n (A ω) = hullFin n s} ∩ ({ω | V ⊆ A ω} ∩ E), ?_, ?_⟩
  · refine MeasurableSet.iUnion fun s => ?_
    have hgen : MeasurableSet[hullSigma h A n] ({ω | dyadicHull n (A ω) = hullFin n s} ∩ E) :=
      (le_sup_right : _ ≤ hullSigma h A n) _ (MeasurableSpace.measurableSet_generateFrom
        ⟨hullFin n s, E, fieldSigma_mono h (V := toOpens V hV)
          (W := toOpens (interior (hullFin n s)) isOpen_interior) s.2 _ hE, rfl⟩)
    have hsub : MeasurableSet[hullSigma h A n] {ω | V ⊆ A ω} :=
      (le_sup_left : _ ≤ hullSigma h A n) _ (gm_setSigma_subset_open A hA hV)
    convert hgen.inter hsub using 1
    ext ω; simp only [mem_inter_iff]; tauto
  · rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hb] with ω hbω
    obtain ⟨s, hs⟩ := exists_hullFin_of_bounded hbω n
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, Subtype.exists]
    constructor
    · rintro ⟨hVA, hEω⟩
      refine ⟨s, ?_, hs, hVA, hEω⟩
      show V ⊆ interior (hullFin n s)
      rw [← hs]; exact hVA.trans (subset_interior_dyadicHull n _)
    · rintro ⟨_, _, _, hVA, hEω⟩
      exact ⟨hVA, hEω⟩

end FieldEv

end LQGMetric.GM
