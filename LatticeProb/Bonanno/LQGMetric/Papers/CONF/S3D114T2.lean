/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114T2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114T1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D110C

/-!
# CONF Lemma 3.6, Step 3: CONF (3.25) on one piece

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, (3.25) (C:1433–1447); decision D114 §4 C2;
route of `handoff/P2-CONF36N.md` §5.

`conf36Eq325_fatG`: **`Conf36Eq325 γ D c p (fatG p)`** for `0 < p.δ < 1/8`. For the piece
`(𝔢, 𝔷, k, 𝔗)`, `𝔯 = 2^k𝔢`, `𝔘 = confU 𝔯 δ 𝔷 𝔗`: on `Q = {𝓑^•_τ ⊆ (cl 𝔘)ᶜ}` every event of
`σ(𝓑^•_τ, h|_{𝓑^•_τ})` mod constants is a.s. an event of `σ((h − h_𝔯(𝔷))|_{ℂ∖𝔘})`
(`conf36_trace_recSigma`, CONF's use of Lemma 2.1 at C:1431), and so are the events
`E^{Ũ}_{r}(𝔷)` (`r ≤ 𝔯/2`) and the `fatG` events (`r ≤ 𝔯/6`) at the radii below `𝔯`
(CONF C:1438–1443: "determined by `E^{Ũ^𝔯}_𝔯(𝔷)` and the events at smaller radii"). The trace
σ-algebra `conf21Tr` collects them; `conf36_avoid_pc_eq` (S3D114S7) writes the piece as
`W ∩ E^𝔘_𝔯(𝔷)` with `W` built from these events, and the piece lies in `Q`
(`conf36T_eq_subset_compl_closure`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- `{ω | ω ∈ Y (f ω)}` as a countable union over the values of `f` -/
theorem conf36_setOf_mem_eq_iUnion {Ω ι : Type} (Y : ι → Set Ω) (f : Ω → ι) :
    {ω | ω ∈ Y (f ω)} = ⋃ i : ι, {ω | f ω = i} ∩ Y i := by
  ext ω
  simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff]
  exact ⟨fun hω => ⟨f ω, rfl, hω⟩, fun ⟨i, h1, h2⟩ => h1 ▸ h2⟩

/-- `{ω | ∀ m ∈ [1, n'], ω ∉ G m}` is measurable if every `G m` is -/
theorem conf36_measurableSet_avoid {Ω : Type} {M : MeasurableSpace Ω} {G : ℕ → Set Ω}
    (hG : ∀ m, MeasurableSet[M] (G m)) (n' : ℕ) :
    MeasurableSet[M] {ω | ∀ m, 1 ≤ m → m ≤ n' → ω ∉ G m} := by
  rw [setOf_forall]
  refine MeasurableSet.iInter fun m => ?_
  by_cases h1 : 1 ≤ m <;> by_cases h2 : m ≤ n' <;> simp only [h1, h2, true_implies,
    false_implies, setOf_true, MeasurableSet.univ]
  exact (hG m).compl

theorem conf36_two_zpow_le {k j : ℤ} (hj : j < k) {𝔢 : ℝ} (h𝔢 : 0 < 𝔢) :
    5 * ((2 : ℝ) ^ j * 𝔢) ≤ 3 * ((2 : ℝ) ^ k * 𝔢) := by
  have h1 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (k - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k / 2 := zpow_sub_one₀ (by norm_num) k
  have h3 : (0 : ℝ) < 2 ^ k := zpow_pos (by norm_num) k
  nlinarith

theorem conf36_zpow_lt_of_six {k j : ℤ} (h : 6 * (2 : ℝ) ^ j ≤ (2 : ℝ) ^ k) : j < k := by
  have h3 : (0 : ℝ) < 2 ^ j := zpow_pos (by norm_num) j
  have : (2 : ℝ) ^ j < 2 ^ k := by linarith
  exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this

/-- **CONF (3.25)** (C:1433–1447) for `Fat = fatG p`, `0 < δ < 1/8` -/
theorem conf36Eq325_fatG {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    (hδ : 0 < p.δ) (hδ8 : p.δ < 1 / 8) : Conf36Eq325 γ D c p (fatG p) := by
  intro hD Ω mΩ P _ h hh z₀ R hR τ hloc _hle x ε hx hε hε1 _hεc n n' hn' A hA i hi
  rcases i with ⟨𝔢, 𝔷, k, 𝔗⟩
  obtain ⟨⟨ω₀, h𝔢⟩, -, -, -⟩ := hi
  have h𝔢0 : 0 < 𝔢 := by
    have := mul_pos (hε1 ω₀).1 hR
    simp only at h𝔢
    rwa [h𝔢] at this
  dsimp only
  set Bf : Ω → Set ℂ := fun ω => filledBall (D (h ω)) z₀ (τ ω) with hBf
  set e : Ω → ℝ := fun ω => ε ω * R with he
  set zf : Ω → ℂ := fun ω => conf36Grid (ε ω * R / 4) (x ω) with hzf
  have h𝔯 : 0 < (2 : ℝ) ^ k * 𝔢 := mul_pos (zpow_pos (by norm_num) k) h𝔢0
  set σK := recSigma h ((2 : ℝ) ^ k * 𝔢) 𝔷 (confU ((2 : ℝ) ^ k * 𝔢) p.δ 𝔷 𝔗)ᶜ with hσK
  letI : MeasurableSpace Ω := mΩ
  set V : Set ℂ := (closure (confU ((2 : ℝ) ^ k * 𝔢) p.δ 𝔷 𝔗))ᶜ with hV
  have hVo : IsOpen V := isClosed_closure.isOpen_compl
  have hVc : IsCompact Vᶜ := by
    rw [hV, compl_compl]
    exact (isBounded_closedBall.subset (GM.p412j_confU_subset _ _ _ _)).isCompact_closure
  have hVK : V ⊆ (confU ((2 : ℝ) ^ k * 𝔢) p.δ 𝔷 𝔗)ᶜ := compl_subset_compl.2 subset_closure
  have hBc : ∀ ω, IsClosed (Bf ω) := fun ω => conf36_isClosed_filledBall _ _ _
  have hQ : AEEventIn P σK {ω | Bf ω ⊆ V} := by
    have := conf36_trace_recSigma h hBc hloc hVo hVc hVK ((2 : ℝ) ^ k * 𝔢) 𝔷
      (G := univ) MeasurableSet.univ
    rwa [inter_univ] at this
  set Tr := conf21Tr P σK _ hQ with hTr
  letI : MeasurableSpace Ω := mΩ
  have hTr0 : localSigma0 h Bf ≤ Tr := fun G hG =>
    conf36_trace_recSigma h hBc hloc hVo hVc hVK ((2 : ℝ) ^ k * 𝔢) 𝔷 hG
  have hTrA : ∀ Y, AEEventIn P σK Y → MeasurableSet[Tr] Y := fun Y hY => conf21_ae_inter hQ hY
  have hset : setSigma Bf ≤ Tr := (confD110_setSigma_le_localSigma0 h Bf).trans hTr0
  have hem : Measurable[localSigma0 h Bf] e := hε.mul_const R
  have hzm : Measurable[localSigma0 h Bf] zf := conf36_measurable_grid ((hε.mul_const R).div_const 4) hx
  set E₀ : Set Ω := {ω | e ω = 𝔢 ∧ zf ω = 𝔷} with hE₀
  have hE₀m : MeasurableSet[Tr] E₀ :=
    hTr0 _ ((hem (measurableSet_singleton 𝔢)).inter (hzm (measurableSet_singleton 𝔷)))
  -- the events `E^{Ũ}` at radii `2^j𝔢 < 𝔯`
  have hEU : ∀ j < k, MeasurableSet[Tr]
      (conf36EUj (xiGamma γ) c D P h p Bf 𝔢 𝔷 j) := by
    intro j hj
    have hr' : 0 < (2 : ℝ) ^ j * 𝔢 := mul_pos (zpow_pos (by norm_num) j) h𝔢0
    unfold conf36EUj
    rw [conf36_setOf_mem_eq_iUnion (fun T' => confEU (xiGamma γ) c D P h p ((2 : ℝ) ^ j * 𝔢) 𝔷 T')
      (fun ω => conf36T p.δ ((2 : ℝ) ^ j * 𝔢) 𝔷 (Bf ω))]
    exact MeasurableSet.iUnion fun T' => (hset _ (conf36_setSigma_T hBc _ _ _ T')).inter
      (hTrA _ (conf36_aeEventIn_recSigma hh hr' (conf36_two_zpow_le hj h𝔢0)
        (conf36_confEU_ball hD hh p hr' 𝔷 T')))
  have hEU0 : ∀ j < k, MeasurableSet[Tr] (E₀ ∩ conf36EUj (xiGamma γ) c D P h p Bf 𝔢 𝔷 j) :=
    fun j hj => hE₀m.inter (hEU j hj)
  have hρ := conf36_measurableSet_rho Tr (ξ := xiGamma γ) (cc := c) (D := D) (P := P) (h := h)
    (p := p) (e := e) (zf := zf) (Bf := Bf) h𝔢0 (fun _ hω => hω) hE₀m hEU0
  -- the `fatG` events at radii `2^j𝔢 ≤ 𝔯/6`
  have hFat : ∀ j : ℤ, 6 * (2 : ℝ) ^ j ≤ (2 : ℝ) ^ k →
      MeasurableSet[Tr] (conf36FatJ (fatG p) (xiGamma γ) c D h p Bf 𝔢 𝔷 j) := by
    intro j hj
    have hr' : 0 < (2 : ℝ) ^ j * 𝔢 := mul_pos (zpow_pos (by norm_num) j) h𝔢0
    unfold conf36FatJ
    have e := conf36_setOf_mem_eq_iUnion (fun T' => {ω | fatG p (D (h ω))
      (scaleFac (xiGamma γ) c (h ω) ((2 : ℝ) ^ j * 𝔢) 𝔷) ((2 : ℝ) ^ j * 𝔢) 𝔷 T'})
      (fun ω => conf36T p.δ ((2 : ℝ) ^ j * 𝔢) 𝔷 (Bf ω))
    simp only [mem_ofPred_eq] at e
    rw [e]
    exact MeasurableSet.iUnion fun T' => (hset _ (conf36_setSigma_T hBc _ _ _ T')).inter
      (hTrA _ (conf36_aeEventIn_recSigma hh hr'
        (conf36_two_zpow_le (conf36_zpow_lt_of_six hj) h𝔢0)
        (conf36_fatG_ball hD hh p hδ hδ8 c hr' 𝔷 T')))
  -- the event `W`
  have hGtR : ∀ m, MeasurableSet[Tr]
      (conf36GtR (fatG p) (xiGamma γ) c D P h p e zf Bf 𝔢 𝔷 k m) := by
    intro m
    unfold conf36GtR
    refine MeasurableSet.iUnion fun k' => ?_
    have hk' := conf36_zpow_lt_of_six k'.2
    exact (((hρ m k'.1 hk').inter (hEU _ hk')).inter (hFat _ k'.2)).inter
      (hset _ (conf36_setSigma_conn Bf _ 𝔷))
  have hRR : MeasurableSet[Tr] (conf36RR (xiGamma γ) c D P h p e zf Bf 𝔢 𝔷 k n) := by
    unfold conf36RR
    refine MeasurableSet.iUnion fun ℓ' => (hρ n ℓ'.1 (conf36_zpow_lt_of_six ℓ'.2)).inter
      (MeasurableSet.iInter fun j => ?_)
    exact (MeasurableSet.const _).compl.union (hEU0 j.1 j.2).compl
  have hW : MeasurableSet[Tr] (conf36W (fatG p) (xiGamma γ) c D P h p e zf Bf A n n' 𝔢 𝔷 k 𝔗) :=
    (((hTr0 _ hA).inter (hset _ (conf36_setSigma_T hBc _ _ _ 𝔗))).inter hRR).inter
      (conf36_measurableSet_avoid hGtR n')
  obtain ⟨F, hF, hQWF⟩ := hW
  refine ⟨F, hF, ?_⟩
  have hsub : conf36Avoid (conf36Gt (fatG p) (xiGamma γ) c D P h p e zf Bf) A n' ∩
      conf36Pc (xiGamma γ) c D P h p e zf Bf n (𝔢, 𝔷, k, 𝔗) ⊆ {ω | Bf ω ⊆ V} :=
    fun ω hω => conf36T_eq_subset_compl_closure hδ h𝔯 hω.2.2.2.2.1
  have heq := conf36_avoid_pc_eq (Fat := fatG p) (ξ := xiGamma γ) (cc := c) (D := D) (P := P)
    (h := h) (p := p) (e := e) (zf := zf) (Bf := Bf) (𝔷 := 𝔷) (k := k) h𝔢0 hn' A 𝔗
  rw [← inter_eq_right.2 hsub, heq, ← inter_assoc]
  exact hQWF.inter EventuallyEq.rfl

end LQGMetric.CONF
