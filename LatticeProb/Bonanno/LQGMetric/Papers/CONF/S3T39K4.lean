/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J8
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114U2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9, packet J6c (part 2): `σ^ε_{s,𝕣}` is an a.s. stopping time (C:1300–1302)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1292–1302: "`R^ε_𝕣(𝓑^•_τ)` is determined by `(𝓑^•_τ, h|_{B_{R}(𝓑^•_τ)})` … if `τ` is a stopping
time for `{(𝓑^•_t, h|_{𝓑^•_t})}`, then so is `σ^ε_{τ,𝕣}`", at a random base `s` and with `h`
modulo additive constants (decision D130 §4, L1).

* `t39k_confE_ball_ae`: `E_r(z) ∩ {B_{5r}(z) ⊆ B}` is a.s. an event of `σ(B, h|_B) mod const`
  (CONF C:1150–1154, 1260: `E_r(z)` is determined by `h|_{B_{5r}(z)}` modulo constants;
  `conf36_confEU_ball`, `conf36_aeEventIn_fieldSigma0On_of_norm`, `conf36_local_ae`, P2-D114);
* `t39k_measurable_rho`, `t39k_measurable_RK`, `t39k_measurableSet_enbhd`: `ρ^n`, `R^ε_𝕣(K)` and
  `{B_{ρ}(K) ⊆ B}` are measurable for any σ-algebra seeing the events, the hits of `K` and the points
  of `B` (adapted from `t39j8_measurable_confRho`, `t39j8_measurable_confRK`,
  `t39j8_measurable_confSigma`, S3T39J8, there for the ambient σ-algebra and `confE`);
* `t39k_enbhd_iff`: inside a bounded `B` only the events `E_r(z)` with `B_{5r}(z) ⊆ B` matter
  (`p412i_RK_congr`, `p412i_ball_subset_enbhd`, GM S4 P412iSig);
* **`t39k_confSigma_ae0`**: the main result (D130 §4 L1).
-/

noncomputable section

open MeasureTheory MeasurableSpace Set Filter Metric TopologicalSpace
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.CONF

variable {Ω : Type}

/-! ## Measurability for an abstract σ-algebra and abstract events -/

section Abstract
variable {M : MeasurableSpace Ω}

/-- `ρ^n_R(z)` is measurable when the events `E_{2^k R}(z)` are (copy of
`t39j8_measurable_confRho`) -/
theorem t39k_measurable_rho (E : Ω → ℝ → ℂ → Prop) {R : ℝ} {z : ℂ}
    (hE : ∀ k : ℤ, MeasurableSet[M] {ω | E ω ((2 : ℝ) ^ k * R) z}) :
    ∀ n, Measurable[M] (fun ω => GM.p412iRho (E ω) R z n)
  | 0 => measurable_const
  | n + 1 => by
    classical
    have ih := t39k_measurable_rho E hE n
    refine Measurable.iInf fun k => ?_
    set S := {ω | 6 * GM.p412iRho (E ω) R z n ≤ ENNReal.ofReal ((2 : ℝ) ^ k * R)} ∩
      {ω | E ω ((2 : ℝ) ^ k * R) z}
    have hS : MeasurableSet[M] S :=
      (measurableSet_le (measurable_const.mul ih) measurable_const).inter (hE k)
    have e : (fun ω => ⨅ (_ : 6 * GM.p412iRho (E ω) R z n ≤ ENNReal.ofReal ((2 : ℝ) ^ k * R))
        (_ : E ω ((2 : ℝ) ^ k * R) z), ENNReal.ofReal ((2 : ℝ) ^ k * R)) =
        S.piecewise (fun _ => ENNReal.ofReal ((2 : ℝ) ^ k * R)) (fun _ => ⊤) := by
      funext ω
      by_cases hω : ω ∈ S
      · rw [S.piecewise_eq_of_mem _ _ hω, iInf_pos (show 6 * GM.p412iRho (E ω) R z n ≤
          ENNReal.ofReal ((2 : ℝ) ^ k * R) from hω.1), iInf_pos (show E ω ((2 : ℝ) ^ k * R) z
          from hω.2)]
      · rw [S.piecewise_eq_of_notMem _ _ hω]
        exact iInf_eq_top.2 fun h1 => iInf_eq_top.2 fun h2 => (hω ⟨h1, h2⟩).elim
    rw [e]
    exact Measurable.piecewise hS measurable_const measurable_const

/-- `R^ε_R(K)` is measurable (copy of `t39j8_measurable_confRK`) -/
theorem t39k_measurable_RK (E : Ω → ℝ → ℂ → Prop) (K : Ω → Set ℂ) (N : ℕ) {R ε : ℝ}
    (hE : ∀ (k a b : ℤ), MeasurableSet[M]
      {ω | E ω ((2 : ℝ) ^ k * (ε * R)) ⟨a * (ε * R / 4), b * (ε * R / 4)⟩})
    (hK : ∀ U : Set ℂ, IsOpen U → MeasurableSet[M] {ω | (K ω ∩ U).Nonempty}) :
    Measurable[M] fun ω => GM.p412iRK (E ω) N R ε (K ω) := by
  classical
  unfold GM.p412iRK
  simp_rw [t39j8_iSup_grid]
  refine (measurable_const.mul (Measurable.iSup fun ab => ?_)).add measurable_const
  set w : ℂ := ⟨ab.1 * (ε * R / 4), ab.2 * (ε * R / 4)⟩
  set H := {ω | w ∈ thickening (ε * R) (K ω)}
  have hH : MeasurableSet[M] H := by
    have e : H = {ω | (K ω ∩ ball w (ε * R)).Nonempty} := by
      ext ω
      simp only [H, mem_ofPred_eq, mem_thickening_iff]
      constructor
      · rintro ⟨y, hy, hd⟩; exact ⟨y, hy, by rwa [mem_ball, dist_comm]⟩
      · rintro ⟨y, hy, hd⟩; exact ⟨y, hy, by rwa [mem_ball, dist_comm] at hd⟩
    rw [e]; exact hK _ isOpen_ball
  have e : (fun ω => ⨆ (_ : w ∈ thickening (ε * R) (K ω)),
      GM.p412iRho (E ω) (ε * R) w N) =
      H.piecewise (fun ω => GM.p412iRho (E ω) (ε * R) w N) (fun _ => 0) := by
    funext ω
    by_cases hω : ω ∈ H
    · rw [H.piecewise_eq_of_mem _ _ hω, iSup_pos (show w ∈ thickening (ε * R) (K ω) from hω)]
    · rw [H.piecewise_eq_of_notMem _ _ hω,
        iSup_neg (show w ∉ thickening (ε * R) (K ω) from hω)]; rfl
  rw [e]
  refine Measurable.piecewise hH (t39k_measurable_rho E (fun k => ?_) N) measurable_const
  obtain ⟨a, b⟩ := ab
  exact hE k a b

/-- `{B_ρ(K) ⊆ B}` is measurable (from the proof of `t39j8_measurable_confSigma`) -/
theorem t39k_measurableSet_enbhd {ρ : Ω → ℝ≥0∞} (hρ : Measurable[M] ρ) (K B : Ω → Set ℂ)
    (hBc : ∀ ω, IsClosed (B ω))
    (hK : ∀ U : Set ℂ, IsOpen U → MeasurableSet[M] {ω | (K ω ∩ U).Nonempty})
    (hB : ∀ x : ℂ, MeasurableSet[M] {ω | x ∈ B ω}) :
    MeasurableSet[M] {ω | enbhd (ρ ω) (K ω) ⊆ B ω} := by
  have hinf : ∀ x : ℂ, Measurable[M] fun ω => Metric.infEDist x (K ω) := by
    intro x
    refine measurable_of_Iio fun t => ?_
    have e : (fun ω => Metric.infEDist x (K ω)) ⁻¹' Iio t =
        {ω | (K ω ∩ Metric.eball x t).Nonempty} := by
      ext ω
      simp only [mem_preimage, mem_Iio, mem_ofPred_eq, Metric.infEDist_lt_iff]
      constructor
      · rintro ⟨y, hy, hxy⟩; exact ⟨y, hy, by rwa [Metric.mem_eball, edist_comm]⟩
      · rintro ⟨y, hy, hxy⟩; exact ⟨y, hy, by rwa [Metric.mem_eball, edist_comm] at hxy⟩
    rw [e]
    exact hK _ Metric.isOpen_eball
  have e : {ω | enbhd (ρ ω) (K ω) ⊆ B ω} = ⋂ i, ({ω | Metric.infEDist (denseSeq ℂ i) (K ω) <
      ρ ω}ᶜ ∪ {ω | denseSeq ℂ i ∈ B ω}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff]
    rw [t39j8_open_subset_closed_iff (O := enbhd (ρ ω) (K ω))
      (isOpen_lt Metric.continuous_infEDist continuous_const) (hBc ω)]
    refine forall_congr' fun i => ?_
    simp only [enbhd, mem_ofPred_eq]
    tauto
  rw [e]
  exact MeasurableSet.iInter fun i => (measurableSet_lt (hinf _) hρ).compl.union (hB _)

end Abstract

/-! ## Deterministic core: only the events inside `B` matter -/

theorem t39k_rk_lt_top_of_subset {E : ℝ → ℂ → Prop} {N : ℕ} {R ε : ℝ} {K B : Set ℂ}
    (hK : K.Nonempty) (hB : Bornology.IsBounded B)
    (hsub : enbhd (GM.p412iRK E N R ε K) K ⊆ B) : GM.p412iRK E N R ε K < ⊤ := by
  by_contra htop
  rw [not_lt_top_iff] at htop
  apply NormedSpace.unbounded_univ ℝ ℂ
  refine hB.subset fun x _ => hsub ?_
  show Metric.infEDist x K < GM.p412iRK E N R ε K
  rw [htop]
  exact lt_top_iff_ne_top.2 (Metric.infEDist_ne_top hK)

/-- **C:1292–1294 (deterministic)**: `B_{R^ε(K)}(K) ⊆ B` for a bounded `B` only depends on the
events `E_r(z)` with `B_{5r}(z) ⊆ B` -/
theorem t39k_enbhd_iff {E : ℝ → ℂ → Prop} {N : ℕ} {R ε : ℝ} (hεR : 0 < ε * R) {K B : Set ℂ}
    (hB : Bornology.IsBounded B) :
    enbhd (GM.p412iRK E N R ε K) K ⊆ B ↔
      enbhd (GM.p412iRK (fun r z => E r z ∧ ball z (5 * r) ⊆ B) N R ε K) K ⊆ B := by
  rcases K.eq_empty_or_nonempty with rfl | hK
  · have e : ∀ ρ : ℝ≥0∞, enbhd ρ (∅ : Set ℂ) = ∅ := fun ρ => by
      ext x; simp [enbhd, Metric.infEDist_empty]
    simp only [e, empty_subset]
  constructor
  · intro H
    have hfin := t39k_rk_lt_top_of_subset hK hB H
    have heq : GM.p412iRK (fun r z => E r z ∧ ball z (5 * r) ⊆ B) N R ε K =
        GM.p412iRK E N R ε K :=
      GM.p412i_RK_congr hεR hfin fun z hz r _ hrρ =>
        ⟨fun h' => ⟨h', ball_subset_closedBall.trans
          ((GM.p412i_ball_subset_enbhd hfin hz hrρ).trans H)⟩, And.left⟩
    rw [heq]; exact H
  · intro H
    have hfin := t39k_rk_lt_top_of_subset hK hB H
    have heq : GM.p412iRK E N R ε K =
        GM.p412iRK (fun r z => E r z ∧ ball z (5 * r) ⊆ B) N R ε K :=
      GM.p412i_RK_congr hεR hfin fun z hz r _ hrρ =>
        ⟨And.left, fun h' => ⟨h', ball_subset_closedBall.trans
          ((GM.p412i_ball_subset_enbhd hfin hz hrρ).trans H)⟩⟩
    rw [heq]; exact H

/-! ## Locality of the events `E_r(z)` modulo constants -/

section Loc
variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
  {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

/-- **C:1150–1154, 1260 mod constants**: `E_r(z) ∩ {B_{5r}(z) ⊆ B}` is a.s. an event of
`σ(B, h|_B) mod const` -/
theorem t39k_confE_ball_ae (hD : IsWeakLQGMetric γ D c) (hh : IsWholePlaneGFF h P)
    (p : CONFParams) {r : ℝ} (hr : 0 < r) (z : ℂ) {B : Ω → Set ℂ} (hBc : ∀ ω, IsClosed (B ω))
    (hBb : ∀ᵐ ω ∂P, Bornology.IsBounded (B ω) ∨ B ω = univ) :
    AEEventIn P (localSigma0 h B)
      (confE (xiGamma γ) c D P h p r z ∩ {ω | ball z (5 * r) ⊆ B ω}) := by
  have hE : AEEventIn P (fieldSigma0On h (ball z (5 * r))) (confE (xiGamma γ) c D P h p r z) := by
    unfold confE
    refine conf21_ae_iInter fun T => ?_
    by_cases hT : ∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))
    swap
    · have e : (⋂ (_ : ∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))),
          confEU (xiGamma γ) c D P h p r z T) = univ := by
        ext ω; simp only [mem_iInter, mem_univ, iff_true]; exact fun h' => absurd h' hT
      rw [e]; exact ⟨univ, MeasurableSet.univ, EventuallyEq.rfl⟩
    have e : (⋂ (_ : ∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))),
        confEU (xiGamma γ) c D P h p r z T) = confEU (xiGamma γ) c D P h p r z T := by
      ext ω; simp only [mem_iInter]; exact ⟨fun h' => h' hT, fun h' _ => h'⟩
    rw [e]
    exact conf36_aeEventIn_fieldSigma0On_of_norm hh hr le_rfl (conf36_sphere_sub_ball hr)
      (conf36_confEU_ball hD hh p hr z T)
  exact conf36_local_ae h hBc hBb isOpen_ball hE

end Loc

/-! ## The main result -/

section Main
variable [mΩ : MeasurableSpace Ω]

omit mΩ in
theorem t39k_filledBallE_ofReal (d : ContMetric) (z₀ : ℂ) (s : ℝ) :
    filledBallE d z₀ (ENNReal.ofReal s) = filledBall d z₀ s := by
  simp only [filledBallE, ENNReal.ofReal_ne_top, ↓reduceIte, ENNReal.toReal_ofReal']
  rcases le_or_gt s 0 with hs | hs
  · rw [max_eq_right hs, t39j6_filledBall_nonpos d z₀ le_rfl, t39j6_filledBall_nonpos d z₀ hs]
  · rw [max_eq_left hs.le]

/-- **CONF C:1300–1302 at a random base, modulo constants (D130 §4, L1)**: if `s` is an a.s.
stopping time of the mod-constant filled-ball filtration and `ε ∈ {2^{-j}}` is (a.s.)
`σ(𝓑^•_s, h|_{𝓑^•_s} mod const)`-measurable, then `σ^ε_{s,𝕣}` (as a real radius; it is a.s.
finite by CONF L3.5, `t39j6_confSigma_ae_ne_top`) is again such an a.s. stopping time. -/
theorem t39k_confSigma_ae0 (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {p : CONFParams}
    (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z₀ : ℂ) {R : ℝ} (hR : 0 < R)
    {s : Ω → ℝ} (hs : IsFilledBallStoppingTimeAE0 P D h z₀ s)
    {ε : Ω → ℝ} (hεv : ∀ ω, ∃ j : ℕ, ε ω = (2 : ℝ)⁻¹ ^ j)
    (hεm : ∃ g : Ω → ℝ, Measurable[filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s ω))] g ∧
      ε =ᵐ[P] g) :
    IsFilledBallStoppingTimeAE0 P D h z₀
      (fun ω => (confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (s ω) ω).toReal) := by
  intro t
  have hlen := GM.ae_mem_lenSet h38 hγ hγ2 hD P h hh
  set K : Ω → Set ℂ := fun ω => filledBall (D (h ω)) z₀ (s ω) with hKdef
  rcases le_or_gt t 0 with ht | ht
  · refine ⟨∅, @MeasurableSet.empty Ω (t39kF0 D h z₀ t), Eventually.of_forall fun ω => ?_⟩
    show (ω ∈ {ω | (confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (s ω) ω).toReal < t}) =
      (ω ∈ (∅ : Set Ω))
    simp only [mem_ofPred_eq, mem_empty_iff_false, eq_iff_iff, iff_false, not_lt]
    exact ht.trans ENNReal.toReal_nonneg
  have hpiece : ∀ q : ℝ, q < t → ∀ j : ℕ, AEEventIn P (t39kF0 D h z₀ t)
      ({ω | s ω < q} ∩ ({ω | ε ω = (2 : ℝ)⁻¹ ^ j} ∩ {ω | enbhd (confRK (xiGamma γ) c D P h p R
        ((2 : ℝ)⁻¹ ^ j) (K ω) ω) (K ω) ⊆ filledBall (D (h ω)) z₀ q})) := by
    intro q hq j
    set B : Ω → Set ℂ := fun ω => filledBall (D (h ω)) z₀ q with hBdef
    have hBc : ∀ ω, IsClosed (B ω) := fun ω => GM.gm_filledBall_isClosed _ _ _
    have hBb : ∀ᵐ ω ∂P, Bornology.IsBounded (B ω) ∨ B ω = univ :=
      hlen.mono fun ω hω => Or.inl (GM.gm_filledBall_isBounded_of_lenSet hω z₀ q)
    have hBF : localSigma0 h B ≤ t39kF0 D h z₀ t := t39k_local_le_F0 D h z₀ hq.le
    have hset := t39k_setSigma_le_trAE hlen hs hq
    have hloc := t39k_localSigma0_le_trAE hlen hs hq
    have hC : AEEventIn P (t39kF0 D h z₀ t) {ω | s ω < q} :=
      t39k_aeEventIn_mono (t39k_F0_mono D h z₀ hq.le) (hs q)
    rw [inter_comm]
    refine t39k_aeEventIn_of_trAE hC (MeasurableSet.inter ?_ ?_)
    · -- `{ε = 2^{-j}}`
      obtain ⟨g, hg, hεg⟩ := hεm
      have e : filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s ω)) = localSigma0 h K := by
        unfold filledBallSigmaAt0; congr 1; funext ω; exact t39k_filledBallE_ofReal _ _ _
      rw [e] at hg
      refine t39k_trAE_congr_on (hloc _ (hg (measurableSet_singleton ((2 : ℝ)⁻¹ ^ j)))) ?_
      filter_upwards [hεg] with ω hω _
      simp only [mem_preimage, mem_singleton_iff, hω]
    · -- `{B_{R^ε(K)}(K) ⊆ 𝓑^•_q}`
      set 𝔢 : ℝ := (2 : ℝ)⁻¹ ^ j with h𝔢def
      have h𝔢 : 0 < 𝔢 * R := mul_pos (pow_pos (by norm_num) j) hR
      set E' : Ω → ℝ → ℂ → Prop := fun ω r z =>
        ω ∈ confE (xiGamma γ) c D P h p r z ∧ ball z (5 * r) ⊆ B ω with hE'def
      have hE' : ∀ r : ℝ, 0 < r → ∀ z : ℂ,
          MeasurableSet[t39jTrAE P (t39kF0 D h z₀ t) {ω | s ω < q}] {ω | E' ω r z} := by
        intro r hr z
        have e : {ω | E' ω r z} = confE (xiGamma γ) c D P h p r z ∩ {ω | ball z (5 * r) ⊆ B ω} :=
          rfl
        rw [e]
        exact t39k_trAE_of_ae (t39k_aeEventIn_mono hBF (t39k_confE_ball_ae hD hh p hr z hBc hBb))
      have hK : ∀ U : Set ℂ, IsOpen U →
          MeasurableSet[t39jTrAE P (t39kF0 D h z₀ t) {ω | s ω < q}]
            {ω | (K ω ∩ U).Nonempty} := fun U hU => hset _ (GM.gm_setSigma_hit_open K hU)
      have hB : ∀ x : ℂ,
          MeasurableSet[t39jTrAE P (t39kF0 D h z₀ t) {ω | s ω < q}] {ω | x ∈ B ω} := by
        intro x
        have e : {ω | x ∈ B ω} = {ω | (B ω ∩ {x}).Nonempty} := by
          ext ω; simp only [mem_ofPred_eq, inter_singleton_nonempty]
        rw [e]
        exact t39k_trAE_of_meas (hBF _ (confD110_setSigma_le_localSigma0 h B _
          (GM.gm_setSigma_hit_closed hBc isClosed_singleton)))
      have hρ := t39k_measurable_RK (M := t39jTrAE P (t39kF0 D h z₀ t) {ω | s ω < q}) E' K
        (confN p 𝔢) (R := R) (ε := 𝔢)
        (fun k a b => hE' _ (mul_pos (zpow_pos (by norm_num) k) h𝔢) _) hK
      refine t39k_trAE_congr_on (t39k_measurableSet_enbhd hρ K B hBc hK hB) ?_
      filter_upwards [hlen] with ω hω _
      show enbhd (confRK (xiGamma γ) c D P h p R 𝔢 (K ω) ω) (K ω) ⊆ B ω ↔
        enbhd (GM.p412iRK (E' ω) (confN p 𝔢) R 𝔢 (K ω)) (K ω) ⊆ B ω
      rw [GM.p412i_confRK_eq]
      exact t39k_enbhd_iff h𝔢 (GM.gm_filledBall_isBounded_of_lenSet hω z₀ q)
  have hG : AEEventIn P (t39kF0 D h z₀ t) (⋃ (q : {q : ℚ // (q : ℝ) < t}), ⋃ j : ℕ,
      ({ω | s ω < ((q : ℚ) : ℝ)} ∩ ({ω | ε ω = (2 : ℝ)⁻¹ ^ j} ∩ {ω | enbhd (confRK (xiGamma γ) c D P h p R
        ((2 : ℝ)⁻¹ ^ j) (K ω) ω) (K ω) ⊆ filledBall (D (h ω)) z₀ ((q : ℚ) : ℝ)}))) :=
    conf21_ae_iUnion fun q => conf21_ae_iUnion fun j => hpiece q q.2 j
  obtain ⟨F, hF, hGF⟩ := hG
  refine ⟨F, hF, EventuallyEq.trans ?_ hGF⟩
  filter_upwards [t39j6_confSigma_ae_ne_top h38 hγ hγ2 hD H35 hη hh z₀ hR] with ω hω
  obtain ⟨j₀, hj₀⟩ := hεv ω
  have hne : confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (s ω) ω ≠ ⊤ := by
    rw [hj₀]; exact hω j₀ (s ω)
  show (ω ∈ {ω | (confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (s ω) ω).toReal < t}) =
    (ω ∈ ⋃ (q : {q : ℚ // (q : ℝ) < t}), ⋃ j : ℕ,
      ({ω | s ω < ((q : ℚ) : ℝ)} ∩ ({ω | ε ω = (2 : ℝ)⁻¹ ^ j} ∩ {ω | enbhd (confRK (xiGamma γ) c D P h p R
        ((2 : ℝ)⁻¹ ^ j) (K ω) ω) (K ω) ⊆ filledBall (D (h ω)) z₀ ((q : ℚ) : ℝ)})))
  apply propext
  simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
  rw [← ENNReal.lt_ofReal_iff_toReal_lt hne]
  constructor
  · intro hlt
    unfold confSigma at hlt
    obtain ⟨s', hlt⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hss', hlt⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hsub, hlt⟩ := iInf_lt_iff.1 hlt
    have hs't : s' < t := (ENNReal.ofReal_lt_ofReal_iff ht).1 hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hs't
    refine ⟨⟨q, hq2⟩, j₀, hss'.trans hq1, hj₀, ?_⟩
    rw [← hj₀]
    exact hsub.trans (GM.gm_filledBall_mono _ _ hq1.le)
  · rintro ⟨⟨q, hq⟩, j, hsq, hj, hsub⟩
    rw [← hj] at hsub
    unfold confSigma
    exact (iInf_le_of_le (q : ℝ) (iInf_le_of_le hsq (iInf_le_of_le hsub le_rfl))).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff ht).2 hq)

end Main

end LQGMetric.CONF
