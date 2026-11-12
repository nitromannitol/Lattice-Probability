/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J10 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_1C
import LatticeProb.Bonanno.LQGMetric.Blueprint.StoppingAE

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.1 for almost sure stopping times (DEC-120 §6 J6, D110 P6 `GM.FilledBallLocalSet`)

Source: CONF = Gwynne–Miller, arXiv:1905.00381, `confluence-final.tex`, Lemma 2.1
(`lem-ball-local`, C:476–479), proof C:481–490; the radii of (3.17) are stopping times only a.s.
(C:1302, GM l. 2189, D120 §3, `IsFilledBallStoppingTimeAE`).

* `t39j10_isLocalSetDet_genAE`: copy of `conf21_isLocalSetDet_gen` (L2_1B) for a.s. stopping
  times: the dyadic events `{⌊2^n τ⌋ = k}` are replaced by their `𝓕_{(k+1)2^{-n}}`-versions
  `G_{(k+1)2^{-n}} ∖ G_{k2^{-n}}`, which changes `{𝒜_{(k+1)2^{-n}} ⊆ U} ∩ {⌊2^n τ⌋ = k}` only on a
  null set; the limit step is pointwise;
* **`confLem2_1_filled_ofAE`**: CONF Lemma 2.1 (filled balls, raw `IsLocalSetDet`, D32) for
  `IsFilledBallStoppingTimeAE` with `τ > 0` a.s. (copy of `confLem2_1_filled_of`, L2_1C).
-/

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF
open GM LocalEvent

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **CONF Lemma 2.1, generic form, for almost sure stopping times** (copy of
`conf21_isLocalSetDet_gen`, L2_1B, P2-CONF21, with `{τ < t}` only a.s. in `𝓕_t`): for a ball family `𝒜` (closed, bounded on `lenSet`,
monotone, hit-measurable, internally determined, right-continuous at `t > 0`) and a stopping
time `τ > 0` (a.s.) of its filtration, `𝒜(D_h, τ)` is a local set (D32). -/
theorem t39j10_isLocalSetDet_genAE {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hlen : ∀ᵐ ω ∂P, D (h ω) ∈ lenSet) (𝒜 : ContMetric → ℝ → Set ℂ)
    (hb : ∀ d ∈ lenSet, ∀ s, Bornology.IsBounded (𝒜 d s)) (hc : ∀ d s, IsClosed (𝒜 d s))
    (hhit : ∀ s V, IsOpen V → MeasurableSet {d | (𝒜 d s ∩ V).Nonempty})
    (hsat : ∀ (d₁ d₂ : ContMetric) (s : ℝ) (U : Set ℂ), IsOpen U → d₁ ∈ lenSet → d₂ ∈ lenSet →
      d₁.internal U = d₂.internal U → 𝒜 d₁ s ⊆ U → 𝒜 d₂ s ⊆ U)
    (hmono : ∀ d s t, s ≤ t → 𝒜 d s ⊆ 𝒜 d t)
    (hrc : ∀ d ∈ lenSet, ∀ t : ℝ, 0 < t → ∀ U : Set ℂ, IsOpen U → 𝒜 d t ⊆ U →
      ∃ ε > 0, 𝒜 d (t + ε) ⊆ U)
    (τ : Ω → ℝ) (hτ : ∀ t : ℝ, AEEventIn P (⨆ (s : ℝ) (_ : s ≤ t),
      localSigma h (fun ω => 𝒜 (D (h ω)) s)) {ω | τ ω < t})
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) : IsLocalSetDet P h (fun ω => 𝒜 (D (h ω)) (τ ω)) := by
  intro U'
  set U : Set ℂ := (U' : Set ℂ) with hUdef
  have hU : IsOpen U := U'.isOpen
  show AEEventIn P (fieldSigma h (toOpens U hU)) _
  let Fs : ℝ → MeasurableSpace Ω := fun t =>
    ⨆ (s : ℝ) (_ : s ≤ t), localSigma h (fun ω => 𝒜 (D (h ω)) s)
  have hFmono : ∀ {t t' : ℝ}, t ≤ t' → Fs t ≤ Fs t' := fun htt' =>
    iSup₂_le fun s hs => le_iSup₂ (f := fun s (_ : s ≤ _) =>
      localSigma h (fun ω => 𝒜 (D (h ω)) s)) s (hs.trans htt')
  have hfl : ∀ (n : ℕ) (k : ℤ), {ω | ⌊(2 : ℝ) ^ n * τ ω⌋ = k} =
      {ω | τ ω < ((k : ℝ) + 1) / 2 ^ n} ∩ {ω | τ ω < (k : ℝ) / 2 ^ n}ᶜ := by
    intro n k
    ext ω
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, not_lt, Int.floor_eq_iff,
      lt_div_iff₀ hp, div_le_iff₀ hp]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  set τn : ℕ → Ω → ℝ := fun n ω => ((⌊(2 : ℝ) ^ n * τ ω⌋ : ℝ) + 1) / 2 ^ n with hτn
  have hEn : ∀ n : ℕ, AEEventIn P (fieldSigma h (toOpens U hU))
      {ω | 𝒜 (D (h ω)) (τn n ω) ⊆ U} := by
    intro n
    have e : {ω | 𝒜 (D (h ω)) (τn n ω) ⊆ U} = ⋃ k : ℤ,
        ({ω | 𝒜 (D (h ω)) (((k : ℝ) + 1) / 2 ^ n) ⊆ U} ∩ {ω | ⌊(2 : ℝ) ^ n * τ ω⌋ = k}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, hτn]
      exact ⟨fun H => ⟨_, H, rfl⟩, fun ⟨k, H, hk⟩ => by rw [hk]; exact H⟩
    rw [e]
    refine conf21_ae_iUnion fun k => ?_
    obtain ⟨G₁, hG₁, he₁⟩ := hτ (((k : ℝ) + 1) / 2 ^ n)
    obtain ⟨G₀, hG₀, he₀⟩ := hτ ((k : ℝ) / 2 ^ n)
    have hk : (k : ℝ) / 2 ^ n ≤ ((k : ℝ) + 1) / 2 ^ n :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hG : MeasurableSet[Fs (((k : ℝ) + 1) / 2 ^ n)] (G₁ ∩ G₀ᶜ) :=
      hG₁.inter (MeasurableSet.compl (hFmono hk _ hG₀))
    obtain ⟨F, hF, hEF⟩ := conf21_trace_stop hD hh hlen 𝒜 hb hc hhit hsat hmono _ U hU hG
    refine ⟨F, hF, EventuallyEq.trans ?_ hEF⟩
    rw [hfl]
    exact Filter.EventuallyEq.inter (Filter.EventuallyEq.refl _ _) (he₁.inter he₀.compl)
  have hae : {ω | 𝒜 (D (h ω)) (τ ω) ⊆ U} =ᵐ[P] ⋃ n : ℕ, {ω | 𝒜 (D (h ω)) (τn n ω) ⊆ U} := by
    filter_upwards [hlen, hpos] with ω hω hτω
    refine propext ⟨fun H => ?_, fun H => ?_⟩
    · obtain ⟨ε, hε, hεU⟩ := hrc _ hω _ hτω U hU H
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (show (1 / 2 : ℝ) < 1 by norm_num)
      refine mem_iUnion.2 ⟨n, (hmono _ _ _ ?_).trans hεU⟩
      have hp : (0 : ℝ) < 2 ^ n := by positivity
      show ((⌊(2 : ℝ) ^ n * τ ω⌋ : ℝ) + 1) / 2 ^ n ≤ τ ω + ε
      rw [div_le_iff₀ hp]
      have h1 := Int.floor_le ((2 : ℝ) ^ n * τ ω)
      have h2 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
      have h3 : 1 < ε * 2 ^ n := by
        have := mul_lt_mul_of_pos_right hn hp
        rwa [h2] at this
      have h4 : (2 : ℝ) ^ n * τ ω = τ ω * 2 ^ n := mul_comm _ _
      rw [add_mul]
      linarith
    · obtain ⟨n, hn⟩ := mem_iUnion.1 H
      refine (hmono _ _ _ ?_).trans hn
      have hp : (0 : ℝ) < 2 ^ n := by positivity
      show τ ω ≤ ((⌊(2 : ℝ) ^ n * τ ω⌋ : ℝ) + 1) / 2 ^ n
      rw [le_div_iff₀ hp]
      have := Int.lt_floor_add_one ((2 : ℝ) ^ n * τ ω)
      have h4 : (2 : ℝ) ^ n * τ ω = τ ω * 2 ^ n := mul_comm _ _
      linarith
  obtain ⟨F, hF, hEF⟩ := conf21_ae_iUnion hEn
  exact ⟨F, hF, hae.trans hEF⟩

/-- **CONF Lemma 2.1, filled balls, almost sure stopping times** (C:478) -/
theorem confLem2_1_filled_ofAE (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (z₀ : ℂ) (τ : Ω → ℝ) (hτ : IsFilledBallStoppingTimeAE P D h z₀ τ)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) :
    IsLocalSetDet P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) :=
  t39j10_isLocalSetDet_genAE hD hh (ae_mem_lenSet h38 hγ hγ2 hD P h hh)
    (fun d s => filledBall d z₀ s) (fun d hd s => gm_filledBall_isBounded_of_lenSet hd z₀ s)
    (fun d s => gm_filledBall_isClosed d z₀ s) (fun s V hV => conf21_hit_filled z₀ s V hV)
    (fun d₁ d₂ s U hU h1 h2 he hB => conf21_sat_filled d₁ d₂ z₀ s U hU h1 h2 he hB)
    (fun d _ _ hst => gm_filledBall_mono d z₀ hst)
    (fun _ hd _ ht _ hU hK => conf21_rc_filled hd z₀ ht hU hK) τ hτ hpos

end LQGMetric.CONF
