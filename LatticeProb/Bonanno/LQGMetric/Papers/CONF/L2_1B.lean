/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L2_1B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_1A

/-!
# CONF Lemma 2.1, part B: stopping times (task P2-CONF21)

Source: CONF = Gwynne–Miller, arXiv:1905.00381, `confluence-final.tex`, Lemma 2.1
(`lem-ball-local`, C:476–479), proof C:481–490: deterministic radii (part A), then "the case of
stopping times which take on only countably many possible values is immediate from the case of
deterministic times. The case of general stopping times follows from the standard strong Markov
property argument (i.e., look at the times `2^{-n}⌈2^n τ⌉` and send `n → ∞`) and the fact that
local sets behave well under limits" (C:483, C:490). Local sets in the determined form of
decision D32 (`IsLocalSetDet`, CONF C:472–473).

* `conf21_trace_local`: for a closed, a.s. bounded random set `A` which is local (D32), and
  `G ∈ σ(A, h|_A)`, the event `{A ⊆ U} ∩ G` is a.s. a `σ(h|_U)`-event (the generators of each
  hull level `hullSigma h A n`, on `{A ⊆ O_n}` with `O_n ⊆ U` the points `2^{1-n}`-inside `U`);
* `conf21_trace_stop`: the same for `G` in the ball filtration `𝓕_s`, at `{𝒜_s ⊆ U}`
  ("immediate from the case of deterministic times");
* `conf21_isLocalSetDet_gen`: the dyadic times `τ_n = 2^{-n}(⌊2^n τ⌋ + 1)` (optional-time form
  of `2^{-n}⌈2^n τ⌉`), `{𝒜_{τ_n} ⊆ U} = ⋃_k {τ_n = (k+1)2^{-n}} ∩ {𝒜_{(k+1)2^{-n}} ⊆ U}`, and the
  limit `n → ∞` by right-continuity of the balls (part A) in place of [QLE, Lemma 6.8];
* **`confLem2_1Pos_of`**: CONF Lemma 2.1 (both halves) for stopping times with `τ > 0` a.s.,
  from DFGPS Lemma 3.8 (bounded compactness of `D_h`, needed for compact balls).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF
open GM LocalEvent

section Tr
variable {Ω : Type} {m0 : MeasurableSpace Ω} {P : Measure[m0] Ω}

lemma conf21_ae_iUnion {ι : Type} [Countable ι] {m : MeasurableSpace Ω} {E : ι → Set Ω}
    (hE : ∀ i, @AEEventIn Ω m0 P m (E i)) : @AEEventIn Ω m0 P m (⋃ i, E i) := by
  choose F hF hEF using hE
  exact ⟨⋃ i, F i, MeasurableSet.iUnion (m := m) hF, EventuallyEq.countable_iUnion hEF⟩

lemma conf21_ae_iInter {ι : Type} [Countable ι] {m : MeasurableSpace Ω} {E : ι → Set Ω}
    (hE : ∀ i, @AEEventIn Ω m0 P m (E i)) : @AEEventIn Ω m0 P m (⋂ i, E i) := by
  choose F hF hEF using hE
  exact ⟨⋂ i, F i, MeasurableSet.iInter (m := m) hF, EventuallyEq.countable_iInter hEF⟩

lemma conf21_ae_inter {m : MeasurableSpace Ω} {E₁ E₂ : Set Ω} (h₁ : @AEEventIn Ω m0 P m E₁)
    (h₂ : @AEEventIn Ω m0 P m E₂) : @AEEventIn Ω m0 P m (E₁ ∩ E₂) := by
  obtain ⟨F₁, hF₁, he₁⟩ := h₁
  obtain ⟨F₂, hF₂, he₂⟩ := h₂
  exact ⟨F₁ ∩ F₂, MeasurableSet.inter (m := m) hF₁ hF₂, he₁.inter he₂⟩

/-- the events `G` with `E ∩ G` a.s. in `m` (for `E` a.s. in `m`) form a σ-algebra -/
def conf21Tr (P : Measure[m0] Ω) (m : MeasurableSpace Ω) (E : Set Ω) (hE : @AEEventIn Ω m0 P m E) :
    MeasurableSpace Ω where
  MeasurableSet' G := @AEEventIn Ω m0 P m (E ∩ G)
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ m, by rw [inter_empty]⟩
  measurableSet_compl G hG := by
    obtain ⟨F, hF, hEF⟩ := hG
    obtain ⟨F₀, hF₀, hE₀⟩ := hE
    have e : E ∩ Gᶜ = E ∩ (E ∩ G)ᶜ := by
      ext ω; simp only [mem_inter_iff, mem_compl_iff]; tauto
    refine ⟨F₀ ∩ Fᶜ, MeasurableSet.inter (m := m) hF₀ (MeasurableSet.compl (m := m) hF), ?_⟩
    rw [e]
    exact hE₀.inter hEF.compl
  measurableSet_iUnion f hf := by
    rw [inter_iUnion]
    exact conf21_ae_iUnion hf

end Tr

/-- two points of a level-`n` dyadic square are at distance `≤ 2 · 2^{-n}` -/
lemma conf21_sq_dist {n : ℕ} {k : ℤ × ℤ} {x y : ℂ} (hx : x ∈ dyadicSq n k)
    (hy : y ∈ dyadicSq n k) : dist x y ≤ 2 / 2 ^ n := by
  obtain ⟨a1, a2, a3, a4⟩ := hx
  obtain ⟨b1, b2, b3, b4⟩ := hy
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e : ((k.1 : ℝ) + 1) / 2 ^ n = k.1 / 2 ^ n + 1 / 2 ^ n := by ring
  have e' : ((k.2 : ℝ) + 1) / 2 ^ n = k.2 / 2 ^ n + 1 / 2 ^ n := by ring
  rw [Complex.sub_re, Complex.sub_im]
  have h1 : |x.re - y.re| ≤ 1 / 2 ^ n := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have h2 : |x.im - y.im| ≤ 1 / 2 ^ n := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have : (2 : ℝ) / 2 ^ n = 1 / 2 ^ n + 1 / 2 ^ n := by ring
  linarith

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- **trace of `σ(A, h|_A)` on `{A ⊆ U}`**: for a closed, a.s. bounded local set `A` (D32) and
`G ∈ σ(A, h|_A)`, `{A ⊆ U} ∩ G` is a.s. an event of `σ(h|_U)` -/
theorem conf21_trace_local (h : Ω → DistC) {A : Ω → Set ℂ} (hAc : ∀ ω, IsClosed (A ω))
    (hAb : ∀ᵐ ω ∂P, Bornology.IsBounded (A ω))
    (hloc : ∀ (V : Set ℂ) (hV : IsOpen V),
      AEEventIn P (fieldSigma h (toOpens V hV)) {ω | A ω ⊆ V})
    {U : Set ℂ} (hU : IsOpen U) {G : Set Ω} (hG : MeasurableSet[localSigma h A] G) :
    AEEventIn P (fieldSigma h (toOpens U hU)) ({ω | A ω ⊆ U} ∩ G) := by
  let O : ℕ → Set ℂ := fun n => interior {x | closedBall x (2 / 2 ^ n) ⊆ U}
  have hOo : ∀ n, IsOpen (O n) := fun n => isOpen_interior
  have hOU : ∀ n, O n ⊆ U := fun n x hx =>
    (interior_subset hx : closedBall x _ ⊆ U) (mem_closedBall_self (by positivity))
  have hmono : ∀ {V : Set ℂ} (hV : IsOpen V), V ⊆ U → fieldSigma h (toOpens V hV) ≤ fieldSigma h (toOpens U hU) :=
    fun hV hVU => GM.fieldSigma_mono h (V := toOpens _ hV) (W := toOpens U hU) hVU
  have hlocU : ∀ {V : Set ℂ} (hV : IsOpen V), V ⊆ U → AEEventIn P (fieldSigma h (toOpens U hU)) {ω | A ω ⊆ V} :=
    fun hV hVU => by
      obtain ⟨F, hF, hEF⟩ := hloc _ hV
      exact ⟨F, hmono hV hVU _ hF, hEF⟩
  let En : ℕ → Set Ω := fun n => {ω | A ω ⊆ O n}
  have hEn : ∀ n, AEEventIn P (fieldSigma h (toOpens U hU)) (En n) := fun n => hlocU (hOo n) (hOU n)
  have key : ∀ n, hullSigma h A n ≤ conf21Tr P (fieldSigma h (toOpens U hU)) (En n) (hEn n) := by
    intro n
    have hset : setSigma A ≤ conf21Tr P (fieldSigma h (toOpens U hU)) (En n) (hEn n) := by
      refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨V, hV, rfl⟩
      have hc : MeasurableSet[conf21Tr P (fieldSigma h (toOpens U hU)) (En n) (hEn n)] {ω | (A ω ∩ V).Nonempty}ᶜ := by
        obtain ⟨F, hFc, hFV, hFU, -⟩ := hV.exists_iUnion_isClosed
        have e : En n ∩ {ω | (A ω ∩ V).Nonempty}ᶜ = ⋂ j, {ω | A ω ⊆ O n ∩ (F j)ᶜ} := by
          ext ω
          simp only [En, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, mem_iInter,
            subset_inter_iff, not_nonempty_iff_eq_empty]
          constructor
          · rintro ⟨h1, h2⟩ j
            refine ⟨h1, fun x hx hxF => ?_⟩
            have : x ∈ A ω ∩ V := ⟨hx, hFV j hxF⟩
            rw [h2] at this
            exact this
          · intro H
            refine ⟨(H 0).1, eq_empty_iff_forall_notMem.2 fun x ⟨hx, hxV⟩ => ?_⟩
            rw [← hFU, mem_iUnion] at hxV
            obtain ⟨j, hj⟩ := hxV
            exact (H j).2 hx hj
        show AEEventIn P (fieldSigma h (toOpens U hU)) (En n ∩ _)
        rw [e]
        exact conf21_ae_iInter fun j =>
          hlocU ((hOo n).inter (hFc j).isOpen_compl) (inter_subset_left.trans (hOU n))
      simpa only [compl_compl] using hc.compl
    have hgen : MeasurableSpace.generateFrom {E | ∃ (S : Set ℂ) (F : Set Ω),
        MeasurableSet[fieldSigma h (toOpens (interior S) isOpen_interior)] F ∧
          E = {ω | dyadicHull n (A ω) = S} ∩ F} ≤ conf21Tr P (fieldSigma h (toOpens U hU)) (En n) (hEn n) := by
      refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨S, F, hF, rfl⟩
      show AEEventIn P (fieldSigma h (toOpens U hU)) (En n ∩ ({ω | dyadicHull n (A ω) = S} ∩ F))
      by_cases hSU : S ⊆ U
      · rw [← inter_assoc]
        have h1 : AEEventIn P (fieldSigma h (toOpens U hU)) (En n ∩ {ω | dyadicHull n (A ω) = S}) :=
          hset _ (measurableSet_hull_eq hAc n S)
        have h2 : MeasurableSet[(fieldSigma h (toOpens U hU))] F := hmono isOpen_interior (interior_subset.trans hSU) _ hF
        exact conf21_ae_inter h1 ⟨F, h2, EventuallyEq.rfl⟩
      · have e : En n ∩ ({ω | dyadicHull n (A ω) = S} ∩ F) = ∅ := by
          refine eq_empty_iff_forall_notMem.2 fun ω ⟨hAO, hS, _⟩ => hSU ?_
          have hS' : dyadicHull n (A ω) = S := hS
          rw [← hS']
          intro y hy
          simp only [dyadicHull, mem_iUnion] at hy
          obtain ⟨k, ⟨a, haS, haA⟩, hyk⟩ := hy
          have ha : closedBall a (2 / 2 ^ n) ⊆ U := interior_subset (hAO haA)
          exact ha (by rw [mem_closedBall]; exact conf21_sq_dist hyk haS)
        rw [e]
        exact ⟨∅, @MeasurableSet.empty _ (fieldSigma h (toOpens U hU)), EventuallyEq.rfl⟩
    exact sup_le hset hgen
  have hGn : ∀ n, MeasurableSet[hullSigma h A n] G := fun n =>
    MeasurableSpace.measurableSet_iInf.1 hG n
  have hae : ({ω | A ω ⊆ U} ∩ G) =ᵐ[P] ⋃ n, (En n ∩ G) := by
    filter_upwards [hAb] with ω hb
    refine propext ⟨fun ⟨hAU, hGω⟩ => ?_, fun hω => ?_⟩
    · have hK := isCompact_of_isClosed_isBounded (hAc ω) hb
      obtain ⟨δ, hδ, hδA⟩ := hK.exists_thickening_subset_open hU hAU
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 4 by positivity)
        (show (1 / 2 : ℝ) < 1 by norm_num)
      have h3 : (2 : ℝ) / 2 ^ n = 2 * (1 / 2) ^ n := by rw [one_div_pow, mul_one_div]
      refine mem_iUnion.2 ⟨n, ?_, hGω⟩
      intro x hx
      refine mem_interior.2 ⟨ball x (δ / 2), fun y hy w hw =>
        hδA (mem_thickening_iff.2 ⟨x, hx, ?_⟩), isOpen_ball, mem_ball_self (by positivity)⟩
      have h1 := mem_ball.1 hy
      have h2 := mem_closedBall.1 hw
      linarith [dist_triangle w y x]
    · obtain ⟨n, hAO, hGω⟩ := mem_iUnion.1 hω
      exact ⟨fun x hx => hOU n (hAO hx), hGω⟩
  obtain ⟨F, hF, hEF⟩ := conf21_ae_iUnion (m := fieldSigma h (toOpens U hU)) fun n => key n G (hGn n)
  exact ⟨F, hF, hae.trans hEF⟩

variable [IsProbabilityMeasure P]

/-- **countably-valued step** (CONF C:483/490 "immediate from the case of deterministic
times"): for `G` in the ball filtration `𝓕_s`, `{𝒜_s ⊆ U} ∩ G` is a.s. a `σ(h|_U)`-event -/
theorem conf21_trace_stop {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hlen : ∀ᵐ ω ∂P, D (h ω) ∈ lenSet) (𝒜 : ContMetric → ℝ → Set ℂ)
    (hb : ∀ d ∈ lenSet, ∀ s, Bornology.IsBounded (𝒜 d s)) (hc : ∀ d s, IsClosed (𝒜 d s))
    (hhit : ∀ s V, IsOpen V → MeasurableSet {d | (𝒜 d s ∩ V).Nonempty})
    (hsat : ∀ (d₁ d₂ : ContMetric) (s : ℝ) (U : Set ℂ), IsOpen U → d₁ ∈ lenSet → d₂ ∈ lenSet →
      d₁.internal U = d₂.internal U → 𝒜 d₁ s ⊆ U → 𝒜 d₂ s ⊆ U)
    (hmono : ∀ d s t, s ≤ t → 𝒜 d s ⊆ 𝒜 d t) (s : ℝ) (U : Set ℂ) (hU : IsOpen U) {G : Set Ω}
    (hG : MeasurableSet[⨆ (r : ℝ) (_ : r ≤ s), localSigma h (fun ω => 𝒜 (D (h ω)) r)] G) :
    AEEventIn P (fieldSigma h (toOpens U hU)) ({ω | 𝒜 (D (h ω)) s ⊆ U} ∩ G) := by
  have hE := conf21_aeEventIn_det hD hh hlen 𝒜 hb hc hhit hsat s U hU
  have hle : (⨆ (r : ℝ) (_ : r ≤ s), localSigma h (fun ω => 𝒜 (D (h ω)) r)) ≤
      conf21Tr P _ _ hE := by
    refine iSup₂_le fun r hr G hG => ?_
    have hT := conf21_trace_local h (A := fun ω => 𝒜 (D (h ω)) r) (fun ω => hc _ _)
      (by filter_upwards [hlen] with ω hω; exact hb _ hω r)
      (fun V hV => conf21_aeEventIn_det hD hh hlen 𝒜 hb hc hhit hsat r V hV) hU hG
    have e : {ω | 𝒜 (D (h ω)) s ⊆ U} ∩ G =
        {ω | 𝒜 (D (h ω)) s ⊆ U} ∩ ({ω | 𝒜 (D (h ω)) r ⊆ U} ∩ G) := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (hmono _ _ _ hr).trans h1, h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
    show AEEventIn _ _ _
    rw [e]
    exact conf21_ae_inter hE hT
  exact hle G hG

/-- **CONF Lemma 2.1, generic form**: for a ball family `𝒜` (closed, bounded on `lenSet`,
monotone, hit-measurable, internally determined, right-continuous at `t > 0`) and a stopping
time `τ > 0` (a.s.) of its filtration, `𝒜(D_h, τ)` is a local set (D32). -/
theorem conf21_isLocalSetDet_gen {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hlen : ∀ᵐ ω ∂P, D (h ω) ∈ lenSet) (𝒜 : ContMetric → ℝ → Set ℂ)
    (hb : ∀ d ∈ lenSet, ∀ s, Bornology.IsBounded (𝒜 d s)) (hc : ∀ d s, IsClosed (𝒜 d s))
    (hhit : ∀ s V, IsOpen V → MeasurableSet {d | (𝒜 d s ∩ V).Nonempty})
    (hsat : ∀ (d₁ d₂ : ContMetric) (s : ℝ) (U : Set ℂ), IsOpen U → d₁ ∈ lenSet → d₂ ∈ lenSet →
      d₁.internal U = d₂.internal U → 𝒜 d₁ s ⊆ U → 𝒜 d₂ s ⊆ U)
    (hmono : ∀ d s t, s ≤ t → 𝒜 d s ⊆ 𝒜 d t)
    (hrc : ∀ d ∈ lenSet, ∀ t : ℝ, 0 < t → ∀ U : Set ℂ, IsOpen U → 𝒜 d t ⊆ U →
      ∃ ε > 0, 𝒜 d (t + ε) ⊆ U)
    (τ : Ω → ℝ) (hτ : ∀ t : ℝ, MeasurableSet[⨆ (s : ℝ) (_ : s ≤ t),
      localSigma h (fun ω => 𝒜 (D (h ω)) s)] {ω | τ ω < t})
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
    refine conf21_ae_iUnion fun k =>
      conf21_trace_stop hD hh hlen 𝒜 hb hc hhit hsat hmono _ U hU ?_
    rw [hfl]
    have hk : (k : ℝ) / 2 ^ n ≤ ((k : ℝ) + 1) / 2 ^ n :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    exact (hτ _).inter (MeasurableSet.compl (hFmono hk _ (hτ _)))
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

end LQGMetric.CONF
