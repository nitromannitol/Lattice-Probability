/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1Filt at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepShift
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepAsm1

/-!
# LM Lemma 3.2 and (3.9): the filtration `𝓕_{r_k}`

Source: LM = Gwynne–Miller, *Local metrics of the Gaussian free field*, arXiv:1905.00379,
`literature/src/1905.00379/local-metrics-final.tex`, Lemma 3.2 (`lem-outside-filtration`,
l. 604–612) and l. 731–734 ((3.9): `E_{r_k} ∈ 𝓕_{s₁r_k} ⊂ 𝓕_{r_{k+1}}`), `N = 0`.

LM's proof (l. 608–609): `h_{r'}(0) − h_r(0)` is the circle average of `h − h_r(0)` over
`∂B_{r'}(0)`, hence `𝓕_r`-measurable, and `h − h_{r'}(0) = (h − h_r(0)) − (h_{r'}(0) − h_r(0))`.
In Lean the circle average is a pathwise limit (junk `0` where it fails to exist), so the identity
`(h − h_r(0))_{r'}(0) = h_{r'}(0) − h_r(0)` holds only almost surely (`ae_circleAvg_addConst`).
Hence we prove the inclusion modulo null sets (`lmF_ae_sub`), and work with the null-augmented
σ-algebras `augSigma P (lmF h r)` (`lmFiltration`), which form a filtration (Lemma 3.2) and
contain the annulus σ-algebras as in (3.9) (`annSigma_le_lmFiltration`). The liminf over
`ε = 1/(n+1)` that passes from `σ(·|_{B_ε(K)})` to `⋂_ε` is own bookkeeping (DEVIATIONS).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric TopologicalSpace

namespace LQGMetric.LM

open Blueprint

variable {Ω : Type} {m0 : MeasurableSpace Ω}

/-- The `P`-augmentation of `m` inside `m0`: `m0`-measurable sets a.e. equal to an `m`-set. -/
def augSigma (P : @Measure Ω m0) (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet[m0] s ∧ ∃ t, MeasurableSet[m] t ∧ s =ᵐ[P] t
  measurableSet_empty := ⟨@MeasurableSet.empty _ m0, ∅, @MeasurableSet.empty _ m, EventuallyEq.rfl⟩
  measurableSet_compl s hs := by
    obtain ⟨hs, t, ht, hst⟩ := hs
    exact ⟨@MeasurableSet.compl _ _ m0 hs, tᶜ, ht.compl, hst.compl⟩
  measurableSet_iUnion f hf := by
    choose hf t ht hft using hf
    exact ⟨@MeasurableSet.iUnion _ _ m0 _ _ hf, ⋃ i, t i, MeasurableSet.iUnion ht,
      EventuallyEq.countable_iUnion hft⟩

lemma augSigma_le (P : @Measure Ω m0) (m : MeasurableSpace Ω) : augSigma P m ≤ m0 :=
  fun _ hs => hs.1

lemma le_augSigma (P : @Measure Ω m0) {m : MeasurableSpace Ω} (hm : m ≤ m0) : m ≤ augSigma P m :=
  fun s hs => ⟨hm s hs, s, hs, EventuallyEq.rfl⟩

lemma augSigma_mono_of (P : @Measure Ω m0) {m m' : MeasurableSpace Ω}
    (h : ∀ s, MeasurableSet[m] s → ∃ t, MeasurableSet[m'] t ∧ s =ᵐ[P] t) :
    augSigma P m ≤ augSigma P m' := by
  rintro s ⟨hs, t, ht, hst⟩
  obtain ⟨t', ht', htt'⟩ := h t ht
  exact ⟨hs, t', ht', hst.trans htt'⟩

/-- `σ(Y|_V)`-sets are a.e. equal to `σ(Z|_V)`-sets when `Y = Z` a.s. -/
lemma ae_fieldSigma {P : Measure Ω} {Y Z : Ω → DistC} (hYZ : ∀ᵐ ω ∂P, Y ω = Z ω) (V : Opens ℂ)
    {s : Set Ω} (hs : MeasurableSet[fieldSigma Y V] s) :
    ∃ t, MeasurableSet[fieldSigma Z V] t ∧ s =ᵐ[P] t := by
  obtain ⟨S, hS, rfl⟩ := hs
  refine ⟨(fun ω => restrictTo V (Z ω)) ⁻¹' S, ⟨S, hS, rfl⟩, ?_⟩
  filter_upwards [hYZ] with ω hω
  simp [hω]

/-- passing to `σ(·|_K) = ⋂_ε σ(·|_{B_ε(K)})`: if `Y = Z` a.s. and `σ(Z|_{B_ε(K')}) ≤ σ(X|_{B_ε(K)})`
for all `ε > 0`, every `σ(Y|_{K'})`-set is a.e. equal to a `σ(X|_K)`-set (liminf over
`ε = 1/(n+1)`). -/
lemma ae_fieldSigmaClosed {P : Measure Ω} {X Y Z : Ω → DistC} {K K' : Set ℂ}
    (hYZ : ∀ᵐ ω ∂P, Y ω = Z ω)
    (hZ : ∀ ε, 0 < ε → fieldSigma Z (nbhdO ε K') ≤ fieldSigma X (nbhdO ε K)) {s : Set Ω}
    (hs : MeasurableSet[fieldSigmaClosed Y K'] s) :
    ∃ t, MeasurableSet[fieldSigmaClosed X K] t ∧ s =ᵐ[P] t := by
  have hsn : ∀ n : ℕ, MeasurableSet[fieldSigma Y (nbhdO (1 / (n + 1 : ℝ)) K')] s := by
    intro n
    unfold fieldSigmaClosed at hs
    rw [MeasurableSpace.measurableSet_iInf] at hs
    have := hs (1 / (n + 1 : ℝ))
    rw [MeasurableSpace.measurableSet_iInf] at this
    exact this (by positivity)
  choose t ht hst using fun n : ℕ => ae_fieldSigma hYZ _ (hsn n)
  have htX : ∀ n : ℕ, MeasurableSet[fieldSigma X (nbhdO (1 / (n + 1 : ℝ)) K)] (t n) :=
    fun n : ℕ => hZ _ (by positivity) _ (ht n)
  refine ⟨⋃ N, ⋂ n, t (n + N), ?_, ?_⟩
  · unfold fieldSigmaClosed
    rw [MeasurableSpace.measurableSet_iInf]
    intro ε
    rw [MeasurableSpace.measurableSet_iInf]
    intro hε
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hε
    have heq : (⋃ N, ⋂ n, t (n + N)) = ⋃ N, ⋂ n, t (n + N + N₀) := by
      ext ω
      simp only [mem_iUnion, mem_iInter]
      constructor
      · rintro ⟨N, hN⟩; exact ⟨N, fun n => by have := hN (n + N₀); rwa [add_right_comm] at this⟩
      · rintro ⟨N, hN⟩; exact ⟨N + N₀, fun n => by have := hN n; rwa [add_assoc] at this⟩
    rw [heq]
    refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => ?_
    refine GM.fieldSigma_mono X ?_ _ (htX (n + N + N₀))
    intro x hx
    refine thickening_mono ?_ K hx
    have h1 : (1 : ℝ) / ((n + N + N₀ : ℕ) + 1) ≤ 1 / ((N₀ : ℝ) + 1) := by
      gcongr; exact_mod_cast Nat.le_add_left _ _
    linarith
  · have hall : ∀ᵐ ω ∂P, ∀ n, (ω ∈ s ↔ ω ∈ t n) := by
      rw [ae_all_iff]; intro n
      filter_upwards [hst n] with ω hω
      exact Iff.of_eq hω
    filter_upwards [hall] with ω hω
    apply propext
    simp only [mem_iUnion, mem_iInter]
    constructor
    · intro h; exact ⟨0, fun n => (hω _).1 h⟩
    · rintro ⟨N, hN⟩; exact (hω _).2 (hN 0)

/-- `σ((X − X_ρ(0))|_W) ≤ σ(X|_V)` when `W ≤ V` and `V` contains a neighbourhood of `∂B_ρ(0)`. -/
lemma fieldSigma_recentre_le (X : Ω → DistC) (ρ : ℝ) {W V : Opens ℂ} (hWV : W ≤ V) {ε : ℝ}
    (hε : 0 < ε) (hS : nbhdO ε (sphere (0 : ℂ) |ρ|) ≤ V) :
    fieldSigma (recentre X ρ) W ≤ fieldSigma X V := by
  have hc : Measurable[fieldSigma X V] fun ω => circleAvg (X ω) ρ 0 :=
    (GM.measurable_circleAvg_fieldSigma X ρ 0 hε).mono (GM.fieldSigma_mono X hS) le_rfl
  have : Measurable[fieldSigma X V] fun ω => restrictTo W (recentre X ρ ω) := by
    refine (@measurable_distOn_iff _ Ω (fieldSigma X V) _).2 fun φ => ?_
    let φ' : TestC := TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := ⊤) φ
    have e : (fun ω => restrictTo W (recentre X ρ ω) φ) =
        fun ω => X ω φ' + (∫ x, φ' x) * -circleAvg (X ω) ρ 0 := by
      funext ω
      show addConst (X ω) (-circleAvg (X ω) ρ 0) φ' = _
      rw [GFFInv.addConst_apply]
    rw [e]
    refine Measurable.add (GM.measurable_pair_fieldSigma X φ' ?_) (hc.neg.const_mul _)
    have : tsupport (φ' : ℂ → ℝ) = tsupport (φ : ℂ → ℝ) := by
      congr 1; ext x; simp [φ', TestFunction.monoCLM_apply]
    rw [this]
    exact φ.tsupport_subset.trans hWV
  exact this.comap_le

lemma measurable_recentre [MeasurableSpace Ω] {h : Ω → DistC} (hh : Measurable h) (r : ℝ) :
    Measurable (recentre h r) := by
  have hc : Measurable fun ω => circleAvg (h ω) r 0 :=
    (GM.measurable_circleAvg_fieldSigmaClosed h r 0 (subset_univ _)).mono
      (GM.fieldSigmaClosed_le_gm hh univ) le_rfl
  refine measurable_distOn_iff.2 fun φ => ?_
  simp only [recentre, GFFInv.addConst_apply]
  exact ((measurable_distOn_apply φ).comp hh).add (hc.neg.const_mul _)

/-- LM l. 608–609: a.s. `h − h_{r'}(0) = (h − h_r(0)) − (h − h_r(0))_{r'}(0)`. -/
lemma recentre_ae_eq [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {r' : ℝ} (hr' : 0 < r') (r : ℝ) :
    ∀ᵐ ω ∂P, recentre h r' ω = recentre (recentre h r) r' ω := by
  filter_upwards [CircleAvg.ae_circleAvg_addConst hh 0 hr'] with ω hω
  simp only [recentre]
  rw [hω, GM.addConst_addConst]
  congr 1; ring

lemma sphere_subset_compl_ball {r r' : ℝ} (hrr' : r ≤ r') :
    sphere (0 : ℂ) |r'| ⊆ (ball (0 : ℂ) r)ᶜ := by
  intro x hx
  simp only [mem_sphere_iff_norm, sub_zero] at hx
  simp only [mem_compl_iff, mem_ball, dist_zero_right, not_lt]
  rw [hx]; exact hrr'.trans (le_abs_self r')

/-- **LM Lemma 3.2** (l. 604–612), `N = 0`, modulo null sets: for `0 < r ≤ r'`, every
`𝓕_{r'}`-set is a.e. equal to an `𝓕_r`-set. -/
theorem lmF_ae_sub [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') {s : Set Ω}
    (hs : MeasurableSet[lmF h r'] s) : ∃ t, MeasurableSet[lmF h r] t ∧ s =ᵐ[P] t := by
  refine ae_fieldSigmaClosed (X := recentre h r) (recentre_ae_eq hh (hr.trans_le hrr') r)
    (fun ε hε => fieldSigma_recentre_le _ r' ?_ hε ?_) hs
  · intro x hx
    refine thickening_subset_of_subset ε ?_ hx
    exact compl_subset_compl.2 (ball_subset_ball hrr')
  · intro x hx
    exact thickening_subset_of_subset ε (sphere_subset_compl_ball hrr') hx

/-- LM l. 731: `σ((h − h_r(0))|_{A_{s₁r,s₂r}(0)})`-sets are a.e. equal to `𝓕_{s₁r}`-sets. -/
theorem annSigma_ae_sub [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {s₁ s₂ r : ℝ} (hr : 0 < r) (hs₁1 : s₁ ≤ 1) {s : Set Ω}
    (hs : MeasurableSet[annSigma h s₁ s₂ r] s) :
    ∃ t, MeasurableSet[lmF h (s₁ * r)] t ∧ s =ᵐ[P] t := by
  obtain ⟨t, ht, hst⟩ := ae_fieldSigma (recentre_ae_eq hh hr (s₁ * r)) _ hs
  refine ⟨t, ?_, hst⟩
  have hK : (annulus 0 (s₁ * r) (s₂ * r) : Set ℂ) ⊆ (ball (0 : ℂ) (s₁ * r))ᶜ := by
    intro x hx
    simp only [mem_compl_iff, mem_ball, dist_zero_right, not_lt]
    have := hx.1; simp only [sub_zero] at this; exact this.le
  have hsr : s₁ * r ≤ r := by nlinarith
  unfold lmF fieldSigmaClosed
  refine (le_iInf₂ fun ε hε => ?_ : fieldSigma _ (annulus 0 (s₁ * r) (s₂ * r)) ≤ _) t ht
  refine fieldSigma_recentre_le _ r ?_ hε ?_
  · intro x hx; exact self_subset_thickening hε _ (hK hx)
  · intro x hx; exact thickening_subset_of_subset ε (sphere_subset_compl_ball hsr) hx

/-- **LM Lemma 3.2** as a filtration: `k ↦ 𝓕_{r_k}` (null-augmented) for `r` antitone. -/
def lmFiltration [MeasurableSpace Ω] (P : Measure Ω) {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hrA : Antitone r) :
    Filtration ℕ ‹MeasurableSpace Ω› where
  seq k := augSigma P (lmF h (r k))
  mono' _ l hkl := augSigma_mono_of P fun _ hs => lmF_ae_sub hh (hr0 l) (hrA hkl) hs
  le' _ := augSigma_le P _

/-- **LM (3.9)** (l. 731–734): `σ((h − h_{r_k}(0))|_{A_{s₁r_k,s₂r_k}(0)}) ⊂ 𝓕_{s₁r_k} ⊂ 𝓕_{r_{k+1}}`. -/
theorem annSigma_le_lmFiltration [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hrA : Antitone r) {s₁ s₂ : ℝ}
    (hs₁1 : s₁ ≤ 1) (hrs : ∀ k, r (k + 1) / r k ≤ s₁) (k : ℕ) :
    annSigma h s₁ s₂ (r k) ≤ lmFiltration P hh hr0 hrA (k + 1) := by
  intro s hs
  refine ⟨((measurable_restrictTo _).comp (measurable_recentre hh.measurable (r k))).comap_le _ hs,
    ?_⟩
  obtain ⟨t, ht, hst⟩ := annSigma_ae_sub hh (hr0 k) hs₁1 hs
  have hle : r (k + 1) ≤ s₁ * r k := (div_le_iff₀ (hr0 k)).1 (hrs k)
  obtain ⟨t', ht', htt'⟩ := lmF_ae_sub hh (hr0 (k + 1)) hle ht
  exact ⟨t', ht', hst.trans htt'⟩

end LQGMetric.LM
