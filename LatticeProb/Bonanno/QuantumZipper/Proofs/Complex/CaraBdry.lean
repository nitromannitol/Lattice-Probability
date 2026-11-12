/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.CaraBdry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraExt
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsReflection

/-!
# EXT-CA C4 and the separation core of C5: boundary values of a conformal map of `H`

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 C4, C5. Throughout, `F` is a continuous extension
of `ψ` to `Hbar` (`EqOn F ψ H`, `ContinuousOn F Hbar`), as produced by C3
(`CA.Car.continuousOn_extension`).

* **C4** `not_forall_eq_const_Ioo`: `F` is not constant on a nondegenerate real interval
  (for `ψ` holomorphic and injective on `H`). Proof as in the blueprint: after subtracting the
  constant, `F - c` is real (zero) on the interval, so Schwarz reflection and the identity
  theorem (node A3, `eqOn_const_of_eq_const_on_Ioo`) give `ψ ≡ c` on a half-disk, contradicting
  injectivity. This is the fact used in Pommerenke, *Boundary Behaviour of Conformal Maps*
  (1992), proof of Prop. 2.5, printed pp. 23–24, that the arcs `f(I_k)` are not points (there via
  the Privalov/Riesz uniqueness theorem; here via reflection, which suffices for constants).
* `closure_image_subset`: every limit point of `ψ` on `S ⊆ H` is a value of `F` on `closure S`
  or the limit `wInf` of `ψ` at `∞` (compactness of `Hbar ∪ {∞}`, C1-type argument).
* `not_mem_connectedComponentIn_of_partition`, `..._of_mem_closure`: the Janiszewski step of
  Pommerenke's proof of Prop. 2.5 (p. 24: "`f(I_j)` and `f(I_k)` lie in different components of
  `ℂ \ J`"). Pommerenke uses the Jordan curve theorem for `J = f(C̄)`; we replace it, as in C3
  (`CaraExtSep.lean`), by Janiszewski's theorem (T3) applied to `Λ` and
  `M = closedBall 0 R₀ \ D` (with `Λ ∩ M ⊆ {q}`), plus the "three disjoint open sets" lemma.
  Departure recorded under DEVIATIONS L-CA-TOPO.
-/

noncomputable section

open Set Metric Filter Topology Complex
open scoped Real

namespace QuantumZipper.CA.Car

open QuantumZipper.CA.Topo

theorem closure_H_eq_Hbar : closure H = Hbar := Complex.closure_setOfPred_lt_im 0

/-- **C4 (no constant boundary arcs).** The continuous extension `F` of an injective holomorphic
map `ψ` of `H` is not constant on any nondegenerate real interval. -/
theorem not_forall_eq_const_Ioo {ψ F : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ H) (hinj : InjOn ψ H)
    (hEq : EqOn F ψ H) (hF : ContinuousOn F Hbar) {a b : ℝ} (hab : a < b) (c : ℂ) :
    ¬ ∀ t ∈ Ioo a b, F t = c := by
  intro hc
  set x : ℝ := (a + b) / 2 with hx
  set r : ℝ := (b - a) / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  have hball : ∀ t : ℝ, (t : ℂ) ∈ ball (x : ℂ) r ↔ t ∈ Ioo a b := by
    intro t
    rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_lt_iff,
      mem_Ioo, hx, hr_def]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  set g : ℂ → ℂ := fun z => F z - c with hg
  have hd : DifferentiableOn ℂ g (H ∩ ball (x : ℂ) r) :=
    ((hψ.mono inter_subset_left).congr fun z hz => hEq hz.1).sub_const c
  have hc' : ContinuousOn g (Hbar ∩ ball (x : ℂ) r) :=
    (hF.mono inter_subset_left).sub continuousOn_const
  have hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (g z).im = 0 := by
    intro z hz hz0
    have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
    rw [hzr] at hz ⊢
    simp only [hg, hc z.re ((hball _).1 hz), sub_self, zero_im]
  have hall := eqOn_const_of_eq_const_on_Ioo hd hc' hreal hab (c := 0)
    (fun t ht => ⟨(hball t).2 ht, by simp [hg, hc t ht]⟩)
  have hmem : ∀ s : ℝ, 0 < s → s < r → (x : ℂ) + (s : ℂ) * I ∈ H ∩ ball (x : ℂ) r := by
    intro s hs hsr
    refine ⟨show 0 < ((x : ℂ) + (s : ℂ) * I).im by simpa using hs, ?_⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
    exact hsr
  have e : ∀ s : ℝ, 0 < s → s < r → ψ ((x : ℂ) + (s : ℂ) * I) = c := by
    intro s hs hsr
    have hm := hmem s hs hsr
    have := hall _ ⟨H_subset_Hbar hm.1, hm.2⟩
    simp only [hg, sub_eq_zero] at this
    rw [← hEq hm.1]
    exact this
  have h23 := hinj (hmem (r / 2) (by positivity) (by linarith)).1
    (hmem (r / 3) (by positivity) (by linarith)).1
    ((e _ (by positivity) (by linarith)).trans (e _ (by positivity) (by linarith)).symm)
  have h2 := congrArg Complex.im h23
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, add_zero,
    zero_add] at h2
  linarith

/-- The value of `F` at a point of `Hbar` is a limit of values of `ψ` on any `𝓝[H]`-neighbourhood
of the point. -/
theorem mem_closure_image_of_mem_nhdsWithin {ψ F : ℂ → ℂ} (hEq : EqOn F ψ H)
    (hF : ContinuousOn F Hbar) {z : ℂ} (hz : z ∈ Hbar) {U : Set ℂ} (hU : U ∈ 𝓝[H] z) :
    F z ∈ closure (ψ '' U) := by
  have : (𝓝[H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H_eq_Hbar ▸ hz)
  exact mem_closure_of_tendsto (tendsto_nhdsWithin_H_of_extension hEq hF hz)
    (Filter.mem_of_superset hU fun w hw => mem_image_of_mem ψ hw)

theorem neBot_cobounded_inf_H : (Bornology.cobounded ℂ ⊓ 𝓟 H).NeBot := by
  set z : ℕ → ℂ := fun n => (((n : ℝ) + 1 : ℝ) : ℂ) * I with hz
  have hzH : ∀ n, z n ∈ H := fun n => by
    show 0 < (z n).im
    simp only [hz, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    positivity
  have hzc : Tendsto z atTop (Bornology.cobounded ℂ) := by
    refine tendsto_norm_atTop_iff_cobounded.1 ?_
    have : (fun n => ‖z n‖) = fun n : ℕ => (n : ℝ) + 1 := funext fun n => by
      simp only [hz, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by positivity)
    rw [this]
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact (tendsto_inf.2 ⟨hzc, tendsto_principal.2 (Eventually.of_forall hzH)⟩).neBot

/-- The limit of `ψ` at `∞` is a limit of values of `ψ` on any neighbourhood of `∞` in `H`. -/
theorem mem_closure_image_of_mem_cobounded {ψ : ℂ → ℂ} {wInf : ℂ}
    (hInf : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf)) {U : Set ℂ}
    (hU : U ∈ Bornology.cobounded ℂ ⊓ 𝓟 H) : wInf ∈ closure (ψ '' U) := by
  have := neBot_cobounded_inf_H
  exact mem_closure_of_tendsto hInf (Filter.mem_of_superset hU fun w hw => mem_image_of_mem ψ hw)

/-- **Cluster values** (compactness of `Hbar ∪ {∞}`): a limit point of `ψ` on `S ⊆ H` is a
value of `F` on `closure S`, or the limit `wInf` of `ψ` at `∞`. -/
theorem closure_image_subset {ψ F : ℂ → ℂ} {wInf : ℂ} (hEq : EqOn F ψ H)
    (hF : ContinuousOn F Hbar) (hInf : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf))
    {S : Set ℂ} (hS : S ⊆ H) : closure (ψ '' S) ⊆ F '' closure S ∪ {wInf} := by
  intro p hp
  set l := comap ψ (𝓝 p) ⊓ 𝓟 S with hl
  have hlne : l.NeBot := by
    refine inf_principal_neBot_iff.2 fun U hU => ?_
    obtain ⟨t, ht, htU⟩ := mem_comap.1 hU
    obtain ⟨_, hwt, ⟨z, hzS, rfl⟩⟩ := mem_closure_iff_nhds.1 hp t ht
    exact ⟨z, htU hwt, hzS⟩
  have hlp : Tendsto ψ l (𝓝 p) := tendsto_iff_comap.2 inf_le_left
  have hlH : l ≤ 𝓟 H := inf_le_right.trans (principal_mono.2 hS)
  by_cases hcob : (l ⊓ Bornology.cobounded ℂ).NeBot
  · right
    have h1 : Tendsto ψ (l ⊓ Bornology.cobounded ℂ) (𝓝 wInf) :=
      hInf.mono_left (by rw [inf_comm]; exact inf_le_inf_left _ hlH)
    exact tendsto_nhds_unique (hlp.mono_left inf_le_left) h1
  · left
    rw [not_neBot, inf_eq_bot_iff] at hcob
    obtain ⟨U, hU, V, hV, hUV⟩ := hcob
    have hb : Bornology.IsBounded (U ∩ S) := by
      have hVb : Bornology.IsBounded Vᶜ := Bornology.isBounded_def.2 (by rwa [compl_compl])
      refine hVb.subset ?_
      intro w hw hwV
      have : w ∈ U ∩ V := ⟨hw.1, hwV⟩
      rw [hUV] at this
      exact this
    have hUS : U ∩ S ∈ l := inter_mem hU (mem_inf_of_right (mem_principal_self S))
    obtain ⟨z, hzK, hcl⟩ := hb.isCompact_closure.exists_clusterPt
      (le_principal_iff.2 (mem_of_superset hUS subset_closure))
    have hzS : z ∈ closure S := closure_mono inter_subset_right hzK
    have hzH : z ∈ Hbar := closure_H_eq_Hbar ▸ closure_mono hS hzS
    have : (𝓝 z ⊓ l).NeBot := hcl
    have h1 : Tendsto ψ (𝓝 z ⊓ l) (𝓝 (F z)) :=
      (tendsto_nhdsWithin_H_of_extension hEq hF hzH).mono_left (inf_le_inf_left _ hlH)
    exact ⟨z, hzS, tendsto_nhds_unique h1 (hlp.mono_left inf_le_right)⟩

/-- **Separation core (Janiszewski step).** Let `Λ` be compact with `Λ \ {q} ⊆ D`, and let
`U₁, U₂ ⊆ H` be disjoint open sets such that `ψ` maps every point of `H \ (U₁ ∪ U₂)` into `Λ`.
Then `Λ` separates `ψ(U₁) \ Λ` from `ψ(U₂) \ Λ`. -/
theorem not_mem_connectedComponentIn_of_partition {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ}
    (h : CarHyp ψ D E R₀) {Λ : Set ℂ} (hΛ : IsCompact Λ) {q : ℂ} (hΛD : Λ \ {q} ⊆ D)
    {U₁ U₂ : Set ℂ} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU₁H : U₁ ⊆ H) (hU₂H : U₂ ⊆ H)
    (hU : Disjoint U₁ U₂) (hcov : ∀ z ∈ H, z ∉ U₁ → z ∉ U₂ → ψ z ∈ Λ)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ U₁) (hz₂ : z₂ ∈ U₂) (hn₁ : ψ z₁ ∉ Λ) (hn₂ : ψ z₂ ∉ Λ) :
    ψ z₂ ∉ connectedComponentIn Λᶜ (ψ z₁) := by
  intro hmem
  set B : Set ℂ := closedBall 0 R₀ \ D with hB
  have hBc : IsCompact B := (isCompact_closedBall _ _).diff h.isOpen
  have hAB : IsPreconnected (Λ ∩ B) := by
    refine Set.Subsingleton.isPreconnected ?_
    refine (subsingleton_singleton (a := q)).anti fun w hw => ?_
    by_contra hwq
    exact hw.2.2 (hΛD ⟨hw.1, hwq⟩)
  have hD1 : ψ z₁ ∈ D := h.bij.mapsTo (hU₁H hz₁)
  have hD2 : ψ z₂ ∈ D := h.bij.mapsTo (hU₂H hz₂)
  have hp : ψ z₁ ∉ Λ ∪ B := fun hw => hw.elim hn₁ fun hb => hb.2 hD1
  have hq : ψ z₂ ∉ Λ ∪ B := fun hw => hw.elim hn₂ fun hb => hb.2 hD2
  have hDpre : IsPreconnected D := by
    rw [← h.bij.image_eq]
    exact (convex_halfSpace_im_gt 0).isPreconnected.image _ h.holo.continuousOn
  have h₂ : ψ z₂ ∈ connectedComponentIn Bᶜ (ψ z₁) :=
    hDpre.subset_connectedComponentIn hD1 (fun w hw hwB => hwB.2 hw : D ⊆ Bᶜ) hD2
  have hJan := janiszewski hΛ hBc hAB hp hq hmem h₂
  set V₁ : Set ℂ := ψ '' U₁ with hV₁d
  set V₂ : Set ℂ := ψ '' U₂ ∪ (closedBall 0 R₀)ᶜ with hV₂d
  have hV₁ : IsOpen V₁ := isOpen_image_of_injOn isOpen_H h.holo h.bij.injOn hU₁ hU₁H
  have hV₂ : IsOpen V₂ := (isOpen_image_of_injOn isOpen_H h.holo h.bij.injOn hU₂ hU₂H).union
    isClosed_closedBall.isOpen_compl
  have hV : Disjoint V₁ V₂ := by
    rw [Set.disjoint_left]
    rintro _ ⟨ζ₁, hζ₁, rfl⟩ (⟨ζ₂, hζ₂, he⟩ | hout)
    · have := h.bij.injOn (hU₂H hζ₂) (hU₁H hζ₁) he
      exact Set.disjoint_left.1 hU hζ₁ (this ▸ hζ₂)
    · exact hout (ball_subset_closedBall (h.bdd (h.bij.mapsTo (hU₁H hζ₁))))
  have hcover : (Λ ∪ B)ᶜ ⊆ V₁ ∪ V₂ := by
    intro w hw
    rw [mem_compl_iff, mem_union, not_or] at hw
    by_cases hwb : w ∈ closedBall (0 : ℂ) R₀
    · have hwD : w ∈ D := by
        by_contra hwD
        exact hw.2 ⟨hwb, hwD⟩
      obtain ⟨ζ, hζ, rfl⟩ := h.bij.surjOn hwD
      by_cases h1 : ζ ∈ U₁
      · exact Or.inl ⟨ζ, h1, rfl⟩
      by_cases h2 : ζ ∈ U₂
      · exact Or.inr (Or.inl ⟨ζ, h2, rfl⟩)
      exact absurd (hcov ζ hζ h1 h2) hw.1
    · exact Or.inr (Or.inr hwb)
  exact not_mem_connectedComponentIn_of_subset_union hV₁ hV₂ hV hcover ⟨z₁, hz₁, rfl⟩
    (Or.inl ⟨z₂, hz₂, rfl⟩) hJan

/-- **Separation core, boundary form.** In the situation of
`not_mem_connectedComponentIn_of_partition`, `Λ` separates limit points of `ψ(U₁)` from limit
points of `ψ(U₂)` (off `Λ`). -/
theorem not_mem_connectedComponentIn_of_mem_closure {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ}
    (h : CarHyp ψ D E R₀) {Λ : Set ℂ} (hΛ : IsCompact Λ) {q : ℂ} (hΛD : Λ \ {q} ⊆ D)
    {U₁ U₂ : Set ℂ} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU₁H : U₁ ⊆ H) (hU₂H : U₂ ⊆ H)
    (hU : Disjoint U₁ U₂) (hcov : ∀ z ∈ H, z ∉ U₁ → z ∉ U₂ → ψ z ∈ Λ)
    {p₁ p₂ : ℂ} (hp₁ : p₁ ∈ closure (ψ '' U₁)) (hp₂ : p₂ ∈ closure (ψ '' U₂)) (hn₁ : p₁ ∉ Λ)
    (hn₂ : p₂ ∉ Λ) : p₂ ∉ connectedComponentIn Λᶜ p₁ := by
  intro hmem
  have hO : IsOpen Λᶜ := hΛ.isClosed.isOpen_compl
  obtain ⟨_, hw₁, ⟨z₁, hz₁, rfl⟩⟩ :=
    mem_closure_iff.1 hp₁ _ hO.connectedComponentIn (mem_connectedComponentIn hn₁)
  obtain ⟨_, hw₂, ⟨z₂, hz₂, rfl⟩⟩ :=
    mem_closure_iff.1 hp₂ _ hO.connectedComponentIn (mem_connectedComponentIn hn₂)
  have e₁ := connectedComponentIn_eq hw₁
  have e₂ := connectedComponentIn_eq hmem
  have e₃ := connectedComponentIn_eq hw₂
  refine not_mem_connectedComponentIn_of_partition h hΛ hΛD hU₁ hU₂ hU₁H hU₂H hU hcov hz₁ hz₂
    (connectedComponentIn_subset _ _ hw₁) (connectedComponentIn_subset _ _ hw₂) ?_
  rw [← e₁, e₂, e₃]
  exact mem_connectedComponentIn (connectedComponentIn_subset _ _ hw₂)

/-- **Separation core, preconnected form.** A preconnected set disjoint from `Λ` cannot contain
both a limit point of `ψ(U₁)` and a limit point of `ψ(U₂)`. -/
theorem not_mem_closure_of_isPreconnected {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ}
    (h : CarHyp ψ D E R₀) {Λ : Set ℂ} (hΛ : IsCompact Λ) {q : ℂ} (hΛD : Λ \ {q} ⊆ D)
    {U₁ U₂ : Set ℂ} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU₁H : U₁ ⊆ H) (hU₂H : U₂ ⊆ H)
    (hU : Disjoint U₁ U₂) (hcov : ∀ z ∈ H, z ∉ U₁ → z ∉ U₂ → ψ z ∈ Λ)
    {Z : Set ℂ} (hZ : IsPreconnected Z) (hZΛ : ∀ p ∈ Z, p ∉ Λ) {p₁ p₂ : ℂ} (h₁ : p₁ ∈ Z)
    (h₂ : p₂ ∈ Z) (hp₁ : p₁ ∈ closure (ψ '' U₁)) : p₂ ∉ closure (ψ '' U₂) := fun hp₂ =>
  not_mem_connectedComponentIn_of_mem_closure h hΛ hΛD hU₁ hU₂ hU₁H hU₂H hU hcov hp₁ hp₂
    (hZΛ _ h₁) (hZΛ _ h₂) (hZ.subset_connectedComponentIn h₁ (fun p hp => hZΛ p hp) h₂)

end QuantumZipper.CA.Car
