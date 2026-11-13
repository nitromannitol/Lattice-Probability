/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CaraRZ at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ArcDeterminesDriver
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.ForwardClock

/-!
# Loewner interface for the Carathéodory extension: nodes RZ and R2

Blueprint `EXT_CA_BLUEPRINT.md`, §3, nodes **RZ** and **R2**.

* `norm_revMap_sub_self_le` (UB): the reverse centered flow moves every point of `ℍ` by at most
  `3M + 6√s`, where `M` bounds the driver on `[0,s]`. This is the reverse-flow analogue of the
  hull-radius estimate of Lawler, *Conformally Invariant Processes in the Plane* (AMS 2005),
  Lemma 4.12, p. 80 (the blueprint says "4.13"; the statement is Lemma 4.12).
* `fwdHull_subset_closedBall`: forward hulls are small,
  `K_s ⊆ closedBall 0 (M + 3√s)` (Lawler, Lemma 4.12, p. 80).
* `fwdHull_nonempty`: forward hulls at positive times are nonempty.
* `zero_mem_closure_revHull` (RZ): the driver's start `0` lies in the closure of every hull.
* R2: `exists_bound_revMap_sub_self`, `tendsto_revMap_cobounded`, `isBounded_image_revMap`,
  `bijOn_revMap_revHull`.

The estimates are all proved from the centered integral equations by a first/last-exit-time
argument: while `‖u‖ ≥ δ` the drift `∫ 2/u` moves by at most `2·(time)/δ`, and `δ := √s`.
-/

noncomputable section

open Set Filter Topology MeasureTheory

namespace QuantumZipper

namespace CaraR

/-! ### Generic exit-time helpers -/

/-- First time in `[a,b]` at which a continuous path enters the closed ball of radius `δ`. -/
theorem exists_first_norm_le {u : ℝ → ℂ} {a b δ : ℝ} (hu : ContinuousOn u (Icc a b)) {r : ℝ}
    (hr : r ∈ Icc a b) (hδ : ‖u r‖ ≤ δ) :
    ∃ r₀ ∈ Icc a b, ‖u r₀‖ ≤ δ ∧ ∀ q ∈ Ico a r₀, δ < ‖u q‖ := by
  set S := Icc a b ∩ (fun q => ‖u q‖) ⁻¹' Iic δ with hSdef
  have hS : IsClosed S := hu.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hne : S.Nonempty := ⟨r, hr, hδ⟩
  have hbdd : BddBelow S := ⟨a, fun q hq => hq.1.1⟩
  have hmem := hS.csInf_mem hne hbdd
  refine ⟨sInf S, hmem.1, hmem.2, fun q hq => ?_⟩
  by_contra h
  push Not at h
  have : sInf S ≤ q := csInf_le hbdd ⟨⟨hq.1, hq.2.le.trans hmem.1.2⟩, h⟩
  exact absurd hq.2 (not_lt.2 this)

/-- Last time in `[a,b]` at which a continuous path lies in the closed ball of radius `δ`. -/
theorem exists_last_norm_le {u : ℝ → ℂ} {a b δ : ℝ} (hu : ContinuousOn u (Icc a b)) {r : ℝ}
    (hr : r ∈ Icc a b) (hδ : ‖u r‖ ≤ δ) :
    ∃ r₁ ∈ Icc a b, ‖u r₁‖ ≤ δ ∧ ∀ q ∈ Ioc r₁ b, δ < ‖u q‖ := by
  set S := Icc a b ∩ (fun q => ‖u q‖) ⁻¹' Iic δ with hSdef
  have hS : IsClosed S := hu.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hne : S.Nonempty := ⟨r, hr, hδ⟩
  have hbdd : BddAbove S := ⟨b, fun q hq => hq.1.2⟩
  have hmem := hS.csSup_mem hne hbdd
  refine ⟨sSup S, hmem.1, hmem.2, fun q hq => ?_⟩
  by_contra h
  push Not at h
  have : q ≤ sSup S := le_csSup hbdd ⟨⟨hmem.1.1.trans hq.1.le, hq.2⟩, h⟩
  exact absurd hq.1 (not_lt.2 this)

/-- The Loewner drift `∫ 2/u` over `[a,b]` is at most `2(b-a)/δ` while `‖u‖ ≥ δ`. -/
theorem norm_integral_two_div_le {u : ℝ → ℂ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hu : ContinuousOn u (Icc a b)) (hlow : ∀ q ∈ Ioo a b, δ ≤ ‖u q‖) :
    ‖∫ q in a..b, 2 / u q‖ ≤ 2 * (b - a) / δ := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  have hcl : ∀ q ∈ Icc a b, δ ≤ ‖u q‖ := by
    have hC : IsClosed (Icc a b ∩ (fun q => ‖u q‖) ⁻¹' Ici δ) :=
      hu.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hsub : Ioo a b ⊆ Icc a b ∩ (fun q => ‖u q‖) ⁻¹' Ici δ :=
      fun q hq => ⟨Ioo_subset_Icc_self hq, hlow q hq⟩
    have := closure_minimal hsub hC
    rw [closure_Ioo hlt.ne] at this
    exact fun q hq => (this hq).2
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 2 / δ)
    (f := fun q => 2 / u q) (fun q hq => by
      rw [uIoc_of_le hab] at hq
      rw [norm_div]
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2]
      exact div_le_div_of_nonneg_left (by norm_num) hδ (hcl q (Ioc_subset_Icc_self hq)))
  rw [abs_of_nonneg (sub_nonneg.2 hab)] at h
  calc _ ≤ 2 / δ * (b - a) := h
    _ = 2 * (b - a) / δ := by ring

/-- One step of the exit-time argument for a solution of `u = z - W + c ∫ 2/u`, `‖c‖ = 1`
(`c = -1`: reverse flow, `c = 1`: forward flow). -/
theorem norm_step_le {u : ℝ → ℂ} {W : ℝ → ℝ} {z c : ℂ} {s δ a b : ℝ} (hc : ‖c‖ = 1)
    (hu : ContinuousOn u (Icc 0 s))
    (hsol : ∀ r ∈ Icc (0 : ℝ) s, u r ≠ 0 ∧ u r = z - W r + c * ∫ q in (0 : ℝ)..r, 2 / u q)
    (hδ : 0 < δ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ s) (hlow : ∀ q ∈ Ioo a b, δ ≤ ‖u q‖) :
    ‖u b - u a + ((W b : ℂ) - W a)‖ ≤ 2 * (b - a) / δ := by
  have hint : ∀ x ∈ Icc (0 : ℝ) s, IntervalIntegrable (fun q => 2 / u q) volume 0 x :=
    fun x hx => by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hx.1]
      exact continuousOn_const.div (hu.mono (Icc_subset_Icc_right hx.2))
        fun q hq => (hsol q ⟨hq.1, hq.2.trans hx.2⟩).1
  have hsplit := intervalIntegral.integral_interval_sub_left (hint b ⟨ha.trans hab, hb⟩)
    (hint a ⟨ha, hab.trans hb⟩)
  have e : u b - u a + ((W b : ℂ) - W a) = c * ∫ q in a..b, 2 / u q := by
    rw [(hsol b ⟨ha.trans hab, hb⟩).2, (hsol a ⟨ha, hab.trans hb⟩).2, ← hsplit]
    ring
  rw [e, norm_mul, hc, one_mul]
  exact norm_integral_two_div_le hab hδ (hu.mono (Icc_subset_Icc ha hb)) hlow

theorem two_mul_div_sqrt {s : ℝ} : 2 * s / Real.sqrt s = 2 * Real.sqrt s := by
  rw [mul_div_assoc, Real.div_sqrt]

/-! ### UB: the reverse flow moves points by a bounded amount -/

/-- **UB.** `‖revMap W s z - z‖ ≤ 3M + 6√s` on `ℍ` when `|W| ≤ M` on `[0,s]` (reverse-flow
analogue of Lawler, *Conformally Invariant Processes in the Plane*, Lemma 4.12, p. 80; blueprint
EXT_CA node R2). -/
theorem norm_revMap_sub_self_le {W : ℝ → ℝ} (hW : Continuous W) {s M : ℝ} (hs : 0 < s)
    (hM : ∀ r ∈ Set.Icc (0 : ℝ) s, |W r| ≤ M) {z : ℂ} (hz : z ∈ H) :
    ‖revMap W s z - z‖ ≤ 3 * M + 6 * Real.sqrt s := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz s hs.le
  rw [revMap_eq W hW z hs.le le_rfl hu]
  have hsol : ∀ r ∈ Icc (0 : ℝ) s,
      u r ≠ 0 ∧ u r = z - W r + (-1 : ℂ) * ∫ q in (0 : ℝ)..r, 2 / u q := fun r hr =>
    ⟨fun h => by have := (hu.2 r hr).1; rw [h] at this; simp at this,
      by rw [(hu.2 r hr).2]; ring⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = Real.sqrt s := ⟨_, rfl⟩
  have hδ : 0 < δ := hδdef ▸ Real.sqrt_pos.2 hs
  have hsδ : 2 * s / δ = 2 * δ := hδdef ▸ two_mul_div_sqrt
  have hWc : ∀ r ∈ Icc (0 : ℝ) s, ‖(W r : ℂ)‖ ≤ M := fun r hr => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hM r hr
  have hs0 : (0 : ℝ) ∈ Icc 0 s := ⟨le_rfl, hs.le⟩
  have hss : s ∈ Icc 0 s := ⟨hs.le, le_rfl⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 hs0)
  have h0 : u 0 = z - W 0 := by rw [(hsol 0 hs0).2]; simp
  have hstep : ∀ a b, 0 ≤ a → a ≤ b → b ≤ s → (∀ q ∈ Ioo a b, δ ≤ ‖u q‖) →
      ‖u b - u a + ((W b : ℂ) - W a)‖ ≤ 2 * δ := fun a b ha hab hb hlow =>
    (norm_step_le (by simp) hu.1 hsol hδ ha hab hb hlow).trans
      (by rw [← hsδ]; exact div_le_div_of_nonneg_right (by linarith) hδ.le)
  rw [← hδdef]
  by_cases hA : ∀ r ∈ Icc (0 : ℝ) s, δ < ‖u r‖
  · have h1 := hstep 0 s le_rfl hs.le le_rfl (fun q hq => (hA q (Ioo_subset_Icc_self hq)).le)
    have e : u s - z = (u s - u 0 + ((W s : ℂ) - W 0)) - W s := by rw [h0]; ring
    rw [e]
    linarith [norm_sub_le (u s - u 0 + ((W s : ℂ) - W 0)) (W s : ℂ), hWc s hss]
  · push Not at hA
    obtain ⟨r, hr, hrδ⟩ := hA
    obtain ⟨r₀, hr₀, hr₀δ, hbef⟩ := exists_first_norm_le hu.1 hr hrδ
    obtain ⟨r₁, hr₁, hr₁δ, haft⟩ := exists_last_norm_le hu.1 hr hrδ
    have h1 := hstep 0 r₀ le_rfl hr₀.1 hr₀.2 (fun q hq => (hbef q ⟨hq.1.le, hq.2⟩).le)
    have h2 := hstep r₁ s hr₁.1 hr₁.2 le_rfl (fun q hq => (haft q ⟨hq.1, hq.2.le⟩).le)
    have hz1 : ‖z‖ ≤ δ + M + 2 * δ := by
      have e : z = (u r₀ + W r₀) - (u r₀ - u 0 + ((W r₀ : ℂ) - W 0)) := by rw [h0]; ring
      rw [e]
      linarith [norm_sub_le (u r₀ + W r₀) (u r₀ - u 0 + ((W r₀ : ℂ) - W 0)),
        norm_add_le (u r₀) (W r₀ : ℂ), hWc r₀ hr₀]
    have hz2 : ‖u s‖ ≤ 2 * δ + δ + M + M := by
      have e : u s = (u s - u r₁ + ((W s : ℂ) - W r₁)) + u r₁ - W s + W r₁ := by ring
      rw [e]
      linarith [norm_add_le ((u s - u r₁ + ((W s : ℂ) - W r₁)) + u r₁ - W s) (W r₁ : ℂ),
        norm_sub_le ((u s - u r₁ + ((W s : ℂ) - W r₁)) + u r₁) (W s : ℂ),
        norm_add_le (u s - u r₁ + ((W s : ℂ) - W r₁)) (u r₁), hWc s hss, hWc r₁ hr₁]
    linarith [norm_sub_le (u s) z]

/-- **R2(a).** `revMap W T` is at bounded distance from the identity on `ℍ`. -/
theorem exists_bound_revMap_sub_self {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T) :
    ∃ C, ∀ z ∈ H, ‖revMap W T z - z‖ ≤ C := by
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hW.continuousOn
  exact ⟨3 * M + 6 * Real.sqrt T, fun z hz =>
    norm_revMap_sub_self_le hW hT (fun r hr => by simpa [Real.norm_eq_abs] using hM r hr) hz⟩

/-! ### Forward hulls: radius bound and non-emptiness -/

/-- **Hull radius.** `K_s ⊆ closedBall 0 (M + 3√s)` when `|A| ≤ M` on `[0,s]`
(Lawler, *Conformally Invariant Processes in the Plane*, Lemma 4.12, p. 80; blueprint EXT_CA node RZ). -/
theorem fwdHull_subset_closedBall {A : ℝ → ℝ} (hA : Continuous A) {s M : ℝ} (hs : 0 < s)
    (hM : ∀ r ∈ Icc (0 : ℝ) s, |A r| ≤ M) :
    fwdHull A s ⊆ Metric.closedBall 0 (M + 3 * Real.sqrt s) := by
  intro z hzK
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hfar
  push Not at hfar
  obtain ⟨hzim, σ, hσs, hsw, hclock⟩ := (FwdClock.mem_fwdHull_iff_clock hA).1 hzK
  obtain ⟨t₀, ht₀, ht₀σ, hcl⟩ := hclock 1
  have hnot : z ∉ fwdHull A t₀ := fun h => by
    have h1 : swallowTime A z ≤ ENNReal.ofReal t₀ := h.2
    rw [hsw, ENNReal.ofReal_le_ofReal_iff ht₀] at h1
    linarith
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull ht₀ hzim hnot
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = Real.sqrt s := ⟨_, rfl⟩
  have hδ : 0 < δ := hδdef ▸ Real.sqrt_pos.2 hs
  have hsδ : 2 * s / δ = 2 * δ := hδdef ▸ two_mul_div_sqrt
  have hδsq : δ ^ 2 = s := hδdef ▸ Real.sq_sqrt hs.le
  have ht₀s : t₀ < s := ht₀σ.trans_le hσs
  have hsol : ∀ r ∈ Icc (0 : ℝ) t₀,
      u r ≠ 0 ∧ u r = z - A r + (1 : ℂ) * ∫ q in (0 : ℝ)..r, 2 / u q := fun r hr =>
    ⟨(hu.2 r hr).1, by rw [one_mul]; exact (hu.2 r hr).2⟩
  by_cases hA' : ∀ r ∈ Icc (0 : ℝ) t₀, δ ≤ ‖u r‖
  · have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t₀)
      (C := 1 / δ ^ 2) (f := fun r => 1 / ‖fwdMap A r z‖ ^ 2) (fun r hr => by
        rw [uIoc_of_le ht₀] at hr
        have hrI : r ∈ Icc 0 t₀ := Ioc_subset_Icc_self hr
        rw [fwdMap_eq hA hzim hu hrI, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact one_div_le_one_div_of_le (pow_pos hδ 2) (pow_le_pow_left₀ hδ.le (hA' r hrI) 2))
    rw [sub_zero, abs_of_nonneg ht₀, Real.norm_eq_abs] at h
    unfold FwdClock.fwdClock at hcl
    have h2 : 1 / δ ^ 2 * t₀ < 1 := by
      rw [hδsq, one_div_mul_eq_div, div_lt_one hs]; exact ht₀s
    linarith [le_abs_self (∫ r in (0 : ℝ)..t₀, 1 / ‖fwdMap A r z‖ ^ 2)]
  · push Not at hA'
    obtain ⟨r, hr, hrδ⟩ := hA'
    obtain ⟨r₀, hr₀, hr₀δ, hbef⟩ := exists_first_norm_le hu.1 hr hrδ.le
    have h1 := (norm_step_le (by simp) hu.1 hsol hδ le_rfl hr₀.1 hr₀.2
      (fun q hq => (hbef q ⟨hq.1.le, hq.2⟩).le)).trans
      (show 2 * (r₀ - 0) / δ ≤ 2 * δ by
        rw [← hsδ]; exact div_le_div_of_nonneg_right (by linarith [hr₀.2]) hδ.le)
    have h0 : u 0 = z - A 0 := by rw [(hsol 0 ⟨le_rfl, ht₀⟩).2]; simp
    have hAr : ‖(A r₀ : ℂ)‖ ≤ M := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hM r₀ ⟨hr₀.1, by linarith [hr₀.2]⟩
    have e : z = (u r₀ + A r₀) - (u r₀ - u 0 + ((A r₀ : ℂ) - A 0)) := by rw [h0]; ring
    rw [e] at hfar
    rw [← hδdef] at hfar
    linarith [norm_sub_le (u r₀ + A r₀) (u r₀ - u 0 + ((A r₀ : ℂ) - A 0)),
      norm_add_le (u r₀) (A r₀ : ℂ)]

/-- Forward hulls at positive times are nonempty: otherwise `fwdMap A s` would be a holomorphic
self-map of `ℍ` inverted by a reverse flow, hence at bounded distance from the identity, so it
could not raise imaginary parts strictly (Phragmén–Lindelöf, `ArcDriver.im_le_im_of_bounded`). -/
theorem fwdHull_nonempty {A : ℝ → ℝ} (hA : Continuous A) (hA0 : A 0 = 0) {s : ℝ} (hs : 0 < s) :
    (fwdHull A s).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hW'c : Continuous (ArcDriver.trev A s) := ArcDriver.continuous_trev hA s
  have hdiff : ∀ w ∈ H, w ∈ H \ fwdHull A s := fun w hw => ⟨hw, by rw [hne]; exact fun h => h⟩
  have hspec := fun w (hw : w ∈ H) => ArcDriver.fwdMap_trev_spec hA hA0 hs (hdiff w hw)
  have hd : DifferentiableOn ℂ (fwdMap A s) H := by
    have := FwdHolo.differentiableOn_fwdMap (W := A) hA hs.le
    rwa [hne, Set.sdiff_empty] at this
  have hmaps : Set.MapsTo (fwdMap A s) H H := fun w hw => (hspec w hw).1
  obtain ⟨C, hC⟩ := exists_bound_revMap_sub_self hW'c hs
  have hbd : ∀ w ∈ H, ‖fwdMap A s w - w‖ ≤ C := fun w hw => by
    have := hC _ (hspec w hw).1
    rw [(hspec w hw).2, norm_sub_rev] at this
    exact this
  have hI : Complex.I ∈ H := by show (0 : ℝ) < Complex.I.im; simp
  have him := ArcDriver.im_le_im_of_bounded hd hmaps hbd hI
  have hz : fwdMap A s Complex.I ∈ H := hmaps hI
  have hrev := (hspec _ hI).2
  have hmono : (revMap (ArcDriver.trev A s) 0 (fwdMap A s Complex.I)).im <
      (revMap (ArcDriver.trev A s) s (fwdMap A s Complex.I)).im :=
    LoewnerAlgebra.strictMonoOn_im_revMap (ArcDriver.trev A s) hW'c _ hz
      (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs.le) hs
  have h0 : revMap (ArcDriver.trev A s) 0 (fwdMap A s Complex.I) = fwdMap A s Complex.I := by
    obtain ⟨u, hu⟩ := exists_isReverseSol _ hW'c _ hz 0 le_rfl
    rw [revMap_eq _ hW'c _ le_rfl le_rfl hu, (hu.2 0 ⟨le_rfl, le_rfl⟩).2]
    simp [ArcDriver.trev_zero]
  rw [h0, hrev] at hmono
  linarith

/-! ### RZ -/

/-- **RZ.** The driver's start `0` lies in the closure of every reverse hull at a positive time
(blueprint EXT_CA node RZ; hull radius from Lawler, *Conformally Invariant Processes in the
Plane*, Lemma 4.12, p. 80). -/
theorem zero_mem_closure_revHull {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 < t) : (0 : ℂ) ∈ closure (revHull W t) := by
  rw [LoewnerAlgebra.revHull_eq_fwdHull_timeRev W hW hW0 ht, Metric.mem_closure_iff]
  intro ε hε
  have hV : Continuous (fun r => W (t - r) - W t) := by fun_prop
  have hV0 : (fun r => W (t - r) - W t) 0 = 0 := by simp
  obtain ⟨η, hη, hηV⟩ := Metric.continuous_iff.1 hV 0 (ε / 4) (by positivity)
  obtain ⟨s, hsdef⟩ : ∃ s, s = min t (min (η / 2) ((ε / 12) ^ 2)) := ⟨_, rfl⟩
  have hs : 0 < s := hsdef ▸ lt_min ht (lt_min (by positivity) (by positivity))
  have hst : s ≤ t := hsdef ▸ min_le_left _ _
  have hsη : s < η := by
    rw [hsdef]
    exact (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hsq : Real.sqrt s ≤ ε / 12 := by
    calc Real.sqrt s ≤ Real.sqrt ((ε / 12) ^ 2) :=
          Real.sqrt_le_sqrt (hsdef ▸ (min_le_right _ _).trans (min_le_right _ _))
      _ = ε / 12 := Real.sqrt_sq (by positivity)
  have hM : ∀ r ∈ Icc (0 : ℝ) s, |(fun r => W (t - r) - W t) r| ≤ ε / 4 := by
    intro r hr
    have := hηV r (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]; linarith [hr.2])
    rw [Real.dist_eq, sub_zero, sub_self, sub_zero] at this
    exact this.le
  obtain ⟨z, hz⟩ := fwdHull_nonempty hV hV0 hs
  refine ⟨z, fwdHull_mono.1 hst hz, ?_⟩
  have hb := fwdHull_subset_closedBall hV hs hM hz
  rw [Metric.mem_closedBall, dist_zero_right] at hb
  rw [dist_comm, dist_zero_right]
  linarith

/-! ### R2: the bounded model -/

/-- **R2(b).** `revMap W T z → ∞` as `z → ∞` in `ℍ`. -/
theorem tendsto_revMap_cobounded {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T) :
    Tendsto (revMap W T) (Bornology.cobounded ℂ ⊓ Filter.principal H)
      (Bornology.cobounded ℂ) := by
  obtain ⟨C, hC⟩ := exists_bound_revMap_sub_self hW hT
  rw [← tendsto_norm_atTop_iff_cobounded]
  have h1 : Tendsto (fun z : ℂ => ‖z‖ + -C) (Bornology.cobounded ℂ ⊓ Filter.principal H)
      atTop :=
    tendsto_atTop_add_const_right _ (-C) (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [mem_inf_of_right (mem_principal_self H)] with z hz
  have h2 := hC z hz
  have h3 := norm_sub_norm_le z (revMap W T z)
  rw [norm_sub_rev] at h3
  linarith

/-- **R2(c).** `revMap W T` is bounded on bounded subsets of `ℍ`. -/
theorem isBounded_image_revMap {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    {B : Set ℂ} (hB : Bornology.IsBounded B) :
    Bornology.IsBounded (revMap W T '' (B ∩ H)) := by
  obtain ⟨C, hC⟩ := exists_bound_revMap_sub_self hW hT
  obtain ⟨R, hR⟩ := hB.subset_closedBall 0
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R + C)).subset ?_
  rintro _ ⟨z, ⟨hzB, hzH⟩, rfl⟩
  have h1 := hR hzB
  rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
  linarith [hC z hzH, norm_sub_norm_le (revMap W T z) z]

/-- **R2(d).** `revMap W T` is a bijection `ℍ → ℍ \ K_T`. -/
theorem bijOn_revMap_revHull {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    Set.BijOn (revMap W T) H (H \ revHull W T) := by
  refine ⟨fun z hz => ⟨?_, fun h => h.2 ⟨z, hz, rfl⟩⟩, injOn_revMap W hW hT, fun w hw => ?_⟩
  · show (0 : ℝ) < (revMap W T z).im
    exact lt_of_lt_of_le (show (0 : ℝ) < z.im from hz) (im_le_im_revMap W hW z hz hT)
  · by_contra h
    exact hw.2 ⟨hw.1, h⟩

end CaraR

end QuantumZipper
