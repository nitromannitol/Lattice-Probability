/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.HullBasics at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CoreArc1
import Mathlib.Analysis.ODE.Gronwall

/-!
# EXT-RS tool nodes D4, D5, D6: basic facts on forward hulls

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §2, nodes **D4**, **D5**, **D6**. Notation:
`f_t := fwdMap W t`, `K_t := fwdHull W t`, `H_t := H \ K_t`.

## Main results (exact statements)

* **D4** (`tendsto_im_fwdMap_hull`). For continuous `W`, `0 ≤ s` and
  `p ∈ fwdHull W s ∨ p.im = 0`:
  `Tendsto (fun z => (fwdMap W s z).im) (𝓝[H \ fwdHull W s] p) (𝓝 0)`.
  Lit: A. Kemppainen, *Schramm–Loewner Evolution* (SpringerBriefs 2017), proof of
  Proposition 4.1 (p. 62): a point of the hull is reached when `Im g_t − …` degenerates, and
  `Im` decreases along the flow. Proof here: a point `p ∈ K_s` has an earlier time `t < s` at
  which it is alive and `|f_t p|` is small (`CoreArc.exists_small_of_mem_fwdHull`, i.e. FD-2);
  `f_t` is continuous at `p` (`FwdHolo.fwdMap_local`), and `Im f_s ≤ Im f_t` on `H_s`
  (`im_isForwardSol_le`). For real `p`, `0 < Im f_s z ≤ Im z`.
* **D5** (`exists_ball_fwdMap_near_sol`, `fwdFlow_near_alive_real`). If
  `IsForwardSol W x T v` with `0 ≤ T` (any `x : ℂ`, in particular `x` real), there are
  `r > 0`, `C ≥ 0` with `ball x r ∩ H ⊆ H \ fwdHull W T` and
  `‖fwdMap W t w − v t‖ ≤ ‖w − x‖ * C` for `w ∈ ball x r ∩ H`, `t ∈ [0,T]`; hence
  `Tendsto (fwdMap W T) (𝓝[H] x) (𝓝 (v T))` and `v T ≠ 0`.
  `fwdFlow_near_alive_real` is the blueprint form for `x : ℝ`:
  `(∃ r > 0, ball (x : ℂ) r ∩ H ⊆ H \ fwdHull W T) ∧
    Tendsto (fwdMap W T) (𝓝[H] (x : ℂ)) (𝓝 (v T)) ∧ v T ≠ 0`.
  Lit: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), proof of
  Lemma 6.2, last paragraph (p. 24 of arXiv math/0106036): the flow from a real point that is not
  swallowed by time `T` controls the flow of nearby points of `ℍ`. Proof here: Grönwall
  (`dist_le_of_trajectories_ODE_of_mem`) for the field `y ↦ 2/(y − W t)`, Lipschitz with
  constant `2/c²` on `{‖y − W t‖ ≥ c}`, plus a first-exit-time argument, plus
  `CoreArc.exists_small_of_mem_fwdHull` to exclude swallowing. `fwd_perturb` itself needs
  `0 < Im x`, so it is not used; its proof is the model.
* **D6** (`not_fwdHull_subset`, `fwdHull_ssubset`, `fwdHull_nonempty_of_pos`). For continuous
  `W` with `W 0 = 0` and `0 ≤ t₁ < t₂`: `¬ fwdHull W t₂ ⊆ fwdHull W t₁`, so
  `fwdHull W t₁ ⊂ fwdHull W t₂`; and `(fwdHull W t).Nonempty` for `t > 0`.
  Lit: Kemppainen, Lemma 4.2 (p. 51): `hcap K = 0` only for `K = ∅`. Proof here: nonemptiness is
  the Phragmén–Lindelöf argument of `CaraR.fwdHull_nonempty` (CaraRZ.lean, not yet built; the
  proof is repeated with the uniform bound `CoreArc.norm_revMap_sub_le` in place of CaraRZ's
  `exists_bound_revMap_sub_self`): with `K_s = ∅`, `f_s` is a holomorphic self-map of `ℍ` at
  bounded distance from the identity, so `Im f_s ≥ Im` (`ArcDriver.im_le_im_of_bounded`), while
  the reverse flow inverting it raises `Im` strictly. Strict growth for `t₁ > 0` then follows
  from the domain Markov property `fwdHull_add_diff` and surjectivity of `f_{t₁} : H_{t₁} → ℍ`
  (`ArcDriver.revMap_trev_spec`) applied to a point of the (nonempty) hull of the shifted
  driver. This replaces the blueprint's route (equal hulls ⇒ `f_{t₂} ∘ f̂_{t₁}` is a
  translation ⇒ contradiction with the clock); both rest on the same Phragmén–Lindelöf lemma.
-/

noncomputable section

open Set Filter Topology Metric

namespace QuantumZipper

namespace RS

variable {W : ℝ → ℝ}

/-! ### Monotonicity of `Im` along the flow -/

/-- On `H_s`, `Im f_s ≤ Im f_t` for `0 ≤ t ≤ s`, and `Im f_s > 0`. -/
theorem im_fwdMap_le_of_le (hW : Continuous W) {s t : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) {z : ℂ}
    (hz : z ∈ H \ fwdHull W s) :
    (fwdMap W s z).im ≤ (fwdMap W t z).im ∧ 0 < (fwdMap W s z).im := by
  obtain ⟨hz0, T', hT', u, hu⟩ := (FwdHolo.mem_compl_fwdHull_iff (ht.trans hts)).mp hz
  have hmt : t ∈ Icc (0 : ℝ) T' := ⟨ht, hts.trans hT'.le⟩
  have hms : s ∈ Icc (0 : ℝ) T' := ⟨ht.trans hts, hT'.le⟩
  rw [fwdMap_eq hW hz0 hu hms, fwdMap_eq hW hz0 hu hmt]
  obtain ⟨hanti, hpos⟩ := im_isForwardSol_le hW hz0 hu
  exact ⟨hanti hmt hms hts, hpos s hms⟩

/-- On `H_s`, `Im f_s z ≤ Im z`. -/
theorem im_fwdMap_le_im (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : z ∈ H \ fwdHull W s) : (fwdMap W s z).im ≤ z.im := by
  have h := (im_fwdMap_le_of_le hW le_rfl hs hz).1
  obtain ⟨hz0, T', hT', u, hu⟩ := (FwdHolo.mem_compl_fwdHull_iff hs).mp hz
  have h0 : fwdMap W 0 z = z - (W 0 : ℂ) := by
    rw [fwdMap_eq hW hz0 hu ⟨le_rfl, hs.trans hT'.le⟩,
      FwdHolo.sol_zero hu (hs.trans hT'.le)]
  rw [h0] at h
  simpa using h

/-! ### D4 -/

/-- **D4.** `Im f_s z → 0` as `z → p` in `H_s`, for `p ∈ K_s` or `p` real. -/
theorem tendsto_im_fwdMap_hull (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s) {p : ℂ}
    (hp : p ∈ fwdHull W s ∨ p.im = 0) :
    Tendsto (fun z => (fwdMap W s z).im) (𝓝[H \ fwdHull W s] p) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rcases hp with hpK | hp0
  · obtain ⟨t, ht, hpt, hsmall⟩ :=
      CoreArc.exists_small_of_mem_fwdHull hW hpK.1 hs hpK (m := ε / 2) (by positivity)
    obtain ⟨m, -, C, hC, η, hη, hloc⟩ := FwdHolo.fwdMap_local hW ht.1 ⟨hpK.1, hpt⟩
    refine ⟨min η (ε / 2 / (C + 1)), by positivity, fun z hz hzp => ?_⟩
    rw [Complex.dist_eq] at hzp
    have h1 : ‖z - p‖ < η := hzp.trans_le (min_le_left _ _)
    have h2 : ‖z - p‖ < ε / 2 / (C + 1) := hzp.trans_le (min_le_right _ _)
    obtain ⟨-, hb⟩ := hloc z h1
    have hb' := (hb t ⟨ht.1, le_rfl⟩).1
    obtain ⟨hmono, hpos⟩ := im_fwdMap_le_of_le hW ht.1 ht.2.le hz
    have h3 : ‖z - p‖ * C ≤ ε / 2 := by
      calc ‖z - p‖ * C ≤ ‖z - p‖ * (C + 1) := by nlinarith [norm_nonneg (z - p)]
        _ ≤ ε / 2 / (C + 1) * (C + 1) := by gcongr
        _ = ε / 2 := by field_simp
    have h4 : (fwdMap W t z).im ≤ (fwdMap W t p).im + ‖fwdMap W t z - fwdMap W t p‖ := by
      have := Complex.abs_im_le_norm (fwdMap W t z - fwdMap W t p)
      rw [Complex.sub_im] at this
      linarith [le_abs_self ((fwdMap W t z).im - (fwdMap W t p).im)]
    have h5 : (fwdMap W t p).im < ε / 2 :=
      ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans_lt hsmall
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    linarith
  · refine ⟨ε, hε, fun z hz hzp => ?_⟩
    have h1 := im_fwdMap_le_im hW hs hz
    have hpos := (im_fwdMap_le_of_le hW hs le_rfl hz).2
    have h2 : z.im ≤ ‖z - p‖ := by
      have := (le_abs_self _).trans (Complex.abs_im_le_norm (z - p))
      rwa [Complex.sub_im, hp0, sub_zero] at this
    rw [Complex.dist_eq] at hzp
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    linarith

/-! ### D5 -/

/-- The Loewner field `y ↦ 2/(y − W t)` is `2/c²`-Lipschitz on `{‖y − W t‖ ≥ c}`. -/
theorem lipschitzOnWith_loewnerField {c : ℝ} (hc : 0 < c) (t : ℝ) :
    LipschitzOnWith (Real.toNNReal (2 / c ^ 2)) (fun y : ℂ => 2 / (y - (W t : ℂ)))
      {y : ℂ | c ≤ ‖y - (W t : ℂ)‖} := by
  apply LipschitzOnWith.of_dist_le'
  intro a ha b hb
  have ha' : c ≤ ‖a - (W t : ℂ)‖ := ha
  have hb' : c ≤ ‖b - (W t : ℂ)‖ := hb
  have ha0 : a - (W t : ℂ) ≠ 0 := by intro h; rw [h, norm_zero] at ha'; linarith
  have hb0 : b - (W t : ℂ) ≠ 0 := by intro h; rw [h, norm_zero] at hb'; linarith
  rw [Complex.dist_eq, Complex.dist_eq]
  have hrw : 2 / (a - (W t : ℂ)) - 2 / (b - (W t : ℂ)) =
      2 * (b - a) / ((a - (W t : ℂ)) * (b - (W t : ℂ))) := by
    field_simp; ring
  rw [hrw, norm_div, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num, norm_sub_rev b a]
  have hprod : c ^ 2 ≤ ‖a - (W t : ℂ)‖ * ‖b - (W t : ℂ)‖ := by nlinarith
  calc 2 * ‖a - b‖ / (‖a - (W t : ℂ)‖ * ‖b - (W t : ℂ)‖) ≤ 2 * ‖a - b‖ / c ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hprod
    _ = 2 / c ^ 2 * ‖a - b‖ := by ring

/-- **Grönwall comparison** of two forward solutions that stay at distance `≥ c` from the
driving point (Lipschitz constant `2/c²`). -/
theorem norm_sol_sub_le {x w : ℂ} {a c : ℝ} (hc : 0 < c) (ha : 0 ≤ a) {u v : ℝ → ℂ}
    (hu : IsForwardSol W w a u) (hv : IsForwardSol W x a v)
    (hu' : ∀ t ∈ Ico (0 : ℝ) a, c ≤ ‖u t‖) (hv' : ∀ t ∈ Ico (0 : ℝ) a, c ≤ ‖v t‖) :
    ∀ t ∈ Icc (0 : ℝ) a, ‖u t - v t‖ ≤ ‖w - x‖ * Real.exp (2 / c ^ 2 * t) := by
  have hIci : ∀ {z : ℂ} {g : ℝ → ℂ}, IsForwardSol W z a g → ∀ t ∈ Ico (0 : ℝ) a,
      HasDerivWithinAt (fun s => g s + (W s : ℂ))
        ((fun s (y : ℂ) => 2 / (y - (W s : ℂ))) t (g t + (W t : ℂ))) (Ici t) t := by
    intro z g hg t ht
    have := (FwdHolo.hasDerivWithinAt_shift hg (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
    simpa using this
  have hcont : ∀ {z : ℂ} {g : ℝ → ℂ}, IsForwardSol W z a g →
      ContinuousOn (fun s => g s + (W s : ℂ)) (Icc 0 a) := fun hg s hs =>
    (FwdHolo.hasDerivWithinAt_shift hg hs).continuousWithinAt
  intro t ht
  have h := dist_le_of_trajectories_ODE_of_mem (v := fun s (y : ℂ) => 2 / (y - (W s : ℂ)))
    (s := fun s => {y : ℂ | c ≤ ‖y - (W s : ℂ)‖}) (K := Real.toNNReal (2 / c ^ 2))
    (δ := ‖w - x‖)
    (fun s _ => lipschitzOnWith_loewnerField hc s) (hcont hu) (hIci hu)
    (fun s hs => by simpa using hu' s hs) (hcont hv) (hIci hv)
    (fun s hs => by simpa using hv' s hs)
    (by simp only [FwdHolo.sol_zero hu ha, FwdHolo.sol_zero hv ha, Complex.dist_eq,
      sub_add_cancel]; exact le_rfl) t ht
  rw [Complex.dist_eq, add_sub_add_right_eq_sub, Real.coe_toNNReal _ (by positivity),
    sub_zero] at h
  exact h

/-- **D5 (quantitative).** Near the start `x` of a forward solution `v` on `[0,T]`, points of
`ℍ` are not swallowed by time `T`, and their flow stays Lipschitz-close to `v`. -/
theorem exists_ball_fwdMap_near_sol (hW : Continuous W) {x : ℂ} {T : ℝ} (hT : 0 ≤ T)
    {v : ℝ → ℂ} (hv : IsForwardSol W x T v) :
    ∃ r > 0, ∃ C : ℝ, 0 ≤ C ∧ ball x r ∩ H ⊆ H \ fwdHull W T ∧
      ∀ w ∈ ball x r ∩ H, ∀ t ∈ Icc (0 : ℝ) T, ‖fwdMap W t w - v t‖ ≤ ‖w - x‖ * C := by
  -- a lower bound `δ` for `‖v‖` on `[0,T]`
  obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMinOn
    (nonempty_Icc.2 hT) hv.1.norm
  set δ := ‖v t₀‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.2 (hv.2 t₀ ht₀).1
  have hvδ : ∀ t ∈ Icc (0 : ℝ) T, δ ≤ ‖v t‖ := fun t ht => hmin ht
  set c := δ / 2 with hcdef
  have hc : 0 < c := by positivity
  set C := Real.exp (2 / c ^ 2 * T) with hCdef
  have hC1 : 1 ≤ C := Real.one_le_exp (by positivity)
  have hCpos : 0 < C := by linarith
  set r := c / C with hrdef
  have hr : 0 < r := by positivity
  have hrC : r * C = c := by rw [hrdef]; field_simp
  have hexp : ∀ t ∈ Icc (0 : ℝ) T, Real.exp (2 / c ^ 2 * t) ≤ C := fun t ht =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity))
  -- key claim: a solution from `w` near `x` stays at distance `> c` from the driver
  have key : ∀ w ∈ ball x r ∩ H, ∀ s ∈ Icc (0 : ℝ) T, ∀ u, IsForwardSol W w s u →
      ∀ t ∈ Icc (0 : ℝ) s, c < ‖u t‖ ∧ ‖u t - v t‖ ≤ ‖w - x‖ * C := by
    intro w hw s hs u hu
    have hwx : ‖w - x‖ < r := by rw [← Complex.dist_eq]; exact hw.1
    have hsmall : ‖w - x‖ * C < c := by rw [← hrC]; exact mul_lt_mul_of_pos_right hwx hCpos
    have hvs : IsForwardSol W x s v := isForwardSol_restrict hv hs.1 hs.2
    have hfar : ∀ t ∈ Icc (0 : ℝ) s, c < ‖u t‖ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨t₁, ht₁, ht₁c⟩ := hcon
      set S := Icc (0 : ℝ) s ∩ (fun q => ‖u q‖) ⁻¹' Iic c with hSdef
      have hS : IsClosed S := hu.1.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have hne : S.Nonempty := ⟨t₁, ht₁, ht₁c⟩
      have hbdd : BddBelow S := ⟨0, fun q hq => hq.1.1⟩
      have hτ : sInf S ∈ S := hS.csInf_mem hne hbdd
      set τ := sInf S with hτdef
      have hbefore : ∀ q ∈ Ico (0 : ℝ) τ, c < ‖u q‖ := by
        intro q hq
        by_contra hq'
        push Not at hq'
        have hqS : q ∈ S := ⟨⟨hq.1, hq.2.le.trans hτ.1.2⟩, hq'⟩
        exact absurd (csInf_le hbdd hqS) (not_le.2 hq.2)
      have huτ := isForwardSol_restrict hu hτ.1.1 hτ.1.2
      have hvτ := isForwardSol_restrict hvs hτ.1.1 hτ.1.2
      have hcmp := norm_sol_sub_le hc hτ.1.1 huτ hvτ (fun q hq => (hbefore q hq).le)
        (fun q hq => by
          have := hvδ q ⟨hq.1, hq.2.le.trans (hτ.1.2.trans hs.2)⟩
          linarith) τ ⟨hτ.1.1, le_rfl⟩
      have hb : ‖u τ - v τ‖ < c :=
        (hcmp.trans (mul_le_mul_of_nonneg_left (hexp τ ⟨hτ.1.1, hτ.1.2.trans hs.2⟩)
          (norm_nonneg _))).trans_lt hsmall
      have hvτδ := hvδ τ ⟨hτ.1.1, hτ.1.2.trans hs.2⟩
      have htri := norm_sub_norm_le (v τ) (v τ - u τ)
      rw [sub_sub_cancel, norm_sub_rev] at htri
      have huc : ‖u τ‖ ≤ c := hτ.2
      linarith
    intro t ht
    refine ⟨hfar t ht, ?_⟩
    have hcmp := norm_sol_sub_le hc hs.1 hu hvs (fun q hq => (hfar q (Ico_subset_Icc_self hq)).le)
      (fun q hq => by
        have := hvδ q ⟨hq.1, hq.2.le.trans hs.2⟩
        linarith) t ht
    exact hcmp.trans (mul_le_mul_of_nonneg_left (hexp t ⟨ht.1, ht.2.trans hs.2⟩)
      (norm_nonneg _))
  have hnot : ∀ w ∈ ball x r ∩ H, w ∉ fwdHull W T := by
    intro w hw hwK
    obtain ⟨s, hs, hsK, hsm⟩ := CoreArc.exists_small_of_mem_fwdHull hW hw.2 hT hwK hc
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hs.1 hw.2 hsK
    have h1 := (key w hw s ⟨hs.1, hs.2.le⟩ u hu s ⟨hs.1, le_rfl⟩).1
    rw [fwdMap_eq hW hw.2 hu ⟨hs.1, le_rfl⟩] at hsm
    linarith
  refine ⟨r, hr, C, hCpos.le, fun w hw => ⟨hw.2, hnot w hw⟩, fun w hw t ht => ?_⟩
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hT hw.2 (hnot w hw)
  rw [fwdMap_eq hW hw.2 hu ht]
  exact (key w hw T ⟨hT, le_rfl⟩ u hu t ht).2

/-- **D5 (limit form).** `f_T w → v T` as `w → x` in `ℍ`. -/
theorem tendsto_fwdMap_of_sol (hW : Continuous W) {x : ℂ} {T : ℝ} (hT : 0 ≤ T)
    {v : ℝ → ℂ} (hv : IsForwardSol W x T v) :
    Tendsto (fwdMap W T) (𝓝[H] x) (𝓝 (v T)) := by
  obtain ⟨r, hr, C, hC, -, hbd⟩ := exists_ball_fwdMap_near_sol hW hT hv
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min r (ε / (C + 1)), by positivity, fun w hw hwx => ?_⟩
  have h1 : dist w x < r := hwx.trans_le (min_le_left _ _)
  have h2 : ‖w - x‖ < ε / (C + 1) := by
    rw [← Complex.dist_eq]; exact hwx.trans_le (min_le_right _ _)
  have hb := hbd w ⟨h1, hw⟩ T ⟨hT, le_rfl⟩
  rw [Complex.dist_eq]
  calc ‖fwdMap W T w - v T‖ ≤ ‖w - x‖ * C := hb
    _ ≤ ‖w - x‖ * (C + 1) := by nlinarith [norm_nonneg (w - x)]
    _ < ε / (C + 1) * (C + 1) := mul_lt_mul_of_pos_right h2 (by linarith)
    _ = ε := by field_simp

/-- **D5 (blueprint form, real starting point).** -/
theorem fwdFlow_near_alive_real (hW : Continuous W) {x : ℝ} {T : ℝ} (hT : 0 ≤ T)
    {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) :
    (∃ r > 0, ball (x : ℂ) r ∩ H ⊆ H \ fwdHull W T) ∧
      Tendsto (fwdMap W T) (𝓝[H] (x : ℂ)) (𝓝 (v T)) ∧ v T ≠ 0 := by
  obtain ⟨r, hr, -, -, hsub, -⟩ := exists_ball_fwdMap_near_sol hW hT hv
  exact ⟨⟨r, hr, hsub⟩, tendsto_fwdMap_of_sol hW hT hv, (hv.2 T ⟨hT, le_rfl⟩).1⟩

/-! ### D6 -/

/-- Forward hulls at positive times are nonempty (the argument of `CaraR.fwdHull_nonempty`,
with `CoreArc.norm_revMap_sub_le` as the uniform bound). -/
theorem fwdHull_nonempty_of_pos {A : ℝ → ℝ} (hA : Continuous A) (hA0 : A 0 = 0) {s : ℝ}
    (hs : 0 < s) : (fwdHull A s).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hW'c : Continuous (ArcDriver.trev A s) := ArcDriver.continuous_trev hA s
  have hdiff : ∀ w ∈ H, w ∈ H \ fwdHull A s := fun w hw => ⟨hw, by rw [hne]; exact fun h => h⟩
  have hspec := fun w (hw : w ∈ H) => ArcDriver.fwdMap_trev_spec hA hA0 hs (hdiff w hw)
  have hd : DifferentiableOn ℂ (fwdMap A s) H := by
    have := FwdHolo.differentiableOn_fwdMap (W := A) hA hs.le
    rwa [hne, Set.sdiff_empty] at this
  have hmaps : Set.MapsTo (fwdMap A s) H H := fun w hw => (hspec w hw).1
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := s)).exists_bound_of_continuousOn hW'c.continuousOn
  have hbd : ∀ w ∈ H, ‖fwdMap A s w - w‖ ≤ 12 * M + 8 * Real.sqrt s := fun w hw => by
    have := CoreArc.norm_revMap_sub_le hW'c (ArcDriver.trev_zero A s) hs
      (fun r hr => by simpa [Real.norm_eq_abs] using hM r hr) (hspec w hw).1
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

/-- `K_0 = ∅`. -/
theorem fwdHull_zero_eq_empty (hW : Continuous W) : fwdHull W 0 = ∅ := by
  ext z
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨hz, hle⟩
  rw [ENNReal.ofReal_zero] at hle
  exact absurd (swallowTime_pos hW hz) (not_lt.2 hle)

/-- **D6.** Hulls grow strictly: `¬ K_{t₂} ⊆ K_{t₁}` for `0 ≤ t₁ < t₂`. -/
theorem not_fwdHull_subset (hW : Continuous W) (hW0 : W 0 = 0) {t₁ t₂ : ℝ} (h1 : 0 ≤ t₁)
    (h12 : t₁ < t₂) : ¬ fwdHull W t₂ ⊆ fwdHull W t₁ := by
  intro hsub
  rcases h1.eq_or_lt with h0 | hpos
  · subst h0
    obtain ⟨z, hz⟩ := fwdHull_nonempty_of_pos hW hW0 h12
    have := hsub hz
    rw [fwdHull_zero_eq_empty hW] at this
    exact this
  · have hW'c : Continuous (fun r => W (t₁ + r) - W t₁) := by fun_prop
    have hW'0 : (fun r => W (t₁ + r) - W t₁) 0 = 0 := by simp
    obtain ⟨w, hw⟩ := fwdHull_nonempty_of_pos hW'c hW'0 (sub_pos.2 h12)
    obtain ⟨hz, hfz⟩ := ArcDriver.revMap_trev_spec hW hW0 hpos hw.1
    have hmem : revMap (ArcDriver.trev W t₁) t₁ w ∈
        fwdHull W (t₁ + (t₂ - t₁)) \ fwdHull W t₁ := by
      rw [fwdHull_add_diff hW h1 (sub_pos.2 h12).le]
      exact ⟨hz, by rw [hfz]; exact hw⟩
    have e : t₁ + (t₂ - t₁) = t₂ := by ring
    rw [e] at hmem
    exact hmem.2 (hsub hmem.1)

/-- **D6 (strict inclusion).** -/
theorem fwdHull_ssubset (hW : Continuous W) (hW0 : W 0 = 0) {t₁ t₂ : ℝ} (h1 : 0 ≤ t₁)
    (h12 : t₁ < t₂) : fwdHull W t₁ ⊂ fwdHull W t₂ :=
  LE.le.ssubset_of_not_superset (fwdHull_mono.1 h12.le) (not_fwdHull_subset hW hW0 h1 h12)

end RS

end QuantumZipper
