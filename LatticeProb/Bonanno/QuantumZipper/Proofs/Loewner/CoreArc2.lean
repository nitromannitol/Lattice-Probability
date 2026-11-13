/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CoreArc2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CoreArc1
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
# CORE_ARC, part 2: no floating piece, and hulls of an arc are initial subarcs

Plan nodes NF and CORE of `blueprint/CORE_ARC_PLAN.md`.

* `no_floating_piece` (NF). A forward hull `K_r` has no floating piece: there are no nonempty
  compact `Q ⊆ K_r` and open `V ⊇ Q` with `closure V` compact, `closure V ⊆ ℍ` and
  `closure V ∩ K_r ⊆ Q`.
  ```
  theorem no_floating_piece {A : ℝ → ℝ} (hA : Continuous A) {r : ℝ} (hr : 0 ≤ r)
      {Q V : Set ℂ} (hQK : Q ⊆ fwdHull A r) (hQc : IsCompact Q) (hQne : Q.Nonempty)
      (hV : IsOpen V) (hQV : Q ⊆ V) (hVc : IsCompact (closure V)) (hVH : closure V ⊆ H)
      (hVK : closure V ∩ fwdHull A r ⊆ Q) : False
  ```
* `mem_fwdHull_of_lt` (CORE, down-closure) and `fwdHull_eq_image_Ioc_arcTime` (CORE): if
  `K_T = γ(0,1]` for a curve `γ` continuous and injective on `[0,1]`, then for `r ∈ [0,T]`
  ```
  fwdHull A r = γ '' Ioc 0 (arcTime A γ r),   arcTime A γ r ∈ Icc 0 1,
  ```
  where `arcTime A γ r = sSup {u ∈ (0,1] | γ u ∈ K_r}`.

## Proof of NF (following the plan)

Let `q₀ ∈ Q` minimise the swallowing time over `Q` (it is lower semicontinuous because
`ℍ \ K_t` is open). The compact set `∂V = closure V \ V` misses `K_r`, so `Im f_s ≥ m > 0`
on `∂V` for all `s ≤ r` (T3). A swallowed point comes close to the driver (T2): there is
`s < σ(q₀)` with `|f_s q₀| < m`. By minimality `closure V ⊆ ℍ \ K_s`, where `f_s` is
holomorphic, injective with nonzero derivative, hence open (inverse function theorem). The
half disk `D = ℍ ∩ B(0,m)` is connected, meets the open set `f_s(V)` at `f_s q₀`, and
`closure f_s(V) ∩ D ⊆ f_s(closure V) ∩ D ⊆ f_s(V)` since `|f_s| ≥ m` on `∂V`. So
`D ⊆ f_s(V)`, which contradicts `Im f_s ≥ c > 0` on the compact set `closure V`.

## Proof of CORE from NF

If `v < u`, `γ u ∈ K_r`, `γ v ∉ K_r`, then `Q = K_r ∩ γ[v,1]` is a floating piece, with
`V` a small open thickening of `Q` (away from `ℝ` and from the compact `γ[0,v]`, which is
disjoint from `Q` by injectivity). So `{u ∈ (0,1] | γ u ∈ K_r}` is down-closed; it contains its
supremum because `ℍ \ K_r` is open.

## Sources

The route is the project's own (`blueprint/CORE_ARC_PLAN.md`), chosen to avoid the Jordan
curve theorem; it uses only compactness, connectedness of a half disk, and the open mapping
property of `f_s` (inverse function theorem). The classical converse statement (hulls of a
simple curve are its initial arcs) is in Lawler, *Conformally Invariant Processes in the Plane*,
§4.4, p. 86 (PDF p. 96); Lawler gives no proof of the direction proved here, so the argument
is the plan's own.
-/

noncomputable section

open Set Filter Topology Metric

namespace QuantumZipper

namespace CoreArc

theorem isOpen_H_coreArc : IsOpen H := isOpen_lt continuous_const Complex.continuous_im

theorem fwdHull_mono_coreArc {A : ℝ → ℝ} {s r : ℝ} (hsr : s ≤ r) :
    fwdHull A s ⊆ fwdHull A r := fun _ hz =>
  ⟨hz.1, hz.2.trans (ENNReal.ofReal_le_ofReal hsr)⟩

/-- The swallowing time is lower semicontinuous on `ℍ`. -/
theorem lowerSemicontinuousOn_swallowTime {A : ℝ → ℝ} (hA : Continuous A) {S : Set ℂ}
    (hS : S ⊆ H) : LowerSemicontinuousOn (swallowTime A) S := by
  intro z hz y hy
  obtain ⟨t, ht, hyt, hts⟩ := ENNReal.lt_iff_exists_real_btwn.1 hy
  have hzO : z ∈ H \ fwdHull A t := ⟨hS hz, fun hK => (not_le.2 hts) hK.2⟩
  have hO := (FwdHolo.isOpen_compl_fwdHull hA ht).mem_nhds hzO
  filter_upwards [nhdsWithin_le_nhds hO] with w hw
  exact hyt.trans (not_le.1 fun h => hw.2 ⟨hw.1, h⟩)

/-- `f_s` maps open subsets of `ℍ \ K_s` to open sets. -/
theorem isOpen_image_fwdMap {A : ℝ → ℝ} (hA : Continuous A) {s : ℝ} (hs : 0 ≤ s) {V : Set ℂ}
    (hV : IsOpen V) (hVs : V ⊆ H \ fwdHull A s) : IsOpen (fwdMap A s '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨v, hv, rfl⟩
  have hO := (FwdHolo.isOpen_compl_fwdHull hA hs).mem_nhds (hVs hv)
  have han := (FwdHolo.differentiableOn_fwdMap hA hs).analyticAt hO
  have hstrict := han.hasStrictDerivAt
  rw [← hstrict.map_nhds_eq (FwdHolo.deriv_fwdMap_ne_zero hA hs (hVs hv))]
  exact image_mem_map (hV.mem_nhds hv)

/-- **NF: no floating piece.** -/
theorem no_floating_piece {A : ℝ → ℝ} (hA : Continuous A) {r : ℝ} (hr : 0 ≤ r)
    {Q V : Set ℂ} (hQK : Q ⊆ fwdHull A r) (hQc : IsCompact Q) (hQne : Q.Nonempty)
    (hV : IsOpen V) (hQV : Q ⊆ V) (hVc : IsCompact (closure V)) (hVH : closure V ⊆ H)
    (hVK : closure V ∩ fwdHull A r ⊆ Q) : False := by
  -- the first swallowed point of `Q`
  obtain ⟨q₀, hq₀, hmin⟩ := (lowerSemicontinuousOn_swallowTime hA
    (fun z hz => (hQK hz).1)).exists_isMinOn hQne hQc
  have hq₀r : swallowTime A q₀ ≤ ENNReal.ofReal r := (hQK hq₀).2
  have hfin : swallowTime A q₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hq₀r
  set σ₀ := (swallowTime A q₀).toReal with hσ₀
  have hσe : swallowTime A q₀ = ENNReal.ofReal σ₀ := (ENNReal.ofReal_toReal hfin).symm
  have hσr : σ₀ ≤ r := ENNReal.toReal_le_of_le_ofReal hr hq₀r
  have hq₀K : q₀ ∈ fwdHull A σ₀ := ⟨(hQK hq₀).1, hσe.le⟩
  -- the boundary of `V`
  have hbdc : IsCompact (closure V \ V) := hVc.diff hV
  have hbdK : closure V \ V ⊆ H \ fwdHull A r := fun z hz =>
    ⟨hVH hz.1, fun hK => hz.2 (hQV (hVK ⟨hz.1, hK⟩))⟩
  obtain ⟨m, hm, hmbd⟩ := exists_im_lower_of_isCompact hA hr hbdc hbdK
  obtain ⟨s, hs, hq₀s, hsm⟩ :=
    exists_small_of_mem_fwdHull hA (hQK hq₀).1 ENNReal.toReal_nonneg hq₀K hm
  have hsr : s ≤ r := hs.2.le.trans hσr
  -- `closure V` is not yet swallowed at time `s`
  have hVs : closure V ⊆ H \ fwdHull A s := by
    intro z hz
    refine ⟨hVH hz, fun hK => ?_⟩
    have hzQ : z ∈ Q := hVK ⟨hz, fwdHull_mono_coreArc hsr hK⟩
    have h1 : swallowTime A q₀ ≤ ENNReal.ofReal s := (hmin hzQ).trans hK.2
    rw [hσe] at h1
    exact (not_le.2 hs.2) ((ENNReal.ofReal_le_ofReal_iff hs.1).1 h1)
  set f := fwdMap A s with hf
  have hcont : ContinuousOn f (closure V) :=
    (FwdHolo.differentiableOn_fwdMap hA hs.1).continuousOn.mono hVs
  have hfH : ∀ z ∈ closure V, 0 < (f z).im := fun z hz =>
    FwdHolo.mapsTo_fwdMap hA hs.1 (hVs hz)
  -- lower bound `c` for `Im f` on `closure V`
  obtain ⟨p, hp, hpmin⟩ := hVc.exists_isMinOn ⟨q₀, subset_closure (hQV hq₀)⟩
    (Complex.continuous_im.comp_continuousOn hcont)
  set c := (f p).im with hc
  have hcpos : 0 < c := hfH p hp
  -- the half disk lies in `f(V)`
  set D : Set ℂ := H ∩ ball 0 m with hD
  have hDpre : IsPreconnected D :=
    ((convex_halfSpace_im_gt (r := 0)).inter (convex_ball 0 m)).isPreconnected
  have hWo : IsOpen (f '' V) :=
    isOpen_image_fwdMap hA hs.1 hV (subset_closure.trans hVs)
  have hq₀D : f q₀ ∈ D ∩ f '' V :=
    ⟨⟨hfH q₀ (subset_closure (hQV hq₀)), by simpa [mem_ball, dist_zero_right] using hsm⟩,
      q₀, hQV hq₀, rfl⟩
  have hclos : closure (f '' V) ∩ D ⊆ f '' V := by
    rintro w ⟨hw, hwD⟩
    have hsub : closure (f '' V) ⊆ f '' closure V :=
      closure_minimal (image_mono subset_closure) (hVc.image_of_continuousOn hcont).isClosed
    obtain ⟨v, hv, rfl⟩ := hsub hw
    by_cases hvV : v ∈ V
    · exact ⟨v, hvV, rfl⟩
    · exfalso
      have h1 := hmbd v ⟨hv, hvV⟩ s ⟨hs.1, hsr⟩
      have h2 : ‖f v‖ < m := by simpa [D, mem_ball, dist_zero_right] using hwD.2
      have h3 := Complex.abs_im_le_norm (f v)
      rw [abs_of_pos (hfH v hv)] at h3
      linarith
  have hDW := hDpre.subset_of_closure_inter_subset hWo ⟨f q₀, hq₀D.1, hq₀D.2⟩ hclos
  -- a point of `D` with small imaginary part
  set a := min m c / 2 with ha
  have hapos : 0 < a := by positivity
  have ham : a < m := by
    have := min_le_left m c
    linarith
  have hac : a < c := by
    have := min_le_right m c
    linarith
  have hwD : Complex.I * (a : ℂ) ∈ D := by
    refine ⟨show 0 < (Complex.I * (a : ℂ)).im by simpa using hapos, ?_⟩
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hapos]
    exact ham
  obtain ⟨v, hv, hfv⟩ := hDW hwD
  have h1 : c ≤ (f v).im := hpmin (subset_closure hv)
  rw [hfv] at h1
  simp at h1
  linarith

/-! ### CORE from NF -/

/-- The parameter of the tip of the hull `K_r` along the arc `γ`. -/
def arcTime (A : ℝ → ℝ) (γ : ℝ → ℂ) (r : ℝ) : ℝ :=
  sSup {u ∈ Ioc (0 : ℝ) 1 | γ u ∈ fwdHull A r}

section Core

variable {A : ℝ → ℝ} {T r : ℝ} {γ : ℝ → ℂ}

/-- **CORE, down-closure.** If `K_T = γ(0,1]`, then `{u ∈ (0,1] | γ u ∈ K_r}` is down-closed. -/
theorem mem_fwdHull_of_lt (hA : Continuous A) (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1)) (hK : fwdHull A T = γ '' Ioc 0 1) (hr : 0 ≤ r) (hrT : r ≤ T)
    {u v : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) (huK : γ u ∈ fwdHull A r) (hv : 0 < v) (hvu : v < u) :
    γ v ∈ fwdHull A r := by
  by_contra hvK
  have hKT : fwdHull A r ⊆ γ '' Ioc 0 1 := hK ▸ fwdHull_mono_coreArc hrT
  set C := γ '' Icc v 1 with hC
  set L := γ '' Icc 0 v with hL
  set Q := fwdHull A r ∩ C with hQ
  have hCc : IsCompact C := isCompact_Icc.image_of_continuousOn
    (hγc.mono (Icc_subset_Icc_left hv.le))
  have hLc : IsCompact L := isCompact_Icc.image_of_continuousOn
    (hγc.mono (Icc_subset_Icc_right (hvu.le.trans hu.2)))
  have hCH : C ⊆ H := by
    rintro _ ⟨w, hw, rfl⟩
    have : γ w ∈ fwdHull A T := hK ▸ ⟨w, ⟨hv.trans_le hw.1, hw.2⟩, rfl⟩
    exact this.1
  have hQc : IsCompact Q := by
    have e : Q = C ∩ (H \ fwdHull A r)ᶜ := by
      ext z
      constructor
      · rintro ⟨hzK, hzC⟩
        exact ⟨hzC, fun hz => hz.2 hzK⟩
      · rintro ⟨hzC, hz⟩
        by_contra hzK
        exact hz ⟨hCH hzC, fun h => hzK ⟨h, hzC⟩⟩
    rw [e]
    exact hCc.inter_right (FwdHolo.isOpen_compl_fwdHull hA hr).isClosed_compl
  have hQne : Q.Nonempty := ⟨γ u, huK, u, ⟨hvu.le, hu.2⟩, rfl⟩
  have hQO : Q ⊆ H ∩ Lᶜ := by
    rintro z ⟨hzK, w, hw, rfl⟩
    refine ⟨hzK.1, ?_⟩
    rintro ⟨w', hw', hww⟩
    have hvu1 : v ≤ 1 := hvu.le.trans hu.2
    have e := hγi ⟨hw'.1, hw'.2.trans hvu1⟩ ⟨hv.le.trans hw.1, hw.2⟩ hww
    have hwv : w = v := le_antisymm (e ▸ hw'.2) hw.1
    exact hvK (hwv ▸ hzK)
  obtain ⟨δ, hδ, hδO⟩ := hQc.exists_cthickening_subset_open
    (isOpen_H_coreArc.inter hLc.isClosed.isOpen_compl) hQO
  have hVcl : closure (thickening δ Q) ⊆ H ∩ Lᶜ :=
    (closure_thickening_subset_cthickening δ Q).trans hδO
  refine no_floating_piece hA hr inter_subset_left hQc hQne isOpen_thickening
    (self_subset_thickening hδ Q)
    (hQc.cthickening.of_isClosed_subset isClosed_closure
      (closure_thickening_subset_cthickening δ Q))
    (hVcl.trans inter_subset_left) ?_
  rintro z ⟨hz, hzK⟩
  refine ⟨hzK, ?_⟩
  obtain ⟨w, hw, rfl⟩ := hKT hzK
  rcases le_or_gt v w with hvw | hwv
  · exact ⟨w, ⟨hvw, hw.2⟩, rfl⟩
  · exact absurd ⟨w, ⟨hw.1.le, hwv.le⟩, rfl⟩ (hVcl hz).2

theorem arcTime_mem_Icc : arcTime A γ r ∈ Icc (0 : ℝ) 1 := by
  set I := {u ∈ Ioc (0 : ℝ) 1 | γ u ∈ fwdHull A r}
  rcases I.eq_empty_or_nonempty with hI | hI
  · simp only [arcTime]
    rw [show {u ∈ Ioc (0 : ℝ) 1 | γ u ∈ fwdHull A r} = I from rfl, hI, Real.sSup_empty]
    exact ⟨le_rfl, zero_le_one⟩
  · obtain ⟨u, hu⟩ := hI
    have hbdd : BddAbove I := ⟨1, fun x hx => hx.1.2⟩
    exact ⟨hu.1.1.le.trans (le_csSup hbdd hu), csSup_le ⟨u, hu⟩ fun x hx => hx.1.2⟩

/-- **CORE.** If `K_T = γ(0,1]` for a curve `γ` continuous and injective on `[0,1]`, then every
hull `K_r`, `r ∈ [0,T]`, is the initial subarc `γ(0, arcTime A γ r]`. -/
theorem fwdHull_eq_image_Ioc_arcTime (hA : Continuous A) (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1)) (hK : fwdHull A T = γ '' Ioc 0 1) (hr : 0 ≤ r) (hrT : r ≤ T) :
    fwdHull A r = γ '' Ioc 0 (arcTime A γ r) := by
  have hKT : fwdHull A r ⊆ γ '' Ioc 0 1 := hK ▸ fwdHull_mono_coreArc hrT
  set I := {u ∈ Ioc (0 : ℝ) 1 | γ u ∈ fwdHull A r} with hIdef
  have hτ : arcTime A γ r = sSup I := rfl
  have hbdd : BddAbove I := ⟨1, fun x hx => hx.1.2⟩
  rcases I.eq_empty_or_nonempty with hI | hIne
  · rw [hτ, hI, Real.sSup_empty, Ioc_self, image_empty]
    refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨w, hw, rfl⟩ := hKT hz
    exact (hI ▸ (⟨hw, hz⟩ : w ∈ I) : w ∈ (∅ : Set ℝ))
  set τ := sSup I with hτdef
  -- every `u ∈ (0, τ)` lies in `I`
  have hbelow : ∀ w, 0 < w → w < τ → w ∈ I := by
    intro w hw hwτ
    obtain ⟨u, hu, hwu⟩ := exists_lt_of_lt_csSup hIne hwτ
    exact ⟨⟨hw, hwu.le.trans hu.1.2⟩, mem_fwdHull_of_lt hA hγc hγi hK hr hrT hu.1 hu.2 hw hwu⟩
  obtain ⟨u₀, hu₀⟩ := hIne
  have hτpos : 0 < τ := hu₀.1.1.trans_le (le_csSup hbdd hu₀)
  have hτ1 : τ ≤ 1 := csSup_le ⟨u₀, hu₀⟩ fun x hx => hx.1.2
  -- `τ ∈ I`
  have hτI : τ ∈ I := by
    refine ⟨⟨hτpos, hτ1⟩, ?_⟩
    by_contra hnot
    have hγτH : γ τ ∈ H := by
      have : γ τ ∈ fwdHull A T := hK ▸ ⟨τ, ⟨hτpos, hτ1⟩, rfl⟩
      exact this.1
    have hO := (FwdHolo.isOpen_compl_fwdHull hA hr).mem_nhds ⟨hγτH, hnot⟩
    have hpre := hγc τ ⟨hτpos.le, hτ1⟩ hO
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
    set w := max (τ / 2) (τ - ε / 2) with hw
    have hwpos : 0 < w := lt_max_of_lt_left (by linarith)
    have hwτ : w < τ := max_lt (by linarith) (by linarith)
    have hwI := hbelow w hwpos hwτ
    have hwd : w ∈ ball τ ε := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor
      · linarith [le_max_right (τ / 2) (τ - ε / 2)]
      · linarith
    exact (hball ⟨hwd, hwpos.le, hwτ.le.trans hτ1⟩).2 hwI.2
  rw [hτ]
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := hKT hz
    exact ⟨w, ⟨hw.1, le_csSup hbdd ⟨hw, hz⟩⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    rcases hw.2.lt_or_eq with hlt | heq
    · exact (hbelow w hw.1 hlt).2
    · exact heq ▸ hτI.2

end Core

end CoreArc

end QuantumZipper
