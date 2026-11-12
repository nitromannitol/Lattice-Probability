/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L2_4S1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4C
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.TopoOrd

/-!
# CONF Lemma 2.4: geodesics cannot cross the geodesics to rational points (order tools)

Source: CONF = Gwynne–Miller arXiv:1905.00381, `confluence-final.tex`, proof of Lemma 2.4,
l. 557–558: "By Lemma 2.3, no `D_h`-geodesic from 0 to `y` can cross any of the `P_{q_n^-}`'s.
It follows that each such geodesic lies to the right of `P_y^-`."

"Cross" is read in the log-cover model of DEC-D (positions on positive Jordan lifts, TOPO-ORD
`DD.topoOrd`), as in CONF's own proof of Lemma 2.5 (l. 593–600).

* `ann_hyps`: the annulus `𝓑^•_s ∖ int 𝓑^•_t` satisfies the hypotheses of `TopoOrd`;
* `lift_tendsto`: positions on a positive Jordan lift depend continuously on the lifted point;
* `exists_normLift`: angle lift of a geodesic on `[t, s]` normalized at its endpoint position;
* `rat_order` (**CONF l. 557**, "no geodesic can cross `P_q`"): if a geodesic `R` ends left
  (right) of the geodesic `G` to a rational point (CONF Lemma 2.2 uniqueness), then it is left
  (right) of `G` at every level `t` — TOPO-ORD plus CONF Lemma 2.3 (`conf_L2_3_det`);
* `step_order`: order of endpoints transfers to every level for two arbitrary geodesics, through a
  geodesic to a rational point with endpoint between them (CONF's `q_n^-`, `exists_rat_near`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.CONF

section Det
variable {D : ContMetric} {z : ℂ} {s t : ℝ}

/-- `𝓑^•_t ⊆ int 𝓑^•_s` for `t < s` -/
theorem filledBall_subset_interior (hts : t < s) :
    filledBall D z t ⊆ interior (filledBall D z s) := by
  intro x hx
  rcases hx with hx | ⟨hxc, hxb⟩
  · exact GM.jb_ballM_subset_interior (D := D) (z := z) (s := s)
      (show D.1 (z, x) < s from lt_of_le_of_lt (DD.cl_closure_ballM_subset D z t hx) hts)
  · set C := connectedComponentIn (closure (ballM D z t))ᶜ x
    have hCs : C ⊆ filledBall D z s := by
      intro y hy
      by_cases hyc : y ∈ closure (ballM D z s)
      · exact Or.inl hyc
      · refine Or.inr ⟨hyc, hxb.subset ?_⟩
        show _ ⊆ connectedComponentIn (closure (ballM D z t))ᶜ x
        rw [connectedComponentIn_eq hy]
        exact connectedComponentIn_mono y
          (compl_subset_compl.2 (DD.cl_closure_ballM_mono D z hts.le))
    exact interior_maximal hCs (GM.jb_isOpen_cc (D := D) (z := z) (s := t) x) (mem_connectedComponentIn hxc)

theorem isConnected_compl_filledBall
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (s : ℝ) : IsConnected (filledBall D z s)ᶜ := by
  have hbd := isBounded_ballM_of_bc hbc z s
  refine ⟨Set.nonempty_compl.2 fun h => noncompact_univ ℂ ?_, GM.jb_isPreconnected_compl hbd⟩
  rw [← h]; exact GM.jb_isCompact_filledBall hbd

/-- the hypotheses of `TopoOrd` for `K₁ = 𝓑^•_t`, `K₂ = 𝓑^•_s` -/
theorem ann_hyps
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (ht0 : 0 < t) (hts : t < s) :
    IsCompact (filledBall D z t) ∧ IsCompact (filledBall D z s) ∧
      z ∈ interior (filledBall D z t) ∧ filledBall D z t ⊆ interior (filledBall D z s) ∧
      IsConnected (filledBall D z t)ᶜ ∧ IsConnected (filledBall D z s)ᶜ :=
  ⟨GM.jb_isCompact_filledBall (isBounded_ballM_of_bc hbc z t),
    GM.jb_isCompact_filledBall (isBounded_ballM_of_bc hbc z s),
    GM.jb_ballM_subset_interior (GM.jb_mem_ballM D z t ht0),
    filledBall_subset_interior hts, isConnected_compl_filledBall hbc t,
    isConnected_compl_filledBall hbc s⟩

end Det

/-- positions on a positive Jordan lift depend continuously on the lifted point -/
theorem lift_tendsto {Γ : Set ℂ} {z : ℂ} {φ : ℝ → ℂ} {θ : ℝ → ℝ}
    (h : DD.IsPosJordanLift Γ z φ θ) {u : ℕ → ℝ} {u₀ : ℝ}
    (h1 : Tendsto (fun n => φ (u n)) atTop (𝓝 (φ u₀)))
    (h2 : Tendsto (fun n => θ (u n)) atTop (𝓝 (θ u₀))) : Tendsto u atTop (𝓝 u₀) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpi := Real.pi_pos
  obtain ⟨δ, hδ, hθδ⟩ := Metric.continuous_iff.1 h.2.2.2.2.1 u₀ (Real.pi / 2) (by linarith)
  obtain ⟨ρ, hρ, hloc⟩ := jordan_local_inv h.1 h.2.1 h.2.2.1 u₀ (lt_min hε hδ)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 h1 ρ hρ
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 h2 (Real.pi / 2) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 := hN₁ n (le_of_max_le_left hn)
  have hn2 := hN₂ n (le_of_max_le_right hn)
  rw [dist_eq_norm] at hn1
  obtain ⟨r', hr'φ, hr'⟩ := hloc (u n) hn1
  obtain ⟨k, hk⟩ := h.phi_eq_imp hr'φ.symm
  have hθk : θ (u n) = θ r' + k * (2 * Real.pi) := by rw [hk, h.theta_add_int]
  have hr'δ := hθδ r' (by rw [Real.dist_eq]; exact lt_of_lt_of_le hr' (min_le_right _ _))
  rw [Real.dist_eq] at hr'δ hn2
  have hk0 : k = 0 := by
    have hlt : |(k : ℝ) * (2 * Real.pi)| < Real.pi := by
      have : (k : ℝ) * (2 * Real.pi) = (θ (u n) - θ u₀) - (θ r' - θ u₀) := by rw [hθk]; ring
      rw [this]
      calc |(θ (u n) - θ u₀) - (θ r' - θ u₀)| ≤ |θ (u n) - θ u₀| + |θ r' - θ u₀| := abs_sub _ _
        _ < Real.pi / 2 + Real.pi / 2 := add_lt_add hn2 hr'δ
        _ = Real.pi := by ring
    by_contra hk
    have h1k : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      exact_mod_cast this
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hlt
    nlinarith
  rw [hk, hk0, Real.dist_eq]
  simp only [Int.cast_zero, zero_mul, add_zero]
  exact lt_of_lt_of_le hr' (min_le_left _ _)

section Det2
variable {D : ContMetric} {z : ℂ} {s t : ℝ}

/-- an angle lift of a geodesic `R` to `φ w` on `[t, s]`, normalized by `α s = θ w`, and the
position of `R t` on a positive Jordan lift of `∂𝓑^•_t` -/
theorem exists_normLift {φ φ₁ : ℝ → ℂ} {θ θ₁ : ℝ → ℝ}
    (hφ : DD.IsPosJordanLift (frontier (filledBall D z s)) z φ θ)
    (hφ₁ : DD.IsPosJordanLift (frontier (filledBall D z t)) z φ₁ θ₁)
    (ht0 : 0 < t) (hts : t < s) {R : ℝ → ℂ} {w : ℝ} (hR : IsGeodesicL D R s z (φ w)) :
    ∃ (α : ℝ → ℝ) (u : ℝ), DD.IsAngleLift z R t s α ∧ α s = θ w ∧ φ₁ u = R t ∧
      θ₁ u = α t := by
  have hy : φ w ∈ frontier (filledBall D z s) := hφ.2.2.2.1 ▸ mem_range_self w
  have hne : ∀ u ∈ Icc t s, R u ≠ z := fun u hu => DD.geodLevel_ne hR (ht0.trans_le hu.1) hu.2
  have hsub : Icc t s ⊆ Icc 0 s := Icc_subset_Icc_left ht0.le
  obtain ⟨α₀, hα₀⟩ := DD.exists_angleLift hts.le ((DD.cl_geodL_continuousOn hR).mono hsub) hne
  have hsI : s ∈ Icc t s := ⟨hts.le, le_rfl⟩
  have hRs := hα₀.2 s hsI
  rw [hR.2.2.1] at hRs
  have hyz : φ w - z ≠ 0 := sub_ne_zero.2 (hR.2.2.1 ▸ hne s hsI)
  obtain ⟨n, hn⟩ := DD.isAngle_sub hyz (hφ.2.2.2.2.2.2 w) hRs
  have hα := hα₀.add_int n
  have htI : t ∈ Icc t s := ⟨le_rfl, hts.le⟩
  obtain ⟨u, hu1, hu2⟩ := hφ₁.exists_pos (DD.geodLevel_frontier hR hy ht0 hts.le)
    (hne t htI) (hα.2 t htI)
  exact ⟨_, u, hα, by show α₀ s + n * (2 * Real.pi) = θ w; linarith, hu1, hu2⟩

/-- **CONF l. 557** with CONF Lemma 2.3: a lifted meeting of a geodesic `R` with the geodesic
`G` to a rational point forces equal positions at level `t` -/
theorem meet_pos_eq {φ₁ : ℝ → ℂ} {θ₁ : ℝ → ℝ}
    (hφ₁ : DD.IsPosJordanLift (frontier (filledBall D z t)) z φ₁ θ₁) (ht0 : 0 < t)
    (hts : t < s) {q : ℚ × ℚ} (hU : UniqueGeod D z (ratPt q)) {G : ℝ → ℂ} {L : ℝ}
    (hG : IsGeodesicL D G L z (ratPt q)) (hsL : s ≤ L) {R : ℝ → ℂ} {y : ℂ}
    (hR : IsGeodesicL D R s z y) {α β : ℝ → ℝ} (hα : DD.IsAngleLift z R t s α)
    (hβ : DD.IsAngleLift z G t s β) {uR uG : ℝ} (h1 : φ₁ uR = R t) (h2 : θ₁ uR = α t)
    (h3 : φ₁ uG = G t) (h4 : θ₁ uG = β t) {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc t s)
    (ht₂ : t₂ ∈ Icc t s) (he : G t₁ = R t₂) (hθ : β t₁ = α t₂) : uR = uG := by
  obtain ⟨h12, heq⟩ := conf_L2_3_det hU hG hR ⟨ht0.le.trans ht₁.1, ht₁.2.trans hsL⟩
    ⟨ht0.le.trans ht₂.1, ht₂.2⟩ he
  subst h12
  have hsub : Icc t t₁ ⊆ Icc t s := Icc_subset_Icc_right ht₁.2
  have hGs : IsGeodesicL D G s z (G s) := geodL_restr hG ⟨hts.le.trans' ht0.le, hsL⟩
  have hne : ∀ r ∈ Icc t t₁, G r ≠ z := fun r hr =>
    DD.geodLevel_ne hGs (ht0.trans_le hr.1) (hr.2.trans ht₁.2)
  have hαG : DD.IsAngleLift z G t t₁ α :=
    ⟨hα.1.mono hsub, fun r hr => by
      rw [heq ⟨ht0.le.trans hr.1, hr.2⟩]; exact hα.2 r (hsub hr)⟩
  have hEq := DD.angleLift_eqOn (hβ.mono hsub) hαG hne ⟨ht₁.1, le_rfl⟩ hθ
  have htt : t ∈ Icc t t₁ := ⟨le_rfl, ht₁.1⟩
  refine hφ₁.pos_unique ?_ ?_
  · rw [h1, h3, heq ⟨ht0.le, ht₁.1⟩]
  · rw [h2, h4, hEq htt]

/-- **CONF l. 557–558** ("no geodesic from 0 to `y` can cross `P_{q}` … it lies to the right"):
the endpoint order of a geodesic `R` and the geodesic `G` to a rational point transfers to every
level `t ∈ (0, s)` (TOPO-ORD + CONF Lemma 2.3) -/
theorem rat_order
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    {φ φ₁ : ℝ → ℂ} {θ θ₁ : ℝ → ℝ}
    (hφ : DD.IsPosJordanLift (frontier (filledBall D z s)) z φ θ)
    (hφ₁ : DD.IsPosJordanLift (frontier (filledBall D z t)) z φ₁ θ₁) (ht0 : 0 < t)
    (hts : t < s) {q : ℚ × ℚ} (hU : UniqueGeod D z (ratPt q)) {G : ℝ → ℂ} {L : ℝ}
    (hG : IsGeodesicL D G L z (ratPt q)) (hsL : s ≤ L) {v : ℝ} (hGv : G s = φ v)
    {R : ℝ → ℂ} {w : ℝ} (hR : IsGeodesicL D R s z (φ w)) {α β : ℝ → ℝ}
    (hα : DD.IsAngleLift z R t s α) (hβ : DD.IsAngleLift z G t s β) (hαs : α s = θ w)
    (hβs : β s = θ v) {uR uG : ℝ} (h1 : φ₁ uR = R t) (h2 : θ₁ uR = α t)
    (h3 : φ₁ uG = G t) (h4 : θ₁ uG = β t) :
    (w ≤ v → uR ≤ uG) ∧ (v ≤ w → uG ≤ uR) := by
  obtain ⟨hK₁, hK₂, hz, h12, hc₁, hc₂⟩ := ann_hyps (z := z) hbc ht0 hts
  have hGs : IsGeodesicL D G s z (φ v) := hGv ▸ geodL_restr hG ⟨hts.le.trans' ht0.le, hsL⟩
  have hfr : ∀ x, φ x ∈ frontier (filledBall D z s) := fun x => hφ.2.2.2.1 ▸ mem_range_self x
  have hsub : Icc t s ⊆ Icc 0 s := Icc_subset_Icc_left ht0.le
  have hRc := (DD.cl_geodL_continuousOn hR).mono hsub
  have hGc := (DD.cl_geodL_continuousOn hGs).mono hsub
  have hRm := DD.geodLevel_mapsTo hR (hfr w) ht0 hts.le
  have hGm := DD.geodLevel_mapsTo hGs (hfr v) ht0 hts.le
  constructor
  · intro hwv
    by_contra hlt
    push Not at hlt
    obtain ⟨t₁, ht₁, t₂, ht₂, he, hθ⟩ := DD.topoOrd _ _ z hK₁ hK₂ hz h12 hc₁ hc₂ φ₁ θ₁ φ θ hφ₁
      hφ G R t s β α hts.le hGc hRc hGm hRm hβ hα uG uR v w h3 h4 h1 h2 hGs.2.2.1.symm
      hβs.symm hR.2.2.1.symm hαs.symm hlt hwv
    exact hlt.ne' (meet_pos_eq hφ₁ ht0 hts hU hG hsL hR hα hβ h1 h2 h3 h4 ht₁ ht₂ he hθ)
  · intro hvw
    by_contra hlt
    push Not at hlt
    obtain ⟨t₁, ht₁, t₂, ht₂, he, hθ⟩ := DD.topoOrd _ _ z hK₁ hK₂ hz h12 hc₁ hc₂ φ₁ θ₁ φ θ hφ₁
      hφ R G t s α β hts.le hRc hGc hRm hGm hα hβ uR uG w v h1 h2 h3 h4 hR.2.2.1.symm
      hαs.symm hGs.2.2.1.symm hβs.symm hlt hvw
    exact hlt.ne (meet_pos_eq hφ₁ ht0 hts hU hG hsL hR hα hβ h1 h2 h3 h4 ht₂ ht₁ he.symm hθ.symm)

/-- the endpoint order of two geodesics to `∂𝓑^•_s` transfers to every level, through the
geodesic to a rational point with endpoint between them (CONF l. 552–558) -/
theorem step_order
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η) (hq : ∀ q : ℚ × ℚ, UniqueGeod D z (ratPt q))
    {φ φ₁ : ℝ → ℂ} {θ θ₁ : ℝ → ℝ}
    (hφ : DD.IsPosJordanLift (frontier (filledBall D z s)) z φ θ)
    (hφ₁ : DD.IsPosJordanLift (frontier (filledBall D z t)) z φ₁ θ₁) (ht0 : 0 < t)
    (hts : t < s) {R₀ R₁ : ℝ → ℂ} {w₀ w₁ : ℝ} (hR₀ : IsGeodesicL D R₀ s z (φ w₀))
    (hR₁ : IsGeodesicL D R₁ s z (φ w₁)) {α₀ α₁ : ℝ → ℝ} (hα₀ : DD.IsAngleLift z R₀ t s α₀)
    (hα₁ : DD.IsAngleLift z R₁ t s α₁) (hα₀s : α₀ s = θ w₀) (hα₁s : α₁ s = θ w₁)
    {p₀ p₁ : ℝ} (h01 : φ₁ p₀ = R₀ t) (h02 : θ₁ p₀ = α₀ t) (h11 : φ₁ p₁ = R₁ t)
    (h12 : θ₁ p₁ = α₁ t) (hw : w₀ < w₁) : p₀ ≤ p₁ := by
  have hs : 0 < s := ht0.trans hts
  obtain ⟨q, G, r, -, hG, hsL, hr, hrw⟩ := exists_rat_near hbc hgeo hs
    (isPosJordanParam_of_lift hφ) ((w₀ + w₁) / 2) (ε := (w₁ - w₀) / 2) (by linarith)
  rw [abs_lt] at hrw
  have hGs : IsGeodesicL D G s z (φ r) := hr ▸ geodL_restr hG ⟨hs.le, hsL.le⟩
  obtain ⟨β, pG, hβ, hβs, hG1, hG2⟩ := exists_normLift hφ hφ₁ ht0 hts hGs
  have hA := (rat_order hbc hφ hφ₁ ht0 hts (hq q) hG hsL.le hr.symm hR₀ hα₀ hβ hα₀s hβs h01
    h02 hG1 hG2).1 (by linarith)
  have hB := (rat_order hbc hφ hφ₁ ht0 hts (hq q) hG hsL.le hr.symm hR₁ hα₁ hβ hα₁s hβs h11
    h12 hG1 hG2).2 (by linarith)
  exact hA.trans hB

end Det2

end LQGMetric.CONF
