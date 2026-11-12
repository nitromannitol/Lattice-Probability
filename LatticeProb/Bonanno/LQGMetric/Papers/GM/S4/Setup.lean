/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Setup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFResults
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# GM §4.1: setup of the proof of Theorem 4.2 (radii, arcs, stopping times)

Source: Gwynne–Miller, *Existence and uniqueness of the LQG metric for γ ∈ (0,2)*,
arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex` (GM), §4.1
"Setup and outline", l. 1609–1700. Inventory: `blueprint/GM_B.md` §2b; work package WP-M2g
(`blueprint/M2.md` §3 row 10).

* **GM (4.5)–(4.6) with decision D16** (`decisions/DEC-B.md` (a), D-B1, DV-B12): the time unit
  is `𝔲 := τ_{ℓ𝕣}(𝕫)` (CONF's `tauR`), and `s_k := 𝔲 (1 + k ε^β)`, `t_k := s_k + ε^{2β} 𝔲`
  (`s4S`, `s4T`). GM's unit `𝔠_𝕣 e^{ξ h_𝕣(𝕫)}` is not a function of the ball filtration (gap R1).
  `s_k ≤ t_k ≤ s_{k+1}` (GM l. 1646: "`t_k ∈ [s_k, s_{k+1}]`") is `gm_s4S_le_s4T`,
  `gm_s4T_le_s4S_succ`.
* **GM.S4.12** (DEC-B (a), "Implied nodes"): `s_k`, `t_k` are stopping times for a monotone
  filtration in which `τ_{ℓ𝕣}` is a stopping time (`gm_S4_12`; DEC-B's own two-line argument:
  `{c τ ≤ s} = {τ ≤ s/c} ∈ 𝓕_{s/c} ⊆ 𝓕_s` for `c ≥ 1`).
* **S-geod-level** (DEC-D (a), "Theorems the CONF §2 package proves"; GM uses it at l. 1669:
  "`P(s_k) ∈ ∂𝓑^•_{s_k}`"): a geodesic from `𝕫` to a point outside `𝓑^•_s` crosses `∂𝓑^•_s` at
  time `s` (`gm_geod_mem_frontier`). Own elementary proof (connectedness of the later part of the
  geodesic, which stays in the unbounded component of `ℂ ∖ cl 𝓑_s`).
* **GM (4.7)**: `Conf_k = confPts`, the arcs `arcOf x` (GM (4.7), l. 1651);
  **GM.S4.1** (l. 1654: "By [CONF, Lemma 2.7], `𝓘_k` is a collection of disjoint arcs of
  `∂𝓑^•_{t_k}` whose union is all of `∂𝓑^•_{t_k}`") is `gm_S4_1`, from CONF Thm 1.4
  (finiteness), CONF Lemma 2.7 applied to the singletons `{x}`, `x ∈ Conf_k` (GM l. 1652–1654),
  and CONF Lemma 2.4 (existence of leftmost geodesics) with S-geod-level for the union.
  The clause "determined by `𝓑^•_{t_k}` and `h|_{𝓑^•_{t_k}}`" (Axiom II) is not formalized here.

Leftmost geodesics are read with the Blueprint's `IsLeftmostGeod` (current `CONFDefs`); the
proofs here use only the conclusions of the CONF Props, so they are unchanged by DEC-D's
redefinition (D-D1), which keeps the names and arities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-! ## The radii `s_k`, `t_k` (GM (4.6), D16) -/

section Times
variable {Ω : Type} [MeasurableSpace Ω]

/-- the time unit `𝔲 = τ_{ℓ𝕣}(𝕫) = inf {s > 0 : 𝓑^•_s(𝕫; D_h) ⊄ B_{ℓ𝕣}(𝕫)}` (GM (4.5), D16) -/
def s4Unit (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 : ℂ) (ℓ 𝕣 : ℝ) (ω : Ω) : ℝ :=
  tauR D h 𝕫 (ℓ * 𝕣) ω

/-- `s_k := τ_{ℓ𝕣}(1 + k ε^β)` (GM (4.6) as repaired by D16 / DV-B12) -/
def s4S (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 : ℂ) (ℓ 𝕣 ε β : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  s4Unit D h 𝕫 ℓ 𝕣 ω * (1 + k * ε ^ β)

/-- `t_k := s_k + ε^{2β} τ_{ℓ𝕣}` (GM (4.6) as repaired by D16 / DV-B12) -/
def s4T (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 : ℂ) (ℓ 𝕣 ε β : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  s4S D h 𝕫 ℓ 𝕣 ε β k ω + ε ^ (2 * β) * s4Unit D h 𝕫 ℓ 𝕣 ω

variable {D : DistC → ContMetric} {h : Ω → DistC} {𝕫 : ℂ} {ℓ 𝕣 ε β : ℝ}

omit [MeasurableSpace Ω] in
theorem gm_s4Unit_nonneg (ω : Ω) : 0 ≤ s4Unit D h 𝕫 ℓ 𝕣 ω :=
  Real.sInf_nonneg (fun _ hx => hx.1.le)

omit [MeasurableSpace Ω] in
/-- `s_k ≤ t_k` (GM l. 1646) -/
theorem gm_s4S_le_s4T (hε : 0 < ε) (k : ℕ) (ω : Ω) :
    s4S D h 𝕫 ℓ 𝕣 ε β k ω ≤ s4T D h 𝕫 ℓ 𝕣 ε β k ω :=
  le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hε.le _) (gm_s4Unit_nonneg ω))

omit [MeasurableSpace Ω] in
/-- `t_k ≤ s_{k+1}` (GM l. 1646: `t_k ∈ [s_k, s_{k+1}]`), for `ε ∈ (0,1]`, `β ≥ 0` -/
theorem gm_s4T_le_s4S_succ (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β) (k : ℕ) (ω : Ω) :
    s4T D h 𝕫 ℓ 𝕣 ε β k ω ≤ s4S D h 𝕫 ℓ 𝕣 ε β (k + 1) ω := by
  have hp : ε ^ (2 * β) ≤ ε ^ β := Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have hu := gm_s4Unit_nonneg (D := D) (h := h) (𝕫 := 𝕫) (ℓ := ℓ) (𝕣 := 𝕣) ω
  have := mul_le_mul_of_nonneg_left hp hu
  simp only [s4T, s4S]
  push_cast
  nlinarith

omit [MeasurableSpace Ω] in
/-- `c τ` is a stopping time for a monotone filtration if `τ ≥ 0` is and `c ≥ 1`
(DEC-B (a): `{c τ ≤ s} = {τ ≤ s/c} ∈ 𝓕_{s/c} ⊆ 𝓕_s`) -/
theorem gm_stop_mul {F : ℝ → MeasurableSpace Ω} (hF : Monotone F) {τ : Ω → ℝ}
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω < t}) {c : ℝ} (hc : 1 ≤ c)
    (t : ℝ) : MeasurableSet[F t] {ω | τ ω * c < t} := by
  rcases lt_or_ge t 0 with ht | ht
  · have : {ω | τ ω * c < t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact ht.le.trans (mul_nonneg (hτ0 ω) (by linarith))
    rw [this]
    exact @MeasurableSet.empty _ (F t)
  · have hc0 : 0 < c := by linarith
    have : {ω | τ ω * c < t} = {ω | τ ω < t / c} := by
      ext ω
      simp only [mem_ofPred_eq]
      rw [lt_div_iff₀ hc0]
    rw [this]
    exact hF (div_le_self ht hc) _ (hτ _)

omit [MeasurableSpace Ω] in
omit [MeasurableSpace Ω] in
/-- the generated filled-ball filtration is monotone (surely; D49) -/
theorem gm_filledBallSigma_mono : Monotone (filledBallSigma D h 𝕫) :=
  fun _ _ hst => iSup₂_mono' fun s hs => ⟨s, hs.trans hst, le_rfl⟩

omit [MeasurableSpace Ω] in
/-- **GM.S4.12** (DEC-B (a), D49): if `τ_{ℓ𝕣}` is a stopping time for the filled-ball
filtration, then so are `s_k` and `t_k` (`ε > 0`, `β ≥ 0`). -/
theorem gm_S4_12
    (hτ : IsFilledBallStoppingTime D h 𝕫 (s4Unit D h 𝕫 ℓ 𝕣)) (hε : 0 < ε) (k : ℕ) :
    IsFilledBallStoppingTime D h 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k) ∧
      IsFilledBallStoppingTime D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k) := by
  have hk : (0 : ℝ) ≤ k * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le _)
  have hk2 : (0 : ℝ) ≤ ε ^ (2 * β) := Real.rpow_nonneg hε.le _
  refine ⟨fun t => gm_stop_mul gm_filledBallSigma_mono gm_s4Unit_nonneg hτ (by linarith) t, fun t => ?_⟩
  have := gm_stop_mul gm_filledBallSigma_mono gm_s4Unit_nonneg hτ (c := 1 + k * ε ^ β + ε ^ (2 * β))
    (by linarith) t
  have e : ∀ ω, s4T D h 𝕫 ℓ 𝕣 ε β k ω =
      s4Unit D h 𝕫 ℓ 𝕣 ω * (1 + k * ε ^ β + ε ^ (2 * β)) := fun ω => by
    simp only [s4T, s4S]; ring
  simp_rw [e]
  exact this

end Times

/-! ## Geodesics cross the boundaries of the filled balls (S-geod-level, DEC-D (a)) -/

section Det
variable {D : ContMetric} {z y : ℂ} {P : ℝ → ℂ} {L s t : ℝ}

/-- a unit-speed `D`-geodesic is Euclidean-continuous on `[0, L]` -/
theorem gm_geodL_continuousOn (hP : IsGeodesicL D P L z y) : ContinuousOn P (Icc 0 L) := by
  intro a ha
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := D.2.euclidean_of_small (P a) ε hε
  refine ⟨δ, hδ, fun {b} hb hab => ?_⟩
  rw [dist_comm, dist_eq_norm]
  apply hδε
  rw [hP.2.2.2 a ha b hb]
  rwa [Real.dist_eq] at hab

theorem gm_geodL_dist (hP : IsGeodesicL D P L z y) {u : ℝ} (hu : u ∈ Icc 0 L) :
    D.1 (z, P u) = u := by
  have := hP.2.2.2 0 ⟨le_rfl, hP.1⟩ u hu
  rw [hP.2.1, sub_zero, abs_of_nonneg hu.1] at this
  exact this

theorem gm_continuous_distFrom (D : ContMetric) (z : ℂ) : Continuous fun w => D.1 (z, w) :=
  (map_continuous D.1).comp (Continuous.prodMk_right z)

theorem gm_closure_ballM_subset (D : ContMetric) (z : ℂ) (s : ℝ) :
    closure (ballM D z s) ⊆ {w | D.1 (z, w) ≤ s} :=
  closure_minimal (fun w (hw : D.1 (z, w) < s) => show D.1 (z, w) ≤ s from hw.le)
    (isClosed_le (gm_continuous_distFrom D z) continuous_const)

theorem gm_closure_ballM_mono (D : ContMetric) (z : ℂ) {s t : ℝ} (hst : s ≤ t) :
    closure (ballM D z s) ⊆ closure (ballM D z t) :=
  closure_mono (fun _ hw => lt_of_lt_of_le hw hst)

/-- filled metric balls increase with the radius -/
theorem gm_filledBall_mono (D : ContMetric) (z : ℂ) {s t : ℝ} (hst : s ≤ t) :
    filledBall D z s ⊆ filledBall D z t := by
  intro x hx
  rcases hx with hx | ⟨hxs, hxb⟩
  · exact Or.inl (gm_closure_ballM_mono D z hst hx)
  · by_cases hxt : x ∈ closure (ballM D z t)
    · exact Or.inl hxt
    · refine Or.inr ⟨hxt, hxb.subset (connectedComponentIn_mono x ?_)⟩
      exact compl_subset_compl.mpr (gm_closure_ballM_mono D z hst)

/-- a point of `∂𝓑^•_t` is outside `𝓑^•_s` for `s < t` when `D(z, y) = t` -/
theorem gm_not_mem_filledBall_of_frontier (hyd : D.1 (z, y) = t) (hy : y ∈ frontier (filledBall D z t))
    (hst : s < t) : y ∉ filledBall D z s := by
  have hyc : y ∉ closure (ballM D z s) := fun h' => by
    have := gm_closure_ballM_subset D z s h'
    simp only [mem_ofPred_eq, hyd] at this
    linarith
  have hopen : IsOpen (connectedComponentIn (closure (ballM D z s))ᶜ y) :=
    isClosed_closure.isOpen_compl.connectedComponentIn
  have hyy : y ∈ connectedComponentIn (closure (ballM D z s))ᶜ y := mem_connectedComponentIn hyc
  have hcl : y ∈ closure (filledBall D z t)ᶜ := by
    rw [← frontier_compl] at hy
    exact frontier_subset_closure hy
  obtain ⟨p, hp1, hp2⟩ := mem_closure_iff.mp hcl _ hopen hyy
  have hpt : p ∉ closure (ballM D z t) ∧
      ¬ Bornology.IsBounded (connectedComponentIn (closure (ballM D z t))ᶜ p) := by
    simp only [filledBall, mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_and] at hp2
    exact ⟨hp2.1, hp2.2 hp2.1⟩
  have heq := connectedComponentIn_eq hp1
  rintro (h' | ⟨_, hb⟩)
  · exact hyc h'
  · apply hpt.2
    refine hb.subset ?_
    rw [heq]
    exact connectedComponentIn_mono p (compl_subset_compl.mpr (gm_closure_ballM_mono D z hst.le))

/-- **S-geod-level** (DEC-D (a); GM l. 1669): a unit-speed `D`-geodesic `P` from `z` to a point
`y ∉ 𝓑^•_s` with `0 < s < L` satisfies `P(s) ∈ ∂𝓑^•_s`. -/
theorem gm_geod_mem_frontier (hP : IsGeodesicL D P L z y) (hs : 0 < s) (hsL : s < L)
    (hy : y ∉ filledBall D z s) : P s ∈ frontier (filledBall D z s) := by
  have hc := gm_geodL_continuousOn hP
  have hsI : s ∈ Icc 0 L := ⟨hs.le, hsL.le⟩
  -- `P(s) ∈ cl 𝓑_s`
  have h1 : P s ∈ closure (ballM D z s) := by
    have hcw : ContinuousWithinAt P (Ico 0 s) s :=
      (hc s hsI).mono (fun u hu => ⟨hu.1, hu.2.le.trans hsL.le⟩)
    have hmem : s ∈ closure (Ico 0 s) := by rw [closure_Ico hs.ne]; exact ⟨hs.le, le_rfl⟩
    refine closure_mono ?_ (hcw.mem_closure_image hmem)
    rintro _ ⟨u, hu, rfl⟩
    show D.1 (z, P u) < s
    rw [gm_geodL_dist hP ⟨hu.1, hu.2.le.trans hsL.le⟩]
    exact hu.2
  -- `P((s, L]) ∩ 𝓑^•_s = ∅`
  have hyc : y ∉ closure (ballM D z s) := fun h' => hy (Or.inl h')
  have hyb : ¬ Bornology.IsBounded (connectedComponentIn (closure (ballM D z s))ᶜ y) :=
    fun hb => hy (Or.inr ⟨hyc, hb⟩)
  have hsub : P '' Ioc s L ⊆ (closure (ballM D z s))ᶜ := by
    rintro _ ⟨u, hu, rfl⟩ h'
    have := gm_closure_ballM_subset D z s h'
    simp only [mem_ofPred_eq] at this
    rw [gm_geodL_dist hP ⟨hs.le.trans hu.1.le, hu.2⟩] at this
    linarith [hu.1]
  have hconn : IsPreconnected (P '' Ioc s L) :=
    isPreconnected_Ioc.image P (hc.mono (fun u hu => ⟨hs.le.trans hu.1.le, hu.2⟩))
  have hyL : y ∈ P '' Ioc s L := ⟨L, ⟨hsL, le_rfl⟩, hP.2.2.1⟩
  have hcc := hconn.subset_connectedComponentIn hyL hsub
  have h2 : P '' Ioc s L ⊆ (filledBall D z s)ᶜ := by
    intro x hx
    rintro (h' | ⟨_, hb⟩)
    · exact hsub hx h'
    · apply hyb
      rwa [connectedComponentIn_eq (hcc hx)]
  have h3 : P s ∈ closure (filledBall D z s)ᶜ := by
    have hcw : ContinuousWithinAt P (Ioc s L) s :=
      (hc s hsI).mono (fun u hu => ⟨hs.le.trans hu.1.le, hu.2⟩)
    have hmem : s ∈ closure (Ioc s L) := by rw [closure_Ioc hsL.ne]; exact ⟨le_rfl, hsL.le⟩
    exact closure_mono h2 (hcw.mem_closure_image hmem)
  rw [closure_compl] at h3
  exact ⟨subset_closure (Or.inl h1), h3⟩

end Det

/-! ## `Conf_k` and the arcs `𝓘_k` (GM (4.7), GM.S4.1) -/

/-- `Conf_k`: the points of `∂𝓑^•_s` hit by leftmost `D`-geodesics from `𝕫` to `∂𝓑^•_t`
(GM l. 1650, with `s = s_k`, `t = t_k`; CONF's `X_{s,t}` = `hitSet`) -/
def confPts (D : ContMetric) (𝕫 : ℂ) (s t : ℝ) : Set ℂ := hitSet D 𝕫 s t

/-- the arc `{y ∈ ∂𝓑^•_t : the leftmost D-geodesic from 𝕫 to y passes through x}` (GM (4.7)) -/
def arcOf (D : ContMetric) (𝕫 : ℂ) (t : ℝ) (x : ℂ) : Set ℂ :=
  {y | y ∈ frontier (filledBall D 𝕫 t) ∧ ∃ Q, IsLeftmostGeod D 𝕫 t y Q ∧ ∃ u ∈ Icc 0 t, Q u = x}

/-- **GM.S4.1** (l. 1648–1654): a.s., for all `0 < s < t`, `Conf = Conf(s,t)` is finite, the sets
`arcOf x` (`x ∈ Conf`) are disjoint arcs of `∂𝓑^•_t`, and their union is `∂𝓑^•_t`. -/
theorem gm_S4_1 (hC24 : CONFLem2_4) (hC27 : CONFLem2_7) (hC14 : CONFThm1_4)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 < s → s < t →
      (confPts (D (h ω)) 𝕫 s t).Finite ∧
      (∀ x ∈ confPts (D (h ω)) 𝕫 s t, IsBdyArc (D (h ω)) 𝕫 t (arcOf (D (h ω)) 𝕫 t x)) ∧
      (confPts (D (h ω)) 𝕫 s t).PairwiseDisjoint (arcOf (D (h ω)) 𝕫 t) ∧
      ⋃ x ∈ confPts (D (h ω)) 𝕫 s t, arcOf (D (h ω)) 𝕫 t x =
        frontier (filledBall (D (h ω)) 𝕫 t) := by
  filter_upwards [hC24 γ hγ hγ2 D c hD P h hh 𝕫, hC27 γ hγ hγ2 D c hD P h hh 𝕫,
    hC14 γ hγ hγ2 D c hD P h hh 𝕫] with ω h24 h27 h14 s t hs hst
  set Dω := D (h ω)
  have hfin : (confPts Dω 𝕫 s t).Finite := (h14 s t hs hst).2
  -- CONF Lemma 2.7 applied to the singletons `{x}`, `x ∈ Conf`
  have h27' := h27 s t hs hst ((fun x => ({x} : Set ℂ)) '' confPts Dω 𝕫 s t) (hfin.image _)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨singleton_subset_iff.mpr hx.1, isConnected_singleton⟩)
    (by
      rintro _ ⟨x, _, rfl⟩ _ ⟨x', _, rfl⟩ hne
      exact disjoint_singleton.mpr (fun h' => hne (by rw [h'])))
  refine ⟨hfin, ?_, ?_, ?_⟩
  · intro x hx
    rcases h27'.1 {x} ⟨x, hx, rfl⟩ with h0 | harc
    · exfalso
      obtain ⟨_, y, Q, hQ, u, hu, hQu⟩ := hx
      have : y ∈ (∅ : Set ℂ) := by
        rw [← h0]
        exact ⟨hQ.1, Q, hQ, u, hu, hQu⟩
      exact this
    · exact harc
  · intro x hx x' hx' hne
    exact h27'.2 ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩ (fun h' => hne (singleton_injective h'))
  · apply Subset.antisymm
    · exact iUnion₂_subset (fun x _ => fun y hy => hy.1)
    · intro y hy
      obtain ⟨Q, hQ⟩ := (h24 t (hs.trans hst) y hy true).1
      have hQg : IsGeodesicL Dω Q t 𝕫 y := hQ.2.1
      have hyd : Dω.1 (𝕫, y) = t := by
        have := gm_geodL_dist hQg ⟨(hs.trans hst).le, le_rfl⟩
        rwa [hQg.2.2.1] at this
      have hfr := gm_geod_mem_frontier hQg hs hst
        (gm_not_mem_filledBall_of_frontier hyd hy hst)
      refine mem_iUnion₂.mpr ⟨Q s, ⟨hfr, y, Q, hQ, s, ⟨hs.le, hst.le⟩, rfl⟩, ?_⟩
      exact ⟨hy, Q, hQ, s, ⟨hs.le, hst.le⟩, rfl⟩

end LQGMetric.GM
