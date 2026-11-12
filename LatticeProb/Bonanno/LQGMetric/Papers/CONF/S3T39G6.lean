/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39G6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39G3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF (3.22)–(3.23): killing an arc, deterministic part

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`
C:1600–1617. "By assertion A of Lemma 3.7, if `R^{ε_k}_𝕣(𝓑^•_{s_k}) ≤ diam 𝓑^•_{s_k}` and `G_I`
occurs, then the interval `I′` … is empty" (C:1600–1602), and (3.22): on `𝓔_𝕣(a)`,
`R^{ε_k}_𝕣(𝓑^•_{s_k}) ≤ diam 𝓑^•_{s_k}` since `B_{a𝕣}(0) ⊆ 𝓑^•_{s_k} ⊆ B_{3𝕣}(0)` (C:1606–1617).

* `t39g_kill`: if no geodesic from `𝕫` to a point outside the interior of `𝓑^•_{t′}` passes
  through `J = I^{(t)}`, then `I^{(t′)} = ∅`. The points of `I^{(t′)} ⊆ ∂𝓑^•_{t′}` lie in
  `𝓑^•_{t′}`, so Lemma 3.7 A is needed for targets in `ℂ ∖ int 𝓑^•_{σ}` (CONF states it for
  `ℂ ∖ 𝓑^•_σ`, C:1460; its proof, C:1467–1470, gives it for every target outside
  `B_{R^ε_𝕣(𝓑^•_τ)}(𝓑^•_τ)`, an open set inside `𝓑^•_σ`, hence for `ℂ ∖ int 𝓑^•_σ`).
* `t39g_confRK_le_ediam`: (3.22).
-/

noncomputable section

open MeasureTheory Set Metric
open LQGMetric.Blueprint LQGMetric.GM

namespace LQGMetric
namespace CONF

/-- **C:1600–1602**: the kill step for one arc -/
theorem t39g_kill {D : ContMetric} {z₀ : ℂ} {τ t t' : ℝ} {I : Set ℂ} (hτ : 0 < τ)
    (hτt : τ ≤ t) (htt' : t ≤ t') (hbd : Bornology.IsBounded (ballM D z₀ τ))
    (hI : I ⊆ frontier (filledBall D z₀ τ))
    (hA : ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ), y ∉ interior (filledBall D z₀ t') →
      IsGeodesicL D Q L z₀ y → ∀ u ∈ Icc 0 L, Q u ∉ t39gArc D z₀ t I) :
    t39gArc D z₀ t' I = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro x ⟨hxf, P, hl, u, hu, hPu⟩
  have hPd : D.1 (z₀, P u) = u := DD.cl_geodL_dist hl.2.1 hu
  have hus : u = τ := hPd.symm.trans (jp_frontier_subset_sphere hbd (hI hPu))
  have hxi : x ∉ interior (filledBall D z₀ t') := hxf.2
  rcases htt'.lt_or_eq with hlt | heq
  · have hl' := DD.isLeftmost_restr hl (hτ.trans_le hτt) hlt
    exact hA x P t' hxi hl.2.1 t ⟨(hτ.trans_le hτt).le, htt'⟩
      ⟨hl'.1, P, hl', u, ⟨hu.1, hus ▸ hτt⟩, hPu⟩
  · subst heq
    have hPx : P t = x := hl.2.1.2.2.1
    exact hA x P t hxi hl.2.1 t ⟨(hτ.trans_le hτt).le, le_rfl⟩
      (hPx ▸ ⟨hxf, P, hl, u, hu, hPu⟩)

section Diam
variable {Ω : Type} [MeasurableSpace Ω] {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric}
  {P : Measure Ω} {h : Ω → DistC} {p : CONFParams} {χ : ℝ} {z₀ : ℂ} {R a : ℝ} {ω : Ω}

/-- **(3.22)** (C:1606–1617): on `𝓔_𝕣(a)`, if `B_{a𝕣}(𝕫) ⊆ K ⊆ B_{3𝕣}(𝕫)` and `ε = 2^{−m}` with
`7ε^{1/2} ≤ a`, then `R^ε_𝕣(K) ≤ diam K` -/
theorem t39g_confRK_le_ediam (hω : ω ∈ confReg ξ cc D P h p χ z₀ R a) (hR : 0 < R)
    (ha : 0 < a) {m : ℕ} (hm : 7 * ((2 : ℝ)⁻¹ ^ m) ^ (1 / 2 : ℝ) ≤ a) {K : Set ℂ}
    (hK3 : K ⊆ ball z₀ (3 * R)) (hKa : ball z₀ (a * R) ⊆ K) :
    confRK ξ cc D P h p R ((2 : ℝ)⁻¹ ^ m) K ω ≤ Metric.ediam K := by
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hsq : δ ≤ δ ^ (1 / 2 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have h1 := t39g_confRK_le hω hR (hsq.trans (by linarith [Real.rpow_nonneg hδ0.le (1 / 2 : ℝ)]))
    hK3
  have haR : 0 < a * R := mul_pos ha hR
  set w : ℂ := ((a * R / 2 : ℝ) : ℂ)
  have hw : ‖w‖ = a * R / 2 := by
    simp only [w, Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos (by positivity)
  have hm1 : z₀ - w ∈ K := hKa (by
    rw [mem_ball, dist_eq_norm, show z₀ - w - z₀ = -w by ring, norm_neg, hw]; linarith)
  have hm2 : z₀ + w ∈ K := hKa (by
    rw [mem_ball, dist_eq_norm, show z₀ + w - z₀ = w by ring, hw]; linarith)
  have hd : edist (z₀ - w) (z₀ + w) = ENNReal.ofReal (a * R) := by
    rw [edist_dist]
    congr 1
    rw [dist_eq_norm, show z₀ - w - (z₀ + w) = -(2 * w) by ring, norm_neg, norm_mul, hw]
    norm_num; ring
  calc confRK ξ cc D P h p R δ K ω ≤ ENNReal.ofReal (7 * δ ^ (1 / 2 : ℝ) * R) := h1
    _ ≤ ENNReal.ofReal (a * R) := ENNReal.ofReal_le_ofReal (by nlinarith)
    _ = edist (z₀ - w) (z₀ + w) := hd.symm
    _ ≤ Metric.ediam K := Metric.edist_le_ediam_of_mem hm1 hm2

end Diam

open Classical in
/-- **C:1740–1744** ("since `n₀` can be made arbitrarily large"): if for every `m` the
probability that `E` occurs and at least `N` arcs of the `m`-th family `A m` meet `X` is
at most `B`, and on `E` any finite subset of `X` is eventually covered by the arcs with at most
one of its points per arc, then `P[E, #X > N] ≤ B` -/
theorem t39g_points_of_arcs {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (E : Set Ω)
    (X : Ω → Set ℂ) (A : (m : ℕ) → Fin m → Ω → Set ℂ) (N : ℕ) (B : ENNReal)
    (hsep : ∀ ω ∈ E, ∀ F : Finset ℂ, (F : Set ℂ) ⊆ X ω → ∀ᶠ m in Filter.atTop,
      (∀ x ∈ F, ∃ i, x ∈ A m i ω) ∧
        ∀ i, ∀ x ∈ F, ∀ y ∈ F, x ∈ A m i ω → y ∈ A m i ω → x = y)
    (hB : ∀ m, P {ω | ω ∈ E ∧ N ≤ (Finset.univ.filter fun i => (A m i ω ∩ X ω).Nonempty).card}
      ≤ B) :
    P {ω | ω ∈ E ∧ ((N : ℕ∞) : ℕ∞) < (X ω).encard} ≤ B := by
  set C : ℕ → Set Ω := fun m =>
    {ω | ω ∈ E ∧ N ≤ (Finset.univ.filter fun i => (A m i ω ∩ X ω).Nonempty).card}
  set Dm : ℕ → Set Ω := fun M => ⋂ m ∈ Set.Ici M, C m
  have hDmono : Monotone Dm := fun M M' hMM' ω hω => by
    simp only [Dm, Set.mem_iInter] at hω ⊢
    exact fun m hm => hω m (le_trans hMM' hm)
  have hsub : {ω | ω ∈ E ∧ ((N : ℕ∞) : ℕ∞) < (X ω).encard} ⊆ ⋃ M, Dm M := by
    rintro ω ⟨hωE, hlt⟩
    obtain ⟨T, hTX, hTc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
    have hTf : T.Finite := Set.finite_of_encard_eq_coe (k := N + 1) (by rw [hTc]; rfl)
    set F := hTf.toFinset
    have hFc : F.card = N + 1 := by
      have := hTf.encard_eq_coe_toFinset_card
      rw [hTc] at this
      exact_mod_cast this.symm
    have hFX : (F : Set ℂ) ⊆ X ω := by rw [Set.Finite.coe_toFinset]; exact hTX
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (hsep ω hωE F hFX)
    refine Set.mem_iUnion.2 ⟨M, ?_⟩
    simp only [Dm, Set.mem_iInter]
    intro m hm
    obtain ⟨hcov, hsep'⟩ := hM m hm
    have h1 := t39g_card_le_arcs F Finset.univ (fun i => A m i ω)
      (fun x hx => (hcov x hx).elim fun i hi => ⟨i, Finset.mem_univ _, hi⟩)
      (fun i _ => hsep' i)
    have h2 : (Finset.univ.filter fun i => (A m i ω ∩ (F : Set ℂ)).Nonempty).card ≤
        (Finset.univ.filter fun i => (A m i ω ∩ X ω).Nonempty).card :=
      Finset.card_le_card fun i hi => by
        rw [Finset.mem_filter] at hi ⊢
        exact ⟨hi.1, hi.2.mono (Set.inter_subset_inter_right _ hFX)⟩
    exact ⟨hωE, by omega⟩
  calc _ ≤ P (⋃ M, Dm M) := measure_mono hsub
    _ = ⨆ M, P (Dm M) := hDmono.measure_iUnion
    _ ≤ B := iSup_le fun M => (measure_mono fun ω hω => by
        simp only [Dm, Set.mem_iInter] at hω
        exact hω M (Set.mem_Ici.2 le_rfl)).trans (hB M)

/-- **continuity from above of filled balls** (used for S2 / C:1467–1470: `B_{R}(𝓑^•_τ)`, open
and inside every `𝓑^•_{s′}`, `s′ > σ^ε_{τ,𝕣}`, lies in `𝓑^•_σ`): for a metric with a geodesic from
`𝕫` to every point and bounded balls, an open set inside `𝓑^•_{s′}` for all `s′ > σ` is inside
`𝓑^•_σ`. Own elementary proof (CONF uses it implicitly at C:1468). -/
theorem t39g_open_subset_filledBall {D : ContMetric} {z₀ : ℂ} {σ : ℝ} (hσ : 0 < σ)
    (hgeo : ∀ w, ∃ (Q : ℝ → ℂ) (L : ℝ), IsGeodesicL D Q L z₀ w)
    (hbd : Bornology.IsBounded (ballM D z₀ (σ + 1)))
    {U : Set ℂ} (hsub : ∀ s', σ < s' → U ⊆ filledBall D z₀ s') :
    U ⊆ filledBall D z₀ σ := by
  intro y hyU
  by_contra hy
  -- points outside `cl 𝓑_σ` are at distance `> σ`
  have hout : ∀ w, w ∉ closure (ballM D z₀ σ) → σ < D.1 (z₀, w) := by
    intro w hw
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · exact hw (subset_closure hlt)
    · obtain ⟨Q, L, hQ⟩ := hgeo w
      have hL : D.1 (z₀, Q L) = L := DD.cl_geodL_dist hQ ⟨hQ.1, le_rfl⟩
      have hQL : Q L = w := hQ.2.2.1
      rw [hQL] at hL
      have hLσ : L = σ := hL.symm.trans heq
      have hmem := gm_geod_mem_closure_ballM hQ (hLσ ▸ hσ) le_rfl
      rw [hQL, hLσ] at hmem
      exact hw hmem
  obtain ⟨R, p, hR, hp⟩ := jb_exists_far hbd
  have hRs : ∀ s ≤ σ + 1, closure (ballM D z₀ s) ⊆ ball 0 R := fun s hs =>
    (DD.cl_closure_ballM_mono D z₀ hs).trans hR
  have hpF : p ∉ closure (ballM D z₀ σ) := fun hpc => by
    have := mem_ball_zero_iff.1 (hRs σ (by linarith) hpc); linarith
  have hyW : y ∈ connectedComponentIn (closure (ballM D z₀ σ))ᶜ p := by
    rw [← jb_compl_filledBall_eq (hRs σ (by linarith)) hp]; exact hy
  have hWo : IsOpen (connectedComponentIn (closure (ballM D z₀ σ))ᶜ p) :=
    isClosed_closure.isOpen_compl.connectedComponentIn
  have hWc : IsConnected (connectedComponentIn (closure (ballM D z₀ σ))ᶜ p) :=
    isConnected_connectedComponentIn_iff.2 hpF
  have hpW : p ∈ connectedComponentIn (closure (ballM D z₀ σ))ᶜ p := mem_connectedComponentIn hpF
  obtain ⟨γ, hγ⟩ := (hWo.isConnected_iff_isPathConnected.1 hWc).joinedIn p hpW y hyW
  have hKc : IsCompact (Set.range γ) := isCompact_range γ.continuous
  have hKF : Set.range γ ⊆ (closure (ballM D z₀ σ))ᶜ := by
    rintro _ ⟨t, rfl⟩; exact connectedComponentIn_subset _ _ (hγ t)
  obtain ⟨x₀, hx₀K, hmin⟩ := hKc.exists_isMinOn (Set.range_nonempty γ)
    (DD.cl_continuous_distFrom D z₀).continuousOn
  have hη : σ < D.1 (z₀, x₀) := hout x₀ (hKF hx₀K)
  set m := min (D.1 (z₀, x₀)) (σ + 1) with hm
  have hσm : σ < m := lt_min hη (by linarith)
  have hm1 : m ≤ D.1 (z₀, x₀) := min_le_left _ _
  have hm2 : m ≤ σ + 1 := min_le_right _ _
  have hKs : Set.range γ ⊆ (closure (ballM D z₀ ((σ + m) / 2)))ᶜ := fun x hx hxc => by
    have h1 : D.1 (z₀, x) ≤ (σ + m) / 2 := DD.cl_closure_ballM_subset D z₀ _ hxc
    have h2 : D.1 (z₀, x₀) ≤ D.1 (z₀, x) := hmin hx
    linarith
  have hpK : p ∈ Set.range γ := ⟨0, γ.source⟩
  have hyK : y ∈ Set.range γ := ⟨1, γ.target⟩
  have hcc := (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn hpK hKs
    hyK
  rw [← jb_compl_filledBall_eq (hRs _ (by linarith)) hp] at hcc
  exact hcc (hsub _ (by linarith) hyU)

/-- `B_{R^ε_𝕣(𝓑^•_s)}(𝓑^•_s) ⊆ int 𝓑^•_σ` for `σ = σ^ε_{s,𝕣}` finite (C:1467–1470): the targets
excluded by L3.6 A include `∂𝓑^•_σ` (statement issue S2 of handoff/P2-CONFT39.md) -/
theorem t39g_enbhd_subset_interior {Ω : Type} [MeasurableSpace Ω] {ξ : ℝ} {cc : ℝ → ℝ}
    {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC} {p : CONFParams} {z₀ : ℂ}
    {R ε s σ : ℝ} {ω : Ω} (hσ : confSigma ξ cc D P h p z₀ R ε s ω = ENNReal.ofReal σ)
    (hσ0 : 0 < σ) (hgeo : ∀ w, ∃ (Q : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) Q L z₀ w)
    (hbd : Bornology.IsBounded (ballM (D (h ω)) z₀ (σ + 1))) :
    enbhd (confRK ξ cc D P h p R ε (filledBall (D (h ω)) z₀ s) ω)
        (filledBall (D (h ω)) z₀ s) ⊆ interior (filledBall (D (h ω)) z₀ σ) := by
  have hopen : IsOpen (enbhd (confRK ξ cc D P h p R ε (filledBall (D (h ω)) z₀ s) ω)
      (filledBall (D (h ω)) z₀ s)) :=
    isOpen_lt Metric.continuous_infEDist continuous_const
  refine interior_maximal (t39g_open_subset_filledBall hσ0 hgeo hbd fun s' hs' => ?_) hopen
  have hlt : confSigma ξ cc D P h p z₀ R ε s ω < ENNReal.ofReal s' := by
    rw [hσ]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hs'
  unfold confSigma at hlt
  obtain ⟨s'', h1⟩ := iInf_lt_iff.1 hlt
  obtain ⟨_, h2⟩ := iInf_lt_iff.1 h1
  obtain ⟨hsub, h3⟩ := iInf_lt_iff.1 h2
  have : s'' < s' := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 h3
  exact hsub.trans (gm_filledBall_mono _ _ this.le)

end CONF
end LQGMetric
