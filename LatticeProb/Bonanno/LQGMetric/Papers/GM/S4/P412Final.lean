/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412Final at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL416b
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.DcSet
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanPunct

/-!
# GM Proposition 4.12, final step: from the external-distance bound to `Stab_{k,r}(z)`

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Proposition 4.12 (`prop-stab`), l. 2257–2276: with (4.40)
`d^{ℂ∖𝓑^•_{t_k}}(P, ∂𝓑^•_{t_k} ∖ I_k) ≥ ρ`, Lemma 4.16 (`diam P'([t_k, |P'|]) ≤ A`), and
`P ∩ B_r(z) ≠ ∅`, the triangle inequality (4.42) gives `d^U(P, P'(t_k)) ≤ 2r + A < ρ`, hence
`P'(t_k) ∈ I_k` "for any possible choice of `P'`", i.e. `Stab_{k,r}(z)` (GM (4.11)).

`p412_hit_mem_of_dU`: every point where a `D(·,·;ℂ∖cl B_r(z))`-geodesic `Q` hits
`∂𝓑^•_t` lies in `I`. GM writes `P'(t_k)` for "the" hitting point; we prove what this uses:
* `p412_avoid_len_le`: if `Q(s) ∈ 𝓑^•_t` then `len(Q|_{[0,s]}) ≤ t` (a `D`-geodesic to `Q(s)`
  stays in `𝓑^•_t`, which avoids `B_r(z)`; minimality of `Q`, `gm_avoid_len_le_internal`);
* `p412_avoid_hit_eq`: hence after its first hit of `∂𝓑^•_t`, `Q` stays at that point as long
  as it is in `𝓑^•_t` (zero length), so all hitting points coincide with the last exit point;
* the set `X = Q((u₁, T]) ∪ cl B_r(z) ⊆ ℂ ∖ 𝓑^•_t` (connected, Euclidean diameter `≤ A + 2r`)
  has `p` and the exit point `Q(u₁)` in its closure, which is GM's (4.42) for `d^U`.
These intermediate facts are implicit in GM (own elementary arguments, DEVIATIONS entry
proposed in the P2-M2J2 report).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

section Final
variable {D : ContMetric} {𝕫 z x : ℂ} {r t : ℝ} {Q : ℝ → ℂ} {T : ℝ}

/-- a `D`-geodesic from `𝕫` to a point of `𝓑^•_t` stays in `𝓑^•_t` -/
theorem p412_internal_filledBall_le (hgeod : ∀ y, ∃ G : ℝ → ℂ, IsGeodesicL D G (D.1 (𝕫, y)) 𝕫 y)
    {y : ℂ} (hy : y ∈ filledBall D 𝕫 t) (hyt : D.1 (𝕫, y) ≤ t) :
    D.internal (filledBall D 𝕫 t) 𝕫 y ≤ ENNReal.ofReal (D.1 (𝕫, y)) := by
  obtain ⟨G, hG⟩ := hgeod y
  refine gm_internal_le_of_geod D hG fun u hu => ?_
  obtain ⟨hL0, hG0, hGL, hGd⟩ := hG
  rcases (hu.2.trans hyt).lt_or_eq with hlt | heq
  · have hd : D.1 (𝕫, G u) = u := by
      have := hGd 0 (left_mem_Icc.2 hL0) u hu
      rw [hG0] at this; rw [this]; simp [abs_of_nonneg hu.1]
    exact Or.inl (subset_closure (show D.1 (𝕫, G u) < t by rw [hd]; exact hlt))
  · have hu' : u = D.1 (𝕫, y) := le_antisymm hu.2 (heq ▸ hyt)
    rw [hu', hGL]; exact hy

/-- If `Q(s) ∈ 𝓑^•_t` and `𝓑^•_t` avoids `B_r(z)`, then `len(Q|_{[0,s]}) ≤ D(𝕫, Q(s))`. -/
theorem p412_avoid_len_le (hQ : IsAvoidGeod D 𝕫 z r x Q T) (hfin : D.len Q 0 T ≠ ⊤)
    (hgeod : ∀ y, ∃ G : ℝ → ℂ, IsGeodesicL D G (D.1 (𝕫, y)) 𝕫 y)
    (hdisj : Disjoint (ball z r) (filledBall D 𝕫 t)) {s : ℝ} (hs : s ∈ Icc 0 T)
    (hQs : Q s ∈ filledBall D 𝕫 t) (hQt : D.1 (𝕫, Q s) ≤ t) :
    D.len Q 0 s ≤ ENNReal.ofReal (D.1 (𝕫, Q s)) :=
  (gm_avoid_len_le_internal hQ hfin hs (V := filledBall D 𝕫 t)
    (fun _ hv hb => disjoint_left.1 hdisj hb hv)).trans
    (p412_internal_filledBall_le hgeod hQs hQt)

/-- Two hitting times `s₁ ≤ s₂` of `∂𝓑^•_t` by `Q` give the same point (zero length between). -/
theorem p412_avoid_hit_eq (hQ : IsAvoidGeod D 𝕫 z r x Q T) (hfin : D.len Q 0 T ≠ ⊤)
    (hgeod : ∀ y, ∃ G : ℝ → ℂ, IsGeodesicL D G (D.1 (𝕫, y)) 𝕫 y)
    (hbd : Bornology.IsBounded (ballM D 𝕫 t))
    (hdisj : Disjoint (ball z r) (filledBall D 𝕫 t)) {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc 0 T)
    (hs₂ : s₂ ∈ Icc 0 T) (h12 : s₁ ≤ s₂) (h1 : Q s₁ ∈ frontier (filledBall D 𝕫 t))
    (h2 : Q s₂ ∈ frontier (filledBall D 𝕫 t)) : Q s₂ = Q s₁ := by
  have hQ0 : Q 0 = 𝕫 := hQ.2.2.1
  have hd1 : D.1 (𝕫, Q s₁) = t := jp_frontier_subset_sphere hbd h1
  have hd2 : D.1 (𝕫, Q s₂) = t := jp_frontier_subset_sphere hbd h2
  have h2K : Q s₂ ∈ filledBall D 𝕫 t := (gm_filledBall_isClosed D 𝕫 t).frontier_subset h2
  have hA := p412_avoid_len_le hQ hfin hgeod hdisj hs₂ h2K hd2.le
  rw [hd2] at hA
  have hB : ENNReal.ofReal t ≤ D.len Q 0 s₁ := by
    have := gm_D_le_len D Q hs₁.1
    rwa [hQ0, hd1] at this
  have hadd := MetricGeometry.curveLength_add (D.pt ∘ Q) hs₁.1 h12
  change D.len Q 0 s₁ + D.len Q s₁ s₂ = D.len Q 0 s₂ at hadd
  have hfin1 : D.len Q 0 s₁ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((le_self_add).trans (hadd.le.trans hA))
  have hzero : D.len Q s₁ s₂ = 0 := by
    have h3 : D.len Q 0 s₁ + D.len Q s₁ s₂ ≤ D.len Q 0 s₁ + 0 := by
      rw [add_zero, hadd]; exact hA.trans hB
    exact le_antisymm ((ENNReal.add_le_add_iff_left hfin1).1 h3) bot_le
  have := gm_D_le_len D Q h12
  rw [hzero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
  have hnn : 0 ≤ D.1 (Q s₁, Q s₂) := dist_nonneg (x := D.pt (Q s₁)) (y := D.pt (Q s₂))
  exact (D.2.eq_of_eq_zero _ _ (le_antisymm this hnn)).symm

/-- **GM Prop 4.12, final step** (l. 2257–2276, (4.40)–(4.42)): let `Q` be a
`D(·,·;ℂ∖cl B_r(z))`-geodesic from `𝕫` to `∂B_r(z)` whose points reached after `D`-length `t`
are within Euclidean distance `A` of each other (Lemma 4.16), let `cl B_r(z) ∩ 𝓑^•_t = ∅`, and
let `p ∈ cl B_r(z)` satisfy `d^{ℂ∖𝓑^•_t}(p, ∂𝓑^•_t ∖ I) ≥ ρ > A + 2r` ((4.40) at a point of
`P ∩ B_r(z)`). Then every point where `Q` hits `∂𝓑^•_t` lies in `I`. -/
theorem p412_hit_mem_of_dU (hQ : IsAvoidGeod D 𝕫 z r x Q T) (hfin : D.len Q 0 T ≠ ⊤)
    (hgeod : ∀ y, ∃ G : ℝ → ℂ, IsGeodesicL D G (D.1 (𝕫, y)) 𝕫 y)
    (hbd : Bornology.IsBounded (ballM D 𝕫 t))
    (hdisj : Disjoint (closedBall z r) (filledBall D 𝕫 t)) {A ρ : ℝ} {I : Set ℂ} {p : ℂ}
    (hp : p ∈ closedBall z r)
    (hdiam : ∀ s₁ ∈ Icc 0 T, ∀ s₂ ∈ Icc 0 T, ENNReal.ofReal t ≤ D.len Q 0 s₁ →
      ENNReal.ofReal t ≤ D.len Q 0 s₂ → ‖Q s₁ - Q s₂‖ ≤ A)
    (hext : ∀ v ∈ frontier (filledBall D 𝕫 t) \ I,
      ENNReal.ofReal ρ ≤ dU (filledBall D 𝕫 t)ᶜ p v)
    (hρ : A + 2 * r < ρ) :
    Q '' Icc 0 T ∩ frontier (filledBall D 𝕫 t) ⊆ I := by
  rintro _ ⟨⟨u₀, hu₀, rfl⟩, hfr⟩
  obtain ⟨hT0, hQc, hQ0, hQT, hxs, hQout, hmin⟩ := hQ
  set K := filledBall D 𝕫 t with hKdef
  have hKc : IsClosed K := gm_filledBall_isClosed D 𝕫 t
  have hr0 : 0 ≤ r := by have := mem_sphere.1 hxs; rw [← this]; exact dist_nonneg
  have hdisj' : Disjoint (ball z r) K := hdisj.mono_left ball_subset_closedBall
  have hxK : x ∉ K := fun hx => disjoint_left.1 hdisj (sphere_subset_closedBall hxs) hx
  -- `D`-length at least `t` after `u₀`
  have hlen : ∀ s ∈ Icc u₀ T, ENNReal.ofReal t ≤ D.len Q 0 s := by
    intro s hs
    have h1 := gm_D_le_len D Q hu₀.1
    rw [hQ0, jp_frontier_subset_sphere hbd hfr] at h1
    have hadd := MetricGeometry.curveLength_add (D.pt ∘ Q) hu₀.1 hs.1
    change D.len Q 0 u₀ + D.len Q u₀ s = D.len Q 0 s at hadd
    exact h1.trans (le_self_add.trans hadd.le)
  have hTT : T ∈ Icc u₀ T := ⟨hu₀.2, le_rfl⟩
  have hA0 : 0 ≤ A :=
    le_trans (by simp) (hdiam T ⟨hT0, le_rfl⟩ T ⟨hT0, le_rfl⟩ (hlen T hTT) (hlen T hTT))
  have hρ0 : 0 < ρ := by linarith
  -- the last time `u₁ ≥ u₀` at which `Q` is in `K`
  set S := Icc u₀ T ∩ Q ⁻¹' K with hSdef
  have hSc : IsClosed S :=
    (hQc.mono (Icc_subset_Icc hu₀.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc hKc
  have hSne : S.Nonempty := ⟨u₀, ⟨le_rfl, hu₀.2⟩, hKc.frontier_subset hfr⟩
  have hSbdd : BddAbove S := ⟨T, fun s hs => hs.1.2⟩
  set u₁ := sSup S with hu₁def
  have hu₁S : u₁ ∈ S := hSc.csSup_mem hSne hSbdd
  have hu₁T : u₁ < T := by
    refine lt_of_le_of_ne hu₁S.1.2 fun h => hxK ?_
    have : Q T ∈ K := h ▸ hu₁S.2
    rwa [hQT] at this
  have hafter : ∀ s ∈ Ioc u₁ T, Q s ∈ Kᶜ := fun s hs hsK =>
    absurd (le_csSup hSbdd ⟨⟨hu₁S.1.1.trans hs.1.le, hs.2⟩, hsK⟩) (not_le.2 hs.1)
  have hQX : Q '' Ioc u₁ T ⊆ Kᶜ := image_subset_iff.2 fun s hs => hafter s hs
  have hIocI : Ioc u₁ T ⊆ Icc 0 T := fun s hs => ⟨hu₀.1.trans (hu₁S.1.1.trans hs.1.le), hs.2⟩
  have hcl : Q u₁ ∈ closure (Q '' Ioc u₁ T) := by
    have hcw : ContinuousWithinAt Q (Ioc u₁ T) u₁ :=
      (hQc u₁ ⟨hu₀.1.trans hu₁S.1.1, hu₁S.1.2⟩).mono hIocI
    have hmem : u₁ ∈ closure (Ioc u₁ T) := by rw [closure_Ioc hu₁T.ne]; exact ⟨le_rfl, hu₁T.le⟩
    exact hcw.mem_closure_image hmem
  have hu₁fr : Q u₁ ∈ frontier K := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hu₁S.2, closure_mono hQX hcl⟩
  have hEq : Q u₁ = Q u₀ :=
    p412_avoid_hit_eq ⟨hT0, hQc, hQ0, hQT, hxs, hQout, hmin⟩ hfin hgeod hbd hdisj' hu₀
      ⟨hu₀.1.trans hu₁S.1.1, hu₁S.1.2⟩ hu₁S.1.1 hfr hu₁fr
  -- the connected set `X = Q((u₁, T]) ∪ cl B_r(z) ⊆ ℂ ∖ K`
  set X := Q '' Ioc u₁ T ∪ closedBall z r with hXdef
  have hXU : X ⊆ Kᶜ := union_subset hQX
    (fun y hy hyK => disjoint_left.1 hdisj hy hyK)
  have hQTX : Q T ∈ Q '' Ioc u₁ T := ⟨T, ⟨hu₁T, le_rfl⟩, rfl⟩
  have hQTB : Q T ∈ closedBall z r := by rw [hQT]; exact sphere_subset_closedBall hxs
  have hXc : IsConnected X := by
    refine ⟨⟨Q T, Or.inr hQTB⟩, IsPreconnected.union (Q T) hQTX hQTB ?_
      (convex_closedBall z r).isPreconnected⟩
    exact ((isConnected_Ioc hu₁T).image Q (hQc.mono hIocI)).isPreconnected
  have hdU := dc_dU_le hXU hXc (subset_closure (Or.inr hp))
    (closure_mono subset_union_left hcl)
  have hd1 : Metric.ediam (Q '' Ioc u₁ T) ≤ ENNReal.ofReal A := by
    refine Metric.ediam_le ?_
    rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩
    rw [edist_dist, dist_eq_norm]
    refine ENNReal.ofReal_le_ofReal (hdiam s₁ (hIocI hs₁) s₂ (hIocI hs₂) ?_ ?_)
    · exact hlen s₁ ⟨hu₁S.1.1.trans hs₁.1.le, hs₁.2⟩
    · exact hlen s₂ ⟨hu₁S.1.1.trans hs₂.1.le, hs₂.2⟩
  have hd2 : Metric.ediam (closedBall z r) ≤ ENNReal.ofReal (2 * r) := by
    refine Metric.ediam_le fun a ha b hb => ?_
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    have := dist_triangle_right a b z
    linarith [mem_closedBall.1 ha, mem_closedBall.1 hb]
  have hX : Metric.ediam X ≤ ENNReal.ofReal (A + 2 * r) := by
    rw [ENNReal.ofReal_add hA0 (by positivity)]
    exact (Metric.ediam_union_le ⟨Q T, hQTX, hQTB⟩).trans (add_le_add hd1 hd2)
  by_contra hI
  have h1 := hext (Q u₀) ⟨hfr, hI⟩
  rw [← hEq] at h1
  have h2 := (h1.trans hdU).trans hX
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  linarith

end Final

end LQGMetric.GM
