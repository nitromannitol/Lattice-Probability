/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.JTransfer at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.JDrawn
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Schoenflies.Disc
import LatticeProb.Bonanno.MatedCRTHarmonic.Topology.PlanarCore

/-!
# Route M, Lemma J (Jordan transfer) and Corollary J′

The transfer argument, on the abstract Core interface
`CellularEmbedding.MonotoneDrawing`. Let `C` be a cycle of `G.adj` whose drawn loop `Λ = Ψ ∘ D(C)` lies in the open
annulus `ρ₁ < |· - z| < ρ₂` and has non-zero degree about `z`.

* `separates_of_isCycle` (**Lemma J**): if `|Ψ w₁ - z| < ρ₁` and `|Ψ w₂ - z| > ρ₂`, every path from `w₁` to `w₂`
  (upstairs) meets `D(C)`.
* `disconnects_of_cycle` (**Corollary J′**, graph form; TF3 Details (a)): if `|Ψ(pt a) - z| < ρ₁` and
  `|Ψ(pt b) - z| > ρ₂`, every walk from `a` to `b` meets the support of `C`; `disconnects_support_of_cycle` is the
  frozen `LFMultigraph.Disconnects` form.
* `disconnects_of_closedWalk`: the same for any closed walk `W` with these properties (W1 + W3 extract a cycle
  inside `W`, then Corollary J′ applies), the form consumed by TF3's Lemma R and Lemma D″.

Proof of Lemma J (TF3 §6). `J = D(C)` is a Jordan curve (W4) with bounded component `Ω` and unbounded component
`Ω′` (landed Jordan curve theorem). A fibre of `Ψ` over a point off `Ψ(J)` is preconnected and misses `J`, so it
lies in `Ω` or in `Ω′`.
*Claim 1* (`w₁ ∈ Ω`): otherwise the fibre of `q₁ = Ψ w₁` misses `closure Ω`; contracting `D(C)` inside the closed
Schoenflies disc of `Ω` (landed `schoenflies_closedDisc`) gives a homotopy of `Λ - q₁` to a constant through loops
avoiding `0`, so `loopDeg (Λ - q₁) = 0`; but `loopDeg (Λ - q₁) = loopDeg (Λ - z) ≠ 0` (Rouché).
*Claim 2* (`w₂ ∈ Ω′`): the ray from `q₂ = Ψ w₂` away from `z` misses `Ψ(J)`, is preconnected and unbounded, and is
covered by the closed sets `Ψ(closure Ω)` (compact) and `Ψ(closure Ω′)` (`Ψ` is proper, hence closed), which are
disjoint on it by the fibre dichotomy; so it lies in `Ψ(closure Ω′)`, and the fibre of `q₂` meets, hence lies in,
`Ω′`.
No approximation of `Ψ` by homeomorphisms and no degree theory beyond the host `loopDeg` API is used.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bornology SimpleGraph SimpleGraph.Walk
open scoped unitInterval
open QuantumZipper.CA.Topo

namespace MatedCRTHarmonic.RouteM

variable {V E : Type*} {G : LFMultigraph V E} {o : V} {H : CellularEmbedding G o} (D : H.MonotoneDrawing)

/-- `Ψ` is proper, hence a closed map. -/
theorem isClosedMap_Ψ : IsClosedMap D.Ψ :=
  (isProperMap_iff_tendsto_cocompact.mpr ⟨D.continuous_Ψ, D.tendsto_Ψ⟩).isClosedMap

/-- **Fibre dichotomy**: a fibre of `Ψ` over a point off `Ψ(J)` lies in one of two disjoint open sets covering
`Jᶜ`. -/
theorem fiber_subset_or_subset {J Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hdisj : Disjoint Ω Ω')
    (hcover : Jᶜ = Ω ∪ Ω') {q : ℂ} (hq : q ∉ D.Ψ '' J) : D.Ψ ⁻¹' {q} ⊆ Ω ∨ D.Ψ ⁻¹' {q} ⊆ Ω' := by
  refine (D.isPreconnected_fiber q).subset_or_subset hΩ hΩ' hdisj fun w hw => ?_
  rw [← hcover]
  exact fun hwJ => hq ⟨w, hwJ, hw⟩

/-- **Lemma J** (TF3 §6). If the drawn loop of a cycle `C` lies in the annulus `ρ₁ < |· - z| < ρ₂` and has
non-zero degree about `z`, then `D(C)` separates every point `w₁` with `|Ψ w₁ - z| < ρ₁` from every point `w₂`
with `|Ψ w₂ - z| > ρ₂`. -/
theorem separates_of_isCycle {c : V} {C : G.adj.Walk c c} (hC : C.IsCycle) {z : ℂ} {ρ₁ ρ₂ : ℝ}
    (hann : ∀ u, ρ₁ < ‖drawnLoop D C u - z‖ ∧ ‖drawnLoop D C u - z‖ < ρ₂)
    (hne : ∀ t, (drawnLoop D C - ContinuousMap.const I z) t ≠ 0)
    (hdeg : loopDeg (drawnLoop D C - ContinuousMap.const I z) hne ≠ 0) {w₁ w₂ : ℂ}
    (h₁ : ‖D.Ψ w₁ - z‖ < ρ₁) (h₂ : ρ₂ < ‖D.Ψ w₂ - z‖) :
    Topology.Separates (range (drawnPath D C)) w₁ w₂ := by
  set P := drawnPath D C with hPdef
  set J := range P with hJdef
  have hJ : LQGMetric.JordanMap.IsJordanCurve J := isJordanCurve_range_drawnPath D hC
  obtain ⟨x₁, hx₁, x₀, -, hb, -, hdisj, hunion, hfr₁, hfr₀⟩ :=
    Planar.Jordan.jordan_curve_components_complex hJ
  set Ω := connectedComponentIn Jᶜ x₁ with hΩdef
  set Ω' := connectedComponentIn Jᶜ x₀ with hΩ'def
  have hJc : IsClosed J := (isCompact_range P.continuous).isClosed
  have hΩo : IsOpen Ω := hJc.isOpen_compl.connectedComponentIn
  have hΩ'o : IsOpen Ω' := hJc.isOpen_compl.connectedComponentIn
  have hKann : ∀ q ∈ D.Ψ '' J, ρ₁ < ‖q - z‖ ∧ ‖q - z‖ < ρ₂ := by
    rintro q hq
    rw [← range_drawnLoop D C] at hq
    obtain ⟨u, rfl⟩ := hq
    exact hann u
  have hfib : ∀ q ∉ D.Ψ '' J, D.Ψ ⁻¹' {q} ⊆ Ω ∨ D.Ψ ⁻¹' {q} ⊆ Ω' := fun q hq =>
    fiber_subset_or_subset D hΩo hΩ'o hdisj hunion hq
  have hclΩ : closure Ω = Ω ∪ J := by rw [closure_eq_self_union_frontier, hfr₁]
  have hclΩ' : closure Ω' = Ω' ∪ J := by rw [closure_eq_self_union_frontier, hfr₀]
  -- Claim 1: `w₁ ∈ Ω`.
  have hw₁ : w₁ ∈ Ω := by
    by_contra hw₁
    set q₁ := D.Ψ w₁ with hq₁def
    have hq₁K : q₁ ∉ D.Ψ '' J := fun hq => lt_asymm (hKann q₁ hq).1 h₁
    have hF : D.Ψ ⁻¹' {q₁} ⊆ Ω' := (hfib q₁ hq₁K).resolve_left fun hsub => hw₁ (hsub rfl)
    have hq₁cl : ∀ w ∈ closure Ω, D.Ψ w ≠ q₁ := by
      intro w hw hwq
      rw [hclΩ] at hw
      rcases hw with hw | hw
      · exact hdisj.ne_of_mem hw (hF hwq) rfl
      · exact hq₁K ⟨w, hw, hwq⟩
    obtain ⟨e, -, -⟩ := Planar.Schoenflies.schoenflies_closedDisc hJ hx₁ hb
    have hPmem : ∀ u, P u ∈ closure Ω := fun u => by
      rw [hclΩ]
      exact Or.inr ⟨u, rfl⟩
    let g : I → closedBall (0 : ℂ) 1 := fun u => e.symm ⟨P u, hPmem u⟩
    have hg : Continuous g := e.symm.continuous.comp (P.continuous.subtype_mk _)
    have hmem : ∀ (s : I) (x : closedBall (0 : ℂ) 1),
        ((1 - (s : ℝ) : ℝ) : ℂ) * (x : ℂ) ∈ closedBall (0 : ℂ) 1 := by
      intro s x
      have hx : ‖(x : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
      have hs0 : 0 ≤ 1 - (s : ℝ) := by linarith [s.2.2]
      have hs1 : 1 - (s : ℝ) ≤ 1 := by linarith [s.2.1]
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
      calc (1 - (s : ℝ)) * ‖(x : ℂ)‖ ≤ 1 * 1 := mul_le_mul hs1 hx (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    let shrink : I × I → closedBall (0 : ℂ) 1 := fun p => ⟨_, hmem p.2 (g p.1)⟩
    have hshrink : Continuous shrink := by
      refine Continuous.subtype_mk ?_ _
      have h1 : Continuous fun p : I × I => ((1 - ((p.2 : I) : ℝ) : ℝ) : ℂ) := by fun_prop
      have h2 : Continuous fun p : I × I => ((g p.1 : closedBall (0 : ℂ) 1) : ℂ) :=
        continuous_subtype_val.comp (hg.comp continuous_fst)
      exact h1.mul h2
    let Hm : C(I × I, ℂ) := ⟨fun p => D.Ψ (e (shrink p) : ℂ) - q₁,
      (D.continuous_Ψ.comp (continuous_subtype_val.comp (e.continuous.comp hshrink))).sub continuous_const⟩
    have hHne : ∀ p, Hm p ≠ 0 := fun p => sub_ne_zero.mpr (hq₁cl _ (e (shrink p)).2)
    have hP01 : P 0 = P 1 := by rw [P.source, P.target]
    have hHc : ∀ s, Hm (0, s) = Hm (1, s) := by
      intro s
      have hg01 : g 0 = g 1 := by
        change e.symm ⟨P 0, hPmem 0⟩ = e.symm ⟨P 1, hPmem 1⟩
        congr 1
        exact Subtype.ext hP01
      change D.Ψ (e (shrink (0, s)) : ℂ) - q₁ = D.Ψ (e (shrink (1, s)) : ℂ) - q₁
      have : shrink (0, s) = shrink (1, s) := by
        apply Subtype.ext
        change ((1 - (s : ℝ) : ℝ) : ℂ) * (g 0 : ℂ) = ((1 - (s : ℝ) : ℝ) : ℂ) * (g 1 : ℂ)
        rw [hg01]
      rw [this]
    have hhom := loopDeg_homotopy Hm hHne hHc
    have hs0 : slice Hm 0 = drawnLoop D C - ContinuousMap.const I q₁ := by
      ext u
      change D.Ψ (e (shrink (u, 0)) : ℂ) - q₁ = D.Ψ (P u) - q₁
      have : shrink (u, 0) = g u := by
        apply Subtype.ext
        change ((1 - ((0 : I) : ℝ) : ℝ) : ℂ) * (g u : ℂ) = (g u : ℂ)
        simp
      rw [this]
      change D.Ψ ((e (e.symm ⟨P u, hPmem u⟩) : closure Ω) : ℂ) - q₁ = D.Ψ (P u) - q₁
      rw [e.apply_symm_apply]
    set c₀ : ℂ := D.Ψ (e ⟨0, mem_closedBall_self zero_le_one⟩ : ℂ) - q₁ with hc₀
    have hs1 : slice Hm 1 = ContinuousMap.const I c₀ := by
      ext u
      change D.Ψ (e (shrink (u, 1)) : ℂ) - q₁ = c₀
      have : shrink (u, 1) = ⟨0, mem_closedBall_self zero_le_one⟩ := by
        apply Subtype.ext
        change ((1 - ((1 : I) : ℝ) : ℝ) : ℂ) * (g u : ℂ) = 0
        simp
      rw [this]
    have hc₀ne : c₀ ≠ 0 := by
      have := hHne (0, 1)
      have h' : Hm (0, 1) = c₀ := by
        have := congrArg (fun γ : C(I, ℂ) => γ 0) hs1
        simpa [slice] using this
      rwa [h'] at this
    have hq₁ne : ∀ t, (drawnLoop D C - ContinuousMap.const I q₁) t ≠ 0 := by
      intro t
      rw [← hs0]
      exact hHne _
    have hdeg0 : loopDeg (drawnLoop D C - ContinuousMap.const I q₁) hq₁ne = 0 := by
      rw [JAux.loopDeg_congr hs0.symm hq₁ne (fun _ => hHne _), hhom,
        JAux.loopDeg_congr hs1 (fun _ => hHne _) (fun _ => hc₀ne)]
      exact loopDeg_const c₀ hc₀ne
    have hrouche : loopDeg (drawnLoop D C - ContinuousMap.const I q₁) hq₁ne =
        loopDeg (drawnLoop D C - ContinuousMap.const I z) hne := by
      refine loopDeg_eq_of_norm_sub_lt _ _ hq₁ne hne ?_ ?_ fun t => ?_
      · simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply, drawnLoop_closed D C]
      · simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply, drawnLoop_closed D C]
      · simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
        have hq : drawnLoop D C t - q₁ - (drawnLoop D C t - z) = -(q₁ - z) := by ring
        rw [hq, norm_neg]
        exact h₁.trans (hann t).1
    exact hdeg (hrouche ▸ hdeg0)
  -- Claim 2: `w₂ ∈ Ω'`.
  have hw₂ : w₂ ∈ Ω' := by
    set q₂ := D.Ψ w₂ with hq₂def
    have hρ₂ : 0 < ρ₂ := lt_of_le_of_lt (norm_nonneg _) (hann 0).2
    have hq₂z : 0 < ‖q₂ - z‖ := hρ₂.trans h₂
    let ray : ℝ → ℂ := fun t => z + (t : ℂ) * (q₂ - z)
    have hray : Continuous ray := by fun_prop
    set S := ray '' Ici 1 with hSdef
    have hSconn : IsPreconnected S := isPreconnected_Ici.image ray hray.continuousOn
    have hq₂S : q₂ ∈ S := ⟨1, mem_Ici.mpr le_rfl, by simp [ray]⟩
    have hraynorm : ∀ t : ℝ, 0 ≤ t → ‖ray t - z‖ = t * ‖q₂ - z‖ := by
      intro t ht
      simp only [ray, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    have hSnorm : ∀ q ∈ S, ‖q₂ - z‖ ≤ ‖q - z‖ := by
      rintro q ⟨t, ht, rfl⟩
      rw [hraynorm t (le_trans zero_le_one ht)]
      exact le_mul_of_one_le_left (norm_nonneg _) ht
    have hSK : ∀ q ∈ S, q ∉ D.Ψ '' J := fun q hq hK =>
      lt_irrefl _ (((hKann q hK).2.trans h₂).trans_le (hSnorm q hq))
    have hAc : IsCompact (D.Ψ '' closure Ω) := hb.isCompact_closure.image D.continuous_Ψ
    have hBc : IsClosed (D.Ψ '' closure Ω') := isClosedMap_Ψ D _ isClosed_closure
    have hScov : S ⊆ D.Ψ '' closure Ω ∪ D.Ψ '' closure Ω' := by
      intro q _
      obtain ⟨w, rfl⟩ := D.surjective_Ψ q
      by_cases hwJ : w ∈ J
      · exact Or.inl ⟨w, by rw [hclΩ]; exact Or.inr hwJ, rfl⟩
      · have hw : w ∈ Jᶜ := hwJ
        rw [hunion] at hw
        rcases hw with hw | hw
        · exact Or.inl ⟨w, subset_closure hw, rfl⟩
        · exact Or.inr ⟨w, subset_closure hw, rfl⟩
    have hSdisj : S ∩ (D.Ψ '' closure Ω ∩ D.Ψ '' closure Ω') = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr ?_
      rintro q ⟨hqS, ⟨w, hw, hwq⟩, ⟨w', hw', hw'q⟩⟩
      have hqK := hSK q hqS
      have hwΩ : w ∈ Ω := by
        rw [hclΩ] at hw
        exact hw.resolve_right fun h => hqK ⟨w, h, hwq⟩
      have hw'Ω' : w' ∈ Ω' := by
        rw [hclΩ'] at hw'
        exact hw'.resolve_right fun h => hqK ⟨w', h, hw'q⟩
      rcases hfib q hqK with hsub | hsub
      · exact hdisj.ne_of_mem (hsub hw'q) hw'Ω' rfl
      · exact hdisj.ne_of_mem hwΩ (hsub hwq) rfl
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hSconn _ _ hAc.isClosed hBc hScov hSdisj with
      hSA | hSB
    · exfalso
      obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall z).mp (hAc.isBounded.subset hSA)
      set t : ℝ := max 1 ((|r| + 1) / ‖q₂ - z‖) with ht
      have ht1 : 1 ≤ t := le_max_left _ _
      have hmemS : ray t ∈ S := ⟨t, mem_Ici.mpr ht1, rfl⟩
      have hle := hr hmemS
      rw [mem_closedBall, dist_eq_norm, hraynorm t (le_trans zero_le_one ht1)] at hle
      have hbig : |r| + 1 ≤ t * ‖q₂ - z‖ := by
        have := le_max_right 1 ((|r| + 1) / ‖q₂ - z‖)
        rw [← ht] at this
        calc |r| + 1 = ((|r| + 1) / ‖q₂ - z‖) * ‖q₂ - z‖ := by field_simp
          _ ≤ t * ‖q₂ - z‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      linarith [le_abs_self r]
    · obtain ⟨w', hw', hw'q⟩ := hSB hq₂S
      have hq₂K := hSK q₂ hq₂S
      have hw'Ω' : w' ∈ Ω' := by
        rw [hclΩ'] at hw'
        exact hw'.resolve_right fun h => hq₂K ⟨w', h, hw'q⟩
      rcases hfib q₂ hq₂K with hsub | hsub
      · exact absurd hw'Ω' fun h => hdisj.ne_of_mem (hsub hw'q) h rfl
      · exact hsub rfl
  -- Conclusion: `Ω` and `Ω'` are different components of `Jᶜ`.
  intro γ
  by_contra hγ
  have hγ' : ∀ t, γ t ∈ Jᶜ := fun t hγt => hγ ⟨t, hγt⟩
  have hsub : range γ ⊆ Ω ∪ Ω' := by
    rintro _ ⟨t, rfl⟩
    have := hγ' t
    rwa [hunion] at this
  rcases (isPreconnected_range γ.continuous).subset_or_subset hΩo hΩ'o hdisj hsub with h | h
  · exact hdisj.ne_of_mem (h ⟨1, γ.target⟩) hw₂ rfl
  · exact hdisj.ne_of_mem hw₁ (h ⟨0, γ.source⟩) rfl

/-- **Corollary J′** (graph form, TF3 §6 and Details (a)): under the hypotheses of Lemma J on the cycle `C`, every
walk from a vertex `a` with `|Ψ(pt a) - z| < ρ₁` to a vertex `b` with `|Ψ(pt b) - z| > ρ₂` meets the support of
`C`. -/
theorem disconnects_of_cycle {c : V} {C : G.adj.Walk c c} (hC : C.IsCycle) {z : ℂ} {ρ₁ ρ₂ : ℝ}
    (hann : ∀ u, ρ₁ < ‖drawnLoop D C u - z‖ ∧ ‖drawnLoop D C u - z‖ < ρ₂)
    (hne : ∀ t, (drawnLoop D C - ContinuousMap.const I z) t ≠ 0)
    (hdeg : loopDeg (drawnLoop D C - ContinuousMap.const I z) hne ≠ 0) {a b : V}
    (ha : ‖D.Ψ (D.pt a) - z‖ < ρ₁) (hb : ρ₂ < ‖D.Ψ (D.pt b) - z‖) (w : G.adj.Walk a b) :
    ∃ y ∈ w.support, y ∈ C.support := by
  obtain ⟨t, ht⟩ := separates_of_isCycle D hC hann hne hdeg ha hb (drawnPath D w)
  exact exists_mem_support_of_mem_range D w C ⟨t, rfl⟩ ht

/-- **Corollary J′ for closed walks** (TF3 §8 steps 4–5, §9 steps 3–4): if the drawn loop of a closed walk `W` lies
in the annulus `ρ₁ < |· - z| < ρ₂` and has non-zero degree about `z`, every walk from a vertex `a` with
`|Ψ(pt a) - z| < ρ₁` to a vertex `b` with `|Ψ(pt b) - z| > ρ₂` meets the support of `W`. (W1 + W3 extract a cycle of
`W` with the same properties, `exists_isCycle_loopDeg_ne_zero`; then `disconnects_of_cycle`.) -/
theorem disconnects_of_closedWalk {u : V} (W : G.adj.Walk u u) {z : ℂ} {ρ₁ ρ₂ : ℝ}
    (hann : ∀ t, ρ₁ < ‖drawnLoop D W t - z‖ ∧ ‖drawnLoop D W t - z‖ < ρ₂)
    (hne : ∀ t, (drawnLoop D W - ContinuousMap.const I z) t ≠ 0)
    (hdeg : loopDeg (drawnLoop D W - ContinuousMap.const I z) hne ≠ 0) {a b : V}
    (ha : ‖D.Ψ (D.pt a) - z‖ < ρ₁) (hb : ρ₂ < ‖D.Ψ (D.pt b) - z‖) (w : G.adj.Walk a b) :
    ∃ y ∈ w.support, y ∈ W.support := by
  obtain ⟨c, C, hC, -, hsupp, hrange, hCne, hCdeg⟩ := exists_isCycle_loopDeg_ne_zero D W hne hdeg
  have hannC : ∀ t, ρ₁ < ‖drawnLoop D C t - z‖ ∧ ‖drawnLoop D C t - z‖ < ρ₂ := by
    intro t
    obtain ⟨s, hs⟩ := hrange ⟨t, rfl⟩
    rw [← hs]
    exact hann s
  obtain ⟨y, hyw, hyC⟩ := disconnects_of_cycle D hC hannC hCne hCdeg ha hb w
  exact ⟨y, hyw, hsupp y hyC⟩

end MatedCRTHarmonic.RouteM
