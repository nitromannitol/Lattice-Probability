/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53I4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53I3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X15
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K1

/-!
# Walled DZZ Lemma 3.12 (Remark 5.2) for the restricted partition, with a margin (P2-DZZ53I)

DZZ arXiv:1807.00422, Lemma 3.12 (l. 1300–1302) and its proof (l. 1428–1499), for the walled
approximate distance `D'^K_δ` of D117 §3 (cells of the global `𝒱_δ` meeting `K`). The proof of
DZZ starts the surgery from a `D'_δ`-geodesic; here it starts from a `D'^K_δ`-geodesic
(`exists_geodesic_chainOn`) and runs the localized surgery `l312SurgeryLoc` (S5L53I3). The
enclosures used by the surgery live in `𝖢_large \ 𝖢` and need not meet `K`, so the cells of the
good sequence are only within `8 δ^{C_Mc}` of `K` (`eventRegularNear`); see the handoff
P2-DZZ53I for why `eventRegularIn` (cells meeting `K` itself) is not reached by DZZ's argument.

* `eventRegularNear K r` = `𝓔_{δ,α*}` ∩ {`D'^K_δ(x,y) < ∞` ⇒ a good sequence of cells meeting the
  closed `r`-neighbourhood of `K`, joining `x`, `y`, with `d ≤ D'^K_δ(x,y) e^{(log δ⁻¹)^{0.6}}`};
* **`dzz_lemma312Near`**: there is `α* > 0` with `𝓔_{δ,α*}` likely and
  `P(eventRegularNear K (8 δ^{C_Mc}) …)ᶜ ≤ e^{−(log δ⁻¹)^{1/4}}` for all small `δ`, every `K` and
  all `u, v ∈ 𝕍`. The probabilistic part is a copy of `dzz_lemma312_of_X` (S3L12W1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

section Geo

variable {m : DyBox → ℝ} {δ : ℝ}

lemma mem_of_mem_support_on {S : Set DyBox} {a : DyBox} (ha : a ∈ S) :
    ∀ {b : DyBox} (p : (cellGraphOn S m δ).Walk a b), ∀ x ∈ p.support, x ∈ S
  | _, .nil, x, hx => by simp at hx; rw [hx]; exact ha
  | _, .cons h p, x, hx => by
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact mem_of_mem_support_on h.2.2 p x hx

/-- **`𝒞_0` for the walled distance**: a loop-free `Neighbour`-chain of cells of `S` joining `u`,
`v`, with at most `D'^S_δ(u, v)` cells (copy of `exists_geodesic_chain`, S3L12S2). -/
theorem exists_geodesic_chainOn {S : Set DyBox} {u v : ℂ} (hfin : approxDistOn S m δ u v ≠ ⊤) :
    ∃ l : List DyBox, JoinsCells m δ u v l ∧ l.IsChain Neighbour ∧ l.Nodup ∧ (∀ c ∈ l, c ∈ S) ∧
      (l.length : ℕ∞) ≤ approxDistOn S m δ u v := by
  have hlt : approxDistOn S m δ u v < approxDistOn S m δ u v + 1 :=
    ENat.lt_add_one_iff hfin |>.2 le_rfl
  conv_lhs at hlt => unfold approxDistOn
  simp only [iInf_lt_iff] at hlt
  obtain ⟨b, b', hb, hb', hlt⟩ := hlt
  have hle := (ENat.lt_add_one_iff hfin).1 hlt
  have hne : (cellGraphOn S m δ).edist b b' ≠ ⊤ := by
    intro h; rw [h] at hle; simp at hle; exact hfin hle
  obtain ⟨p₀, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  set p := p₀.bypass
  have hpl : p.length ≤ p₀.length := SimpleGraph.Walk.length_bypass_le_length p₀
  have hcell : ∀ x ∈ p.support, IsCell m δ x := by
    intro x hx
    have := isCell_of_mem_support hb.1 (p.mapLe (cellGraphOn_le S m δ)) x
      (by rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hx)
    exact this
  refine ⟨p.support, ⟨by simp, hcell, ?_, ?_⟩,
    (SimpleGraph.Walk.isChain_adj_support p).imp fun a b h => h.1.2.2,
    (SimpleGraph.Walk.bypass_isPath p₀).support_nodup, mem_of_mem_support_on hb.2.2 p, ?_⟩
  · rw [SimpleGraph.Walk.head_support]; exact hb.2.1
  · rw [SimpleGraph.Walk.getLast_support]; exact hb'.2.1
  · rw [SimpleGraph.Walk.length_support]
    refine le_trans ?_ hle
    rw [← hp]; push_cast; gcongr

end Geo

lemma l53Near_zero_of_mem {K : Set ℂ} {c : DyBox} (h : c ∈ cellsMeeting K) : L53Near K 0 c := by
  obtain ⟨z, hz1, hz2⟩ := h
  exact ⟨z, hz1, z, hz2, by simp⟩

lemma mem_cellsMeeting_of_near {K : Set ℂ} {r : ℝ} {c : DyBox} (h : L53Near K r c) :
    c ∈ cellsMeeting (Metric.cthickening r K) := by
  obtain ⟨z, hz, k, hk, hd⟩ := h
  exact ⟨z, hz, Metric.mem_cthickening_of_dist_le z k r K hk hd⟩

/-- DEC-93 packet P-6, proved (S3L12W10/W11, S3L12X3, S3L12X15). -/
theorem l53_cellRingOfCross : CellRingOfCross :=
  cellRingOfCross_of_ring (cellRingOfCrossRing_of_fine (fineRingOfCross_of_coarse
    coarseRingOfCross_holds))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Walled `𝓔_{δ,α*,x,y}` with margin `r`**: `𝓔_{δ,α*}` and, when `D'^K_δ(x,y) < ∞`, a good
sequence of cells meeting the closed `r`-neighbourhood of `K` joining `x`, `y`, with
`d ≤ D'^K_δ(x,y) e^{(log δ⁻¹)^{0.6}}`. -/
def eventRegularNear (K : Set ℂ) (r : ℝ) (γ : ℝ) (W : WNSpace → Ω → ℝ) (αs δ : ℝ) (x y : ℂ) :
    Set Ω :=
  eventEDeltaAlpha γ W αs δ ∩
    {ω | approxLGDIn K γ W δ x y ω ≠ ⊤ →
      ∃ l : List DyBox, JoinsCells (approxLQG γ W ω) δ x y l ∧ IsGoodSeq (epsStar αs δ) l ∧
        (∀ c ∈ l, c ∈ cellsMeeting (Metric.cthickening r K)) ∧
        ((l.length : ℕ∞) : ℝ≥0∞) ≤ ((approxLGDIn K γ W δ x y ω : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ)))}

/-- **Walled DZZ Lemma 3.12 with margin** (DZZ L3.12, l. 1300–1302, proof l. 1428–1499, for
`D'^K_δ`). -/
theorem dzz_lemma312Near (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ αs : ℝ, 0 < αs ∧ HighProb P (fun δ => eventEDeltaAlpha γ W αs δ) ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ K : Set ℂ, ∀ u ∈ dzzV, ∀ v ∈ dzzV,
        P (eventRegularNear K (8 * δ ^ dzzCMc γ) γ W αs δ u v)ᶜ ≤
          ENNReal.ofReal (Real.exp (-(Real.log δ⁻¹ ^ (1 / 4 : ℝ)))) := by
  have := hW.isProbabilityMeasure
  have h316 := dzz_lemma316X hW hγ hγ2
  obtain ⟨α₁, h316⟩ := h316
  obtain ⟨αs, hαs, δ₁, hδ₁, hb⟩ := h316 (max α₁ 1) (le_max_left _ _)
  have hα : 0 < max α₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hαs0 : 0 < αs := hα.trans hαs
  have hE1 := dzz_lemma34_of_pos hW hγ hγ2 hαs0
  refine ⟨αs, hαs0, hE1, ?_⟩
  obtain ⟨c₁, hc₁, δ₂, hδ₂, h₁⟩ := hE1
  obtain ⟨c₂, hc₂, δ₃, hδ₃, h₂⟩ := dzz_lemma34_fine hW hγ hγ2 hα
  obtain ⟨δ₄, hδ₄, hsurg⟩ := l312SurgeryLoc hγ hγ2 hαs0
  have hCmc : 0 ≤ dzzCmc γ := dzzCmc_nonneg hγ hγ2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ dzzCmc γ / Real.log 2 := div_nonneg hCmc hl2.le
  obtain ⟨L₀, hL₀⟩ := (l312_asym hc₁ hc₂ hA).exists_forall_of_atTop
  refine ⟨min (min δ₁ δ₂) (min (min δ₃ δ₄) (Real.exp (-(max L₀ 2)))), by positivity,
    fun δ hδ K u hu v hv => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ_1 : δ < δ₁ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ_2 : δ < δ₂ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ_3 : δ < δ₃ := hδ.2.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδ_4 : δ < δ₄ := hδ.2.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδ_e : δ < Real.exp (-(max L₀ 2)) := hδ.2.trans_le ((min_le_right _ _).trans
    (min_le_right _ _))
  set L := Real.log δ⁻¹ with hLdef
  have hLlog : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hLmax : max L₀ 2 < L := by
    have := Real.log_lt_log hδ0 hδ_e
    rw [Real.log_exp, hLlog] at this
    linarith
  have hL2 : 2 < L := lt_of_le_of_lt (le_max_right _ _) hLmax
  have hδ1 : δ < 1 := by
    have : Real.log δ < 0 := by rw [hLlog]; linarith
    exact (Real.log_neg_iff hδ0).mp this
  have hrpow : ∀ c : ℝ, δ ^ c = Real.exp (-(c * L)) := by
    intro c; rw [Real.rpow_def_of_pos hδ0, hLlog]; ring_nf
  -- notation
  set m := fun ω => approxLQG γ W ω
  set k := epsStarN αs δ
  have hk : 1 ≤ k := one_le_epsStarN hαs0 (by linarith)
  set y := dzzCmc γ * Real.logb 2 δ⁻¹ with hy
  have hlogb : Real.logb 2 δ⁻¹ = L / Real.log 2 := rfl
  have hy0 : 0 ≤ y := by rw [hy, hlogb]; positivity
  set N := ⌊y⌋₊ with hN
  have hNy : (N : ℝ) ≤ y := Nat.floor_le hy0
  have hyAL : y = dzzCmc γ / Real.log 2 * L := by rw [hy, hlogb]; ring
  have hnN : ∀ b : DyBox, b.n ≤ N → (b.n : ℝ) ≤ y := fun b hb =>
    ((Nat.le_floor_iff hy0).mp hb)
  set E2 := eventEFine γ W (max α₁ 1) δ
  set S1 : DyBox → Set Ω := fun b => {_ω | 1 ≤ b.n} ∩
    ({ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ E2 ∩ (encEventCross γ W αs δ b)ᶜ)
  set S2 : DyBox → Set Ω := fun b => {_ω | 1 ≤ b.n} ∩
    ({ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ E2 ∩
      {ω | ∃ b' ∈ boxColl b (epsStarN αs δ), δ ^ 2 ≤ approxLQG γ W ω b'})
  set U1 := {ω | ∃ b : DyBox, b.n ≤ N ∧ ω ∈ S1 b}
  set Uu := {ω | ∃ b : DyBox, b.n ≤ N ∧ u ∈ b.largeBox ∧ ω ∈ S2 b}
  set Uv := {ω | ∃ b : DyBox, b.n ≤ N ∧ v ∈ b.largeBox ∧ ω ∈ S2 b}
  -- the inclusion
  have hsub : (eventRegularNear K (8 * δ ^ dzzCMc γ) γ W αs δ u v)ᶜ ⊆
      (eventEDeltaAlpha γ W αs δ)ᶜ ∪ E2ᶜ ∪ U1 ∪ Uu ∪ Uv := by
    intro ω hω
    by_contra hne
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hne
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hne
    apply hω
    have hcs := h2.1
    have hlev : ∀ C, IsCell (m ω) δ C → 1 ≤ C.n ∧ C.n ≤ N := fun C hC =>
      ⟨one_le_n_of_side_le hδ0 hδ1 (dzzCMc_pos γ) (hcs.2 C hC).2,
        (Nat.le_floor_iff hy0).mpr (n_le_of_rpow_le_side hδ0 (hcs.2 C hC).1)⟩
    have henc : ∀ C, IsCell (m ω) δ C → HasCrossRing C (epsStarN αs δ)
        fun b' => m ω b' < δ ^ 2 := by
      intro C hC
      by_contra hnot
      exact h3 ⟨C, (hlev C hC).2, (hlev C hC).1, ⟨hC.1.le, h2⟩, hnot⟩
    have hgood : ∀ x ∈ dzzV, (¬ ∃ b : DyBox, b.n ≤ N ∧ x ∈ b.largeBox ∧ ω ∈ S2 b) →
        IsGoodPoint (m ω) δ (epsStar αs δ) x := by
      intro x _ hx
      refine isGoodPoint_of_boxColl hk fun C hC hxC b' hb' => ?_
      by_contra hlt
      exact hx ⟨C, (hlev C hC).2, hxC, (hlev C hC).1, ⟨hC.1.le, h2⟩, b', hb', not_lt.mp hlt⟩
    have gu := hgood u hu h4
    have gv := hgood v hv h5
    have hring : ∀ C, IsCell (m ω) δ C → CellRing (m ω) δ (epsStar αs δ) C := fun C hC => by
      have := l53_cellRingOfCross (m ω) δ C _ hC (hlev C hC).1 (henc C hC)
      simpa [epsStar] using this
    refine ⟨h1, fun hfin => ?_⟩
    obtain ⟨l0, hj0, hch0, hnd0, hS0, hlen0⟩ := exists_geodesic_chainOn hfin
    obtain ⟨l, hl1, hl2, hl3, hl4⟩ := hsurg δ ⟨hδ0, hδ_4⟩ (m ω) hcs.2 hring u v gu gv K _ le_rfl
      l0 hj0 hch0 hnd0 (fun c hc => l53Near_zero_of_mem (hS0 c hc))
    refine ⟨l, hl1, hl2, fun c hc => mem_cellsMeeting_of_near (hl3 c hc), hl4.trans ?_⟩
    gcongr; exact hlen0
  -- the bounds
  have hreal : ∀ (s : Set Ω) (x : ℝ), 0 ≤ x → P s ≤ ENNReal.ofReal x → P.real s ≤ x :=
    fun s x hx h => ENNReal.toReal_le_of_le_ofReal hx h
  have b1 : P.real (eventEDeltaAlpha γ W αs δ)ᶜ ≤ Real.exp (-(c₁ * L)) := by
    rw [← hrpow]; exact hreal _ _ (by positivity) (h₁ δ ⟨hδ0, hδ_2⟩)
  have b2 : P.real E2ᶜ ≤ Real.exp (-(c₂ * L)) := by
    rw [← hrpow]; exact hreal _ _ (by positivity) (h₂ δ ⟨hδ0, hδ_3⟩)
  have b3 : P.real U1 ≤ (N + 1) * ((2 : ℝ) ^ N) ^ 2 * δ ^ (10 * dzzCmc γ + 10) := by
    refine measureReal_levels_le N S1 (by positivity) fun b hbN => ?_
    by_cases h1 : 1 ≤ b.n
    · exact (measureReal_mono inter_subset_right).trans
        (hreal _ _ (by positivity) (hb δ ⟨hδ0, hδ_1⟩ b h1 (hnN b hbN)).1)
    · have : S1 b = ∅ := by
        ext ω; simp only [S1, mem_inter_iff, mem_ofPred_eq, h1, false_and, mem_empty_iff_false]
      rw [this, measureReal_empty]; positivity
  have bw : ∀ x ∈ dzzV, P.real {ω | ∃ b : DyBox, b.n ≤ N ∧ x ∈ b.largeBox ∧ ω ∈ S2 b} ≤
      9 * (N + 1) * Real.exp (-Real.sqrt L) := by
    intro x hx
    refine measureReal_window_levels_le N hx S2 (by positivity) fun b hbN _ => ?_
    by_cases h1 : 1 ≤ b.n
    · exact (measureReal_mono inter_subset_right).trans
        (hreal _ _ (by positivity) (hb δ ⟨hδ0, hδ_1⟩ b h1 (hnN b hbN)).2)
    · have : S2 b = ∅ := by
        ext ω; simp only [S2, mem_inter_iff, mem_ofPred_eq, h1, false_and, mem_empty_iff_false]
      rw [this, measureReal_empty]; positivity
  have b4 := bw u hu
  have b5 := bw v hv
  -- `(N + 1) (2^N)² δ^{10 C_mc + 10} ≤ (A L + 1) e^{-10 L}`
  have hN1 : (N : ℝ) + 1 ≤ dzzCmc γ / Real.log 2 * L + 1 := by linarith
  have hpow : ((2 : ℝ) ^ N) ^ 2 * δ ^ (10 * dzzCmc γ + 10) ≤ Real.exp (-(10 * L)) := by
    rw [two_pow_sq_eq, hrpow, ← Real.exp_add, Real.exp_le_exp]
    have : (N : ℝ) * Real.log 2 ≤ dzzCmc γ * L := by
      have := mul_le_mul_of_nonneg_right (hNy.trans_eq hyAL) hl2.le
      rwa [show dzzCmc γ / Real.log 2 * L * Real.log 2 = dzzCmc γ * L by field_simp] at this
    nlinarith
  have b3' : P.real U1 ≤ (dzzCmc γ / Real.log 2 * L + 1) * Real.exp (-(10 * L)) := by
    refine b3.trans ?_
    rw [mul_assoc]
    exact mul_le_mul hN1 hpow (by positivity) (by positivity)
  have b45 : ∀ x ∈ dzzV, P.real {ω | ∃ b : DyBox, b.n ≤ N ∧ x ∈ b.largeBox ∧ ω ∈ S2 b} ≤
      9 * ((dzzCmc γ / Real.log 2 * L + 1) * Real.exp (-Real.sqrt L)) := by
    intro x hx
    refine (bw x hx).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN1 (by positivity)) (by norm_num)
  have htot : P.real (eventRegularNear K (8 * δ ^ dzzCMc γ) γ W αs δ u v)ᶜ ≤ Real.exp (-(L ^ (1 / 4 : ℝ))) := by
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
    refine (measureReal_union_le _ _).trans ?_
    have u1 := measureReal_union_le (μ := P) ((eventEDeltaAlpha γ W αs δ)ᶜ ∪ E2ᶜ ∪ U1) Uu
    have u2 := measureReal_union_le (μ := P) ((eventEDeltaAlpha γ W αs δ)ᶜ ∪ E2ᶜ) U1
    have u3 := measureReal_union_le (μ := P) (eventEDeltaAlpha γ W αs δ)ᶜ E2ᶜ
    have := hL₀ L (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hLmax))
    have b4' := b45 u hu
    have b5' := b45 v hv
    linarith
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal htot


end DZZ
end LQGMetric
