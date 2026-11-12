/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32YCross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32YGeo

/-!
# DZZ P3.2 upper bound at the walled measure: the wall-interior crossing claim (D102, P-4aW)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`: the crossing claim of Lemma 3.5
(l. 1071–1079) with balls (P3.2 upper bound, l. 1098–1101), for the wall-interior ring curves
`∂B' ∩ 𝕍_{−r}` of decision D102 (decisions/DEC-102.md §4). The proof is the text of
`l32BallCrossingC_holds` (S3P32VCross) with the reduced rings `ringSqW` (`not_esc_ringW`,
`ringSqW_conn`, S3P32YSq), the curves `∂B ∩ 𝕍_{−r}` (`isPathConnected_frontier_chainW`), the
key meeting lemma `frontier_inter_W_of_bdry` and the ends `ball_endW` (S3P32YGeo).

**`l32BallCrossingW_holds : L32BallCrossingW`**, hence **`l32UpperCross_ofW'`**. Own argument
(DV-D84, DV-D102).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

set_option maxHeartbeats 1000000 in
/-- **DZZ's crossing claim for balls, wall-interior rings** (l. 1071–1079, 1098–1101; D102). -/
theorem l32BallCrossingW_holds : L32BallCrossingW := by
  intro m μ δ lam R ρ k N₀ A B _ hlam hR hr0 hr2 _ hN₀ h1 henc hAV hBV _ _ hA hB
  classical
  have hQ : 0 < 4 ^ (k + 2) * (lam + 1) := by positivity
  by_cases htop : approxDistSet m δ A B = ⊤
  · rw [htop]
    have hpos : ENNReal.ofReal (4 ^ (k + 2) * (lam + 1)) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hQ
    rw [ENat.toENNReal_top, ENNReal.top_mul hpos, top_add]
    exact le_top
  have hfin : ((approxDistSet m δ A B : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((approxDistSet m δ A B).toNat : ℝ) := by
    rw [ENNReal.ofReal_natCast, ← ENat.toENNReal_coe, ENat.natCast_toNat htop]
  obtain ⟨u, hu, v, hv, T, T', ⟨hT, hTu⟩, ⟨hT', hT'v⟩, q, hqd, -⟩ := exists_walk_of_le hfin
  set d := q.length + 1 with hd
  set C : ℕ → DyBox := fun i => q.getVert i with hCdef
  have hCc : ∀ i, IsCell m δ (C i) := fun i =>
    isCell_of_mem_support' hT q _ (q.getVert_mem_support i)
  set N := N₀ + k + 1 with hNdef
  have hNδ : ∀ b, IsCell m δ b → b.n ≤ N := fun b hb => by have := hN₀ b hb; omega
  have hE : ∀ i, HasEnclosure (C i) k fun b' => PhiLeW μ δ ρ b' lam := fun i => henc _ (hCc i)
  choose l hlne hlch hlall hlenc using hE
  have hlN : ∀ i, ∀ b ∈ l i, b.n = (C i).n + k := fun i b hb => (hlall i b hb).1.1
  have hlN' : ∀ i, ∀ b ∈ l i, b.n + 1 ≤ N := fun i b hb => by
    have := hlN i b hb; have := hN₀ _ (hCc i); omega
  have hlev1 : ∀ i, ∀ b ∈ l i, 1 ≤ b.n := fun i b hb => by
    have := hlN i b hb; have := h1 _ (hCc i); omega
  have hlsep : ∀ i, SqSep N (C i) {b | b ∈ l i} := fun i =>
    sqSep_of_enclosesBox (hlenc i) (fun b hb => by have := hlN' i b hb; omega)
      (by have := hN₀ _ (hCc i); omega)
  set Ring : ℕ → Set DyBox := fun i => ringSqW N {b | b ∈ l i} with hRing
  -- F1
  have hF1 : ∀ i < d, ∀ s : DyBox, s.n = N → s.closedBox ⊆ (C i).closedBox →
      s ∉ Ring i ∧ ¬ Esc (Ring i) (C i).largeBox s := by
    intro i _ s hs hsC
    refine ⟨?_, not_esc_ringW (hlsep i) (fun b hb => by have := hlN' i b hb; omega)
      (fun b hb => (hlall i b hb).2.1) hs hsC⟩
    rintro ⟨b, hb, hbs⟩
    exact disjoint_left.mp (hlall i b hb).2.1 (interior_mono hbs.2.1 (center_mem_interior' s))
      (hsC (center_mem_closedBox' s))
  have hconn : ∀ i, ∀ x ∈ Ring i, ∀ y ∈ Ring i, ConnIn (Ring i) x y := fun i =>
    ringSqW_conn (l i) (hlch i) (fun b hb => by have := hlN' i b hb; omega)
      (fun b hb => hlev1 i b hb) (fun b hb b' hb' => by rw [hlN i b hb, hlN i b' hb'])
  obtain ⟨M, p, lab, hp0, hpM, hl0, hlM, hall, hsteps⟩ := exists_labelled_path hNδ q hT
    (boxAt N u) (boxAt N v) rfl (boxAt_sub_of_mem hTu (hNδ T hT)) rfl
    (boxAt_sub_of_mem hT'v (hNδ T' hT'))
  obtain ⟨r, g, hgd, hch, hE0, hEr⟩ := l35_recursion (N := N) (d := d) (M := M) C Ring p lab
    (fun i _ => h1 _ (hCc i)) (fun i _ => by have := hN₀ _ (hCc i); omega) hF1
    (fun i _ => hconn i) (fun t ht => (hall t ht).1) (fun t ht => (hsteps t ht).1)
    (fun t ht => ⟨by have := (hall t ht).2.1; omega, (hall t ht).2.2⟩)
    (fun t ht => (hsteps t ht).2) hl0 (by omega)
  rw [hp0] at hE0
  rw [hpM] at hEr
  have hX : ∀ i, ∀ x ∈ Ring i, x.n = N ∧ x.closedBox ⊆ (C i).largeBox := by
    rintro i x ⟨b, hb, hxb⟩
    exact ⟨hxb.1, hxb.2.1.trans (hlall i b hb).1.2⟩
  -- the two ends
  obtain ⟨zA, ⟨BA, hBA, hzA⟩, KA, TA, hTA, hKA, hmA, uA, huA, hjA⟩ := ball_endW hr0.le hAV hA
    (hCc (g 0)) (by have := hN₀ _ (hCc (g 0)); omega) (fun b hb => (hlall _ b hb).1.2)
    (hX (g 0)) hu hE0 hR
  obtain ⟨zB, ⟨BB, hBB, hzB⟩, KB, TB, hTB, hKB, hmB, vB, hvB, hjB⟩ := ball_endW hr0.le hBV hB
    (hCc (g r)) (by have := hN₀ _ (hCc (g r)); omega) (fun b hb => (hlall _ b hb).1.2)
    (hX (g r)) hv hEr hR
  -- the boundary sets of the rings
  set Γ : ℕ → Set ℂ := fun i => ⋃ b ∈ l i, frontier b.closedBox ∩ dzzVIn ρ with hΓdef
  have hsd : ∀ i, ∀ b ∈ l i, 2 * ρ < b.side := by
    intro i b hb
    have hn : b.n ≤ N₀ + k := by have := hlN i b hb; have := hN₀ _ (hCc i); omega
    have : (2⁻¹ : ℝ) ^ (N₀ + k) ≤ b.side :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    linarith
  have hΓ : ∀ i, IsPathConnected (Γ i) := fun i =>
    isPathConnected_frontier_chainW (l i) (hlne i) (hlch i)
      (fun b hb b' hb' => by rw [hlN i b hb, hlN i b' hb']) (hlev1 i) (hsd i)
  have hmeet : ∀ q' < r, (Γ (g q') ∩ Γ (g (q' + 1))).Nonempty := by
    intro q' hq'
    obtain ⟨x, ⟨b, hb, hxb⟩, y, ⟨b', hb', hyb'⟩, hxy⟩ := (hch q' hq').2
    obtain ⟨w, ⟨hw1, hw2⟩, hwV⟩ := frontier_inter_W_of_bdry (hlN' _ b hb) (hlN' _ b' hb') hxb hyb'
      hxy (r := ρ) (by rw [hNdef, Nat.add_sub_cancel]; exact hr2)
    exact ⟨w, mem_biUnion hb ⟨hw1, hwV⟩, mem_biUnion hb' ⟨hw2, hwV⟩⟩
  -- the ball covers of the ring boxes
  have hcov : ∀ i b, ∃ S : Finset (ℂ × ℝ), b ∈ l i → ((S.card : ℝ) ≤ lam ∧
      frontier b.closedBox ∩ dzzVIn ρ ⊆ ⋃ p ∈ S, Metric.ball p.1 p.2 ∧
      ∀ p ∈ S, μ (Metric.ball p.1 p.2) ≤ ENNReal.ofReal (δ ^ 2)) := by
    intro i b
    by_cases hb : b ∈ l i
    · obtain ⟨S, hS⟩ := exists_cover_of_phiLeW (hlall i b hb).2.2
      exact ⟨S, fun _ => hS⟩
    · exact ⟨∅, fun h => absurd h hb⟩
  choose SB hSB using hcov
  set SR : ℕ → Finset (ℂ × ℝ) := fun i => (l i).toFinset.biUnion (SB i) with hSRdef
  set SY := (Finset.range (r + 1)).biUnion fun q' => SR (g q') with hSYdef
  set Tt := TA ∪ TB ∪ SY with hTtdef
  set St : Set ℂ := KA ∪ KB ∪ ⋃ q' ∈ Finset.range (r + 1), Γ (g q') with hStdef
  have hΓSt : ∀ q' ≤ r, Γ (g q') ⊆ St := fun q' hq' y hy =>
    Or.inr (mem_biUnion (Finset.mem_range.2 (by omega)) hy)
  -- the crossing: a path from `uA` to `vB` in `St`
  have hmid : ∀ q' ≤ r, ∀ z ∈ Γ (g q'), JoinedIn St zA z := by
    have hzA' : zA ∈ Γ (g 0) := mem_biUnion hBA hzA
    intro q'
    induction q' with
    | zero => intro _ z hz; exact ((hΓ _).joinedIn _ hzA' _ hz).mono (hΓSt 0 (Nat.zero_le _))
    | succ q' ih =>
      intro hq' z hz
      obtain ⟨w, hw1, hw2⟩ := hmeet q' (by omega)
      exact (ih (by omega) w hw1).trans (((hΓ _).joinedIn _ hw2 _ hz).mono (hΓSt _ hq'))
  have hjoin : JoinedIn St uA vB :=
    ((hjA.mono fun y hy => Or.inl (Or.inl hy)).trans (hmid r le_rfl zB (mem_biUnion hBB hzB))).trans
      (hjB.symm.mono fun y hy => Or.inl (Or.inr hy))
  -- the cover
  have hfr : ∀ q' ≤ r, ∀ b ∈ l (g q'), ∀ y ∈ frontier b.closedBox ∩ dzzVIn ρ,
      y ∈ ⋃ p ∈ Tt, Metric.ball p.1 p.2 := by
    intro q' hq' b hb y hy
    obtain ⟨pp, hpp, hy'⟩ := mem_iUnion₂.1 ((hSB (g q') b hb).2.1 hy)
    refine mem_iUnion₂.2 ⟨pp, ?_, hy'⟩
    refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨q', Finset.mem_range.2 (by omega), ?_⟩)
    exact Finset.mem_biUnion.2 ⟨b, List.mem_toFinset.2 hb, hpp⟩
  have hcover : St ⊆ ⋃ p ∈ Tt, Metric.ball p.1 p.2 := by
    rintro y ((hy | hy) | hy)
    · rcases hKA hy with rfl | hy'
      · exact hfr 0 (Nat.zero_le _) BA hBA _ hzA
      · obtain ⟨pp, hpp, h⟩ := mem_iUnion₂.1 hy'
        exact mem_iUnion₂.2 ⟨pp, Finset.mem_union_left _ (Finset.mem_union_left _ hpp), h⟩
    · rcases hKB hy with rfl | hy'
      · exact hfr r le_rfl BB hBB _ hzB
      · obtain ⟨pp, hpp, h⟩ := mem_iUnion₂.1 hy'
        exact mem_iUnion₂.2 ⟨pp, Finset.mem_union_left _ (Finset.mem_union_right _ hpp), h⟩
    · obtain ⟨q', hq', hy'⟩ := mem_iUnion₂.1 hy
      obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.1 hy'
      exact hfr q' (by have := Finset.mem_range.1 hq'; omega) b hb y hyb
  have hmass : ∀ pp ∈ Tt, μ (Metric.ball pp.1 pp.2) ≤ ENNReal.ofReal (δ ^ 2) := by
    intro pp hpp
    rcases Finset.mem_union.1 hpp with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      · exact hmA pp h'
      · exact hmB pp h'
    · obtain ⟨q', -, h'⟩ := Finset.mem_biUnion.1 h
      obtain ⟨b, hb, h''⟩ := Finset.mem_biUnion.1 h'
      exact (hSB _ b (List.mem_toFinset.1 hb)).2.2 pp h''
  have hcount := lgdMinSet_le_of_cover (μ := μ) (δ := δ) huA hvB hjoin hcover hmass
  -- the count
  have hrd : r + 1 ≤ d := by
    have := le_chain (fun q' hq' => (hch q' hq').1) r le_rfl
    have := hgd r le_rfl; omega
  have hSRle : ∀ i, ((SR i).card : ℝ) ≤ (4 : ℝ) ^ (k + 2) * lam := by
    intro i
    have e1 : ((SR i).card : ℝ) ≤ ∑ b ∈ (l i).toFinset, ((SB i b).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have e2 : ∑ b ∈ (l i).toFinset, ((SB i b).card : ℝ) ≤ ∑ _b ∈ (l i).toFinset, lam :=
      Finset.sum_le_sum fun b hb => (hSB i b (List.mem_toFinset.1 hb)).1
    rw [Finset.sum_const, nsmul_eq_mul] at e2
    have hc : ((l i).toFinset.card : ℝ) ≤ (4 : ℝ) ^ (k + 2) := by
      exact_mod_cast card_toFinset_boxColl_le (fun b hb => (hlall i b hb).1)
    have : ((l i).toFinset.card : ℝ) * lam ≤ (4 : ℝ) ^ (k + 2) * lam :=
      mul_le_mul_of_nonneg_right hc (by linarith)
    linarith
  have hSY : (SY.card : ℝ) ≤ d * ((4 : ℝ) ^ (k + 2) * lam) := by
    have e1 : (SY.card : ℝ) ≤ ∑ q' ∈ Finset.range (r + 1), ((SR (g q')).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have e2 : ∑ q' ∈ Finset.range (r + 1), ((SR (g q')).card : ℝ) ≤
        ∑ _q' ∈ Finset.range (r + 1), (4 : ℝ) ^ (k + 2) * lam :=
      Finset.sum_le_sum fun q' _ => hSRle _
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at e2
    have e3 : ((r + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hrd
    have : 0 ≤ (4 : ℝ) ^ (k + 2) * lam := by positivity
    nlinarith
  have hS : (Tt.card : ℝ) ≤ d * (4 ^ (k + 2) * (lam + 1)) + (2 * R + 8) := by
    have c1 : Tt.card ≤ TA.card + TB.card + SY.card :=
      (Finset.card_union_le _ _).trans (by gcongr; exact Finset.card_union_le _ _)
    have c1' : (Tt.card : ℝ) ≤ TA.card + TB.card + SY.card := by exact_mod_cast c1
    have : (0 : ℝ) ≤ d * 4 ^ (k + 2) := by positivity
    nlinarith
  calc ((lgdMinSet μ δ A B : ℕ∞) : ℝ≥0∞)
      ≤ ((Tt.card : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.2 hcount
    _ = ENNReal.ofReal (Tt.card : ℝ) := by rw [ENat.toENNReal_coe, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (d * (4 ^ (k + 2) * (lam + 1)) + (2 * R + 8)) :=
        ENNReal.ofReal_le_ofReal hS
    _ = (d : ℝ≥0∞) * ENNReal.ofReal (4 ^ (k + 2) * (lam + 1)) + ENNReal.ofReal (2 * R + 8) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ _ := by
        gcongr
        rw [← ENat.toENNReal_coe]
        exact ENat.toENNReal_le.2 hqd

/-- **`L32UpperCross` from the wall-interior (eq-B-percolation-Psi) and (eq-B-good-Psi)**
(D102). -/
theorem l32UpperCross_ofW' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WhiteNoise.WNSpace → Ω → ℝ} (hW : WhiteNoise.IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {μ : Ω → Measure ℂ} {ξ ξd : ℝ} {r : ℝ → ℝ} (hr : IsClipDepth γ r)
    (h1 : L32EncPhiHPW P γ W μ r) (h2 : L32StartPhiHPC P γ W μ r) (hξ : 0 < ξ)
    (hξd : ξd < dzzCMc γ) : L32UpperCross P γ W μ ξ ξd :=
  l32UpperCross_ofW hW hγ hγ2 hr l32BallCrossingW_holds h1 h2 hξ hξd

end DZZ
end LQGMetric
