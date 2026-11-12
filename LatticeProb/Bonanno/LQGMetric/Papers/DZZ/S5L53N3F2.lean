/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53N3F2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53N3F1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53FN3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53FN1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53YC2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53NU2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53O2A

/-!
# DZZ Lemma 5.3, node 3: the per-cell bound on the fibres of the chain (P2-DZZ53N3F)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2425–2514 (desirability of `𝖢_i` given the chain,
by the Peierls argument on the `K × K` sub-grid of `𝖢_i`). **`l53n3_cell_core`**: for large `k`,
every `1 ≤ l ≤ k` and every grid count `2N + 2 = K_L = 2^{⌊L^{0.51}⌋}`, depth `n` and column count
`j` with the covering condition `2(N-n) + 11 + 128 j < 0.1 ε*² (2N+2)`, `N + 1 ≥ 2^{127}` and the
threshold condition `L^{0.97} + log((2N+2)² + 1) ≤ 2L^{0.98}`, the cell clause `L53CellAt`
(S5L53FN3, = HB2's conjunct 2) holds with
`β = 4(2N+1) 2^{-(N-n+1)} + 32 · 2^{-j}`.

Assembly of: GB5 `l53_box_desirable_prob_proxy` (G-J3 core) on the event `E ∩ {𝒞 = c₀}` and
`A₀ = {𝒞 = c₀}` (R3: `measurableSet_l53Chain_eq_wn`), `l53_box_rhs_le`; `hε` from YC2
`l53_bad_cond_proxy'` with NU2 `l53_scales_ok` (`Kt = N + 1 ≤ K_L`, cut-off `r = t/(16 K_L)`);
`hdom` from GA2 `l53MB_dom` (`ℓ = 4κ`); `hR₀` from `disjoint_compl_fineReg` and
`sqBox_seven_subset_largeBox`; the interfaces from O1A `l53_l313_iface_sidePiece`,
`l53_cover_sidePiece` and NN1 `l53_l313_iface_ge_max`; G-G1 `l53_sqBox_five_subset_tildeBox`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox GMCIdent

set_option maxHeartbeats 1600000 in
/-- **Node 3 per cell on the fibres of the chain** (DZZ l. 2425–2514). -/
theorem l53n3_cell_core {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (αs : ℝ)
    {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) :
    ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → l ≤ k → ∀ N n j : ℕ,
      2 ^ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊ = 2 * N + 2 → 1 ≤ n → n ≤ N →
      (2 : ℝ) ^ 127 ≤ N + 1 →
      20 * (2 * ((N : ℝ) - n) + 3 + 128 * j) * (2 : ℝ)⁻¹ ^ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊ <
        epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 →
      ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ) + Real.log ((((2 * N + 2) ^ 2 : ℕ) : ℝ) + 1) ≤
        2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ) →
      L53CellAt hW γ αs u v k l
        (4 * ((2 * N + 1 : ℕ) * (2⁻¹ : ℝ≥0∞) ^ (N - n + 1)) + 32 * (2⁻¹ : ℝ≥0∞) ^ j) := by
  have := hW.isProbabilityMeasure
  obtain ⟨k₁, hk₁⟩ := l53_bad_cond_proxy' hW hγ hγ2 (ξ' := 1 / 4) (by norm_num) le_rfl hu hv huv
  obtain ⟨k₂, hk₂⟩ := l53_scales_ok hu hv huv (dzzCmc γ + 1) 1
  obtain ⟨k₃, hk₃⟩ := l53_chainBox_n_le αs (dzzCmc γ)
  obtain ⟨k₄, hk₄⟩ := l53MB_dom hW hγ hγ2 αs 1 4
  obtain ⟨k₅, hk₅⟩ := l53_sqBox_five_subset_tildeBox γ huv
  refine ⟨max (max (max k₁ k₂) (max k₃ k₄)) (max k₅ 2), fun k l hk hlk N n j hK hn hnN hNbig
    hnum hthr c₀ _hlen i hi2 hi => ?_⟩
  simp only [max_le_iff] at hk
  obtain ⟨⟨⟨hk1, hk2⟩, ⟨hk3, hk4⟩⟩, ⟨hk5, hk6⟩⟩ := hk
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hL1 : 1 ≤ (k : ℝ) * Real.log 2 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk6
    nlinarith
  set κ := ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊ with hκ
  set δ : ℝ := (2 : ℝ)⁻¹ ^ k with hδ
  set R : Set ℂ := Metric.cthickening (2 * δ ^ dzzCMc γ)
    (Metric.cthickening (8 * δ ^ dzzCMc γ) (l53Region u v)) with hR
  set T₁ : ℝ := l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ) with hT₁
  set A₀ : Set Ω := {ω | l53Chain γ W αs δ u v R T₁ ω = c₀} with hA₀
  set E : Set Ω := l53E4 hW γ δ ∩ cellSizeEvent γ W δ with hE
  set T : ℝ := (∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l)
    {u} {v} ∂P) + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ) with hT
  set β : ℝ≥0∞ :=
    4 * ((2 * N + 1 : ℕ) * (2⁻¹ : ℝ≥0∞) ^ (N - n + 1)) + 32 * (2⁻¹ : ℝ≥0∞) ^ j with hβ
  have hA₀w : MeasurableSet[wnSigma W (fineReg c₀)ᶜ] A₀ :=
    measurableSet_l53Chain_eq_wn γ αs δ u v R T₁ c₀
  have hA₀m : MeasurableSet A₀ := wnSigma_le hW _ _ hA₀w
  -- reduce to `A₀ ∩ E` nonempty and `P A₀ ≠ 0`
  by_cases h0 : P A₀ = 0
  · show P[_ | A₀] ≤ β
    rw [cond_eq_zero_of_meas_eq_zero h0]; exact bot_le
  by_cases hne : (A₀ ∩ E).Nonempty
  swap
  · show P[_ | A₀] ≤ β
    rw [← cond_inter_self hA₀m]
    rw [not_nonempty_iff_eq_empty] at hne
    have : A₀ ∩ (E ∩ {ω | ¬ L53DesClause (μH[1] : Measure ℂ)
        (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) ((2 : ℝ)⁻¹ ^ (k + l))
        (l53EX P γ W u v l + 2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
        (l53Iface c₀ (i - 1)) (l53Iface c₀ i)}) = ∅ := by
      rw [← inter_assoc, hne, empty_inter]
    rw [this, measure_empty]; exact bot_le
  obtain ⟨ω₀, hω₀A, hω₀E⟩ := hne
  -- the chain `c₀` at `ω₀`
  have hlen3 : 3 ≤ c₀.length := by omega
  have hc0 : c₀ ≠ [] := by rintro rfl; simp at hlen3
  have hspec : L53Q (epsStar αs δ) u v R T₁ (fun b => IsCell (approxLQG γ W ω₀) δ b) c₀ := by
    have := l53Chain_spec (γ := γ) (W := W) (αs := αs) (δ := δ) (u := u) (v := v) (R := R)
      (T := T₁) (ω := ω₀) (by rw [hω₀A]; exact hc0)
    rwa [hω₀A] at this
  have hQ := hspec.1
  set C : DyBox := c₀.getD (i - 1) root with hCdef
  have hC : C ∈ c₀ := by
    rw [hCdef, l53NN_getD_eq c₀ (by omega)]; exact List.getElem_mem _
  obtain ⟨C₀, hC₀, hCC₀, hCs⟩ := hQ.2.1 C hC
  have hCn : C.n = C₀.n + 2 * epsStarN αs δ := l53fn_n_eq hCs
  obtain ⟨hC₀lo, hC₀hi⟩ := hω₀E.2.2 C₀ hC₀
  have hsC := side_pos' C
  have hsC₀ := side_pos' C₀
  have he1 : epsStar αs δ ^ 2 ≤ 1 := l53_l313_eps_sq_le_one hQ hC
  have he0 : 0 < epsStar αs δ := by unfold epsStar; positivity
  have hCleC₀ : C.side ≤ C₀.side := by rw [hCs]; nlinarith
  -- scales
  set t : ℝ := (2 : ℝ)⁻¹ ^ (C.n + κ) with htdef
  have ht : 0 < t := by positivity
  have hKR : (2 : ℝ) ^ κ = 2 * N + 2 := by exact_mod_cast hK
  have hCt : C.side = (2 * N + 2) * t := by rw [l53n3_side_eq C κ, hKR]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsub : ∀ z ∈ l53EvenBox N, (l53Sub C κ N z).closedBox ⊆ C.closedBox :=
    fun z hz => l53_sub_subset C hK hz
  have hsubside : ∀ z : ℤ × ℤ, (l53Sub C κ N z).side = t := fun z => rfl
  -- G-G1
  have hC5 : sqBox C.center (5 * C.side) ⊆ tildeBox u v :=
    hk₅ k hk5 C (hCleC₀.trans hC₀hi) (hspec.2.1 C hC)
  have hKw : ∀ z ∈ l53EvenBox N,
      sqBox (l53Sub C κ N z).center (5 * (l53Sub C κ N z).side) ⊆ tildeBox u v := by
    intro z hz
    refine (l53n3_sqBox_five_mono (hsub z hz) ?_).trans hC5
    rw [hsubside, hCt]; nlinarith
  -- the proxy
  set m : ℕ := C.n + κ + (4 * κ + 0) with hm
  set cB : ℝ≥0∞ := ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ 2 / C.side ^ 2 *
    Real.exp (((k : ℝ) * Real.log 2) ^ (0.91 : ℝ))) with hcB
  have hCnk : (C.n : ℝ) ≤ (dzzCmc γ + 1) * k := hk₃ k hk3 C₀ C hC₀lo hCn
  have hℓ₀ : (2 : ℝ) ^ (0 : ℕ) ≤ 1 * ((k : ℝ) * Real.log 2) := by simpa using hL1
  obtain ⟨hr1, hsc⟩ := hk₂ k hk2 κ rfl 0 hℓ₀ C (l53Sub C κ N (0, 0)) hCnk rfl m rfl
  obtain ⟨-, hms, hmt, -, -⟩ := hsc _ hr1 le_rfl
  -- `R₀`
  have hR₀ : ∀ z ∈ l53EvenBox N, Disjoint (fineReg c₀)ᶜ
      (Ioo 0 (C.side ^ 2) ×ˢ sqBox (l53Sub C κ N z).center (7 * (l53Sub C κ N z).side)) := by
    intro z hz
    refine disjoint_compl_fineReg hC (sqBox_seven_subset_largeBox (hsub z hz) ?_) subset_rfl
    rw [hsubside, hCt]; nlinarith
  -- `Kt = N + 1`
  set Kt : ℝ≥0∞ := ((N + 1 : ℕ) : ℝ≥0∞) with hKt
  have hN8 : (8 : ℝ) ≤ N + 1 := le_trans (by norm_num) hNbig
  have hK8 : 8 ≤ Kt := by
    rw [hKt]; exact_mod_cast (show (8 : ℕ) ≤ N + 1 by exact_mod_cast hN8)
  have hKt0 : Kt ≠ 0 := by rw [hKt]; exact_mod_cast (Nat.succ_ne_zero N)
  have hKtt : Kt ≠ ⊤ := ENNReal.natCast_ne_top _
  have hKtle : (ENNReal.ofReal ((2 : ℝ) ^ κ))⁻¹ ≤ Kt⁻¹ := by
    apply ENNReal.inv_le_inv.2
    rw [hKt, hKR, ← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal; push_cast; linarith
  -- `hε`
  have hε : ∀ z ∈ l53EvenBox N, P[l53ZBadQ (proxyMass W γ m cB
      (sqBox (l53Sub C κ N z).center (5 * (l53Sub C κ N z).side))) ((2 : ℝ)⁻¹ ^ (k + l)) T
      (frontier (l53Sub C κ N z).closedBox)
      (Kt⁻¹ * μH[1] (frontier (l53Sub C κ N z).closedBox))
      (Kt⁻¹ * μH[1] (frontier (l53Sub C κ N z).closedBox)) | A₀] ≤
      2 * ENNReal.ofReal (2 * ((2 : ℝ) ^ κ)⁻¹ ^ 4) * Kt ^ 2 := by
    intro z hz
    obtain ⟨hr1z, hscz⟩ := hk₂ k hk2 κ rfl 0 hℓ₀ C (l53Sub C κ N z) hCnk rfl m rfl
    obtain ⟨hr0, hms', hmt', hrK, hpair⟩ := hscz _ hr1z le_rfl
    exact hk₁ k l hk1 hlk (l53Sub C κ N z) m hsC hr0 hms' hmt' (hR₀ z hz) hA₀w h0 hKt0 hKtt
      (hrK.trans (by gcongr))
      (hpair (1 / 4) ((hKw z hz).trans (tildeBox_subset_dzzVXi hu hv huv)))
  -- `hdom` on `E ∩ A₀`
  have hdom : ∀ ω ∈ E ∩ A₀, ∀ z ∈ l53EvenBox N, ∀ (c : ℚ × ℚ) (q : ℚ),
      Metric.ball (ratPt c) q ⊆ sqBox (l53Sub C κ N z).center (5 * (l53Sub C κ N z).side) →
        dzzMuIn γ W ω (Metric.ball (ratPt c) q) ≤
          proxyMass W γ m cB (sqBox (l53Sub C κ N z).center (5 * (l53Sub C κ N z).side))
            ω c q := by
    rintro ω ⟨⟨hω4, hωS⟩, hωA⟩ z hz c q hball
    have hspecω : L53Q (epsStar αs δ) u v R T₁ (fun b => IsCell (approxLQG γ W ω) δ b) c₀ := by
      have := l53Chain_spec (γ := γ) (W := W) (αs := αs) (δ := δ) (u := u) (v := v) (R := R)
        (T := T₁) (ω := ω) (by rw [hωA]; exact hc0)
      rwa [hωA] at this
    obtain ⟨C₁, hC₁, hCC₁, hCs₁⟩ := hspecω.1.2.1 C hC
    have hℓ : (2 : ℝ) ^ (4 * κ + 0) ≤ (2 : ℝ) ^ (4 * κ) * (1 * ((k : ℝ) * Real.log 2)) := by
      rw [add_zero]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (4 * κ)]
    exact hk₄ k hk4 ω hω4 C₁ (hωS.2 C₁ hC₁).1 hC₁.1.le C (l53fn_n_eq hCs₁) (l53Sub C κ N z) rfl
      ((hsub z hz).trans hCC₁) (4 * κ + 0) hℓ c q
      (l53_sub_openSquare_of_tildeBox hu hv huv (hball.trans (hKw z hz)))
  -- the interfaces (O1A, O2A)
  have hK80 : 80 ≤ Kt := by
    rw [hKt]; exact_mod_cast (show (80 : ℕ) ≤ N + 1 by
      have : (80 : ℝ) ≤ N + 1 := le_trans (by norm_num) hNbig
      exact_mod_cast this)
  have hp := (l53_node3_cover hQ hK hnN hK80 hnum (i - 2) (by omega)).2
  have hn' := (l53_node3_cover hQ hK hnN hK80 hnum (i - 1) (by omega)).1
  rw [show i - 2 + 1 = i - 1 by omega] at hp
  rw [show i - 1 + 1 = i by omega] at hn'
  obtain ⟨Sp, hSp⟩ := hp
  obtain ⟨Sn, hSn⟩ := hn'
  obtain ⟨hεθ, hbin⟩ := l53n3_eps hK hNbig
  have hG := l53_box_desirable_prob_proxy hW C hK hn hnN γ m cB hms hmt hA₀w h0 hR₀
    ((2 : ℝ)⁻¹ ^ (k + l)) T hK8 l53n3_theta hεθ hε j (E ∩ A₀) (dzzMuIn γ W) (tildeBox u v)
    hKw hdom Sp Sn (fun p hp => hp.elim (hSp.1 p) (hSn.1 p)) hSp.2.1 hSn.2.1 hSp.2.2.1
    hSn.2.2.1 hSp.2.2.2.1 hSp.2.2.2.2.1 hSn.2.2.2.2.2
  have hrhs := l53_box_rhs_le (j := j) hn hnN l53n3_theta hbin
  have hTe : T = l53EX P γ W u v l + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ) := rfl
  have hthr' : T + Real.log ((((2 * N + 2) ^ 2 : ℕ) : ℝ) + 1) ≤
      l53EX P γ W u v l + 2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ) := by
    rw [hTe]; linarith
  refine le_trans ?_ (hG.trans hrhs)
  rw [← cond_inter_self hA₀m]
  refine measure_mono ?_
  rintro ω ⟨hωA, hωE, hωD⟩
  exact ⟨⟨hωE, hωA⟩, fun hc => hωD (hc.mono hthr')⟩

end DZZ
end LQGMetric
