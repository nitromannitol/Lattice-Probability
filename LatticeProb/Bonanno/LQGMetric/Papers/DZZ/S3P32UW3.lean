/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32UW3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UW2

/-!
# Walled (Eq.boundDprime), UW3: `L32UpperCrossOn` at a dyadic wall (P2-DZZUPW, P-317K-UP)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Prop 3.2, (Eq.boundDprime) l. 1088–1101, with
Remark 5.2 (l. 2281–2284): **`l32UpperCrossOn_of`**, `L32UpperCrossOn P γ W B̄w (cellsInside Bw) μ
ξ ξd` from the walled probabilistic inputs `L32EncPhiHPWOn`, `L32StartPhiHPCOn` (S3P32UW2). The
proof is a copy of `l32UpperCross_ofW` (S3P32XW, D102) with the walled deterministic step
`l32BallCrossingOn` (S3P32UW1), plus: `δ^{C_Mc} < s_{Bw}` (so the cells split `Bw`,
`wsplit_of_side`), the ends pulled back into `𝕍_{−r/s}` (`mem_dzzVIn_of_kXi`), the level bound
`N₀ − n_{Bw}` of the pulled-back cells.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
/-- **Walled (Eq.boundDprime) at a dyadic wall** (DZZ l. 1088–1101 + Remark 5.2) from the walled
(eq-B-percolation-Psi) and (eq-B-good-Psi). -/
theorem l32UpperCrossOn_of {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} {ξ ξd : ℝ} {r : ℝ → ℝ}
    (hr : IsClipDepth γ r) (Bw : DyBox)
    (h1 : L32EncPhiHPWOn P γ W μ Bw r) (h2 : L32StartPhiHPCOn P γ W μ Bw r) (hξ : 0 < ξ)
    (hξd : ξd < dzzCMc γ) : L32UpperCrossOn P γ W Bw.closedBox (cellsInside Bw) μ ξ ξd := by
  have := hW.isProbabilityMeasure
  set C := dzzCmc γ with hCdef
  set c := dzzCMc γ with hcdef
  have hC : 0 < C := by have := l31theta_pos hγ hγ2; rw [hCdef]; unfold dzzCmc; linarith
  have hc : 0 < c := dzzCMc_pos γ
  set s := Bw.side with hsdef
  have hs0 : 0 < s := wside_pos Bw
  obtain ⟨c₁, hc₁, δ₁, hδ₁, hb1⟩ := h1
  obtain ⟨c₂, hc₂, δ₂, hδ₂, hb2⟩ := h2
  obtain ⟨δ₃, hδ₃, hasym⟩ := l35_asym hC hc hξ hξd
  set c0 := min (min c₁ c₂) 1 with hc0def
  have hc0 : 0 < c0 := lt_min (lt_min hc₁ hc₂) one_pos
  set K := 4 + l31const γ with hKdef
  have hl31 : 0 ≤ l31const γ := by unfold l31const; positivity
  have hK : 0 < K := by rw [hKdef]; linarith
  -- `δ^C ≤ 4ξ` keeps the ends out of the clipped strip
  obtain ⟨δ₄, hδ₄, hδ₄ξ⟩ : ∃ δ₄ : ℝ, 0 < δ₄ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₄, δ ^ C ≤ 4 * ξ := by
    refine ⟨min 1 ((4 * ξ) ^ (1 / C)), by positivity, fun δ hδ => ?_⟩
    have hlt : δ < (4 * ξ) ^ (1 / C) := hδ.2.trans_le (min_le_right _ _)
    have := Real.rpow_le_rpow hδ.1.le hlt.le hC.le
    rwa [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hC.ne', Real.rpow_one] at this
  -- `δ^{C_Mc} < s_{Bw}`: the cells split the wall box
  obtain ⟨δ₅, hδ₅, hδ₅s⟩ : ∃ δ₅ : ℝ, 0 < δ₅ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₅, δ ^ c < s := by
    refine ⟨(s / 2) ^ (1 / c), by positivity, fun δ hδ => ?_⟩
    have := Real.rpow_lt_rpow hδ.1.le hδ.2 hc
    rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one] at this
    linarith
  refine ⟨c0 / 2, by positivity,
    min (min (min δ₁ δ₂) (min δ₃ δ₄)) (min (min (1 / 2) δ₅) ((1 / K) ^ (2 / c0))), by positivity,
    ?_⟩
  rintro δ ⟨hδ0, hδ⟩ A B ⟨hAB, hAK, hBK⟩
  obtain ⟨⟨⟨hδ1', hδ2'⟩, hδ3', hδ4'⟩, ⟨hδh, hδ5'⟩, hδK⟩ := by simpa only [lt_min_iff] using hδ
  have hδ1 : δ < 1 := by linarith
  obtain ⟨-, -, as3, -⟩ := hasym δ ⟨hδ0, hδ3'⟩
  obtain ⟨hr0, hr4⟩ := hr δ ⟨hδ0, hδ1⟩
  have hrξ : r δ ≤ ξ := by
    have h4 := hδ₄ξ δ ⟨hδ0, hδ4'⟩
    have hk : (2⁻¹ : ℝ) ^ kL37 γ δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hδC : 0 ≤ δ ^ C := by positivity
    nlinarith
  have hδs : δ ^ c < s := hδ₅s δ ⟨hδ0, hδ5'⟩
  set L := Real.log δ⁻¹ with hLdef
  have hL0 : 0 < L := by
    rw [hLdef, Real.log_inv]; have := Real.log_neg hδ0 hδ1; linarith
  set k := kL37 γ δ with hkdef
  set lam := lamP32 δ with hlamdef
  have hlam1 : 1 ≤ lam := Real.one_le_exp (Real.rpow_nonneg hL0.le _)
  set R := δ ^ (-(c / 2)) * lam with hRdef
  have hR0 : 0 ≤ R := by positivity
  set rp := r δ / s with hrpdef
  have hrp0 : 0 < rp := div_pos hr0 hs0
  have hpull : ∀ X : Set ℂ, X ⊆ kXi Bw.closedBox ξ → wHom Bw ⁻¹' X ⊆ dzzVIn rp :=
    fun X hX x hx => by simpa using mem_dzzVIn_of_kXi hξ hrξ (hX hx)
  have hAV := hpull A hAK
  have hBV := hpull B hBK
  have hAi : A ⊆ interior Bw.closedBox := hAK.trans (kXi_sub_interior hξ)
  have hBi : B ⊆ interior Bw.closedBox := hBK.trans (kXi_sub_interior hξ)
  set G : Set Ω := encPhiAllWOn γ W μ Bw rp δ ∩
    startPhiEvCOn γ W μ Bw rp δ (c / 2) (wHom Bw ⁻¹' A) ∩
    startPhiEvCOn γ W μ Bw rp δ (c / 2) (wHom Bw ⁻¹' B) ∩ cellSizeEvent γ W δ with hGdef
  have hsub : G ⊆ p32CrossEventOn (cellsInside Bw) γ W μ δ A B := by
    rintro ω ⟨⟨⟨hE, hSA⟩, hSB⟩, hcs⟩
    set m := approxLQG γ W ω with hmdef
    have hside : ∀ b, IsCell m δ b → b.side ≤ δ ^ c := fun b hb => (hcs.2 b hb).2
    have hsplit : WSplit m δ Bw :=
      wsplit_of_side hcs.1 fun b hb => (hside b hb).trans_lt hδs
    have hstartC : ∀ A' : Set ℂ, IsXiAdmissibleSet ξd δ A' →
        ω ∈ startPhiEvCOn γ W μ Bw rp δ (c / 2) (wHom Bw ⁻¹' A') →
        BallStartCondC (wPullMeas Bw (μ ω)) (fun c => m (wEmb Bw c)) δ rp R (wHom Bw ⁻¹' A') := by
      intro A' hA'adm hSA'
      by_cases hs : ∃ u, wHom Bw ⁻¹' A' = {u}
      · obtain ⟨u, hu⟩ := hs
        exact Or.inl ⟨u, hu, fun b hb hub => hSA' u hu b ((isCell_wEmb_iff hsplit).2 hb) hub⟩
      · rcases hA'adm with ⟨a, rfl⟩ | ⟨hconn, hdiam⟩
        · exact absurd ⟨(wHom Bw).symm a, preimage_wHom_singleton Bw a⟩ hs
        · refine Or.inr ⟨(wHom Bw).isConnected_preimage.2 hconn, fun b hb hsub => ?_⟩
          have hsub' : A' ⊆ (wEmb Bw b).largeBox := by
            intro x hx
            rw [largeBox_wEmb]
            exact ⟨(wHom Bw).symm x, hsub (by simpa using hx), by simp⟩
          have hd := Metric.diam_le_of_forall_dist_le
            (by linarith [side_pos' (wEmb Bw b)] : (0 : ℝ) ≤ 4 * (wEmb Bw b).side)
            fun x hx y hy => dist_le_of_mem_largeBox (hsub' hx) (hsub' hy)
          have := hside _ ((isCell_wEmb_iff hsplit).2 hb)
          linarith
    have hne : ∀ A' : Set ℂ, IsXiAdmissibleSet ξd δ A' → A'.Nonempty := by
      intro A' h
      rcases h with ⟨a, rfl⟩ | ⟨hconn, -⟩
      · exact singleton_nonempty a
      · exact hconn.nonempty
    -- the level bound `N₀`: the largest level with `2^{-N₀} ≥ δ^C`
    obtain ⟨N₀, hN₀lt, hN₀ge⟩ : ∃ N₀ : ℕ, (2⁻¹ : ℝ) ^ (N₀ + 1) < δ ^ C ∧
        δ ^ C ≤ (2⁻¹ : ℝ) ^ N₀ := by
      classical
      have hex : ∃ N : ℕ, (2⁻¹ : ℝ) ^ (N + 1) < δ ^ C := by
        obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one (Real.rpow_pos_of_pos hδ0 C)
          (show (2 : ℝ)⁻¹ < 1 by norm_num)
        exact ⟨N₁, lt_of_le_of_lt
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hN₁⟩
      refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0, pow_zero]; exact Real.rpow_le_one hδ0.le hδ1.le hC.le
      · have hmin := Nat.find_min hex (Nat.sub_lt hpos one_pos)
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hpos.ne')] at hmin
        exact not_lt.1 hmin
    have hN₀ : ∀ b, IsCell m δ b → b.n ≤ N₀ := by
      intro b hb
      by_contra hlt
      have h1 := (hcs.2 b hb).1
      have h2 : b.side ≤ (2 : ℝ)⁻¹ ^ (N₀ + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith
    -- the wall level is below `N₀`
    have hBN : Bw.n ≤ N₀ := by
      obtain ⟨T, hT, -⟩ := hcs.1 Bw.center (closedBox_sub_dzzV' Bw (center_mem_closedBox' Bw))
      have hTn := hN₀ T hT
      by_contra hlt
      have : s ≤ T.side := by
        rw [hsdef]; unfold DyBox.side
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith [hside T hT]
    have hN₀' : ∀ b, IsCell m δ b → b.n ≤ Bw.n + (N₀ - Bw.n) := fun b hb => by
      have := hN₀ b hb; omega
    have hr2 : 2 * r δ < (2⁻¹ : ℝ) ^ (N₀ + k) := by
      rw [pow_add]
      have hk0 : 0 ≤ (2⁻¹ : ℝ) ^ k := by positivity
      have := mul_le_mul_of_nonneg_right hN₀ge hk0
      linarith
    have hr2' : 2 * rp < (2⁻¹ : ℝ) ^ (N₀ - Bw.n + k) := by
      have e : (2⁻¹ : ℝ) ^ (N₀ - Bw.n + k) * s = (2⁻¹ : ℝ) ^ (N₀ + k) := by
        rw [hsdef]; unfold DyBox.side; rw [← pow_add]; congr 1; omega
      rw [hrpdef, show 2 * (r δ / s) = (2 * r δ) / s by ring, div_lt_iff₀ hs0, e]
      exact hr2
    exact l32BallCrossingOn hδ0 hlam1 hR0 hrp0 hr2' hcs.1 hN₀' hsplit (fun b hb => hE b hb)
      hAi hBi hAV hBV (hne A hAB.adm_left) (hne B hAB.adm_right)
      (hstartC A hAB.adm_left hSA) (hstartC B hAB.adm_right hSB)
  -- the probability
  have p1 := hb1 δ ⟨hδ0, hδ1'⟩
  have p2 := startPhiEvCOn_bound (P := P) (γ := γ) (W := W) (μ := μ) (Bw := Bw) (r := rp)
    (δ := δ) (ι := c / 2) (A := wHom Bw ⁻¹' A) (fun u hu => hb2 δ ⟨hδ0, hδ2'⟩ u hu) hAV
  have p3 := startPhiEvCOn_bound (P := P) (γ := γ) (W := W) (μ := μ) (Bw := Bw) (r := rp)
    (δ := δ) (ι := c / 2) (A := wHom Bw ⁻¹' B) (fun u hu => hb2 δ ⟨hδ0, hδ2'⟩ u hu) hBV
  have p4 := dzz_lemma31_bound hW hγ hγ2 hδ0 (show δ ≤ 1 / 2 by linarith)
  have p4' : P (cellSizeEvent γ W δ)ᶜ ≤ ENNReal.ofReal (l31const γ * δ) :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 p4
  have m1 : δ ^ c₁ ≤ δ ^ c0 := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le
    ((min_le_left _ _).trans (min_le_left _ _))
  have m2 : δ ^ c₂ ≤ δ ^ c0 := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le
    ((min_le_left _ _).trans (min_le_right _ _))
  have m3 : δ ≤ δ ^ c0 := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_right (min c₁ c₂) 1)
    rwa [Real.rpow_one] at this
  have hhalf : δ ^ (c0 / 2) ≤ 1 / K := by
    have := Real.rpow_le_rpow hδ0.le hδK.le (by positivity : 0 ≤ c0 / 2)
    rwa [← Real.rpow_mul (by positivity), show 2 / c0 * (c0 / 2) = 1 by field_simp,
      Real.rpow_one] at this
  have hsplit : δ ^ c0 = δ ^ (c0 / 2) * δ ^ (c0 / 2) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have hpos : 0 ≤ δ ^ (c0 / 2) := by positivity
  have hKh : K * δ ^ (c0 / 2) ≤ 1 := by
    rw [le_div_iff₀ hK] at hhalf; linarith
  have hfin : δ ^ c₁ + δ ^ c₂ + δ ^ c₂ + l31const γ * δ ≤ δ ^ (c0 / 2) := by
    have h1 : δ ^ c₁ + δ ^ c₂ + δ ^ c₂ + l31const γ * δ ≤ K * δ ^ c0 := by
      rw [hKdef]; nlinarith
    rw [hsplit] at h1
    nlinarith
  calc P (p32CrossEventOn (cellsInside Bw) γ W μ δ A B)ᶜ ≤ P Gᶜ :=
        measure_mono (compl_subset_compl.2 hsub)
    _ ≤ P (encPhiAllWOn γ W μ Bw rp δ)ᶜ +
          P (startPhiEvCOn γ W μ Bw rp δ (c / 2) (wHom Bw ⁻¹' A))ᶜ +
          P (startPhiEvCOn γ W μ Bw rp δ (c / 2) (wHom Bw ⁻¹' B))ᶜ +
          P (cellSizeEvent γ W δ)ᶜ := by
        rw [hGdef, compl_inter, compl_inter, compl_inter]
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ ^ c₁) + ENNReal.ofReal (δ ^ c₂) + ENNReal.ofReal (δ ^ c₂) +
          ENNReal.ofReal (l31const γ * δ) := by gcongr
    _ = ENNReal.ofReal (δ ^ c₁ + δ ^ c₂ + δ ^ c₂ + l31const γ * δ) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (δ ^ (c0 / 2)) := ENNReal.ofReal_le_ofReal hfin

end DZZ
end LQGMetric
