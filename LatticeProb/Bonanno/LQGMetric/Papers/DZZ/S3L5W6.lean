/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5W6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5W5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5Main
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K3

/-!
# Walled DZZ Lemma 3.5, W6: the assembly (P2-DZZL35W)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 907–916, proof l. 1037–1083) for the walled
approximate distance `D'_S` at a dyadic wall `K = B̄w`, `S = cellsInside Bw` (Remark 5.2,
l. 2281–2284; D117/D123). Copy of `dzz_lemma35U_of_crossing` (S3L5Main, P2-DZZ3G) with
* the crossing claim `l35CrossingOn` (S3L5W2, from the proved `l35Crossing_holds`),
* the enclosures relative to the wall `l37_cells_encW` (S3L5W5),
* the walled start pieces `L35StartW` (OPEN input: DZZ l. 1058–1066 for `D'_S`, in pulled-back
  form `startGoodW`),
* `wsplit_of_side`: on Lemma 3.1, `Bw` is split at `δ` once `δ^{C_Mc} < s_{Bw}`;
* `kXi_sub_interior`: `K^ξ ⊆ int K`;
* the lower bound (Eq.lowerboundforDprime) transferred by `D' ≤ D'_S`.

* **`dzz_lemma35UOn_of_start`**: `L35StartW → DZZLemma35UOn P γ W B̄w (cellsInside Bw) ξ ξd`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The pulled-back start event at `x ∈ B̄w` (DZZ l. 1058–1066 for `D'_S`): for every cell `𝖢`
inside the wall (pulled back to `b`) with `ψ⁻¹x ∈ b_large`,
`D'_{S,δ'}(x, ∂𝖢_large ∩ B̄w) ≤ δ^{-ι}(δ/δ')³`, written on the grid of `𝕍`. -/
def startGoodW (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ δ' ι : ℝ) (Bw : DyBox) (x : ℂ) : Set Ω :=
  {ω | ∀ b, IsCell (fun c => approxLQG γ W ω (wEmb Bw c)) δ b → (wHom Bw).symm x ∈ b.largeBox →
    ((approxDistSet (fun c => approxLQG γ W ω (wEmb Bw c)) δ' {(wHom Bw).symm x}
      (frontier b.largeBox ∩ dzzV) : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-ι) * (δ / δ') ^ 3)}

/-- **The walled start pieces** (DZZ l. 1058–1066 for `D'_S`; OPEN): `l35_start_hp` for
`startGoodW`, at the points of `K^ξ`. -/
def L35StartW (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (α ι ξ : ℝ) (Bw : DyBox) : Prop :=
  ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ δ' ∈ Ioc (0 : ℝ) δ, ∀ x ∈ kXi Bw.closedBox ξ,
    P.real (startGoodW γ W δ δ' ι Bw x ∩ eventEFine γ W α δ)ᶜ ≤
      δ ^ (ι / 20) + P.real (eventEFine γ W α δ)ᶜ

/-- The start event of an end `A` (trivial unless `A` is a point). -/
def startEvW (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ δ' ι : ℝ) (Bw : DyBox) (A : Set ℂ) : Set Ω :=
  {ω | ∀ u, A = {u} → ω ∈ startGoodW γ W δ δ' ι Bw u}

lemma startEvW_bound [IsFiniteMeasure P] {γ δ δ' ι q ξ : ℝ} {Bw : DyBox} {A : Set ℂ}
    {E : Set Ω}
    (h : ∀ u ∈ kXi Bw.closedBox ξ, P.real (startGoodW γ W δ δ' ι Bw u ∩ E)ᶜ ≤ q + P.real Eᶜ)
    (hq : 0 ≤ q) (hA : A ⊆ kXi Bw.closedBox ξ) :
    P.real (startEvW γ W δ δ' ι Bw A ∩ E)ᶜ ≤ q + P.real Eᶜ := by
  by_cases hs : ∃ u, A = {u}
  · obtain ⟨u, rfl⟩ := hs
    have e : startEvW γ W δ δ' ι Bw {u} = startGoodW γ W δ δ' ι Bw u := by
      ext ω
      refine ⟨fun h => h u rfl, fun h u' hu' => ?_⟩
      obtain rfl := Set.singleton_eq_singleton_iff.1 hu'
      exact h
    rw [e]; exact h u (hA rfl)
  · have e : startEvW γ W δ δ' ι Bw A = univ := by
      ext ω
      simp only [startEvW, mem_ofPred_eq, mem_univ, iff_true]
      intro u hu; exact absurd ⟨u, hu⟩ hs
    rw [e, univ_inter]; linarith

lemma preimage_wHom_singleton (Bw : DyBox) (u : ℂ) :
    wHom Bw ⁻¹' {u} = {(wHom Bw).symm u} := by
  ext x
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

lemma kXi_sub_interior {Bw : DyBox} {ξ : ℝ} (hξ : 0 < ξ) :
    kXi Bw.closedBox ξ ⊆ interior Bw.closedBox := by
  intro x hx
  have hne : (Bw.closedBox)ᶜ.Nonempty := ⟨(2 : ℂ), fun h => by
    have := (closedBox_sub_dzzV' Bw h).2.1; norm_num at this⟩
  have := (Metric.infDist_pos_iff_notMem_closure hne).2 (lt_of_lt_of_le hξ hx)
  rwa [closure_compl, notMem_compl_iff] at this

omit [MeasurableSpace Ω] in
/-- On the partition by cells of side `< s_{Bw}`, `Bw` and its ancestors are split. -/
lemma wsplit_of_side {m : DyBox → ℝ} {δ : ℝ} {Bw : DyBox}
    (hpart : ∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v)
    (hside : ∀ b, IsCell m δ b → b.side < Bw.side) : WSplit m δ Bw := by
  intro i hi
  obtain ⟨T, hT, hTm⟩ := hpart Bw.center (closedBox_sub_dzzV' Bw (center_mem_closedBox' Bw))
  have hn : Bw.n < T.n := by
    by_contra h
    push Not at h
    have : Bw.side ≤ T.side := by
      unfold DyBox.side; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    linarith [hside T hT]
  have hTB : T.anc Bw.n = Bw := by
    have h1 := hTm.2
    rw [← h1, anc_boxAt hn.le, boxAt_center rfl]
  have := hT.2 i (by omega)
  rwa [← anc_anc T hi, hTB] at this

set_option maxHeartbeats 1000000 in
/-- **Walled DZZ Lemma 3.5** (`DZZLemma35UOn` at the dyadic wall `B̄w`, cells `cellsInside Bw`,
D123) from the walled start pieces `L35StartW` (copy of `dzz_lemma35U_of_crossing`), for
`0 < ξ` and `ξd < C_Mc`. -/
theorem dzz_lemma35UOn_of_start (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (Bw : DyBox) {ξ ξd : ℝ} (hξ : 0 < ξ) (hξd : ξd < dzzCMc γ)
    (hst : L35StartW P γ W (4 * dzzCmc γ + 1) (dzzCMc γ / 2) ξ Bw) :
    DZZLemma35UOn P γ W Bw.closedBox (cellsInside Bw) ξ ξd := by
  have := hW.isProbabilityMeasure
  set C := dzzCmc γ with hCdef
  set c := dzzCMc γ with hcdef
  have hC : 0 < C := by have := l31theta_pos hγ hγ2; rw [hCdef]; unfold dzzCmc; linarith
  have hc : 0 < c := dzzCMc_pos γ
  set ι := c / 2 with hιdef
  have hι : 0 < ι := by positivity
  set α := 4 * C + 1 with hαdef
  have hα : 4 * C < α := by linarith
  have hα0 : 0 < α := by linarith
  obtain ⟨cE, hcE, δE, hδE, hEb⟩ := dzz_lemma34_fine (P := P) (W := W) hW hγ hγ2 hα0
  obtain ⟨δ₁, hδ₁, hcells⟩ := l37_cells_encW hW hγ hγ2 hα
  obtain ⟨δ₂, hδ₂, hstart⟩ := hst
  obtain ⟨δ₃, hδ₃, hasym⟩ := l35_asym hC hc hξ hξd
  set c0 := min 1 (min cE (ι / 20)) with hc0def
  have hc0 : 0 < c0 := lt_min one_pos (lt_min hcE (by positivity))
  set K := 6 + l31const γ with hKdef
  have hK : 0 < K := by rw [hKdef]; unfold l31const; positivity
  have hBs := wside_pos Bw
  set δ₄ := (Bw.side / 2) ^ (1 / c) with hδ₄def
  have hδ₄ : 0 < δ₄ := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨c0 / 2, by positivity, min (min (min δE δ₁) (min δ₂ δ₃))
    (min (min (1 / 2) δ₄) ((1 / K) ^ (2 / c0))), by positivity, ?_⟩
  rintro δ ⟨hδ0, hδ⟩ δ' ⟨hδ'0, hδ'δ⟩ A B hAB
  have hδE' : δ < δE := hδ.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδ1' : δ < δ₁ := hδ.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδ2' : δ < δ₂ := hδ.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hδ3' : δ < δ₃ := hδ.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hδh : δ < 1 / 2 := hδ.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδ4' : δ < δ₄ := hδ.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδc : δ ^ c < Bw.side := by
    have h1 := Real.rpow_lt_rpow hδ0.le hδ4' hc
    rw [hδ₄def, ← Real.rpow_mul (by positivity), one_div_mul_cancel hc.ne', Real.rpow_one] at h1
    linarith
  have hδK : δ < (1 / K) ^ (2 / c0) := hδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ < 1 := by linarith
  obtain ⟨as1, as2, as3, as4⟩ := hasym δ ⟨hδ0, hδ3'⟩
  set L := Real.log δ⁻¹ with hLdef
  have hL0 : 0 < L := by
    rw [hLdef, Real.log_inv]; have := Real.log_neg hδ0 hδ1; linarith
  set E := eventEFine γ W α δ with hEdef
  set k := kL37 γ δ with hkdef
  set lam := lamL37 δ δ' with hlamdef
  set r3 := (δ / δ') ^ 3 with hr3def
  have hr3 : 1 ≤ r3 := one_le_pow₀ (by rw [le_div_iff₀ hδ'0]; linarith)
  set R := δ ^ (-ι) * r3 with hRdef
  have hδι : 1 ≤ δ ^ (-ι) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hδ1.le
    (by linarith)
  have hR1 : 1 ≤ R := one_le_mul_of_one_le_of_one_le hδι hr3
  have hlam : lam = r3 * Real.exp (L ^ (0.7 : ℝ)) := rfl
  have hlam1 : 1 ≤ lam := by
    rw [hlam]
    exact one_le_mul_of_one_le_of_one_le hr3 (Real.one_le_exp (Real.rpow_nonneg hL0.le _))
  set Q := r3 * Real.exp (L ^ (0.8 : ℝ)) with hQdef
  -- `2^k ≤ 4 C L`
  have hkx : (2 : ℝ) ^ k ≤ 4 * C * L := by
    have hfl : ⌊4 * C * L⌋₊ ≠ 0 := by
      have := Nat.floor_pos.2 (show (1 : ℝ) ≤ 4 * C * L by linarith); omega
    have h1 := Nat.pow_log_le_self 2 hfl
    have h2 : ((2 ^ k : ℕ) : ℝ) ≤ (⌊4 * C * L⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2; exact h2.trans (Nat.floor_le (by linarith))
  have ha : 4 ^ (k + 2) * (lam + 1) ≤ Q / 2 := by
    have e4 : (4 : ℝ) ^ (k + 2) = 16 * ((2 : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul, pow_add, show (4 : ℝ) ^ 2 = 16 by norm_num, mul_comm,
        show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm k 2]
    have h2k : ((2 : ℝ) ^ k) ^ 2 ≤ (4 * C * L) ^ 2 := pow_le_pow_left₀ (by positivity) hkx 2
    have hl2 : lam + 1 ≤ 2 * lam := by linarith
    have hE7 := Real.exp_pos (L ^ (0.7 : ℝ))
    have hr0 : 0 < r3 := by linarith
    calc 4 ^ (k + 2) * (lam + 1) ≤ (16 * (4 * C * L) ^ 2) * (2 * lam) := by
          rw [e4]; gcongr
      _ = 1024 * C ^ 2 * L ^ 2 * Real.exp (L ^ (0.7 : ℝ)) * r3 / 2 := by rw [hlam]; ring
      _ ≤ Real.exp (L ^ (0.8 : ℝ)) * r3 / 2 := by gcongr
      _ = Q / 2 := by rw [hQdef]; ring
  have hb : 2 * R + 8 ≤ 20 * δ ^ (-ι) * (Q / 2) := by
    have hE8 : 1 ≤ Real.exp (L ^ (0.8 : ℝ)) := Real.one_le_exp (Real.rpow_nonneg hL0.le _)
    have : 20 * δ ^ (-ι) * (Q / 2) = 10 * R * Real.exp (L ^ (0.8 : ℝ)) := by
      rw [hQdef, hRdef]; ring
    rw [this]; nlinarith
  -- the deterministic inclusion
  set G : Set Ω := (allCellsEncW γ W δ δ' Bw ∩ E) ∩ (startEvW γ W δ δ' ι Bw A ∩ E) ∩
    (startEvW γ W δ δ' ι Bw B ∩ E) ∩ cellSizeEvent γ W δ' with hGdef
  have hsub : G ⊆ lem35EventOn (cellsInside Bw) γ W δ δ' A B := by
    rintro ω ⟨⟨⟨⟨hcell, hE⟩, hSA, -⟩, hSB, -⟩, hcs'⟩
    set m := approxLQG γ W ω with hmdef
    have hside : ∀ b, IsCell m δ b → b.side ≤ δ ^ c := fun b hb => (hE.1.2 b hb).2
    have hsp : WSplit m δ Bw := wsplit_of_side hE.1.1 fun b hb => (hside b hb).trans_lt hδc
    have hstartC : ∀ A' : Set ℂ, A' ⊆ kXi Bw.closedBox ξ → IsXiAdmissibleSet ξd δ A' →
        ω ∈ startEvW γ W δ δ' ι Bw A' →
        StartCond (fun c => m (wEmb Bw c)) δ δ' R (wHom Bw ⁻¹' A') := by
      intro A' hA'V hA'adm hSA'
      by_cases hs : ∃ u, A' = {u}
      · obtain ⟨u, hu⟩ := hs
        refine Or.inl ⟨(wHom Bw).symm u, by rw [hu, preimage_wHom_singleton], fun b hb hub =>
          hSA' u hu b hb hub⟩
      · rcases hA'adm with h | ⟨hconn, hdiam⟩
        · exact absurd h hs
        · refine Or.inr ⟨?_, fun b hb hsub => ?_⟩
          · rw [← (wHom Bw).image_symm]
            exact hconn.image _ (wHom Bw).symm.continuous.continuousOn
          have hsub' : A' ⊆ (wEmb Bw b).largeBox := by
            intro x hx
            rw [largeBox_wEmb]
            exact ⟨(wHom Bw).symm x, hsub (by simpa using hx), by simp⟩
          have hb' := (isCell_wEmb_iff hsp).2 hb
          have hd := Metric.diam_le_of_forall_dist_le
            (by linarith [wside_pos (wEmb Bw b)] : (0 : ℝ) ≤ 4 * (wEmb Bw b).side)
            fun x hx y hy => dist_le_of_mem_largeBox (hsub' hx) (hsub' hy)
          have := hside _ hb'
          linarith
    have hAV : A ⊆ dzzV := fun x hx => (hAB.1.subset_left hx).1
    have hBV : B ⊆ dzzV := fun x hx => (hAB.1.subset_right hx).1
    have hne : ∀ A' : Set ℂ, IsXiAdmissibleSet ξd δ A' → A'.Nonempty := by
      intro A' h
      rcases h with ⟨a, rfl⟩ | ⟨hconn, -⟩
      · exact singleton_nonempty a
      · exact hconn.nonempty
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ b, IsCell m δ' b → b.n ≤ N₀ := by
      obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one (Real.rpow_pos_of_pos hδ'0 (dzzCmc γ))
        (show (2 : ℝ)⁻¹ < 1 by norm_num)
      refine ⟨N₀, fun b hb => ?_⟩
      by_contra hlt
      have h1 := (hcs'.2 b hb).1
      have h2 : b.side ≤ (2 : ℝ)⁻¹ ^ N₀ :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith
    have hD := l35CrossingOn (m := m) (δ := δ) (δ' := δ') (lam := lam) (R := R) (k := k)
      (N₀ := N₀) (Bw := Bw) (A := A) (B := B) hδ'0 hδ'δ.le hlam1 (by linarith) hE.1.1 hcs'.1 hN₀
      hsp (fun b hb => hcell hsp b hb) (hAB.2.1.trans (kXi_sub_interior hξ))
      (hAB.2.2.trans (kXi_sub_interior hξ)) (hne A hAB.1.adm_left) (hne B hAB.1.adm_right)
      (hstartC A hAB.2.1 hAB.1.adm_left hSA) (hstartC B hAB.2.2 hAB.1.adm_right hSB)
    -- the lower bound `d ≥ 20 δ^{-ι}`
    set n := ⌈20 * δ ^ (-ι)⌉₊ with hndef
    have hn : (n : ℝ) ≤ 20 * δ ^ (-ι) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hlow := approxDistSet_ge_of_dist (m := m) (δ := δ) (s := δ ^ c) (n := n) hside
      (A := A) (B := B) fun x hx y hy => by
        have := hAB.1.dist_ge x hx y hy
        have h2 : 2 * δ ^ c * n ≤ 2 * δ ^ c * (20 * δ ^ (-ι) + 1) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
        linarith
    have hN : ENNReal.ofReal (20 * δ ^ (-ι)) ≤
        ((approxDistSetOn (cellsInside Bw) m δ A B : ℕ∞) : ℝ≥0∞) := by
      refine le_trans ?_ (ENat.toENNReal_le.2 (hlow.trans
        (approxDistSet_le_approxDistSetOn _ _ _ A B)))
      rw [show (n : ℕ∞) + 1 = ((n + 1 : ℕ) : ℕ∞) by push_cast; rfl, ENat.toENNReal_coe,
        ← ENNReal.ofReal_natCast]
      refine ENNReal.ofReal_le_ofReal ?_
      push_cast
      linarith [Nat.le_ceil (20 * δ ^ (-ι))]
    exact ennreal_chain hD ha hb (by positivity) hN (by positivity)
  -- the probability
  have pE : P.real Eᶜ ≤ δ ^ cE :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hEb δ ⟨hδ0, hδE'⟩)
  have p1 := hcells δ ⟨hδ0, hδ1'⟩ δ' ⟨hδ'0, hδ'δ.le⟩ Bw
  have p2 := startEvW_bound (A := A) (E := E)
    (fun u hu => hstart δ ⟨hδ0, hδ2'⟩ δ' ⟨hδ'0, hδ'δ.le⟩ u hu) (by positivity) hAB.2.1
  have p3 := startEvW_bound (A := B) (E := E)
    (fun u hu => hstart δ ⟨hδ0, hδ2'⟩ δ' ⟨hδ'0, hδ'δ.le⟩ u hu) (by positivity) hAB.2.2
  have p4 := dzz_lemma31_bound hW hγ hγ2 hδ'0 (by linarith)
  have hl31 : 0 ≤ l31const γ := by unfold l31const; positivity
  have p4' : l31const γ * δ' ≤ l31const γ * δ := mul_le_mul_of_nonneg_left hδ'δ.le hl31
  have hGc : P.real Gᶜ ≤ δ + δ ^ (ι / 20) + δ ^ (ι / 20) + l31const γ * δ + 3 * δ ^ cE := by
    rw [hGdef, compl_inter, compl_inter, compl_inter]
    refine (measureReal_union4_le _ _ _ _).trans ?_
    linarith
  have m1 : δ ≤ δ ^ c0 := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_left 1 (min cE (ι / 20)))
    rwa [Real.rpow_one] at this
  have m2 : δ ^ cE ≤ δ ^ c0 := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le
    ((min_le_right _ _).trans (min_le_left _ _))
  have m3 : δ ^ (ι / 20) ≤ δ ^ c0 := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hhalf : δ ^ (c0 / 2) ≤ 1 / K := by
    have := Real.rpow_le_rpow hδ0.le hδK.le (by positivity : 0 ≤ c0 / 2)
    rwa [← Real.rpow_mul (by positivity), show 2 / c0 * (c0 / 2) = 1 by field_simp,
      Real.rpow_one] at this
  have hsplit : δ ^ c0 = δ ^ (c0 / 2) * δ ^ (c0 / 2) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have hpos : 0 ≤ δ ^ (c0 / 2) := by positivity
  have hKh : K * δ ^ (c0 / 2) ≤ 1 := by
    rw [le_div_iff₀ hK] at hhalf; linarith
  have hfin : P.real Gᶜ ≤ δ ^ (c0 / 2) := by
    have h1 : P.real Gᶜ ≤ K * δ ^ c0 := by
      rw [hKdef]; nlinarith
    rw [hsplit] at h1
    nlinarith
  calc P (lem35EventOn (cellsInside Bw) γ W δ δ' A B)ᶜ ≤ P Gᶜ := measure_mono (compl_subset_compl.2 hsub)
    _ = ENNReal.ofReal (P.real Gᶜ) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (δ ^ (c0 / 2)) := ENNReal.ofReal_le_ofReal hfin

end DZZ
end LQGMetric
