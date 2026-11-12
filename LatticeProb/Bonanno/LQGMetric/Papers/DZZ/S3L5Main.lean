/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5Asym
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L9

/-!
# DZZ Lemma 3.5 from the crossing claim (P2-DZZ3G)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1037–1083): the proof of
Lemma 3.5 with all probabilistic steps done here:
`𝓔_{δ,α}` (`dzz_lemma34_fine`, α = 4 C_mc + 1), the enclosures around all `δ`-cells
(`l37_cells_enc`), the start/end pieces (`l35_start_hp`, `ι = C_Mc/2`), Lemma 3.1 at `δ'`
(the `δ'`-partition), the lower bound (Eq.lowerboundforDprime) (`approxDistSet_ge_of_dist`),
and the final arithmetic (`ennreal_chain`, `l35_asym`). The only remaining input is DZZ's
deterministic crossing claim `L35Crossing` (open, S3L5Cross).

Deviation: DZZ choose `ι = C_Mc/3`; we take `ι = C_Mc/2` (any `ι < C_Mc` works); the lemma is
proved for `ξd < C_Mc` (DZZ: `0 < ξ < C_Mc/3`, `ξd = ξ`).

* `startEv`, `startEv_bound`: the `ℂ_start` event of an end (trivial unless it is a point).
* `dzz_lemma35U_of_crossing : L35Crossing → DZZLemma35U P γ W ξ ξd`.
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

/-- The `ℂ_start` event of an end `A` (trivial unless `A` is a point). -/
def startEv (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ δ' ι : ℝ) (A : Set ℂ) : Set Ω :=
  {ω | ∀ u, A = {u} → ω ∈ startGood γ W δ δ' ι u}

lemma startEv_bound [IsFiniteMeasure P] {γ δ δ' ι q : ℝ} {A : Set ℂ} {E : Set Ω}
    (h : ∀ u ∈ dzzV, P.real (startGood γ W δ δ' ι u ∩ E)ᶜ ≤ q + P.real Eᶜ) (hq : 0 ≤ q)
    (hA : A ⊆ dzzV) : P.real (startEv γ W δ δ' ι A ∩ E)ᶜ ≤ q + P.real Eᶜ := by
  by_cases hs : ∃ u, A = {u}
  · obtain ⟨u, rfl⟩ := hs
    have e : startEv γ W δ δ' ι {u} = startGood γ W δ δ' ι u := by
      ext ω
      refine ⟨fun h => h u rfl, fun h u' hu' => ?_⟩
      obtain rfl := Set.singleton_eq_singleton_iff.1 hu'
      exact h
    rw [e]; exact h u (hA rfl)
  · have e : startEv γ W δ δ' ι A = univ := by
      ext ω
      simp only [startEv, mem_setOf_eq, mem_univ, iff_true]
      intro u hu; exact absurd ⟨u, hu⟩ hs
    rw [e, univ_inter]; linarith

lemma dist_le_of_mem_largeBox {b : DyBox} {x y : ℂ} (hx : x ∈ b.largeBox)
    (hy : y ∈ b.largeBox) : dist x y ≤ 4 * b.side := by
  obtain ⟨x1, x2⟩ := hx
  obtain ⟨y1, y2⟩ := hy
  rw [Complex.dist_eq]
  have a1 : |(x - y).re| ≤ 2 * b.side := by
    rw [Complex.sub_re]; have := abs_le.1 x1; have := abs_le.1 y1
    rw [abs_le]; constructor <;> linarith
  have a2 : |(x - y).im| ≤ 2 * b.side := by
    rw [Complex.sub_im]; have := abs_le.1 x2; have := abs_le.1 y2
    rw [abs_le]; constructor <;> linarith
  linarith [Complex.norm_le_abs_re_add_abs_im (x - y)]

lemma measureReal_union4_le [IsFiniteMeasure P] (X Y Z T : Set Ω) :
    P.real (X ∪ Y ∪ Z ∪ T) ≤ P.real X + P.real Y + P.real Z + P.real T := by
  have h1 := measureReal_union_le (μ := P) (X ∪ Y ∪ Z) T
  have h2 := measureReal_union_le (μ := P) (X ∪ Y) Z
  have h3 := measureReal_union_le (μ := P) X Y
  linarith

set_option maxHeartbeats 1000000 in
/-- **DZZ Lemma 3.5** (uniform form `DZZLemma35U`, decision D71) from DZZ's deterministic
crossing claim `L35Crossing`, for `0 < ξ` and `ξd < C_Mc`. -/
theorem dzz_lemma35U_of_crossing (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : L35Crossing) {ξ ξd : ℝ} (hξ : 0 < ξ) (hξd : ξd < dzzCMc γ) :
    DZZLemma35U P γ W ξ ξd := by
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
  obtain ⟨δ₁, hδ₁, hcells⟩ := l37_cells_enc hW hγ hγ2 hα
  obtain ⟨δ₂, hδ₂, hstart⟩ := l35_start_hp (α := α) hW hγ hγ2 hα0 hι
  obtain ⟨δ₃, hδ₃, hasym⟩ := l35_asym hC hc hξ hξd
  set c0 := min 1 (min cE (ι / 20)) with hc0def
  have hc0 : 0 < c0 := lt_min one_pos (lt_min hcE (by positivity))
  set K := 6 + l31const γ with hKdef
  have hK : 0 < K := by rw [hKdef]; unfold l31const; positivity
  refine ⟨c0 / 2, by positivity, min (min (min δE δ₁) (min δ₂ δ₃))
    (min (1 / 2) ((1 / K) ^ (2 / c0))), by positivity, ?_⟩
  rintro δ ⟨hδ0, hδ⟩ δ' ⟨hδ'0, hδ'δ⟩ A B hAB
  have hδE' : δ < δE := hδ.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδ1' : δ < δ₁ := hδ.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδ2' : δ < δ₂ := hδ.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hδ3' : δ < δ₃ := hδ.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hδh : δ < 1 / 2 := hδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
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
  set G : Set Ω := (allCellsEnc γ W δ δ' ∩ E) ∩ (startEv γ W δ δ' ι A ∩ E) ∩
    (startEv γ W δ δ' ι B ∩ E) ∩ cellSizeEvent γ W δ' with hGdef
  have hsub : G ⊆ lem35Event γ W δ δ' A B := by
    rintro ω ⟨⟨⟨⟨hcell, hE⟩, hSA, -⟩, hSB, -⟩, hcs'⟩
    set m := approxLQG γ W ω with hmdef
    have hside : ∀ b, IsCell m δ b → b.side ≤ δ ^ c := fun b hb => (hE.1.2 b hb).2
    have hstartC : ∀ A' : Set ℂ, A' ⊆ dzzVXi ξ → IsXiAdmissibleSet ξd δ A' →
        ω ∈ startEv γ W δ δ' ι A' → StartCond m δ δ' R A' := by
      intro A' hA'V hA'adm hSA'
      by_cases hs : ∃ u, A' = {u}
      · obtain ⟨u, hu⟩ := hs
        exact Or.inl ⟨u, hu, fun b hb hub => hSA' u hu b hb hub⟩
      · rcases hA'adm with h | ⟨hconn, hdiam⟩
        · exact absurd h hs
        · refine Or.inr ⟨hconn, fun b hb hsub => ?_⟩
          have hd := Metric.diam_le_of_forall_dist_le (by linarith [side_pos' b] : (0 : ℝ) ≤ 4 * b.side)
            fun x hx y hy => dist_le_of_mem_largeBox (hsub hx) (hsub hy)
          have := hside b hb
          linarith
    have hAV : A ⊆ dzzV := fun x hx => (hAB.subset_left hx).1
    have hBV : B ⊆ dzzV := fun x hx => (hAB.subset_right hx).1
    have hne : ∀ A' : Set ℂ, IsXiAdmissibleSet ξd δ A' → A'.Nonempty := by
      intro A' h
      rcases h with ⟨a, rfl⟩ | ⟨hconn, -⟩
      · exact singleton_nonempty a
      · exact hconn.nonempty
    have hcellsn : ∀ b, IsCell m δ b → 1 ≤ b.n := by
      intro b hb
      by_contra h0
      have h0' : b.n = 0 := by omega
      have : b.side = 1 := by unfold DyBox.side; rw [h0', pow_zero]
      have hlt : δ ^ c < 1 := Real.rpow_lt_one hδ0.le hδ1 hc
      linarith [hside b hb]
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ b, IsCell m δ' b → b.n ≤ N₀ := by
      obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one (Real.rpow_pos_of_pos hδ'0 (dzzCmc γ))
        (show (2 : ℝ)⁻¹ < 1 by norm_num)
      refine ⟨N₀, fun b hb => ?_⟩
      by_contra hlt
      have h1 := (hcs'.2 b hb).1
      have h2 : b.side ≤ (2 : ℝ)⁻¹ ^ N₀ :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith
    have hD := hX m δ δ' lam R k N₀ A B hδ'0 hδ'δ.le hlam1 (by linarith) hE.1.1 hcs'.1 hN₀
      hcellsn
      (fun b hb => hcell b hb) hAV hBV (hne A hAB.adm_left) (hne B hAB.adm_right)
      (hstartC A hAB.subset_left hAB.adm_left hSA) (hstartC B hAB.subset_right hAB.adm_right hSB)
    -- the lower bound `d ≥ 20 δ^{-ι}`
    set n := ⌈20 * δ ^ (-ι)⌉₊ with hndef
    have hn : (n : ℝ) ≤ 20 * δ ^ (-ι) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hlow := approxDistSet_ge_of_dist (m := m) (δ := δ) (s := δ ^ c) (n := n) hside
      (A := A) (B := B) fun x hx y hy => by
        have := hAB.dist_ge x hx y hy
        have h2 : 2 * δ ^ c * n ≤ 2 * δ ^ c * (20 * δ ^ (-ι) + 1) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
        linarith
    have hN : ENNReal.ofReal (20 * δ ^ (-ι)) ≤
        ((approxDistSet m δ A B : ℕ∞) : ℝ≥0∞) := by
      refine le_trans ?_ (ENat.toENNReal_le.2 hlow)
      rw [show (n : ℕ∞) + 1 = ((n + 1 : ℕ) : ℕ∞) by push_cast; rfl, ENat.toENNReal_coe,
        ← ENNReal.ofReal_natCast]
      refine ENNReal.ofReal_le_ofReal ?_
      push_cast
      linarith [Nat.le_ceil (20 * δ ^ (-ι))]
    exact ennreal_chain hD ha hb (by positivity) hN (by positivity)
  -- the probability
  have pE : P.real Eᶜ ≤ δ ^ cE :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hEb δ ⟨hδ0, hδE'⟩)
  have p1 := hcells δ ⟨hδ0, hδ1'⟩ δ' ⟨hδ'0, hδ'δ.le⟩
  have p2 := startEv_bound (A := A) (E := E) (fun u hu => hstart δ ⟨hδ0, hδ2'⟩ δ' ⟨hδ'0, hδ'δ.le⟩ u hu)
    (by positivity) fun x hx => (hAB.subset_left hx).1
  have p3 := startEv_bound (A := B) (E := E) (fun u hu => hstart δ ⟨hδ0, hδ2'⟩ δ' ⟨hδ'0, hδ'δ.le⟩ u hu)
    (by positivity) fun x hx => (hAB.subset_right hx).1
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
  calc P (lem35Event γ W δ δ' A B)ᶜ ≤ P Gᶜ := measure_mono (compl_subset_compl.2 hsub)
    _ = ENNReal.ofReal (P.real Gᶜ) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (δ ^ (c0 / 2)) := ENNReal.ofReal_le_ofReal hfin

end DZZ
end LQGMetric
