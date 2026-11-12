/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32XW at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32VGeo

/-!
# DZZ P3.2 upper bound at the walled measure: wall-interior ring boundaries (D102)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Proposition 3.2, upper bound,
l. 1088–1153 (cover of the ring boundaries `∂B'_i` by `4ε/t` balls of radius `ts` at the grid
corners, l. 1131–1137). Decision D102 (decisions/DEC-102.md), refining D97/D101.

At the walled measure `μIn = dzzWall dzzV (M^W)` every ball of finite mass lies in the closed
square, hence in the open square. D101 covered the clipped boundary `∂(B' ∩ 𝕍_{−r})`; this is
impossible for a ring box touching `∂𝕍` (handoff/P2-DZZ32C.md: the side on the line at depth `r`
needs `≳ √(εs/r)` balls, a power of `δ⁻¹`). D102 replaces the covered curve by the
**wall-interior boundary** `∂B' ∩ 𝕍_{−r}`: the sides of `B'` on `∂𝕍` are dropped, no new side at
depth `r` is added. DZZ's own balls (l. 1131–1137) minus those centred on `∂𝕍` cover it
(the ball at the corner `(x, ts)` covers `{x} × (0, 2ts)`), so DZZ's count `4ε/t ≤ λ` is kept.

* `cellPhiW μ δ r b`, `PhiLeW`: the cover number of `∂B ∩ 𝕍_{−r}` and `Φ^W ≤ λ`.
* `L32BallCrossingW` (open, deterministic): the clipped crossing `L32BallCrossingC` with `PhiLeW`.
* `encPhiAllW`, `L32EncPhiHPW` (open, probabilistic): (eq-B-percolation-Psi) with `PhiLeW`.
* `IsBdrySqW`, `ringSqW`: the level-`N` boundary squares of a ring box that touch a side of the
  box not on `∂𝕍` (the squares DZZ's crossing uses on the level-`N` grid, decision D84, now
  without the squares that touch the box only through the wall).
* **`l32UpperCross_ofW`**: `L32UpperCross P γ W μ ξ ξd` from `L32BallCrossingW`, `L32EncPhiHPW`
  and the unchanged `L32StartPhiHPC` (the proof of `l32UpperCross_ofC`, S3P32UClip, verbatim).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `Φ^W_{B,δ,r}`: the least number of open balls of `μ`-mass at most `δ²` covering the
wall-interior boundary `∂B ∩ 𝕍_{−r}` (the sides of `B` on `∂𝕍` are not covered). -/
def cellPhiW (μ : Measure ℂ) (δ r : ℝ) (b : DyBox) : ℕ∞ :=
  ⨅ (S : Finset (ℂ × ℝ)) (_ : frontier b.closedBox ∩ dzzVIn r ⊆ ⋃ p ∈ S, Metric.ball p.1 p.2)
    (_ : ∀ p ∈ S, μ (Metric.ball p.1 p.2) ≤ ENNReal.ofReal (δ ^ 2)), (S.card : ℕ∞)

/-- `Φ^W_{B,δ,r} ≤ λ`. -/
def PhiLeW (μ : Measure ℂ) (δ r : ℝ) (b : DyBox) (lam : ℝ) : Prop :=
  ∃ N : ℕ, cellPhiW μ δ r b = N ∧ (N : ℝ) ≤ lam

/-- `Φ^W ≤ λ`: a cover of `∂B ∩ 𝕍_{−r}` by at most `λ` balls of mass `≤ δ²`. -/
lemma exists_cover_of_phiLeW {μ : Measure ℂ} {δ r : ℝ} {b : DyBox} {lam : ℝ}
    (h : PhiLeW μ δ r b lam) :
    ∃ S : Finset (ℂ × ℝ), (S.card : ℝ) ≤ lam ∧
      frontier b.closedBox ∩ dzzVIn r ⊆ ⋃ p ∈ S, Metric.ball p.1 p.2 ∧
      ∀ p ∈ S, μ (Metric.ball p.1 p.2) ≤ ENNReal.ofReal (δ ^ 2) := by
  obtain ⟨N, hN, hNl⟩ := h
  have hlt : cellPhiW μ δ r b < ((N + 1 : ℕ) : ℕ∞) := by
    rw [hN]; exact_mod_cast Nat.lt_succ_self N
  simp only [cellPhiW, iInf_lt_iff] at hlt
  obtain ⟨S, hcov, hmass, hcard⟩ := hlt
  have : S.card ≤ N := by
    have : S.card < N + 1 := by exact_mod_cast hcard
    omega
  refine ⟨S, ?_, hcov, hmass⟩
  have : (S.card : ℝ) ≤ N := by exact_mod_cast this
  linarith

/-- **The wall-interior crossing claim for balls** (open, deterministic; D102): the clipped
crossing `L32BallCrossingC` with the covered curves `∂B' ∩ 𝕍_{−r}` in place of `∂(B' ∩ 𝕍_{−r})`;
`2r` is smaller than the side `2^{-(n+k)}` of every ring box and the ends lie in `𝕍_{−r}`. -/
def L32BallCrossingW : Prop :=
  ∀ (m : DyBox → ℝ) (μ : Measure ℂ) (δ lam R r : ℝ) (k N₀ : ℕ) (A B : Set ℂ), 0 < δ → 1 ≤ lam →
    0 ≤ R → 0 < r → 2 * r < (2⁻¹ : ℝ) ^ (N₀ + k) →
    (∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) → (∀ b, IsCell m δ b → b.n ≤ N₀) →
    (∀ b, IsCell m δ b → 1 ≤ b.n) →
    (∀ b, IsCell m δ b → HasEnclosure b k fun b' => PhiLeW μ δ r b' lam) →
    A ⊆ dzzVIn r → B ⊆ dzzVIn r → A.Nonempty → B.Nonempty →
    BallStartCondC μ m δ r R A → BallStartCondC μ m δ r R B →
    ((lgdMinSet μ δ A B : ℕ∞) : ℝ≥0∞) ≤
      ((approxDistSet m δ A B : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (4 ^ (k + 2) * (lam + 1)) +
        ENNReal.ofReal (2 * R + 8)

/-- All `δ`-cells have an enclosure by boxes with `Φ^W_{B',δ,r} ≤ λ`. -/
def encPhiAllW (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (r δ : ℝ) : Set Ω :=
  {ω | ∀ b, IsCell (approxLQG γ W ω) δ b →
    HasEnclosure b (kL37 γ δ) fun b' => PhiLeW (μ ω) δ r b' (lamP32 δ)}

/-- **(eq-B-percolation-Psi) for the wall-interior boundaries + union bound over the cells**
(open; D102), with depth `r δ`. True at `μIn` for every positive depth: DZZ's balls of radius
`ts` at the grid corners of `𝓑'_i` on `∂B'_i` not on `∂𝕍` (l. 1131–1137). -/
def L32EncPhiHPW (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ)
    (r : ℝ → ℝ) : Prop :=
  HighProb P fun δ => encPhiAllW γ W μ (r δ) δ

/-- A level-`N` square of `B` touching a side of `B` that is not on `∂𝕍` (the boundary squares
`IsBdrySq` of the level-`N` crossing, D84, without those that touch `B` only through the wall). -/
def IsBdrySqW (N : ℕ) (B b : DyBox) : Prop :=
  b.n = N ∧ b.closedBox ⊆ B.closedBox ∧
    ((b.j = B.j * 2 ^ (N - B.n) ∧ B.j ≠ 0) ∨
      (b.j + 1 = (B.j + 1) * 2 ^ (N - B.n) ∧ B.j + 1 ≠ 2 ^ B.n) ∨
      (b.k = B.k * 2 ^ (N - B.n) ∧ B.k ≠ 0) ∨
      (b.k + 1 = (B.k + 1) * 2 ^ (N - B.n) ∧ B.k + 1 ≠ 2 ^ B.n))

/-- The wall-interior boundary squares of the boxes of `U`. -/
def ringSqW (N : ℕ) (U : Set DyBox) : Set DyBox := {b | ∃ B ∈ U, IsBdrySqW N B b}

set_option maxHeartbeats 1000000 in
/-- **`L32UpperCross` at any measure from the wall-interior crossing, `L32EncPhiHPW` and
`L32StartPhiHPC`** (DZZ l. 1088–1101 following Lemma 3.5, l. 1054–1083; D102). The proof is
that of `l32UpperCross_ofC` (S3P32UClip) with `PhiLeW` in place of `PhiLeC`. -/
theorem l32UpperCross_ofW {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} {ξ ξd : ℝ} {r : ℝ → ℝ}
    (hr : IsClipDepth γ r) (hX : L32BallCrossingW)
    (h1 : L32EncPhiHPW P γ W μ r) (h2 : L32StartPhiHPC P γ W μ r) (hξ : 0 < ξ)
    (hξd : ξd < dzzCMc γ) : L32UpperCross P γ W μ ξ ξd := by
  have := hW.isProbabilityMeasure
  set C := dzzCmc γ with hCdef
  set c := dzzCMc γ with hcdef
  have hC : 0 < C := by have := l31theta_pos hγ hγ2; rw [hCdef]; unfold dzzCmc; linarith
  have hc : 0 < c := dzzCMc_pos γ
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
    have hδ1 : δ < 1 := hδ.2.trans_le (min_le_left _ _)
    have hlt : δ < (4 * ξ) ^ (1 / C) := hδ.2.trans_le (min_le_right _ _)
    have := Real.rpow_le_rpow hδ.1.le hlt.le hC.le
    rwa [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hC.ne', Real.rpow_one] at this
  refine ⟨c0 / 2, by positivity,
    min (min δ₁ δ₂) (min (min δ₃ δ₄) (min (1 / 2) ((1 / K) ^ (2 / c0)))), by positivity, ?_⟩
  rintro δ ⟨hδ0, hδ⟩ A B hAB
  have hδ1' : δ < δ₁ := hδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ2' : δ < δ₂ := hδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ3' : δ < δ₃ := hδ.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδ4' : δ < δ₄ := hδ.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδh : δ < 1 / 2 := hδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hδK : δ < (1 / K) ^ (2 / c0) := hδ.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hδ1 : δ < 1 := by linarith
  obtain ⟨-, -, as3, -⟩ := hasym δ ⟨hδ0, hδ3'⟩
  obtain ⟨hr0, hr4⟩ := hr δ ⟨hδ0, hδ1⟩
  have hrξ : r δ ≤ ξ := by
    have h4 := hδ₄ξ δ ⟨hδ0, hδ4'⟩
    have hk : (2⁻¹ : ℝ) ^ kL37 γ δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hδC : 0 ≤ δ ^ C := by positivity
    nlinarith
  set L := Real.log δ⁻¹ with hLdef
  have hL0 : 0 < L := by
    rw [hLdef, Real.log_inv]; have := Real.log_neg hδ0 hδ1; linarith
  set k := kL37 γ δ with hkdef
  set lam := lamP32 δ with hlamdef
  have hlam1 : 1 ≤ lam := Real.one_le_exp (Real.rpow_nonneg hL0.le _)
  set R := δ ^ (-(c / 2)) * lam with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hAV : A ⊆ dzzVIn (r δ) := hAB.subset_left.trans (dzzVXi_sub_dzzVIn hrξ)
  have hBV : B ⊆ dzzVIn (r δ) := hAB.subset_right.trans (dzzVXi_sub_dzzVIn hrξ)
  set G : Set Ω := encPhiAllW γ W μ (r δ) δ ∩ startPhiEvC γ W μ (r δ) δ (c / 2) A ∩
    startPhiEvC γ W μ (r δ) δ (c / 2) B ∩ cellSizeEvent γ W δ with hGdef
  have hsub : G ⊆ p32CrossEvent γ W μ δ A B := by
    rintro ω ⟨⟨⟨hE, hSA⟩, hSB⟩, hcs⟩
    set m := approxLQG γ W ω with hmdef
    have hside : ∀ b, IsCell m δ b → b.side ≤ δ ^ c := fun b hb => (hcs.2 b hb).2
    have hstartC : ∀ A' : Set ℂ, IsXiAdmissibleSet ξd δ A' →
        ω ∈ startPhiEvC γ W μ (r δ) δ (c / 2) A' → BallStartCondC (μ ω) m δ (r δ) R A' := by
      intro A' hA'adm hSA'
      by_cases hs : ∃ u, A' = {u}
      · obtain ⟨u, hu⟩ := hs
        exact Or.inl ⟨u, hu, fun b hb hub => hSA' u hu b hb hub⟩
      · rcases hA'adm with h | ⟨hconn, hdiam⟩
        · exact absurd h hs
        · refine Or.inr ⟨hconn, fun b hb hsub => ?_⟩
          have hd := Metric.diam_le_of_forall_dist_le
            (by linarith [side_pos' b] : (0 : ℝ) ≤ 4 * b.side)
            fun x hx y hy => dist_le_of_mem_largeBox (hsub hx) (hsub hy)
          have := hside b hb
          linarith
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
    have hr2 : 2 * r δ < (2⁻¹ : ℝ) ^ (N₀ + k) := by
      rw [pow_add]
      have hk0 : 0 ≤ (2⁻¹ : ℝ) ^ k := by positivity
      have := mul_le_mul_of_nonneg_right hN₀ge hk0
      linarith
    exact hX m (μ ω) δ lam R (r δ) k N₀ A B hδ0 hlam1 hR0 hr0 hr2 hcs.1 hN₀ hcellsn
      (fun b hb => hE b hb) hAV hBV (hne A hAB.adm_left) (hne B hAB.adm_right)
      (hstartC A hAB.adm_left hSA) (hstartC B hAB.adm_right hSB)
  -- the probability
  have p1 := hb1 δ ⟨hδ0, hδ1'⟩
  have p2 := startPhiEvC_bound (P := P) (γ := γ) (W := W) (μ := μ) (r := r δ) (δ := δ)
    (ι := c / 2) (A := A) (fun u hu => hb2 δ ⟨hδ0, hδ2'⟩ u hu) hAV
  have p3 := startPhiEvC_bound (P := P) (γ := γ) (W := W) (μ := μ) (r := r δ) (δ := δ)
    (ι := c / 2) (A := B) (fun u hu => hb2 δ ⟨hδ0, hδ2'⟩ u hu) hBV
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
  calc P (p32CrossEvent γ W μ δ A B)ᶜ ≤ P Gᶜ := measure_mono (compl_subset_compl.2 hsub)
    _ ≤ P (encPhiAllW γ W μ (r δ) δ)ᶜ + P (startPhiEvC γ W μ (r δ) δ (c / 2) A)ᶜ +
          P (startPhiEvC γ W μ (r δ) δ (c / 2) B)ᶜ + P (cellSizeEvent γ W δ)ᶜ := by
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
