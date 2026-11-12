/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17S1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17C
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P9Ev

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17, Step 2: the sets `Y_S` (P2-DG317S)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.17, Step 2
(DG:1557–1565): "For each of the `δ_ε`-side length squares `S ∈ 𝒮_{δ_ε}`, let `Y_S` be the union
of the paths `P_R` over the at most twelve `δ_ε × (δ_ε/2)` or `(δ_ε/2) × δ_ε` rectangles `R` as
above which overlap with `S`. Then `Y_S` is connected …, (eqn-lfpp-max-Y)
`max_{z,w ∈ Y_S} D^ε(z,w) ≤ 12 N e^{ξ ĥ(v_S)}`. Furthermore, if `S, S̃` share a side then
`Y_S ∩ Y_{S̃} ≠ ∅`."

Here `S = gridSquare (2^{-M}) k`, `t = 2^{-M-1} = δ_ε/2`, `k = (a,b)`, and the rectangles of DG's
family used are the six with corners `t(2a+i, 2b+j)`, `i + j ≤ 1`, of both orientations (the
horizontal ones `t(2a+i, 2b+j) + [0,2t] × [0,t]`, the vertical ones `+ [0,t] × [0,2t]`); their
crossings `KH`, `KV` are the paths `P_R` (`P39H`, `P39V` of P2-DG105j). Of DG's at most twelve
rectangles we only need these six: they already give connectivity (through the hub
`H(2a,2b) ∩ V(2a,2b)`, every point of `Y_S` is within three crossings of the hub, hence the
constant `6` instead of DG's `12`) and the intersections with the neighbours
(`H(2a+1,2b) ∩ V(2a+2,2b)`, `V(2a,2b+1) ∩ H(2a,2b+2)`, by `P39H.meet`).
* `p17sY` — the set `Y_S` (`univ` for indices outside `𝕊`, never used there);
* `p17s_hY`, `p17s_hadj`, `p17s_hnear` — the inputs `hY`, `hadj`, `hnear` of
  `dg_prop317_step3'`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint

variable {μ : Measure ℂ} {ε : ℝ} {Q : Set ℂ}

/-- the crossings of the six rectangles of the square `k` at level `M` with bound `N k` -/
def P17SHyp (μ : Measure ℂ) (ε : ℝ) (Q : Set ℂ) (M : ℕ) (KH KV : ℕ → ℕ → Set ℂ)
    (N : ℤ × ℤ → ℝ) : Prop :=
  ∀ k ∈ dgIdx M, ∀ i j : ℕ, i ≤ 1 → j ≤ 1 →
    P39H μ ε Q (N k) (p39d (M + 1) * ((2 * k.1.toNat + i : ℕ) : ℝ))
      (p39d (M + 1) * ((2 * k.1.toNat + i : ℕ) : ℝ) + 2 * p39d (M + 1))
      (p39d (M + 1) * ((2 * k.2.toNat + j : ℕ) : ℝ))
      (p39d (M + 1) * ((2 * k.2.toNat + j : ℕ) : ℝ) + p39d (M + 1))
      (KH (2 * k.1.toNat + i) (2 * k.2.toNat + j)) ∧
    P39V μ ε Q (N k) (p39d (M + 1) * ((2 * k.1.toNat + i : ℕ) : ℝ))
      (p39d (M + 1) * ((2 * k.1.toNat + i : ℕ) : ℝ) + p39d (M + 1))
      (p39d (M + 1) * ((2 * k.2.toNat + j : ℕ) : ℝ))
      (p39d (M + 1) * ((2 * k.2.toNat + j : ℕ) : ℝ) + 2 * p39d (M + 1))
      (KV (2 * k.1.toNat + i) (2 * k.2.toNat + j))

/-- DG's `Y_S` (DG:1561) -/
def p17sY (KH KV : ℕ → ℕ → Set ℂ) (M : ℕ) (k : ℤ × ℤ) : Set ℂ :=
  open Classical in
  if k ∈ dgIdx M then
    KH (2 * k.1.toNat) (2 * k.2.toNat) ∪ KH (2 * k.1.toNat + 1) (2 * k.2.toNat) ∪
      KH (2 * k.1.toNat) (2 * k.2.toNat + 1) ∪ KV (2 * k.1.toNat) (2 * k.2.toNat) ∪
      KV (2 * k.1.toNat) (2 * k.2.toNat + 1) ∪ KV (2 * k.1.toNat + 1) (2 * k.2.toNat)
  else univ

variable {M : ℕ} {KH KV : ℕ → ℕ → Set ℂ} {N : ℤ × ℤ → ℝ} {k : ℤ × ℤ}

lemma p17s_cast (a i : ℕ) : ((2 * a + i : ℕ) : ℝ) = 2 * a + i := by push_cast; ring

/-- the hub `H(2a,2b) ∩ V(2a,2b)` and the internal intersections of `Y_S` -/
lemma p17s_meets (H : P17SHyp μ ε Q M KH KV N) {k : ℤ × ℤ} (hk : k ∈ dgIdx M) :
    (KH (2 * k.1.toNat) (2 * k.2.toNat) ∩ KV (2 * k.1.toNat) (2 * k.2.toNat)).Nonempty ∧
    (KH (2 * k.1.toNat) (2 * k.2.toNat) ∩ KV (2 * k.1.toNat + 1) (2 * k.2.toNat)).Nonempty ∧
    (KH (2 * k.1.toNat + 1) (2 * k.2.toNat) ∩ KV (2 * k.1.toNat + 1) (2 * k.2.toNat)).Nonempty ∧
    (KH (2 * k.1.toNat) (2 * k.2.toNat + 1) ∩ KV (2 * k.1.toNat) (2 * k.2.toNat)).Nonempty ∧
    (KH (2 * k.1.toNat) (2 * k.2.toNat + 1) ∩ KV (2 * k.1.toNat) (2 * k.2.toNat + 1)).Nonempty := by
  have ht := p39d_pos (M + 1)
  have H00 := (H k hk 0 0 (by norm_num) (by norm_num)).1
  have H10 := (H k hk 1 0 (by norm_num) (by norm_num)).1
  have H01 := (H k hk 0 1 (by norm_num) (by norm_num)).1
  have V00 := (H k hk 0 0 (by norm_num) (by norm_num)).2
  have V10 := (H k hk 1 0 (by norm_num) (by norm_num)).2
  have V01 := (H k hk 0 1 (by norm_num) (by norm_num)).2
  simp only [add_zero] at H00 H10 H01 V00 V10 V01
  simp only [p17s_cast, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at H00 H10 H01 V00 V10 V01
  refine ⟨H00.meet V00 ?_ ?_ ?_ ?_ ?_ ?_, H00.meet V10 ?_ ?_ ?_ ?_ ?_ ?_,
    H10.meet V10 ?_ ?_ ?_ ?_ ?_ ?_, H01.meet V00 ?_ ?_ ?_ ?_ ?_ ?_,
    H01.meet V01 ?_ ?_ ?_ ?_ ?_ ?_⟩ <;> nlinarith

/-- every point of `Y_S` is within `3 N` of the hub -/
lemma p17s_hub (H : P17SHyp μ ε Q M KH KV N) {k : ℤ × ℤ} (hk : k ∈ dgIdx M) {h : ℂ}
    (hh : h ∈ KH (2 * k.1.toNat) (2 * k.2.toNat) ∩ KV (2 * k.1.toNat) (2 * k.2.toNat))
    {y : ℂ} (hy : y ∈ p17sY KH KV M k) :
    (dgLGD μ ε Q y h : ℝ≥0∞) ≤ ENNReal.ofReal (N k) + ENNReal.ofReal (N k) +
      ENNReal.ofReal (N k) := by
  obtain ⟨-, ⟨p₁, p₁H, p₁V⟩, ⟨p₂, p₂H, p₂V⟩, ⟨p₃, p₃H, p₃V⟩, ⟨p₄, p₄H, p₄V⟩⟩ := p17s_meets H hk
  have H00 := (H k hk 0 0 (by norm_num) (by norm_num)).1
  have H10 := (H k hk 1 0 (by norm_num) (by norm_num)).1
  have H01 := (H k hk 0 1 (by norm_num) (by norm_num)).1
  have V00 := (H k hk 0 0 (by norm_num) (by norm_num)).2
  have V10 := (H k hk 1 0 (by norm_num) (by norm_num)).2
  have V01 := (H k hk 0 1 (by norm_num) (by norm_num)).2
  simp only [add_zero] at H00 H10 H01 V00 V10 V01
  have hz : ∀ x : ℝ≥0∞, x ≤ x + ENNReal.ofReal (N k) + ENNReal.ofReal (N k) := fun x =>
    le_add_right le_self_add
  have hz2 : ∀ x : ℝ≥0∞, x ≤ ENNReal.ofReal (N k) + x + ENNReal.ofReal (N k) := fun x =>
    le_add_right le_add_self
  simp only [p17sY, hk, ite_true, mem_union] at hy
  rcases hy with ((((hy | hy) | hy) | hy) | hy) | hy
  · exact (H00.dist hy hh.1).trans (hz _)
  · -- `H(2a+1,2b) → V(2a+1,2b) → H(2a,2b)`
    refine (p39_tri3 y p₂ p₁ h).trans ?_
    gcongr
    · exact H10.dist hy p₂H
    · exact V10.dist p₂V p₁V
    · exact H00.dist p₁H hh.1
  · -- `H(2a,2b+1) → V(2a,2b)`
    calc (dgLGD μ ε Q y h : ℝ≥0∞) ≤ dgLGD μ ε Q y p₃ + dgLGD μ ε Q p₃ h := p39_tri y p₃ h
      _ ≤ ENNReal.ofReal (N k) + ENNReal.ofReal (N k) :=
          add_le_add (H01.dist hy p₃H) (V00.dist p₃V hh.2)
      _ ≤ _ := le_self_add
  · exact (V00.dist hy hh.2).trans (hz _)
  · -- `V(2a,2b+1) → H(2a,2b+1) → V(2a,2b)`
    refine (p39_tri3 y p₄ p₃ h).trans ?_
    gcongr
    · exact V01.dist hy p₄V
    · exact H01.dist p₄H p₃H
    · exact V00.dist p₃V hh.2
  · -- `V(2a+1,2b) → H(2a,2b)`
    calc (dgLGD μ ε Q y h : ℝ≥0∞) ≤ dgLGD μ ε Q y p₁ + dgLGD μ ε Q p₁ h := p39_tri y p₁ h
      _ ≤ ENNReal.ofReal (N k) + ENNReal.ofReal (N k) :=
          add_le_add (V10.dist hy p₁V) (H00.dist p₁H hh.1)
      _ ≤ _ := le_self_add

lemma p17s_ofReal_six {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (6 * x) = (ENNReal.ofReal x + ENNReal.ofReal x + ENNReal.ofReal x) +
      (ENNReal.ofReal x + ENNReal.ofReal x + ENNReal.ofReal x) := by
  have h3 : ENNReal.ofReal (3 * x) = ENNReal.ofReal x + ENNReal.ofReal x + ENNReal.ofReal x := by
    rw [show 3 * x = x + x + x by ring, ENNReal.ofReal_add (by linarith) hx,
      ENNReal.ofReal_add hx hx]
  rw [show 6 * x = 3 * x + 3 * x by ring, ENNReal.ofReal_add (by linarith) (by linarith), h3]

/-- **DG (eqn-lfpp-max-Y)**: `max_{y,y' ∈ Y_S} D^ε(y, y'; Q) ≤ 6 N_S` -/
theorem p17s_hY (H : P17SHyp μ ε Q M KH KV N) (hN : ∀ k, 0 ≤ N k) :
    ∀ k ∈ dgIdx M, ∀ y ∈ p17sY KH KV M k, ∀ y' ∈ p17sY KH KV M k,
      (dgLGD μ ε Q y y' : ℝ≥0∞) ≤ ENNReal.ofReal (6 * N k) := by
  intro k hk y hy y' hy'
  obtain ⟨⟨h, hh⟩, -⟩ := p17s_meets H hk
  rw [p17s_ofReal_six (hN k)]
  calc (dgLGD μ ε Q y y' : ℝ≥0∞) ≤ dgLGD μ ε Q y h + dgLGD μ ε Q h y' := p39_tri y h y'
    _ ≤ dgLGD μ ε Q y h + dgLGD μ ε Q y' h := by gcongr; exact p39_symm _ _
    _ ≤ _ := add_le_add (p17s_hub H hk hh hy) (p17s_hub H hk hh hy')

lemma p17s_subH (hk : k ∈ dgIdx M) {i j : ℕ} (hij : i + j ≤ 1) :
    KH (2 * k.1.toNat + i) (2 * k.2.toNat + j) ⊆ p17sY KH KV M k := by
  intro y hy
  simp only [p17sY, hk, ite_true, mem_union]
  rcases (show (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) by omega) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

lemma p17s_subV (hk : k ∈ dgIdx M) {i j : ℕ} (hij : i + j ≤ 1) :
    KV (2 * k.1.toNat + i) (2 * k.2.toNat + j) ⊆ p17sY KH KV M k := by
  intro y hy
  simp only [p17sY, hk, ite_true, mem_union]
  rcases (show (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) by omega) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

lemma p17s_nonempty (H : P17SHyp μ ε Q M KH KV N) (k : ℤ × ℤ) :
    (p17sY KH KV M k).Nonempty := by
  by_cases hk : k ∈ dgIdx M
  · obtain ⟨⟨h, hh, -⟩, -⟩ := p17s_meets H hk
    exact ⟨h, p17s_subH (i := 0) (j := 0) hk (by norm_num) hh⟩
  · simp [p17sY, hk]

/-- the right neighbour: `H(2a+1,2b) ∩ V(2a+2,2b) ≠ ∅` -/
lemma p17s_right (H : P17SHyp μ ε Q M KH KV N) {k k' : ℤ × ℤ} (hk : k ∈ dgIdx M)
    (hk' : k' ∈ dgIdx M) (e1 : k'.1.toNat = k.1.toNat + 1) (e2 : k'.2.toNat = k.2.toNat) :
    (p17sY KH KV M k ∩ p17sY KH KV M k').Nonempty := by
  have ht := p39d_pos (M + 1)
  have H10 := (H k hk 1 0 (by norm_num) (by norm_num)).1
  have V00 := (H k' hk' 0 0 (by norm_num) (by norm_num)).2
  have hs := p17s_subV (KH := KH) (KV := KV) (i := 0) (j := 0) hk' (by norm_num)
  rw [e1, e2] at V00 hs
  simp only [add_zero] at H10 V00 hs
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_add] at H10 V00
  obtain ⟨p, hp1, hp2⟩ := H10.meet V00 (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
    (by nlinarith) (by nlinarith)
  exact ⟨p, p17s_subH (i := 1) (j := 0) hk (by norm_num) (by simpa using hp1), hs hp2⟩

/-- the upper neighbour: `V(2a,2b+1) ∩ H(2a,2b+2) ≠ ∅` -/
lemma p17s_up (H : P17SHyp μ ε Q M KH KV N) {k k' : ℤ × ℤ} (hk : k ∈ dgIdx M)
    (hk' : k' ∈ dgIdx M) (e1 : k'.1.toNat = k.1.toNat) (e2 : k'.2.toNat = k.2.toNat + 1) :
    (p17sY KH KV M k ∩ p17sY KH KV M k').Nonempty := by
  have ht := p39d_pos (M + 1)
  have V01 := (H k hk 0 1 (by norm_num) (by norm_num)).2
  have H00 := (H k' hk' 0 0 (by norm_num) (by norm_num)).1
  have hs := p17s_subH (KH := KH) (KV := KV) (i := 0) (j := 0) hk' (by norm_num)
  rw [e1, e2] at H00 hs
  simp only [add_zero] at V01 H00 hs
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_add] at V01 H00
  obtain ⟨p, hp1, hp2⟩ := H00.meet V01 (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
    (by nlinarith) (by nlinarith)
  exact ⟨p, p17s_subV (i := 0) (j := 1) hk (by norm_num) (by simpa using hp2), hs hp1⟩

/-- **adjacent `Y_S` intersect** (DG:1565) -/
theorem p17s_hadj (H : P17SHyp μ ε Q M KH KV N) :
    ∀ k k', dgAdj k k' → (p17sY KH KV M k ∩ p17sY KH KV M k').Nonempty := by
  intro k k' h
  by_cases hk : k ∈ dgIdx M
  swap
  · simp only [p17sY, hk, ite_false, univ_inter]; exact p17s_nonempty H k'
  by_cases hk' : k' ∈ dgIdx M
  swap
  · simp only [p17sY, hk', ite_false, inter_univ]; exact p17s_nonempty H k
  have a1 := hk.1; have a2 := hk.2.2.1; have a3 := hk'.1; have a4 := hk'.2.2.1
  unfold dgAdj at h
  rcases abs_cases (k.1 - k'.1) with ⟨e1, s1⟩ | ⟨e1, s1⟩ <;>
    rcases abs_cases (k.2 - k'.2) with ⟨e2, s2⟩ | ⟨e2, s2⟩
  · rcases (show (k.1 = k'.1 + 1 ∧ k.2 = k'.2) ∨ (k.2 = k'.2 + 1 ∧ k.1 = k'.1) by omega) with
      ⟨c1, c2⟩ | ⟨c1, c2⟩
    · rw [inter_comm]; exact p17s_right H hk' hk (by omega) (by omega)
    · rw [inter_comm]; exact p17s_up H hk' hk (by omega) (by omega)
  · rcases (show (k.1 = k'.1 + 1 ∧ k.2 = k'.2) ∨ (k'.2 = k.2 + 1 ∧ k.1 = k'.1) by omega) with
      ⟨c1, c2⟩ | ⟨c1, c2⟩
    · rw [inter_comm]; exact p17s_right H hk' hk (by omega) (by omega)
    · exact p17s_up H hk hk' (by omega) (by omega)
  · rcases (show (k'.1 = k.1 + 1 ∧ k.2 = k'.2) ∨ (k.2 = k'.2 + 1 ∧ k.1 = k'.1) by omega) with
      ⟨c1, c2⟩ | ⟨c1, c2⟩
    · exact p17s_right H hk hk' (by omega) (by omega)
    · rw [inter_comm]; exact p17s_up H hk' hk (by omega) (by omega)
  · rcases (show (k'.1 = k.1 + 1 ∧ k.2 = k'.2) ∨ (k'.2 = k.2 + 1 ∧ k.1 = k'.1) by omega) with
      ⟨c1, c2⟩ | ⟨c1, c2⟩
    · exact p17s_right H hk hk' (by omega) (by omega)
    · exact p17s_up H hk hk' (by omega) (by omega)

/-- `Y_S` comes within `4 t = 2 δ_ε` of every point of `S` (the hub) -/
theorem p17s_hnear (H : P17SHyp μ ε Q M KH KV N) :
    ∀ k ∈ dgIdx M, ∀ x ∈ gridSquare ((2 : ℝ)⁻¹ ^ M) k, ∃ y ∈ p17sY KH KV M k,
      ‖y - x‖ ≤ 4 * p39d (M + 1) := by
  intro k hk x hx
  obtain ⟨⟨h, hh⟩, -⟩ := p17s_meets H hk
  have H00 := (H k hk 0 0 (by norm_num) (by norm_num)).1
  have V00 := (H k hk 0 0 (by norm_num) (by norm_num)).2
  simp only [add_zero] at H00 V00
  have him := H00.im_mem hh.1
  have hre := V00.re_mem hh.2
  have ea : ((2 * k.1.toNat : ℕ) : ℝ) = 2 * (k.1 : ℝ) := by
    push_cast; rw [← Int.cast_natCast, Int.toNat_of_nonneg hk.1]
  have eb : ((2 * k.2.toNat : ℕ) : ℝ) = 2 * (k.2 : ℝ) := by
    push_cast; rw [← Int.cast_natCast, Int.toNat_of_nonneg hk.2.2.1]
  rw [ea] at hre
  rw [eb] at him
  have es : (2 : ℝ)⁻¹ ^ M = 2 * p39d (M + 1) := by rw [p39d_succ]; ring
  obtain ⟨x1, x2, x3, x4⟩ := hx
  rw [es] at x1 x2 x3 x4
  have ht := p39d_pos (M + 1)
  refine ⟨h, p17s_subH (i := 0) (j := 0) hk (by norm_num) (by simpa using hh.1), ?_⟩
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]
  have c1 : |h.re - x.re| ≤ 2 * p39d (M + 1) := abs_le.2 ⟨by nlinarith [hre.1, hre.2],
    by nlinarith [hre.1, hre.2]⟩
  have c2 : |h.im - x.im| ≤ 2 * p39d (M + 1) := abs_le.2 ⟨by nlinarith [him.1, him.2],
    by nlinarith [him.1, him.2]⟩
  linarith

end LQGMetric.DG
