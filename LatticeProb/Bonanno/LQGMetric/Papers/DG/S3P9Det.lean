/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P9Det at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P9Top

/-!
# DG Proposition 3.9, the deterministic chain (P2-DG105j)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Proposition 3.9
(DG:1346–1391). On the event of Lemma 3.14 (both orientations) every grid rectangle `R` of level
`m ≥ k₀` carries a crossing path `P_R` whose points are pairwise at `D^ε(·,·;Q)`-distance
`≤ M_m` (`P39Hyp`). For a dyadic square `S` of level `k` (index `(a,b)`) the *hub* `h(S)` is a
point of `P_{H} ∩ P_{V}` for the bottom-left horizontal and vertical rectangles of level `k+1`
inside `S` (a point of DG's `#`-set `X_S`, DG:1352). Then
* `p39_step` (DG (eqn-dyadic-seq-diam)): `D(h(S), h(S̃)) ≤ 2M_{k+1} + M_{k+2}` for a child `S̃`;
* `p39_right`, `p39_up`: `D(h(S), h(S')) ≤ 4 M_{k+1}` for horizontally / vertically adjacent `S'`
  of the same level (DG:1384, "summing over dyadic squares whose union contains a path").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- the dyadic scale `2^{-m}` -/
abbrev p39d (m : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ m

lemma p39d_pos (m : ℕ) : 0 < p39d m := by positivity

lemma p39d_succ (m : ℕ) : p39d (m + 1) = p39d m / 2 := by
  simp only [p39d, pow_succ]; ring

lemma p39_c2 (k a : ℕ) : p39d (k + 1) * ((2 * a : ℕ) : ℝ) = p39d k * a := by
  rw [p39d_succ]; push_cast; ring

lemma p39_c2i (k a i : ℕ) :
    p39d (k + 1) * ((2 * a + i : ℕ) : ℝ) = p39d k * a + i * p39d (k + 1) := by
  rw [p39d_succ]; push_cast; ring

/-- **the event of DG Lemma 3.14 in both orientations**, as crossing paths of the grid
rectangles of level `m ≥ k₀` near the square `c + [0,L]²` -/
def P39Hyp (μ : Measure ℂ) (ε : ℝ) (Q : Set ℂ) (c : ℂ) (L : ℝ) (k₀ : ℕ) (Mf : ℕ → ℝ)
    (KH KV : ℕ → ℕ → ℕ → Set ℂ) : Prop :=
  (∀ m A B : ℕ, k₀ ≤ m → (A : ℝ) * p39d m ≤ L + p39d m → (B : ℝ) * p39d m ≤ L + p39d m →
    P39H μ ε Q (Mf m) (c.re + p39d m * A) (c.re + p39d m * A + 2 * p39d m)
      (c.im + p39d m * B) (c.im + p39d m * B + p39d m) (KH m A B)) ∧
  (∀ m A B : ℕ, k₀ ≤ m → (A : ℝ) * p39d m ≤ L + p39d m → (B : ℝ) * p39d m ≤ L + p39d m →
    P39V μ ε Q (Mf m) (c.re + p39d m * A) (c.re + p39d m * A + p39d m)
      (c.im + p39d m * B) (c.im + p39d m * B + 2 * p39d m) (KV m A B))

variable {μ : Measure ℂ} {ε : ℝ} {Q : Set ℂ} {c : ℂ} {L : ℝ} {k₀ : ℕ} {Mf : ℕ → ℝ}
  {KH KV : ℕ → ℕ → ℕ → Set ℂ}

/-- the index condition of a square of level `k` -/
def P39Ok (L : ℝ) (k₀ k a b : ℕ) : Prop :=
  k₀ ≤ k ∧ (a : ℝ) * p39d k ≤ L ∧ (b : ℝ) * p39d k ≤ L

/-- the hub of the square of level `k`, index `(a,b)` -/
def p39Hub (KH KV : ℕ → ℕ → ℕ → Set ℂ) (k a b : ℕ) : ℂ :=
  Classical.epsilon fun p => p ∈ KH (k + 1) (2 * a) (2 * b) ∩ KV (k + 1) (2 * a) (2 * b)

/-- the index condition at level `k+1` for `2a + i`, `i ≤ 1` -/
lemma p39_ok1 {k a : ℕ} (i : ℕ) (hi : i ≤ 1) (ha : (a : ℝ) * p39d k ≤ L) :
    ((2 * a + i : ℕ) : ℝ) * p39d (k + 1) ≤ L + p39d (k + 1) := by
  have e := p39_c2i k a i
  have : (i : ℝ) ≤ 1 := by exact_mod_cast hi
  have h1 := p39d_pos (k + 1)
  nlinarith

lemma p39_ok0 {k a : ℕ} (ha : (a : ℝ) * p39d k ≤ L) :
    ((2 * a : ℕ) : ℝ) * p39d (k + 1) ≤ L + p39d (k + 1) := by
  have e := p39_c2 k a
  have h1 := p39d_pos (k + 1)
  nlinarith

lemma p39_hub_mem (H : P39Hyp μ ε Q c L k₀ Mf KH KV) {k a b : ℕ} (h : P39Ok L k₀ k a b) :
    p39Hub KH KV k a b ∈ KH (k + 1) (2 * a) (2 * b) ∧
      p39Hub KH KV k a b ∈ KV (k + 1) (2 * a) (2 * b) := by
  obtain ⟨hk, ha, hb⟩ := h
  have hH := H.1 (k + 1) (2 * a) (2 * b) (by omega) (p39_ok0 ha) (p39_ok0 hb)
  have hV := H.2 (k + 1) (2 * a) (2 * b) (by omega) (p39_ok0 ha) (p39_ok0 hb)
  have hd := p39d_pos (k + 1)
  have hex := hH.meet hV le_rfl (by linarith) (by linarith) le_rfl (by linarith) (by linarith)
  exact Classical.epsilon_spec hex

/-- the triangle inequality along three and four points -/
lemma p39_tri3 (z p q w : ℂ) :
    (dgLGD μ ε Q z w : ℝ≥0∞) ≤ dgLGD μ ε Q z p + dgLGD μ ε Q p q + dgLGD μ ε Q q w := by
  calc (dgLGD μ ε Q z w : ℝ≥0∞) ≤ dgLGD μ ε Q z q + dgLGD μ ε Q q w := p39_tri z q w
    _ ≤ _ := by gcongr; exact p39_tri z p q

lemma p39_tri4 (z p q r w : ℂ) :
    (dgLGD μ ε Q z w : ℝ≥0∞) ≤ dgLGD μ ε Q z p + dgLGD μ ε Q p q + dgLGD μ ε Q q r +
      dgLGD μ ε Q r w := by
  calc (dgLGD μ ε Q z w : ℝ≥0∞) ≤ dgLGD μ ε Q z r + dgLGD μ ε Q r w := p39_tri z r w
    _ ≤ _ := by gcongr; exact p39_tri3 z p q r

/-- **DG (eqn-dyadic-seq-diam)**: the hub of a child is close to the hub of its parent -/
theorem p39_step (H : P39Hyp μ ε Q c L k₀ Mf KH KV) {k a b i j : ℕ} (hi : i ≤ 1) (hj : j ≤ 1)
    (h : P39Ok L k₀ k a b) (h' : P39Ok L k₀ (k + 1) (2 * a + i) (2 * b + j)) :
    (dgLGD μ ε Q (p39Hub KH KV k a b) (p39Hub KH KV (k + 1) (2 * a + i) (2 * b + j)) :
      ℝ≥0∞) ≤ ENNReal.ofReal (Mf (k + 1)) + ENNReal.ofReal (Mf (k + 1)) +
        ENNReal.ofReal (Mf (k + 1 + 1)) := by
  obtain ⟨hk, ha, hb⟩ := h
  obtain ⟨-, ha', hb'⟩ := h'
  have hd1 := p39d_pos (k + 1)
  have hd2 := p39d_pos (k + 1 + 1)
  have e2 : p39d (k + 1 + 1) = p39d (k + 1) / 2 := p39d_succ (k + 1)
  have hi' : (i : ℝ) ≤ 1 := by exact_mod_cast hi
  have hj' : (j : ℝ) ≤ 1 := by exact_mod_cast hj
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hV1 := H.2 (k + 1) (2 * a) (2 * b) (by omega) (p39_ok0 ha) (p39_ok0 hb)
  have hH1 := H.1 (k + 1) (2 * a) (2 * b + j) (by omega) (p39_ok0 ha) (p39_ok1 j hj hb)
  have hV2 := H.2 (k + 1 + 1) (2 * (2 * a + i)) (2 * (2 * b + j)) (by omega) (p39_ok0 ha')
    (p39_ok0 hb')
  have c1 := p39_c2 k a
  have c2 := p39_c2i k b j
  have c3 := p39_c2 (k + 1) (2 * a + i)
  have c4 := p39_c2 (k + 1) (2 * b + j)
  have c5 := p39_c2i k a i
  have c6 := p39_c2 k b
  obtain ⟨p₁, hp₁H, hp₁V⟩ := hH1.meet hV1 le_rfl (by linarith) (by linarith)
    (by rw [c2, c6]; nlinarith) (by linarith) (by rw [c2, c6]; nlinarith)
  obtain ⟨p₂, hp₂H, hp₂V⟩ := hH1.meet hV2 (by rw [c3, c5, c1]; nlinarith)
    (by linarith) (by rw [c3, c5, c1]; nlinarith) (by rw [c4]) (by linarith)
    (by rw [c4]; nlinarith)
  have hub1 := (p39_hub_mem H ⟨hk, ha, hb⟩).2
  have hub2 := (p39_hub_mem H ⟨by omega, ha', hb'⟩).2
  refine (p39_tri3 _ p₁ p₂ _).trans ?_
  gcongr
  · exact hV1.dist hub1 hp₁V
  · exact hH1.dist hp₁H hp₂H
  · exact hV2.dist hp₂V hub2

/-- adjacent squares in a row (DG:1384) -/
theorem p39_right (H : P39Hyp μ ε Q c L k₀ Mf KH KV) {k a b : ℕ}
    (h : P39Ok L k₀ k a b) (h' : P39Ok L k₀ k (a + 1) b) :
    (dgLGD μ ε Q (p39Hub KH KV k a b) (p39Hub KH KV k (a + 1) b) : ℝ≥0∞) ≤
      4 * ENNReal.ofReal (Mf (k + 1)) := by
  obtain ⟨hk, ha, hb⟩ := h
  obtain ⟨-, ha', hb'⟩ := h'
  have hd1 := p39d_pos (k + 1)
  have e1 : p39d (k + 1) = p39d k / 2 := p39d_succ k
  have hH0 := H.1 (k + 1) (2 * a) (2 * b) (by omega) (p39_ok0 ha) (p39_ok0 hb)
  have hV1 := H.2 (k + 1) (2 * a + 1) (2 * b) (by omega) (p39_ok1 1 le_rfl ha) (p39_ok0 hb)
  have hH1 := H.1 (k + 1) (2 * a + 1) (2 * b) (by omega) (p39_ok1 1 le_rfl ha) (p39_ok0 hb)
  have hV2 := H.2 (k + 1) (2 * (a + 1)) (2 * b) (by omega) (p39_ok0 ha') (p39_ok0 hb')
  have c1 := p39_c2 k a
  have c5 := p39_c2i k a 1
  have c7 := p39_c2 k (a + 1)
  simp only [Nat.cast_one, one_mul] at c5
  have e7 : ((a + 1 : ℕ) : ℝ) = a + 1 := by push_cast; ring
  obtain ⟨p₁, hp₁H, hp₁V⟩ := hH0.meet hV1 (by rw [c1, c5]; linarith) (by linarith)
    (by rw [c1, c5]; linarith) le_rfl (by linarith) (by linarith)
  obtain ⟨p₂, hp₂H, hp₂V⟩ := hH1.meet hV1 le_rfl (by linarith) (by linarith) le_rfl
    (by linarith) (by linarith)
  obtain ⟨p₃, hp₃H, hp₃V⟩ := hH1.meet hV2 (by rw [c5, c7, e7]; nlinarith) (by linarith)
    (by rw [c5, c7, e7]; nlinarith) le_rfl (by linarith) (by linarith)
  have hub1 := (p39_hub_mem H ⟨hk, ha, hb⟩).1
  have hub2 := (p39_hub_mem H ⟨hk, ha', hb'⟩).2
  refine (p39_tri4 _ p₁ p₂ p₃ _).trans ?_
  calc _ ≤ ENNReal.ofReal (Mf (k + 1)) + ENNReal.ofReal (Mf (k + 1)) +
        ENNReal.ofReal (Mf (k + 1)) + ENNReal.ofReal (Mf (k + 1)) := by
        gcongr
        · exact hH0.dist hub1 hp₁H
        · exact hV1.dist hp₁V hp₂V
        · exact hH1.dist hp₂H hp₃H
        · exact hV2.dist hp₃V hub2
    _ = _ := by ring

/-- adjacent squares in a column (DG:1384) -/
theorem p39_up (H : P39Hyp μ ε Q c L k₀ Mf KH KV) {k a b : ℕ}
    (h : P39Ok L k₀ k a b) (h' : P39Ok L k₀ k a (b + 1)) :
    (dgLGD μ ε Q (p39Hub KH KV k a b) (p39Hub KH KV k a (b + 1)) : ℝ≥0∞) ≤
      4 * ENNReal.ofReal (Mf (k + 1)) := by
  obtain ⟨hk, ha, hb⟩ := h
  obtain ⟨-, ha', hb'⟩ := h'
  have hd1 := p39d_pos (k + 1)
  have e1 : p39d (k + 1) = p39d k / 2 := p39d_succ k
  have hV0 := H.2 (k + 1) (2 * a) (2 * b) (by omega) (p39_ok0 ha) (p39_ok0 hb)
  have hH1 := H.1 (k + 1) (2 * a) (2 * b + 1) (by omega) (p39_ok0 ha) (p39_ok1 1 le_rfl hb)
  have hV1 := H.2 (k + 1) (2 * a) (2 * b + 1) (by omega) (p39_ok0 ha) (p39_ok1 1 le_rfl hb)
  have hH2 := H.1 (k + 1) (2 * a) (2 * (b + 1)) (by omega) (p39_ok0 ha') (p39_ok0 hb')
  have c1 := p39_c2 k b
  have c5 := p39_c2i k b 1
  have c7 := p39_c2 k (b + 1)
  simp only [Nat.cast_one, one_mul] at c5
  have e7 : ((b + 1 : ℕ) : ℝ) = b + 1 := by push_cast; ring
  obtain ⟨p₁, hp₁H, hp₁V⟩ := hH1.meet hV0 le_rfl (by linarith) (by linarith)
    (by rw [c1, c5]; linarith) (by linarith) (by rw [c1, c5]; linarith)
  obtain ⟨p₂, hp₂H, hp₂V⟩ := hH1.meet hV1 le_rfl (by linarith) (by linarith) le_rfl
    (by linarith) (by linarith)
  obtain ⟨p₃, hp₃H, hp₃V⟩ := hH2.meet hV1 le_rfl (by linarith) (by linarith)
    (by rw [c5, c7, e7]; nlinarith) (by linarith) (by rw [c5, c7, e7]; nlinarith)
  have hub1 := (p39_hub_mem H ⟨hk, ha, hb⟩).2
  have hub2 := (p39_hub_mem H ⟨hk, ha', hb'⟩).1
  refine (p39_tri4 _ p₁ p₂ p₃ _).trans ?_
  calc _ ≤ ENNReal.ofReal (Mf (k + 1)) + ENNReal.ofReal (Mf (k + 1)) +
        ENNReal.ofReal (Mf (k + 1)) + ENNReal.ofReal (Mf (k + 1)) := by
        gcongr
        · exact hV0.dist hub1 hp₁V
        · exact hH1.dist hp₁H hp₂H
        · exact hV1.dist hp₂V hp₃V
        · exact hH2.dist hp₃H hub2
    _ = _ := by ring

end DG
end LQGMetric
