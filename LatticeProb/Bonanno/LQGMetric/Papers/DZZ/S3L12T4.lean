/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12T4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12T3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L316P2

/-!
# DZZ Lemma 3.12, one-step claim: the length of the replacing segment (P2-DZZ312S)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1457: "in every step, the number of
cells increases by at most `4 (ε*)^{-2}`": the replacing segment consists of distinct cells of side
`≥ ε* s_𝖢` meeting `𝖢_large`. Own elementary count (bound `32 (ε*)^{-2}`, DEVIATIONS P2-DZZ316 item 2):
each such cell contains a square of level `n_𝖢 + k` (`ε* = 2^{-k}`) meeting `𝖢_large`, and there
are at most `(3·2^k + 1)²` of those.

* `exists_sq_of_mem_closedBox`: a point of a closed box of level `≤ K` lies in a level-`K` square
  of the box;
* **`length_le_of_near`**: a loop-free list of cells of side `≥ 2^{-k} s_𝖢` whose closures meet
  `𝖢_large` has at most `32 · 4^k` elements.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma exists_sq_of_mem_closedBox {b : DyBox} {K : ℕ} (hb : b.n ≤ K) {z : ℂ}
    (hz : z ∈ b.closedBox) :
    ∃ q : DyBox, q.n = K ∧ q.closedBox ⊆ b.closedBox ∧ z ∈ q.closedBox := by
  obtain ⟨a1, a2, a3, a4⟩ := (bx_mem_closedBox hb).1 hz
  have hP : 1 ≤ 2 ^ (K - b.n) := Nat.one_le_two_pow
  have e1 : (((b.j + 1) * 2 ^ (K - b.n) : ℕ) : ℝ) = ((b.j * 2 ^ (K - b.n) : ℕ) : ℝ) +
      ((2 ^ (K - b.n) : ℕ) : ℝ) := by push_cast; ring
  have e2 : (((b.k + 1) * 2 ^ (K - b.n) : ℕ) : ℝ) = ((b.k * 2 ^ (K - b.n) : ℕ) : ℝ) +
      ((2 ^ (K - b.n) : ℕ) : ℝ) := by push_cast; ring
  obtain ⟨xj, hj1, hj2, hj3, hj4, -, -⟩ := exists_ringClamp hP a1 (by rw [← e1]; exact a2)
  obtain ⟨xk, hk1, hk2, hk3, hk4, -, -⟩ := exists_ringClamp hP a3 (by rw [← e2]; exact a4)
  have hbj := b.hj; have hbk := b.hk
  have hpow : 2 ^ b.n * 2 ^ (K - b.n) = 2 ^ K := by rw [← pow_add]; congr 1; omega
  have hlt : ∀ i x : ℕ, i < 2 ^ b.n → x + 1 ≤ i * 2 ^ (K - b.n) + 2 ^ (K - b.n) → x < 2 ^ K :=
    fun i x hi hx => by
      have : (i + 1) * 2 ^ (K - b.n) ≤ 2 ^ b.n * 2 ^ (K - b.n) :=
        Nat.mul_le_mul_right _ hi
      rw [hpow] at this; nlinarith
  refine ⟨⟨K, xj, xk, hlt b.j xj hbj hj2, hlt b.k xk hbk hk2⟩, rfl, ?_, ?_⟩
  · refine bx_sub_closedBox rfl hb ?_ ?_ ?_ ?_ <;> push_cast <;> push_cast at hj1 hj2 hk1 hk2 <;>
      [exact_mod_cast hj1; (have := hj2; push_cast at this ⊢; linarith);
       exact_mod_cast hk1; (have := hk2; push_cast at this ⊢; linarith)]
  · rw [bx_mem_closedBox (le_refl K)]
    simp only [Nat.sub_self, pow_zero, mul_one]
    push_cast
    exact ⟨hj3, hj4, hk3, hk4⟩

/-- **Length of the replacing segment** (DZZ l. 1457): a loop-free list of cells of side
`≥ 2^{-k} s_𝖢` whose closures meet `𝖢_large` has at most `32 · 4^k` elements. -/
theorem length_le_of_near {C : DyBox} {k : ℕ} {R : List DyBox} (hnd : R.Nodup)
    (hcell : ∀ c ∈ R, IsCell m δ c) (hside : ∀ c ∈ R, (2 : ℝ)⁻¹ ^ k * C.side ≤ c.side)
    (hmeet : ∀ c ∈ R, (c.closedBox ∩ C.largeBox).Nonempty) : R.length ≤ 32 * 4 ^ k := by
  set K := C.n + k
  have hlev : ∀ c ∈ R, c.n ≤ K := by
    intro c hc
    have h := hside c hc
    have e : (2 : ℝ)⁻¹ ^ k * C.side = (2 : ℝ)⁻¹ ^ K := by
      unfold DyBox.side; rw [← pow_add, add_comm]
    rw [e] at h; unfold DyBox.side at h
    by_contra hcon
    have : (2 : ℝ)⁻¹ ^ c.n < (2 : ℝ)⁻¹ ^ K :=
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith
  have hsq : ∀ c ∈ R, ∃ q : DyBox, q.n = K ∧ q.closedBox ⊆ c.closedBox ∧
      (q.closedBox ∩ C.largeBox).Nonempty := by
    intro c hc
    obtain ⟨z, hzc, hzL⟩ := hmeet c hc
    obtain ⟨q, hq, hqc, hzq⟩ := exists_sq_of_mem_closedBox (hlev c hc) hzc
    exact ⟨q, hq, hqc, z, hzq, hzL⟩
  choose! Q hQn hQc hQL using hsq
  set P : ℕ := 2 ^ k
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  set g : DyBox → ℤ × ℤ := fun c => ((Q c).j - C.j * P, (Q c).k - C.k * P)
  have hCside : C.side * 2 ^ K = P := by
    rw [bx_side_mul (show C.n ≤ K by omega)]; simp [K, P]
  have hcen_re : C.center.re * 2 ^ K = (C.j + 1 / 2) * P := by
    simp only [DyBox.center]; rw [mul_assoc, hCside]
  have hcen_im : C.center.im * 2 ^ K = (C.k + 1 / 2) * P := by
    simp only [DyBox.center]; rw [mul_assoc, hCside]
  have hrange : ∀ c ∈ R, g c ∈ (Finset.Icc (-(P : ℤ)) (2 * P)) ×ˢ (Finset.Icc (-(P : ℤ)) (2 * P)) := by
    intro c hc
    obtain ⟨z, hzq, hzL⟩ := hQL c hc
    have hz := (bx_mem_closedBox (b := Q c) (N := K) (hQn c hc).le).1 hzq
    rw [hQn c hc] at hz
    simp only [Nat.sub_self, pow_zero, mul_one] at hz
    push_cast at hz
    obtain ⟨a1, a2, a3, a4⟩ := hz
    simp only [DyBox.largeBox, mem_ofPred_eq, abs_le] at hzL
    obtain ⟨⟨b1, b2⟩, b3, b4⟩ := hzL
    have hp : (0 : ℝ) < 2 ^ K := by positivity
    have c1 : (z.re - C.center.re) * 2 ^ K ≤ C.side * 2 ^ K := mul_le_mul_of_nonneg_right b2 hp.le
    have c2 : -C.side * 2 ^ K ≤ (z.re - C.center.re) * 2 ^ K := mul_le_mul_of_nonneg_right b1 hp.le
    have c3 : (z.im - C.center.im) * 2 ^ K ≤ C.side * 2 ^ K := mul_le_mul_of_nonneg_right b4 hp.le
    have c4 : -C.side * 2 ^ K ≤ (z.im - C.center.im) * 2 ^ K := mul_le_mul_of_nonneg_right b3 hp.le
    have r1 : z.re * 2 ^ K ≤ (C.j + 1 / 2) * P + P := by linarith
    have r2 : (C.j + 1 / 2) * P - P ≤ z.re * 2 ^ K := by linarith
    have r3 : z.im * 2 ^ K ≤ (C.k + 1 / 2) * P + P := by linarith
    have r4 : (C.k + 1 / 2) * P - P ≤ z.im * 2 ^ K := by linarith
    have hP1' : (1 : ℝ) ≤ P := by exact_mod_cast hP1
    simp only [g, Finset.mem_product, Finset.mem_Icc]
    have d1 : (((Q c).j : ℤ) - C.j * P : ℤ) > -(P : ℤ) - 1 := by
      have : (((Q c).j : ℝ) - C.j * P) > -(P : ℝ) - 1 := by nlinarith
      exact_mod_cast this
    have d2 : (((Q c).j : ℤ) - C.j * P : ℤ) < 2 * P + 1 := by
      have : (((Q c).j : ℝ) - C.j * P) < 2 * P + 1 := by nlinarith
      exact_mod_cast this
    have d3 : (((Q c).k : ℤ) - C.k * P : ℤ) > -(P : ℤ) - 1 := by
      have : (((Q c).k : ℝ) - C.k * P) > -(P : ℝ) - 1 := by nlinarith
      exact_mod_cast this
    have d4 : (((Q c).k : ℤ) - C.k * P : ℤ) < 2 * P + 1 := by
      have : (((Q c).k : ℝ) - C.k * P) < 2 * P + 1 := by nlinarith
      exact_mod_cast this
    omega
  have hinj : Set.InjOn g {c | c ∈ R} := by
    intro c hc c' hc' e
    simp only [g, Prod.mk.injEq] at e
    have ej : (Q c).j = (Q c').j := by omega
    have ek : (Q c).k = (Q c').k := by omega
    have eq : Q c = Q c' := DyBox.ext (by rw [hQn c hc, hQn c' hc']) ej ek
    have n1 := hlev c hc; have n2 := hlev c' hc'
    have hq := hQn c hc
    exact isSqCell_unique ⟨hcell c hc, by omega, anc_eq_of_sub hq n1 (hQc c hc)⟩
      ⟨hcell c' hc', by omega, anc_eq_of_sub hq n2 (eq ▸ hQc c' hc')⟩
  have hcard : R.toFinset.card ≤ ((Finset.Icc (-(P : ℤ)) (2 * P)) ×ˢ
      (Finset.Icc (-(P : ℤ)) (2 * P))).card :=
    Finset.card_le_card_of_injOn g (fun c hc => hrange c (List.mem_toFinset.1 hc))
      (fun c hc c' hc' e => hinj (List.mem_toFinset.1 hc) (List.mem_toFinset.1 hc') e)
  rw [List.toFinset_card_of_nodup hnd, Finset.card_product, Int.card_Icc] at hcard
  have e4 : (4 : ℕ) ^ k = P * P := by simp only [P]; rw [← mul_pow]; norm_num
  have : (2 * (P : ℤ) + 1 - -(P : ℤ)).toNat = 3 * P + 1 := by omega
  rw [this] at hcard
  rw [e4]; nlinarith

end DZZ
end LQGMetric
