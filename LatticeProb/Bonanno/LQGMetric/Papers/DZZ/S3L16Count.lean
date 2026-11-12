/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L16Count at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L16Var

/-!
# DZZ Lemma 3.16: union bound over `𝓑(B, 2^{-k})` (P2-DZZ312)

`𝓑(B, 2^{-k})` (the `4^{k+1}` level-`(n_B + k)` boxes in `B_large`) and the union bound over it
(own elementary count, used in (eq-for-B'-good), DZZ l. 1408–1412).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- One coordinate: the column `j'` of a box of `𝓑(B, 2^{-k})` satisfies
`j 2^k ≤ j' + 2^{k-1} < j 2^k + 2^{k+1}`. -/
lemma boxColl_coord {n k j j' : ℕ} (hk : 1 ≤ k)
    (h1 : |(j' : ℝ) * (2 : ℝ)⁻¹ ^ (n + k) - (j + 1 / 2) * (2 : ℝ)⁻¹ ^ n| ≤ (2 : ℝ)⁻¹ ^ n)
    (h2 : |((j' : ℝ) + 1) * (2 : ℝ)⁻¹ ^ (n + k) - (j + 1 / 2) * (2 : ℝ)⁻¹ ^ n| ≤ (2 : ℝ)⁻¹ ^ n) :
    j * 2 ^ k ≤ j' + 2 ^ (k - 1) ∧ j' + 2 ^ (k - 1) < j * 2 ^ k + 2 ^ (k + 1) := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set h := (2 : ℝ)⁻¹ ^ (n + (K + 1)) with hh
  have hpos : 0 < h := by positivity
  have hs : (2 : ℝ)⁻¹ ^ n = 2 * 2 ^ K * h := by
    rw [hh, pow_add, pow_succ]
    field_simp
    rw [← mul_pow]; norm_num
  rw [hs] at h1 h2
  have a1 := (abs_le.mp h1).1
  have a2 := (abs_le.mp h2).2
  have hK : (0 : ℝ) < 2 ^ K := by positivity
  have r1 : ((j * 2 ^ (K + 1) : ℕ) : ℝ) ≤ ((j' + 2 ^ K : ℕ) : ℝ) := by
    push_cast
    have : ((j : ℝ) * (2 * 2 ^ K) - 2 ^ K) * h ≤ j' * h := by nlinarith
    have := le_of_mul_le_mul_right this hpos
    rw [pow_succ]; nlinarith
  have r2 : ((j' + 2 ^ K : ℕ) : ℝ) + 1 ≤ ((j * 2 ^ (K + 1) + 2 ^ (K + 1 + 1) : ℕ) : ℝ) := by
    push_cast
    have : ((j' : ℝ) + 1) * h ≤ ((j : ℝ) * (2 * 2 ^ K) + 3 * 2 ^ K) * h := by nlinarith
    have := le_of_mul_le_mul_right this hpos
    have e1 : (2 : ℝ) ^ (K + 1) = 2 * 2 ^ K := by ring
    have e2 : (2 : ℝ) ^ (K + 1 + 1) = 4 * 2 ^ K := by ring
    rw [e1, e2]; nlinarith
  constructor
  · exact_mod_cast r1
  · have : j' + 2 ^ K + 1 ≤ j * 2 ^ (K + 1) + 2 ^ (K + 1 + 1) := by exact_mod_cast r2
    omega

/-- Union bound over `𝓑(B, 2^{-k})`: at most `(2^{k+1})²` boxes. -/
lemma measureReal_boxColl_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (b : DyBox) {k : ℕ} (hk : 1 ≤ k) (S : DyBox → Set Ω) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ b' ∈ boxColl b k, P.real (S b') ≤ B) :
    P.real {ω | ∃ b' ∈ boxColl b k, ω ∈ S b'} ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * B := by
  classical
  set T : Fin (2 ^ (k + 1)) → Fin (2 ^ (k + 1)) → Set Ω := fun d e =>
    {ω | ∃ b' ∈ boxColl b k, b'.j + 2 ^ (k - 1) = b.j * 2 ^ k + d ∧
      b'.k + 2 ^ (k - 1) = b.k * 2 ^ k + e ∧ ω ∈ S b'}
  have hsub : {ω | ∃ b' ∈ boxColl b k, ω ∈ S b'} ⊆ ⋃ d, ⋃ e, T d e := by
    rintro ω ⟨b', hb', hω⟩
    have hn := hb'.1
    have hz1 : (⟨b'.j * b'.side, b'.k * b'.side⟩ : ℂ) ∈ b'.closedBox := by
      have := b'.side_pos'
      simp only [DyBox.closedBox, mem_ofPred_eq]; refine ⟨le_rfl, ?_, le_rfl, ?_⟩ <;> nlinarith
    have hz2 : (⟨(b'.j + 1) * b'.side, (b'.k + 1) * b'.side⟩ : ℂ) ∈ b'.closedBox := by
      have := b'.side_pos'
      simp only [DyBox.closedBox, mem_ofPred_eq]; refine ⟨?_, le_rfl, ?_, le_rfl⟩ <;> nlinarith
    have m1 := hb'.2 hz1
    have m2 := hb'.2 hz2
    simp only [DyBox.largeBox, DyBox.center, DyBox.side, hn, mem_ofPred_eq] at m1 m2
    obtain ⟨cj1, cj2⟩ := boxColl_coord (n := b.n) hk m1.1 m2.1
    obtain ⟨ck1, ck2⟩ := boxColl_coord (n := b.n) hk m1.2 m2.2
    refine mem_iUnion.2 ⟨⟨b'.j + 2 ^ (k - 1) - b.j * 2 ^ k, by omega⟩,
      mem_iUnion.2 ⟨⟨b'.k + 2 ^ (k - 1) - b.k * 2 ^ k, by omega⟩, b', hb', ?_, ?_, hω⟩⟩
    · simp only; omega
    · simp only; omega
  have hT : ∀ d e, P.real (T d e) ≤ B := by
    intro d e
    by_cases hne : (T d e).Nonempty
    · obtain ⟨ω₀, b₀, hb₀, hb₀j, hb₀k, -⟩ := hne
      have : T d e ⊆ S b₀ := by
        rintro ω ⟨b', hb', hbj, hbk, hω⟩
        have : b' = b₀ := DyBox.ext (hb'.1.trans hb₀.1.symm) (by omega) (by omega)
        rwa [← this]
      exact (measureReal_mono this).trans (hB b₀ hb₀)
    · rw [not_nonempty_iff_eq_empty.mp hne, measureReal_empty]; exact hB0
  refine (measureReal_mono hsub).trans ?_
  refine (measureReal_iUnion_fintype_le _).trans ?_
  calc ∑ d, P.real (⋃ e, T d e) ≤ ∑ _d : Fin (2 ^ (k + 1)), (2 : ℝ) ^ (k + 1) * B := by
        refine Finset.sum_le_sum fun d _ => (measureReal_iUnion_fintype_le _).trans ?_
        calc ∑ e, P.real (T d e) ≤ ∑ _e : Fin (2 ^ (k + 1)), B :=
              Finset.sum_le_sum fun e _ => hT d e
          _ = (2 : ℝ) ^ (k + 1) * B := by simp
    _ = ((2 : ℝ) ^ (k + 1)) ^ 2 * B := by simp; ring

end DZZ
end LQGMetric
