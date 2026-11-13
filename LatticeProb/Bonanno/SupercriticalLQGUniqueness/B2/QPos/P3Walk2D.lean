/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3Walk2D at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3Block1D
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBox

 








set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P3

 

def stepVec : Bool × Bool → ℤ × ℤ
  | (true, true) => (1, 0)
  | (false, false) => (-1, 0)
  | (true, false) => (0, 1)
  | (false, true) => (0, -1)

theorem stepVec_add (s : Bool × Bool) : (stepVec s).1 + (stepVec s).2 = sgn s.1 := by
  rcases s with ⟨_ | _, _ | _⟩ <;> rfl

theorem stepVec_sub (s : Bool × Bool) : (stepVec s).1 - (stepVec s).2 = sgn s.2 := by
  rcases s with ⟨_ | _, _ | _⟩ <;> rfl

theorem latticeAdjacent_add_stepVec (z : ℤ × ℤ) (s : Bool × Bool) :
    latticeAdjacent z (z + stepVec s) := by
  rcases s with ⟨_ | _, _ | _⟩ <;> simp [latticeAdjacent, stepVec] <;> ring

theorem stepVec_surj (d : ℤ × ℤ) (hd : latticeAdjacent (0, 0) d) :
    ∃ s : Bool × Bool, stepVec s = d := by
  rcases d with ⟨a, b⟩
  rcases hd with h | h | h | h <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h
  · exact ⟨(true, true), rfl⟩
  · exact ⟨(false, false), rfl⟩
  · exact ⟨(true, false), rfl⟩
  · exact ⟨(false, true), rfl⟩

theorem stepVec_injective : Function.Injective stepVec := by
  intro s s' h
  rcases s with ⟨_ | _, _ | _⟩ <;> rcases s' with ⟨_ | _, _ | _⟩ <;> simp_all [stepVec]

 
def wpos {N : ℕ} (z : ℤ × ℤ) (ω : Fin N → Bool × Bool) (k : ℕ) : ℤ × ℤ :=
  z + ∑ i ∈ range k, stepVec (ext ω i)

@[simp] theorem wpos_zero {N : ℕ} (z : ℤ × ℤ) (ω : Fin N → Bool × Bool) : wpos z ω 0 = z := by
  simp [wpos]

theorem wpos_succ {N : ℕ} (z : ℤ × ℤ) (ω : Fin N → Bool × Bool) (k : ℕ) :
    wpos z ω (k + 1) = wpos z ω k + stepVec (ext ω k) := by
  simp [wpos, sum_range_succ, add_assoc]

theorem wpos_adj {N : ℕ} (z : ℤ × ℤ) (ω : Fin N → Bool × Bool) (k : ℕ) :
    latticeAdjacent (wpos z ω k) (wpos z ω (k + 1)) := by
  rw [wpos_succ]; exact latticeAdjacent_add_stepVec _ _

theorem wpos_cons_succ {N : ℕ} (z : ℤ × ℤ) (s : Bool × Bool) (ω : Fin N → Bool × Bool) (k : ℕ) :
    wpos z (Fin.cons s ω : Fin (N + 1) → Bool × Bool) (k + 1) = wpos (z + stepVec s) ω k := by
  unfold wpos
  rw [sum_range_succ']
  simp only [ext_cons_succ, ext_cons_zero]
  abel

theorem ext_fst {N : ℕ} (ω : Fin N → Bool × Bool) (i : ℕ) :
    ext (fun l => (ω l).1) i = (ext ω i).1 := by
  unfold ext; split_ifs <;> rfl

theorem ext_snd {N : ℕ} (ω : Fin N → Bool × Bool) (i : ℕ) :
    ext (fun l => (ω l).2) i = (ext ω i).2 := by
  unfold ext; split_ifs <;> rfl

 
theorem wpos_add {N : ℕ} (z : ℤ × ℤ) (ω : Fin N → Bool × Bool) (k : ℕ) :
    (wpos z ω k).1 + (wpos z ω k).2 = z.1 + z.2 + psum (fun l => (ω l).1) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [wpos_succ, psum_succ, ext_fst]
    have := stepVec_add (ext ω k)
    simp only [Prod.fst_add, Prod.snd_add]
    linarith

 
theorem wpos_sub {N : ℕ} (z : ℤ × ℤ) (ω : Fin N → Bool × Bool) (k : ℕ) :
    (wpos z ω k).1 - (wpos z ω k).2 = z.1 - z.2 + psum (fun l => (ω l).2) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [wpos_succ, psum_succ, ext_snd]
    have := stepVec_sub (ext ω k)
    simp only [Prod.fst_add, Prod.snd_add]
    linarith

 
theorem card_filter_fst_snd (N : ℕ) (P Q : (Fin N → Bool) → Prop) [DecidablePred P]
    [DecidablePred Q] :
    ((univ.filter fun ω : Fin N → Bool × Bool =>
        P (fun l => (ω l).1) ∧ Q (fun l => (ω l).2)).card : ℝ) =
      ((univ.filter P).card : ℝ) * ((univ.filter Q).card : ℝ) := by
  classical
  let e := Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bool) (fun _ => Bool)
  have h1 : (univ.filter fun ω : Fin N → Bool × Bool =>
        P (fun l => (ω l).1) ∧ Q (fun l => (ω l).2)).card =
      (univ.filter fun p : (Fin N → Bool) × (Fin N → Bool) => P p.1 ∧ Q p.2).card := by
    rw [card_eq_sum_ones, sum_filter, card_eq_sum_ones, sum_filter]
    exact Fintype.sum_equiv e _ _ (fun ω => rfl)
  have h2 : (univ.filter fun p : (Fin N → Bool) × (Fin N → Bool) => P p.1 ∧ Q p.2) =
      (univ.filter P) ×ˢ (univ.filter Q) := by
    ext p; simp
  rw [h1, h2, card_product]
  push_cast; ring

def TubeGood (j t : ℕ) (P : ℕ → ℤ × ℤ) (z : ℤ × ℤ) (M : ℕ)
    (ω : Fin (t * M) → Bool × Bool) : Prop :=
  ∀ i < M, (∀ k ≤ t, |(wpos z ω (t * i + k)).1 - (P i).1| ≤ 129 * j ∧
      |(wpos z ω (t * i + k)).2 - (P i).2| ≤ 129 * j) ∧
    |(wpos z ω (t * (i + 1))).1 - (P (i + 1)).1| ≤ j ∧
    |(wpos z ω (t * (i + 1))).2 - (P (i + 1)).2| ≤ j

theorem tubeGood_of_blockGood (j t : ℕ) (P : ℕ → ℤ × ℤ) (z : ℤ × ℤ) (M : ℕ)
    (hz : |(z.1 + z.2) - ((P 0).1 + (P 0).2)| ≤ j ∧ |(z.1 - z.2) - ((P 0).1 - (P 0).2)| ≤ j)
    (ω : Fin (t * M) → Bool × Bool)
    (hU : BlockGood j t (fun i => (P i).1 + (P i).2) (z.1 + z.2) M (fun l => (ω l).1))
    (hV : BlockGood j t (fun i => (P i).1 - (P i).2) (z.1 - z.2) M (fun l => (ω l).2)) :
    TubeGood j t P z M ω := by
  intro i hi
  
  have hstart : |(z.1 + z.2) + psum (fun l => (ω l).1) (t * i) - ((P i).1 + (P i).2)| ≤ j ∧
      |(z.1 - z.2) + psum (fun l => (ω l).2) (t * i) - ((P i).1 - (P i).2)| ≤ j := by
    rcases i with _ | i
    · simpa using hz
    · exact ⟨(hU i (by omega)).1, (hV i (by omega)).1⟩
  obtain ⟨hU1, hU2⟩ := hU i hi
  obtain ⟨hV1, hV2⟩ := hV i hi
  beta_reduce at hU1 hV1 hstart
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have hu := wpos_add z ω (t * i + k)
    have hv := wpos_sub z ω (t * i + k)
    have hu2 := hU2 k hk
    have hv2 := hV2 k hk
    obtain ⟨hs1, hs2⟩ := hstart
    rw [abs_le] at hs1 hs2 ⊢
    rw [abs_lt] at hu2 hv2
    rw [abs_le]
    constructor <;> constructor <;> omega
  · have hu := wpos_add z ω (t * (i + 1))
    rw [abs_le] at hU1 hV1 ⊢
    have hv := wpos_sub z ω (t * (i + 1))
    constructor <;> omega
  · have hu := wpos_add z ω (t * (i + 1))
    rw [abs_le] at hU1 hV1 ⊢
    have hv := wpos_sub z ω (t * (i + 1))
    constructor <;> omega

open Classical in
 

theorem tube2D (j : ℕ) (hj : 0 < j) (P : ℕ → ℤ × ℤ) (M : ℕ)
    (hP : ∀ i < M, |((P (i + 1)).1 + (P (i + 1)).2) - ((P i).1 + (P i).2)| ≤ j ∧
      |((P (i + 1)).1 - (P (i + 1)).2) - ((P i).1 - (P i).2)| ≤ j)
    (z : ℤ × ℤ)
    (hz : |(z.1 + z.2) - ((P 0).1 + (P 0).2)| ≤ j ∧ |(z.1 - z.2) - ((P 0).1 - (P 0).2)| ≤ j) :
    ((1 / 16384 : ℝ) * 4 ^ (64 * j ^ 2)) ^ M ≤
      ((univ.filter fun ω : Fin (64 * j ^ 2 * M) → Bool × Bool =>
        TubeGood j (64 * j ^ 2) P z M ω).card : ℝ) := by
  set t := 64 * j ^ 2 with ht
  have hU := multiBlock j hj (fun i => (P i).1 + (P i).2) M (fun i hi => (hP i hi).1)
    (z.1 + z.2) hz.1
  have hV := multiBlock j hj (fun i => (P i).1 - (P i).2) M (fun i hi => (hP i hi).2)
    (z.1 - z.2) hz.2
  have hprod := card_filter_fst_snd (t * M)
    (fun σ => BlockGood j t (fun i => (P i).1 + (P i).2) (z.1 + z.2) M σ)
    (fun σ => BlockGood j t (fun i => (P i).1 - (P i).2) (z.1 - z.2) M σ)
  have hsub : ((univ.filter fun ω : Fin (t * M) → Bool × Bool =>
        BlockGood j t (fun i => (P i).1 + (P i).2) (z.1 + z.2) M (fun l => (ω l).1) ∧
        BlockGood j t (fun i => (P i).1 - (P i).2) (z.1 - z.2) M (fun l => (ω l).2)).card : ℝ) ≤
      ((univ.filter fun ω : Fin (t * M) → Bool × Bool => TubeGood j t P z M ω).card : ℝ) := by
    exact_mod_cast card_le_card (by
      intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω ⊢
      exact tubeGood_of_blockGood j t P z M hz ω hω.1 hω.2)
  have h4 : (4 : ℝ) ^ t = 2 ^ t * 2 ^ t := by
    rw [← mul_pow]; norm_num
  calc ((1 / 16384 : ℝ) * 4 ^ t) ^ M
      = ((1 / 128 : ℝ) * 2 ^ t) ^ M * ((1 / 128 : ℝ) * 2 ^ t) ^ M := by
        rw [← mul_pow, h4]; ring_nf
    _ ≤ _ * _ := mul_le_mul hU hV (by positivity) (by positivity)
    _ = _ := hprod.symm
    _ ≤ _ := hsub

end SupercriticalLQGUniqueness.B2.QPos.P3
