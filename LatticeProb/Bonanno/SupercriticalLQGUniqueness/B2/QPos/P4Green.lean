/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4Green at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4WalkOps

 














set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P4

open P3

 
def pt (U : Finset (ℤ × ℤ)) (b c : ℤ × ℤ) : ℝ := if c = b ∧ b ∈ U then 1 else 0

theorem pt_nonneg (U : Finset (ℤ × ℤ)) (b c : ℤ × ℤ) : 0 ≤ pt U b c := by
  unfold pt; split_ifs <;> norm_num

theorem pt_le_ind (U : Finset (ℤ × ℤ)) (b c : ℤ × ℤ) : pt U b c ≤ ind U c := by
  unfold pt ind
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.1 ▸ h1.2) h2
  · norm_num
  · exact le_rfl

theorem pt_of_not_mem {U : Finset (ℤ × ℤ)} {b c : ℤ × ℤ} (hc : c ∉ U) : pt U b c = 0 := by
  unfold pt
  rw [if_neg]
  rintro ⟨rfl, h⟩
  exact hc h

 
theorem exists_strip (U : Finset (ℤ × ℤ)) : ∃ R : ℤ, ∀ c ∈ U, |c.1 - 0| < R := by
  refine ⟨(U.sup fun c => c.1.natAbs : ℕ) + 1, fun c hc => ?_⟩
  have h : c.1.natAbs ≤ U.sup fun c => c.1.natAbs :=
    Finset.le_sup (f := fun c : ℤ × ℤ => c.1.natAbs) hc
  rw [sub_zero, Int.abs_eq_natAbs]
  omega

theorem summable_alive (U : Finset (ℤ × ℤ)) (a : ℤ × ℤ) :
    Summable (fun t => alive U t a) := by
  obtain ⟨R, hR⟩ := exists_strip U
  exact summable_of_sum_range_le (fun t => alive_nonneg U t a)
    (fun t => sum_alive_le U 0 R hR t a)

theorem killIter_pt_le (U : Finset (ℤ × ℤ)) (t : ℕ) (b a : ℤ × ℤ) :
    (killOp U)^[t] (pt U b) a ≤ alive U t a :=
  killIter_mono U t (pt_le_ind U b) a

theorem killIter_pt_nonneg (U : Finset (ℤ × ℤ)) (t : ℕ) (b a : ℤ × ℤ) :
    0 ≤ (killOp U)^[t] (pt U b) a :=
  killIter_nonneg U t (pt_nonneg U b) a

theorem summable_killIter_pt (U : Finset (ℤ × ℤ)) (b a : ℤ × ℤ) :
    Summable (fun t => (killOp U)^[t] (pt U b) a) :=
  Summable.of_nonneg_of_le (fun t => killIter_pt_nonneg U t b a)
    (fun t => killIter_pt_le U t b a) (summable_alive U a)

theorem killIter_pt_of_not_mem (U : Finset (ℤ × ℤ)) (t : ℕ) (b : ℤ × ℤ) {c : ℤ × ℤ}
    (hc : c ∉ U) : (killOp U)^[t] (pt U b) c = 0 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact pt_of_not_mem hc
  · exact killIter_out U t _ hc ht

 
def green (U : Finset (ℤ × ℤ)) (a b : ℤ × ℤ) : ℝ :=
  ∑' t, (killOp U)^[t] (pt U b) a

theorem green_nonneg (U : Finset (ℤ × ℤ)) (a b : ℤ × ℤ) : 0 ≤ green U a b :=
  tsum_nonneg fun t => killIter_pt_nonneg U t b a

theorem green_of_not_mem_left {U : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (ha : a ∉ U)
    (b : ℤ × ℤ) : green U a b = 0 := by
  unfold green
  simp [killIter_pt_of_not_mem U _ b ha]

theorem green_of_not_mem_right {U : Finset (ℤ × ℤ)} (a : ℤ × ℤ) {b : ℤ × ℤ}
    (hb : b ∉ U) : green U a b = 0 := by
  have hpt : pt U b = fun _ => 0 := by
    funext c
    unfold pt
    rw [if_neg]
    rintro ⟨_, h⟩
    exact hb h
  have h0 : ∀ t, (killOp U)^[t] (fun _ : ℤ × ℤ => (0 : ℝ)) a = 0 := by
    intro t
    have := killIter_smul U t 0 (fun _ => (0 : ℝ)) a
    simpa using this
  unfold green
  rw [hpt]
  simp [h0]

 
theorem killOp_eq_avg {U : Finset (ℤ × ℤ)} {f : ℤ × ℤ → ℝ} (hf : ∀ c, c ∉ U → f c = 0)
    {a : ℤ × ℤ} (ha : a ∈ U) : killOp U f a = avg f a := by
  rw [killOp_of_mem ha]
  congr 1
  funext c
  split_ifs with hc
  · rfl
  · exact (hf c hc).symm

 
theorem green_eq {U : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (ha : a ∈ U) (b : ℤ × ℤ) :
    green U a b = pt U b a + avg (fun c => green U c b) a := by
  unfold green
  rw [(summable_killIter_pt U b a).tsum_eq_zero_add]
  congr 1
  have hstep : ∀ t, (killOp U)^[t + 1] (pt U b) a = avg ((killOp U)^[t] (pt U b)) a := by
    intro t
    rw [Function.iterate_succ_apply']
    exact killOp_eq_avg (fun c hc => killIter_pt_of_not_mem U t b hc) ha
  simp_rw [hstep]
  unfold avg
  rw [tsum_div_const]
  congr 1
  rw [Summable.tsum_finsetSum (fun s _ => summable_killIter_pt U b _)]

 

 
def shiftSet (U : Finset (ℤ × ℤ)) (z : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  U.map ⟨fun c => c + z, add_left_injective z⟩

theorem mem_shiftSet {U : Finset (ℤ × ℤ)} {z c : ℤ × ℤ} :
    c ∈ shiftSet U z ↔ c - z ∈ U := by
  unfold shiftSet
  simp only [mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa using hd
  · intro h
    exact ⟨c - z, h, by abel⟩

theorem avg_shift (f : ℤ × ℤ → ℝ) (z c : ℤ × ℤ) :
    avg (fun d => f (d - z)) c = avg f (c - z) := by
  unfold avg
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  abel

theorem killIter_shift (U : Finset (ℤ × ℤ)) (z : ℤ × ℤ) (t : ℕ) (f : ℤ × ℤ → ℝ) (c : ℤ × ℤ) :
    (killOp (shiftSet U z))^[t] (fun d => f (d - z)) c = (killOp U)^[t] f (c - z) := by
  induction t generalizing f c with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hK : killOp (shiftSet U z) (fun d => f (d - z)) = fun d => killOp U f (d - z) := by
      funext d
      by_cases hd : d - z ∈ U
      · have hd' : d ∈ shiftSet U z := mem_shiftSet.mpr hd
        rw [killOp_of_mem hd', killOp_of_mem hd]
        rw [← avg_shift]
        congr 1
        funext e
        by_cases he : e - z ∈ U
        · rw [if_pos (mem_shiftSet.mpr he), if_pos he]
        · rw [if_neg (fun h => he (mem_shiftSet.mp h)), if_neg he]
      · have hd' : d ∉ shiftSet U z := fun h => hd (mem_shiftSet.mp h)
        rw [killOp_of_not_mem hd', killOp_of_not_mem hd]
    rw [hK]
    exact ih _ c

theorem pt_shift (U : Finset (ℤ × ℤ)) (z b : ℤ × ℤ) :
    pt (shiftSet U z) (b + z) = fun d => pt U b (d - z) := by
  funext d
  unfold pt
  have h1 : (d = b + z) ↔ (d - z = b) := by
    constructor
    · rintro rfl; abel
    · intro h; rw [← h]; abel
  have h2 : (b + z ∈ shiftSet U z) ↔ (b ∈ U) := by
    rw [mem_shiftSet]; simp
  simp only [h1, h2]

 
theorem green_shift (U : Finset (ℤ × ℤ)) (z a b : ℤ × ℤ) :
    green (shiftSet U z) (a + z) (b + z) = green U a b := by
  unfold green
  congr 1
  funext t
  rw [pt_shift, killIter_shift]
  simp

 

theorem latticeAdjacent_sub {a c : ℤ × ℤ} (h : latticeAdjacent a c) :
    latticeAdjacent (0, 0) (c - a) := by
  rcases a with ⟨a1, a2⟩
  rcases c with ⟨c1, c2⟩
  simp only [latticeAdjacent, Prod.mk_sub_mk] at h ⊢
  omega

open Classical in
 
theorem sum_adj_eq (U : Finset (ℤ × ℤ)) (a : ℤ × ℤ) (g : ℤ × ℤ → ℝ)
    (hg : ∀ c, c ∉ U → g c = 0) :
    ∑ c ∈ U, (if latticeAdjacent a c then g c else 0) =
      ∑ s : Bool × Bool, g (a + stepVec s) := by
  classical
  rw [← Finset.sum_filter]
  have himg : ∑ s : Bool × Bool, g (a + stepVec s) =
      ∑ c ∈ (Finset.univ.image fun s : Bool × Bool => a + stepVec s), g c := by
    rw [Finset.sum_image]
    intro s _ s' _ h
    exact stepVec_injective (add_left_cancel h)
  rw [himg]
  apply Finset.sum_subset_zero_on_sdiff
  · intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨s, hs⟩ := stepVec_surj (c - a) (latticeAdjacent_sub hc.2)
    rw [Finset.mem_image]
    exact ⟨s, Finset.mem_univ _, by rw [hs]; abel⟩
  · intro c hc
    rw [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter] at hc
    obtain ⟨⟨s, _, rfl⟩, hn⟩ := hc
    apply hg
    intro hU
    exact hn ⟨hU, latticeAdjacent_add_stepVec a s⟩
  · intro c _
    rfl

 
def incr (U : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) : ℝ :=
  green U x x + green U y y - green U x y - green U y x

end SupercriticalLQGUniqueness.B2.QPos.P4
