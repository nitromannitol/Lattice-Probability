/-
The multiparameter subadditive ergodic theorem of Akcoglu and Krengel, along cubes: the mean half.

A set function `f` on boxes of `ℤ^d`, stationary under a measure-preserving action `τ` of the
lattice, bounded by a multiple of the volume, and subadditive when a box splits into two boxes,
has a volume-normalised mean that converges along the cubes `[0, n)^d`: `akcoglu_krengel_mean`
proves `(∫ f (latticeCube d n) dμ) / n^d → L` for some `L`. Subadditivity is required only for a
box split into two boxes, which is all that cube partitions use and what the random Abelian
sandpile verifies (its boxes are connected). The one-parameter theorem is
`LatticeProb.Prob.Kingman`, proved there for both halves by Steele's argument; the almost sure
half here needs a multiparameter ergodic theorem the library does not yet have, so only the mean
half is proved.

The route restricts the mean `G k := ∫ f (sideBox k) dμ` of the box `[0, k)` to integer side
vectors `k : Fin d → ℕ`, where it satisfies `0 ≤ G k ≤ C ∏ k i` and the one-coordinate
subadditivity `G (k[i:=a+b]) ≤ G (k[i:=a]) + G (k[i:=b])`, and iterates that bound over each
coordinate in turn to squeeze `G(n·1)/n^d` between `G(m·1)/m^d + d C m / n` for every `1 ≤ m ≤ n`;
a Fekete-type lemma on this bound gives the limit.

The proof was written by the library's proof fleet (deepseek-v4.1-flash and Mistral leanstral)
from a statement-owned decomposition and verified by the library gates.
-/
import LatticeProb.Prob.Kingman
import LatticeProb.Site

open MeasureTheory Filter Topology

namespace LatticeProb

/-- The box `[a, b]` of `ℤ^d`, in the product order. -/
noncomputable def latticeBox {d : ℕ} (a b : Site d) : Finset (Site d) := Finset.Icc a b

/-- The cube `[0, n)^d`. -/
noncomputable def latticeCube (d n : ℕ) : Finset (Site d) := Finset.Icc 0 (fun _ => (n : ℤ) - 1)

/-- `B` is the disjoint union of the boxes `B₁` and `B₂`. -/
def IsBoxSplit {d : ℕ} (B B₁ B₂ : Finset (Site d)) : Prop :=
  (∃ a b, B = latticeBox a b) ∧ (∃ a b, B₁ = latticeBox a b) ∧ (∃ a b, B₂ = latticeBox a b) ∧
    Disjoint B₁ B₂ ∧ B₁ ∪ B₂ = B

variable {Ω : Type*} [MeasurableSpace Ω]

namespace AKMeanAux

/-- The box `[0, k)` with side vector `k`. -/
private noncomputable def sideBox {d : ℕ} (k : Fin d → ℕ) : Finset (Site d) :=
  Finset.Icc 0 (fun i => (k i : ℤ) - 1)

/-! ### Layer B: pure lemmas on an abstract side-function `G` -/

-- induction q with | zero => simp | succ q ih => rewrite (q+1)*m + r = m + (q*m + r) (by ring),
-- apply hsub k i m (q*m+r), then ih; push_cast; linarith.
/-- Iterating one-coordinate subadditivity `q` times bounds `G` at `q*m+r` by `q*G(m) + G(r)`. -/
private theorem update_mul_add_le_mul_update_add {d : ℕ} (G : (Fin d → ℕ) → ℝ)
    (hsub : ∀ k i a b, G (Function.update k i (a + b))
      ≤ G (Function.update k i a) + G (Function.update k i b))
    (k : Fin d → ℕ) (i : Fin d) (q m r : ℕ) :
    G (Function.update k i (q * m + r)) ≤ q * G (Function.update k i m) + G (Function.update k i r)
        := by
  induction q with
  | zero => simp
  | succ n ih =>
      rw [show (n + 1) * m + r = m + (n * m + r) by ring_nf]
      push_cast
      linarith [hsub k i m (n * m + r), ih]


-- Product bound. Finset.prod_update_of_mem (Finset.mem_univ i) splits off the factor r:
-- ∏ l, update v i r l = r * ∏ l ∈ univ \ {i}, v l.  Since S ⊆ univ.erase i (hi),
-- q^|S| * ∏_{l≠i} v l = ∏_{l≠i} (if l ∈ S then q*m else n) (Finset.prod_ite, Finset.prod_const,
-- Finset.filter_mem_eq_inter); each factor ≤ n (hqm), so ≤ n^(d-1) by Finset.prod_le_pow_card
-- (card (univ \ {i}) = d - 1: Finset.card_sdiff, Finset.card_univ, Fintype.card_fin).  -- SPLIT?
/-- A product bound: `q^|S|` times a mixed `m`/`n` product is at most `r * n^(d-1)`. -/
private theorem pow_card_mul_prod_update_le_core {d : ℕ} (S : Finset (Fin d)) (i : Fin d)
    (hi : i ∉ S) (q m n r : ℕ)
    (hqm : q * m ≤ n) :
    (q : ℝ) ^ S.card * ∏ l, ((Function.update (fun l => if l ∈ S then m else n) i r l : ℕ) : ℝ)
      ≤ r * (n : ℝ) ^ (d - 1) := by
  have hcard : (Finset.univ \ ({i} : Finset (Fin d))).card = d - 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_singleton, Finset.card_univ,
      Fintype.card_fin]
  have hprod : ∏ l, ((Function.update (fun l => if l ∈ S then m else n) i r l : ℕ) : ℝ)
      = (r : ℝ) * ∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)),
          (if x ∈ S then (m : ℝ) else (n : ℝ)) := by
    rw [show (∏ l, ((Function.update (fun l => if l ∈ S then m else n) i r l : ℕ) : ℝ))
        = ∏ l, (Function.update (fun l => (if l ∈ S then (m : ℝ) else (n : ℝ))) i (r : ℝ) l)
        from Finset.prod_congr rfl (fun l _ => by
          rcases eq_or_ne l i with h | h
          · subst h; simp
          · rw [Function.update_of_ne h, Function.update_of_ne h]
            by_cases hl : l ∈ S <;> simp [hl])]
    rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  have hq : ∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)), (if x ∈ S then (q : ℝ) else (1 : ℝ))
      = (q : ℝ) ^ S.card := by
    rw [Finset.prod_ite]
    have hf : (Finset.univ \ ({i} : Finset (Fin d))).filter (fun x => x ∈ S) = S := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨-, hxS⟩; exact hxS
      · intro hxS; exact ⟨fun h => hi (h ▸ hxS), hxS⟩
    rw [hf, Finset.prod_const]
    simp
  have hkey : ∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)),
        (if x ∈ S then (q : ℝ) * (m : ℝ) else (n : ℝ))
      = (q : ℝ) ^ S.card * ∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)),
          (if x ∈ S then (m : ℝ) else (n : ℝ)) := by
    have hpt : ∀ x : Fin d, (if x ∈ S then (q : ℝ) * (m : ℝ) else (n : ℝ))
        = (if x ∈ S then (q : ℝ) else (1 : ℝ)) * (if x ∈ S then (m : ℝ) else (n : ℝ)) := by
      intro x
      by_cases hx : x ∈ S <;> simp [hx]
    calc ∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)),
          (if x ∈ S then (q : ℝ) * (m : ℝ) else (n : ℝ))
        = ∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)),
            ((if x ∈ S then (q : ℝ) else (1 : ℝ)) *
              (if x ∈ S then (m : ℝ) else (n : ℝ))) :=
          Finset.prod_congr rfl (fun x _ => hpt x)
      _ = (∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)), (if x ∈ S then (q : ℝ) else (1 : ℝ))) *
            (∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)),
              (if x ∈ S then (m : ℝ) else (n : ℝ))) := Finset.prod_mul_distrib
      _ = (q : ℝ) ^ S.card * ∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)),
            (if x ∈ S then (m : ℝ) else (n : ℝ)) := by rw [hq]
  have hbound : ∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)),
        (if x ∈ S then (q : ℝ) * (m : ℝ) else (n : ℝ)) ≤ (n : ℝ) ^ (d - 1) := by
    calc ∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)),
          (if x ∈ S then (q : ℝ) * (m : ℝ) else (n : ℝ))
        ≤ ∏ _x ∈ (Finset.univ \ {i} : Finset (Fin d)), (n : ℝ) :=
          Finset.prod_le_prod
            (fun x _ => by
              by_cases hx : x ∈ S <;> simp only [hx, if_true, if_false] <;> positivity)
            (fun x _ => by
              by_cases hx : x ∈ S
              · simp only [hx, if_true]
                exact_mod_cast hqm
              · simp [hx])
      _ = (n : ℝ) ^ (d - 1) := by rw [Finset.prod_const, hcard]
  have hmain : (q : ℝ) ^ S.card * ∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)),
      (if x ∈ S then (m : ℝ) else (n : ℝ)) ≤ (n : ℝ) ^ (d - 1) := hkey ▸ hbound
  rw [hprod]
  calc (q : ℝ) ^ S.card * ((r : ℝ) * ∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)),
        (if x ∈ S then (m : ℝ) else (n : ℝ)))
      = (r : ℝ) * ((q : ℝ) ^ S.card * ∏ x ∈ (Finset.univ \ {i} : Finset (Fin d)),
        (if x ∈ S then (m : ℝ) else (n : ℝ))) := by ring
    _ ≤ (r : ℝ) * (n : ℝ) ^ (d - 1) := mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg r)

/-- Restatement of `pow_card_mul_prod_update_le_core`. -/
private theorem pow_card_mul_prod_update_le {d : ℕ} (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S)
    (q m n r : ℕ)
    (hqm : q * m ≤ n) :
    (q : ℝ) ^ S.card * ∏ l, ((Function.update (fun l => if l ∈ S then m else n) i r l : ℕ) : ℝ)
      ≤ r * (n : ℝ) ^ (d - 1) := by
  exact pow_card_mul_prod_update_le_core S i hi q m n r hqm


-- Induction step over the set S of coordinates already shrunk from n = q*m+r to m.
-- v S i = n (hi), so G (v S) = G (update (v S) i (q*m+r)) (Function.update_eq_self); apply
-- update_mul_add_le_mul_update_add; update (v S) i m = v (insert i S) (funext l; by_cases l = i;
-- simp [Finset.mem_insert]);
-- bound G (update (v S) i r) by hC and pow_card_mul_prod_update_le (multiply by q^|S| ≥ 0, C ≥ 0);
-- Finset.card_insert_of_notMem hi, pow_succ; nlinarith / linarith.   -- SPLIT?
/-- The induction step shrinking one more coordinate from `q*m+r` to `m`, at cost
`C*r*(qm+r)^(d-1)`. -/
private theorem pow_card_mul_le_step_add {d : ℕ} (G : (Fin d → ℕ) → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ k, G k ≤ C * ∏ i, (k i : ℝ))
    (hsub : ∀ k i a b, G (Function.update k i (a + b))
      ≤ G (Function.update k i a) + G (Function.update k i b))
    (q m r : ℕ) (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S) :
    (q : ℝ) ^ S.card * G (fun l => if l ∈ S then m else q * m + r) ≤
      (q : ℝ) ^ S.card * (q : ℝ) * G (fun l => if l ∈ insert i S then m else q * m + r)
        + C * (r : ℝ) * ((q : ℝ) * m + r) ^ (d - 1) := by
  classical
  have hupd0 : Function.update (fun l : Fin d => if l ∈ S then m else q * m + r) i (q * m + r)
      = (fun l : Fin d => if l ∈ S then m else q * m + r) := by
    funext l
    by_cases hli : l = i
    · subst hli; simp [hi]
    · simp [hli]
  have hupd1 : Function.update (fun l : Fin d => if l ∈ S then m else q * m + r) i m
      = (fun l : Fin d => if l ∈ insert i S then m else q * m + r) := by
    funext l
    by_cases hli : l = i
    · subst hli; simp
    · have hl : (l ∈ insert i S) = (l ∈ S) := by simp [Finset.mem_insert, hli]
      simp [hli, hl]
  have h1 := update_mul_add_le_mul_update_add G hsub
      (fun l : Fin d => if l ∈ S then m else q * m + r) i q m r
  rw [hupd0, hupd1] at h1
  have hq0 : (0 : ℝ) ≤ (q : ℝ) ^ S.card := by positivity
  have hCu : G (Function.update (fun l : Fin d => if l ∈ S then m else q * m + r) i r)
      ≤ C * ∏ l, ((Function.update (fun l : Fin d => if l ∈ S then m else q * m + r) i r l : ℕ) : ℝ)
          :=
    hC _
  have h2 := pow_card_mul_prod_update_le S i hi q m (q * m + r) r (Nat.le_add_right (q * m) r)
  have hNN : ((q * m + r : ℕ) : ℝ) = (q : ℝ) * m + r := by push_cast; ring
  have hA : (q : ℝ) ^ S.card
        * ((q : ℝ) * G (fun l : Fin d => if l ∈ insert i S then m else q * m + r)
           + G (Function.update (fun l : Fin d => if l ∈ S then m else q * m + r) i r))
      = (q : ℝ) ^ S.card * (q : ℝ)
          * G (fun l : Fin d => if l ∈ insert i S then m else q * m + r)
        + (q : ℝ) ^ S.card
          * G (Function.update (fun l : Fin d => if l ∈ S then m else q * m + r) i r) := by
    ring
  have hA1 : (q : ℝ) ^ S.card * G (fun l : Fin d => if l ∈ S then m else q * m + r)
      ≤ (q : ℝ) ^ S.card * (q : ℝ)
          * G (fun l : Fin d => if l ∈ insert i S then m else q * m + r)
        + (q : ℝ) ^ S.card
          * G (Function.update (fun l : Fin d => if l ∈ S then m else q * m + r) i r) := by
    have h := mul_le_mul_of_nonneg_left h1 hq0
    rw [hA] at h
    exact h
  have hB : (q : ℝ) ^ S.card
        * G (Function.update (fun l : Fin d => if l ∈ S then m else q * m + r) i r)
      ≤ (q : ℝ) ^ S.card
        *
            (C * ∏ l,
            ((Function.update (fun l : Fin d => if l ∈ S then m else q * m + r) i r l : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hCu hq0
  have hB1 : (q : ℝ) ^ S.card
        *
            (C * ∏ l,
            ((Function.update (fun l : Fin d => if l ∈ S then m else q * m + r) i r l : ℕ) : ℝ))
      = C * ((q : ℝ) ^ S.card
        * ∏ l, ((Function.update (fun l : Fin d => if l ∈ S then m else q * m + r) i r l : ℕ) : ℝ))
            := by
    ring
  have hE : C * ((q : ℝ) ^ S.card
        * ∏ l, ((Function.update (fun l : Fin d => if l ∈ S then m else q * m + r) i r l : ℕ) : ℝ))
      ≤ C * ((r : ℝ) * ((q * m + r : ℕ) : ℝ) ^ (d - 1)) :=
    mul_le_mul_of_nonneg_left h2 hC0
  have hE' : C * ((r : ℝ) * ((q * m + r : ℕ) : ℝ) ^ (d - 1))
      = C * (r : ℝ) * ((q : ℝ) * m + r) ^ (d - 1) := by
    rw [hNN]; ring
  have hchain : (q : ℝ) ^ S.card
        * G (Function.update (fun l : Fin d => if l ∈ S then m else q * m + r) i r)
      ≤ C * (r : ℝ) * ((q : ℝ) * m + r) ^ (d - 1) :=
    le_trans hB (le_trans (le_of_eq hB1) (le_trans hE (le_of_eq hE')))
  exact le_trans hA1 (add_le_add le_rfl hchain)

/-- `pow_card_mul_le_step_add`, rewritten with `(insert i S).card`. -/
private theorem pow_card_insert_mul_le_step_add {d : ℕ} (G : (Fin d → ℕ) → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ k, G k ≤ C * ∏ i, (k i : ℝ))
    (hsub : ∀ k i a b, G (Function.update k i (a + b))
      ≤ G (Function.update k i a) + G (Function.update k i b))
    (q m r : ℕ) (S : Finset (Fin d)) (i : Fin d) (hi : i ∉ S) :
    (q : ℝ) ^ S.card * G (fun l => if l ∈ S then m else q * m + r)
      ≤ (q : ℝ) ^ (insert i S).card * G (fun l => if l ∈ insert i S then m else q * m + r)
        + C * r * ((q * m + r : ℕ) : ℝ) ^ (d - 1) := by
  rw [Finset.card_insert_of_notMem hi, pow_succ]; push_cast; exact pow_card_mul_le_step_add G C hC0
      hC hsub q m r S i hi


-- Finset.induction_on S: empty: simp (v ∅ = fun _ => n, card 0); insert i S:
-- pow_card_insert_mul_le_step_add,
-- Finset.card_insert_of_notMem, push_cast, linarith.
/-- Summing the step bound over all coordinates in `S` bounds `G` at the constant vector `q*m+r`. -/
private theorem const_le_pow_card_mul_add_sum {d : ℕ} (G : (Fin d → ℕ) → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ k, G k ≤ C * ∏ i, (k i : ℝ))
    (hsub : ∀ k i a b, G (Function.update k i (a + b))
      ≤ G (Function.update k i a) + G (Function.update k i b))
    (q m r : ℕ) (S : Finset (Fin d)) :
    G (fun _ => q * m + r)
      ≤ (q : ℝ) ^ S.card * G (fun l => if l ∈ S then m else q * m + r)
        + S.card * (C * r * ((q * m + r : ℕ) : ℝ) ^ (d - 1)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    have h3 := pow_card_insert_mul_le_step_add G C hC0 hC hsub q m r S i hi
    rw [Finset.card_insert_of_notMem hi] at h3 ⊢
    push_cast at h3 ih ⊢
    linarith


-- const_le_pow_card_mul_add_sum with S = univ (simp: Finset.mem_univ, Finset.card_univ,
-- Fintype.card_fin),
-- q := n / m, r := n % m (Nat.div_add_mod' / Nat.div_add_mod: m * (n/m) + n % m = n).
-- Then: r ≤ m (Nat.mod_lt), (q*m)^d ≤ n^d (Nat.div_mul_le_self, pow_le_pow_left), and G ≥ 0 give
-- q^d G(m1) ≤ n^d G(m1)/m^d; divide by n^d > 0 (div_le_iff₀), n^(d-1)/n^d = 1/n
-- (pow_sub₀ or n^d = n * n^(d-1) via Nat.sub_add_cancel hd).  -- SPLIT?
/-- The two-scale bound `G(n)/n^d ≤ G(m)/m^d + d*C*m/n` for `1 ≤ m ≤ n`. -/
private theorem div_pow_le_div_pow_add_div {d : ℕ} (hd : 1 ≤ d) (G : (Fin d → ℕ) → ℝ) (C : ℝ)
    (hC0 : 0 ≤ C)
    (hG0 : ∀ k, 0 ≤ G k) (hC : ∀ k, G k ≤ C * ∏ i, (k i : ℝ))
    (hsub : ∀ k i a b, G (Function.update k i (a + b))
      ≤ G (Function.update k i a) + G (Function.update k i b))
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    G (fun _ => n) / (n : ℝ) ^ d ≤ G (fun _ => m) / (m : ℝ) ^ d + d * C * m / n := by
  have hn : (0 : ℕ) < n := Nat.lt_of_lt_of_le hm hmn
  have hnpos : (0 : ℝ) < (n : ℝ) := (by exact_mod_cast hn)
  have hmpos : (0 : ℝ) < (m : ℝ) := (by exact_mod_cast hm)
  have hqmr : n / m * m + n % m = n := Nat.div_add_mod' n m
  have hqmle : n / m * m ≤ n := Nat.div_mul_le_self n m
  have hrle : n % m ≤ m := Nat.le_of_lt (Nat.mod_lt n hm)
  have hmpow : (0 : ℝ) < (m : ℝ) ^ d := pow_pos hmpos d
  have hnpow : (0 : ℝ) < (n : ℝ) ^ d := pow_pos hnpos d
  have h4 := const_le_pow_card_mul_add_sum G C hC0 hC hsub (n / m) m (n % m) Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h4
  have hfun : (fun l : Fin d => if l ∈ Finset.univ then m else n / m * m + n % m) = (fun _ => m) :=
      (by funext l; simp)
  rw [hfun] at h4
  have hGfun : (fun _ : Fin d => n / m * m + n % m) = (fun _ => n) := (by funext l; exact hqmr)
  rw [hGfun] at h4
  have hcast : ((n / m * m + n % m : ℕ) : ℝ) = (n : ℝ) := (by rw [hqmr])
  rw [hcast] at h4
  have hA : ((n / m : ℕ) : ℝ) ^ d * G (fun _ => m) ≤ G (fun _ => m) / (m : ℝ) ^ d * (n : ℝ) ^ d :=
      (by
    have hqmleR : ((n / m : ℕ) : ℝ) * (m : ℝ) ≤ (n : ℝ) := (by exact_mod_cast hqmle)
    have h0qm : (0 : ℝ) ≤ ((n / m : ℕ) : ℝ) * (m : ℝ) := (by positivity)
    have hpow : (((n / m : ℕ) : ℝ) * (m : ℝ)) ^ d ≤ (n : ℝ) ^ d := pow_le_pow_left₀ h0qm hqmleR d
    rw [mul_pow] at hpow
    have hQle : ((n / m : ℕ) : ℝ) ^ d ≤ (n : ℝ) ^ d / (m : ℝ) ^ d :=
        (by rw [le_div_iff₀ hmpow]; exact hpow)
    have h1 := mul_le_mul_of_nonneg_right hQle (hG0 (fun _ => m))
    have h2 : (n : ℝ) ^ d / (m : ℝ) ^ d * G (fun _ => m) = G (fun _ => m) / (m : ℝ) ^ d * (n : ℝ) ^
        d := (by ring_nf)
    linarith)
  have hRle : ((n % m : ℕ) : ℝ) ≤ (m : ℝ) := (by exact_mod_cast hrle)
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := (by positivity)
  have hnn0 : (0 : ℝ) ≤ (n : ℝ) ^ (d - 1) := (by positivity)
  have hB1 : (d : ℝ) * (C * ((n % m : ℕ) : ℝ) * (n : ℝ) ^ (d - 1)) ≤ (d : ℝ) *
      (C * (m : ℝ) * (n : ℝ) ^ (d - 1)) := (by
    have hnn : (0 : ℝ) ≤ (d : ℝ) * C * (n : ℝ) ^ (d - 1) := mul_nonneg (mul_nonneg hd0 hC0) hnn0
    have h := mul_le_mul_of_nonneg_right hRle hnn
    nlinarith [h])
  have hpow_n : (n : ℝ) ^ (d - 1) * (n : ℝ) = (n : ℝ) ^ d :=
      (by rw [← pow_succ, Nat.sub_add_cancel hd])
  have hnd : (n : ℝ) ^ d / (n : ℝ) = (n : ℝ) ^ (d - 1) :=
      (by rw [div_eq_iff hnpos.ne']; exact hpow_n.symm)
  have hB2 : (d : ℝ) * (C * (m : ℝ) * (n : ℝ) ^ (d - 1)) = (d : ℝ) * C * (m : ℝ) / (n : ℝ) * (n : ℝ)
      ^ d := (by
    rw [← hnd]; ring)
  have hB : (d : ℝ) * (C * ((n % m : ℕ) : ℝ) * (n : ℝ) ^ (d - 1)) ≤ (d : ℝ) * C * (m : ℝ) / (n : ℝ)
      * (n : ℝ) ^ d := hB1.trans_eq hB2
  have hexp : (G (fun _ => m) / (m : ℝ) ^ d + (d : ℝ) * C * (m : ℝ) / (n : ℝ)) * (n : ℝ) ^ d = G
      (fun _ => m) / (m : ℝ) ^ d * (n : ℝ) ^ d + (d : ℝ) * C * (m : ℝ) / (n : ℝ) * (n : ℝ) ^ d :=
      (by ring_nf)
  rw [div_le_iff₀ hnpow, hexp]
  linarith [h4, hA, hB]


-- L := ⨅ m, a (m + 1) (bounded below by 0: ⟨0, Set.forall_mem_range.2 fun m => ha0 _⟩).
-- For n ≥ 1: L ≤ a n by ciInf_le with index n - 1 (Nat.sub_add_cancel).
/-- `⨅ m, a (m+1) ≤ a n` for `n ≥ 1`. -/
private theorem iInf_succ_le (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (n : ℕ) (hn : 1 ≤ n) :
    (⨅ m : ℕ, a (m + 1)) ≤ a n := by
  have hbdd : BddBelow (Set.range fun m : ℕ => a (m + 1)) :=
    ⟨0, Set.forall_mem_range.2 fun m => ha0 _⟩
  have h := ciInf_le hbdd (n - 1)
  rwa [Nat.sub_add_cancel hn] at h


-- Given ε > 0: exists_lt_of_ciInf_lt (L < L + ε/2) gives m with a (m+1) < L + ε/2;
-- choose N ≥ m+1 with K*(m+1)/N < ε/2 (exists_nat_gt; div_lt_iff₀); for n ≥ N use hsub and
-- div_le_div_of_nonneg_left (K*(m+1) ≥ 0 needs hK : 0 ≤ K).
/-- Eventually `a n < (⨅ m, a (m+1)) + ε`, from the two-scale bound `hsub`. -/
private theorem eventually_lt_iInf_succ_add_core (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (K : ℝ)
    (_hK : 0 ≤ K)
    (hsub : ∀ m n, 1 ≤ m → m ≤ n → a n ≤ a m + K * m / n) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n → a n < (⨅ m : ℕ, a (m + 1)) + ε := by
  have hbdd : BddBelow (Set.range fun m : ℕ => a (m + 1)) :=
    ⟨0, by rintro _ ⟨m, rfl⟩; exact ha0 _⟩
  have hε2 : 0 < ε / 2 := by linarith
  have hLt : (⨅ m : ℕ, a (m + 1)) < (⨅ m : ℕ, a (m + 1)) + ε / 2 := by linarith
  obtain ⟨m, hm⟩ := exists_lt_of_ciInf_lt hLt
  obtain ⟨N, hN⟩ := exists_nat_gt (K * ((m + 1 : ℕ) : ℝ) / (ε / 2))
  refine ⟨max N (m + 1), fun n hn => ?_⟩
  have hNle : N ≤ n := le_trans (le_max_left _ _) hn
  have hmn : m + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h0 : (0 : ℕ) < n := Nat.lt_of_lt_of_le (Nat.succ_pos m) hmn
    exact_mod_cast h0
  have h2 : K * ((m + 1 : ℕ) : ℝ) < (N : ℝ) * (ε / 2) := (div_lt_iff₀ hε2).mp hN
  have h3 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNle
  have h3' : (N : ℝ) * (ε / 2) ≤ (n : ℝ) * (ε / 2) :=
    mul_le_mul_of_nonneg_right h3 (le_of_lt hε2)
  have h1 : K * ((m + 1 : ℕ) : ℝ) < (ε / 2) * (n : ℝ) := by
    linarith [h2, h3', mul_comm (N : ℝ) (ε / 2)]
  have h4 : K * ((m + 1 : ℕ) : ℝ) / (n : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hnpos]
    linarith [h1]
  have h5 : a n ≤ a (m + 1) + K * ((m + 1 : ℕ) : ℝ) / (n : ℝ) :=
    hsub (m + 1) n (Nat.succ_le_succ (Nat.zero_le m)) hmn
  linarith

/-- Restatement of `eventually_lt_iInf_succ_add_core`. -/
private theorem eventually_lt_iInf_succ_add (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (K : ℝ) (hK : 0 ≤ K)
    (hsub : ∀ m n, 1 ≤ m → m ≤ n → a n ≤ a m + K * m / n) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n → a n < (⨅ m : ℕ, a (m + 1)) + ε := by
  exact eventually_lt_iInf_succ_add_core a ha0 K hK hsub ε hε


-- Fekete: ⟨⨅ m, a (m+1), tendsto_order.2 ⟨fun b hb => eventually_atTop.2 ⟨1, fun n hn =>
-- lt_of_lt_of_le hb (iInf_succ_le ..)⟩, fun b hb => (eventually_lt_iInf_succ_add with ε := b - L)
-- ...⟩⟩.
/-- Fekete's lemma: `a` converges to `⨅ m, a (m+1)` under the two-scale bound `hsub`. -/
private theorem exists_tendsto_of_subadditive_core (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (K : ℝ)
    (hK : 0 ≤ K)
    (hsub : ∀ m n, 1 ≤ m → m ≤ n → a n ≤ a m + K * m / n) :
    ∃ L : ℝ, Tendsto a atTop (𝓝 L) := by
  have h6 : ∀ n, 1 ≤ n → (⨅ m : ℕ, a (m + 1)) ≤ a n := by
    intro n hn
    have hbd : BddBelow (Set.range fun m : ℕ => a (m + 1)) :=
      ⟨0, Set.forall_mem_range.2 (fun m => ha0 (m + 1))⟩
    have h := ciInf_le hbd (n - 1)
    rwa [Nat.sub_add_cancel hn] at h
  have h7 : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n → a n < (⨅ m : ℕ, a (m + 1)) + ε := by
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have hL : (⨅ m : ℕ, a (m + 1)) < (⨅ m : ℕ, a (m + 1)) + ε / 2 := by linarith
    obtain ⟨m, hm⟩ := exists_lt_of_ciInf_lt (f := fun m : ℕ => a (m + 1)) hL
    obtain ⟨N, hN⟩ := exists_nat_gt (K * ((m : ℝ) + 1) / (ε / 2))
    refine ⟨max (m + 1) N, fun n hn => ?_⟩
    have hmn : m + 1 ≤ n := le_trans (le_max_left _ _) hn
    have hNn : N ≤ n := le_trans (le_max_right _ _) hn
    have hNpos : (0 : ℝ) < N :=
      lt_of_le_of_lt (div_nonneg (mul_nonneg hK (by positivity)) (le_of_lt hε2)) hN
    have h1 : K * ((m : ℝ) + 1) / (N : ℝ) < ε / 2 := by
      rw [div_lt_iff₀ hNpos, mul_comm (ε / 2)]
      exact (div_lt_iff₀ hε2).1 hN
    have h2 : K * ((m : ℝ) + 1) / (n : ℝ) < ε / 2 := by
      refine lt_of_le_of_lt ?_ h1
      exact div_le_div_of_nonneg_left (mul_nonneg hK (by positivity)) hNpos (by exact_mod_cast hNn)
    have hsub' := hsub (m + 1) n (by omega) hmn
    push_cast at hsub'
    linarith
  refine ⟨(⨅ m : ℕ, a (m + 1)), ?_⟩
  rw [tendsto_order]
  constructor
  · intro b hb
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    exact lt_of_lt_of_le hb (h6 n hn)
  · intro b hb
    obtain ⟨N, hN⟩ := h7 (b - ⨅ m : ℕ, a (m + 1)) (by linarith)
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have := hN n hn
    linarith

/-- Restatement of `exists_tendsto_of_subadditive_core`. -/
private theorem exists_tendsto_of_subadditive (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (K : ℝ) (hK : 0 ≤ K)
    (hsub : ∀ m n, 1 ≤ m → m ≤ n → a n ≤ a m + K * m / n) :
    ∃ L : ℝ, Tendsto a atTop (𝓝 L) := by
  exact exists_tendsto_of_subadditive_core a ha0 K hK hsub


/-! ### Layer A: boxes and the mean functional -/

-- Classical: obtain ⟨C, hC⟩; take max C 0; le_max_left, mul_le_mul_of_nonneg_right
-- (Nat.cast_nonneg).
omit [MeasurableSpace Ω] in
/-- A possibly negative bound `C` on `f` can be replaced by the nonnegative `max C 0`. -/
private theorem exists_nonneg_bound_of_bound {d : ℕ} (f : Finset (Site d) → Ω → ℝ)
    (hbd : ∃ C, ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) :
    ∃ C, 0 ≤ C ∧ ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card := by
  obtain ⟨C, hC⟩ := hbd
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro A ω
  refine ⟨(hC A ω).1, ?_⟩
  calc f A ω ≤ C * (A.card : ℝ) := (hC A ω).2
    _ ≤ max C 0 * (A.card : ℝ) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)


-- Integrable.of_bound (hmeas A).aestronglyMeasurable (C * A.card) (ae_of_all: Real.norm_eq_abs,
-- abs_of_nonneg).
/-- `f A` is integrable, from the pointwise bound `f A ω ≤ C * A.card`. -/
private theorem integrable_of_bound_card {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Finset (Site d) → Ω → ℝ) (hmeas : ∀ A, Measurable (f A)) (C : ℝ)
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (A : Finset (Site d)) :
    Integrable (f A) μ := by
  refine Integrable.of_bound (hmeas A).aestronglyMeasurable (C * A.card) (ae_of_all μ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hC A ω).1]
  exact (hC A ω).2


-- simp_rw [hstat]; then as in LatticeProb.integral_comp_iterate (Kingman.lean):
-- conv_rhs => rw [← (hτ z).map_eq]; integral_map (hτ z).measurable.aemeasurable
-- (hmeas A).aestronglyMeasurable.
/-- Stationarity moves the integral of `f` on a translated box back to the original box. -/
private theorem integral_map_addRight_eq_integral {d : ℕ} (μ : Measure Ω) (τ : Site d → Ω → Ω)
    (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (f : Finset (Site d) → Ω → ℝ) (hmeas : ∀ A, Measurable (f A))
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    (A : Finset (Site d)) (z : Site d) :
    ∫ ω, f (A.map (Equiv.addRight z).toEmbedding) ω ∂μ = ∫ ω, f A ω ∂μ := by
  have h1 : ∀ ω, f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω) := fun ω => hstat A z ω
  rw [funext h1]
  conv_rhs => rw [← (hτ z).map_eq]
  rw
      [integral_map (hτ z).measurable.aemeasurable
      (by rw [(hτ z).map_eq]; exact (hmeas A).aestronglyMeasurable)]


-- simp [sideBox, Finset.mem_Icc, Pi.le_def, forall_and]; Int.le_sub_one_iff.
/-- `x ∈ sideBox k` iff each coordinate `x i` lies in `[0, k i)`. -/
private theorem mem_sideBox_iff {d : ℕ} (k : Fin d → ℕ) (x : Site d) :
    x ∈ sideBox k ↔ ∀ i, 0 ≤ x i ∧ x i < k i := by
  simp [sideBox, Finset.mem_Icc, Pi.le_def, forall_and]


-- sideBox, Pi.card_Icc, Int.card_Icc, simp (((k i : ℤ) - 1 + 1 - 0).toNat = k i).
/-- `(sideBox k).card = ∏ i, k i`. -/
private theorem card_sideBox {d : ℕ} (k : Fin d → ℕ) : (sideBox k).card = ∏ i, k i := by
  rw [sideBox, Pi.card_Icc]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Int.card_Icc]
  simp


-- The translate of a box is a box: unfold sideBox latticeBox; ext x;
-- Finset.mem_map_equiv, Equiv.addRight_symm / Equiv.coe_addRight, Finset.mem_Icc, Pi.le_def,
-- sub_nonneg / le_sub_iff_add_le; or Finset.map_add_right_Icc after identifying the embedding.
/-- Translating `sideBox k` by `z` gives the box `latticeBox z (z + k - 1)`. -/
private theorem sideBox_map_addRight_eq_latticeBox {d : ℕ} (k : Fin d → ℕ) (z : Site d) :
    (sideBox k).map (Equiv.addRight z).toEmbedding
      = latticeBox z (z + fun i => (k i : ℤ) - 1) := by
  have hz : (Equiv.toEmbedding (Equiv.addRight z) : Site d ↪ Site d) = addRightEmbedding z := rfl
  rw [show sideBox k = Finset.Icc (0 : Site d) (fun i => (k i : ℤ) - 1) from rfl, hz,
    Finset.map_add_right_Icc]
  rw [show latticeBox z (z + fun i => (k i : ℤ) - 1)
      = Finset.Icc z (z + fun i => (k i : ℤ) - 1) from rfl]
  congr 1
  · ext i; simp
  · ext i; simp [add_comm]


-- Finset.disjoint_left; x in the first box has x i < a (mem_sideBox_iff at i,
-- Function.update_self);
-- x in the translate has x - Pi.single i a in sideBox (Finset.mem_map_equiv), so x i ≥ a
-- (Pi.sub_apply, Pi.single_eq_same). omega.
-- Points of the first box have i-th coordinate < a: mem_sideBox_iff at i (the `.2` conjunct),
-- then Function.update_self under the cast; exact_mod_cast.
/-- Points of `sideBox (update k i a)` have `i`-th coordinate below `a`. -/
private theorem lt_of_mem_sideBox_update {d : ℕ} (k : Fin d → ℕ) (i : Fin d) (a : ℕ) (x : Site d)
    (hx : x ∈ sideBox (Function.update k i a)) : x i < (a : ℤ) := by
  have h := ((mem_sideBox_iff _ x).1 hx i).2
  rw [Function.update_self] at h
  exact h

-- Points of the translated box have i-th coordinate ≥ a: Finset.mem_map gives x = y + single i a
-- with y ∈ sideBox (mem_sideBox_iff at i, `.1` conjunct: 0 ≤ y i); Pi.add_apply, Pi.single_eq_same.
/-- Points of the `a`-translate of `sideBox (update k i b)` have `i`-th coordinate at least `a`. -/
private theorem le_of_mem_sideBox_update_map {d : ℕ} (k : Fin d → ℕ) (i : Fin d) (a b : ℕ)
    (x : Site d)
    (hx : x ∈ (sideBox (Function.update k i b)).map
      (Equiv.addRight (Pi.single i (a : ℤ))).toEmbedding) : (a : ℤ) ≤ x i := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
  have h := ((mem_sideBox_iff _ y).1 hy i).1
  simp only [Equiv.toEmbedding_apply, Equiv.coe_addRight, Pi.add_apply, Pi.single_eq_same]
  omega

/-- `sideBox (update k i a)` and the `a`-translate of `sideBox (update k i b)` are disjoint. -/
private theorem disjoint_sideBox_update_map {d : ℕ} (k : Fin d → ℕ) (i : Fin d) (a b : ℕ) :
    Disjoint (sideBox (Function.update k i a))
      ((sideBox (Function.update k i b)).map (Equiv.addRight (Pi.single i (a : ℤ))).toEmbedding) :=
          by
  exact Finset.disjoint_left.mpr fun x h1 h2 =>
    absurd (lt_of_mem_sideBox_update k i a x h1)
        (not_lt.mpr (le_of_mem_sideBox_update_map k i a b x h2))

-- ext x; Finset.mem_union, Finset.mem_map_equiv, mem_sideBox_iff three times; coordinatewise:
-- at j = i split on x i < a (Function.update_self, Pi.single_eq_same), at j ≠ i
-- (Function.update_of_ne, Pi.single_eq_of_ne) nothing changes; push_cast; omega.  -- SPLIT?
/-- Their union is `sideBox (update k i (a+b))`: the one-coordinate box split. -/
private theorem union_sideBox_update_map_eq_sideBox_update_add {d : ℕ} (k : Fin d → ℕ) (i : Fin d)
    (a b : ℕ) :
    sideBox (Function.update k i a)
      ∪ (sideBox (Function.update k i b)).map (Equiv.addRight (Pi.single i (a : ℤ))).toEmbedding
      = sideBox (Function.update k i (a + b)) := by
  ext x
  simp only [Finset.mem_union, mem_sideBox_iff, Finset.mem_map, Equiv.toEmbedding_apply,
    Equiv.coe_addRight]
  constructor
  · rintro (hA | ⟨y, hy, hyx⟩)
    · intro j
      have h := hA j
      by_cases hj : j = i
      · rw [hj] at h ⊢
        rw [Function.update_self] at h
        rw [Function.update_self]
        exact ⟨h.1, by omega⟩
      · rw [Function.update_of_ne hj] at h
        rw [Function.update_of_ne hj]
        exact h
    · intro j
      have h := hy j
      have hyx' := congrFun hyx j
      rw [Pi.add_apply] at hyx'
      rw [← hyx']
      by_cases hj : j = i
      · rw [hj] at h ⊢
        rw [Function.update_self] at h
        rw [Function.update_self, Pi.single_eq_same]
        push_cast at h ⊢
        omega
      · rw [Function.update_of_ne hj] at h
        rw [Pi.single_eq_of_ne hj, add_zero, Function.update_of_ne hj]
        exact h
  · intro hC
    by_cases hlt : x i < (a : ℤ)
    · left
      intro j
      have h := hC j
      by_cases hj : j = i
      · rw [hj] at h ⊢
        rw [Function.update_self] at h
        rw [Function.update_self]
        push_cast at h
        exact ⟨h.1, hlt⟩
      · rw [Function.update_of_ne hj] at h
        rw [Function.update_of_ne hj]
        exact h
    · right
      refine ⟨x - Pi.single i (a : ℤ), ?_, ?_⟩
      · intro j
        have h := hC j
        have hax : (a : ℤ) ≤ x i := le_of_not_gt hlt
        by_cases hj : j = i
        · rw [hj] at h ⊢
          rw [Function.update_self] at h
          rw [Function.update_self]
          simp only [Pi.sub_apply, Pi.single_eq_same]
          push_cast at h ⊢
          exact ⟨by omega, by omega⟩
        · rw [Function.update_of_ne hj] at h
          rw [Function.update_of_ne hj]
          simp only [Pi.sub_apply, Pi.single_eq_of_ne hj, sub_zero]
          exact h
      · ext j
        simp


-- ⟨⟨0, _, rfl⟩, ⟨0, _, rfl⟩, ⟨_, _, sideBox_map_addRight_eq_latticeBox _ _⟩,
-- disjoint_sideBox_update_map .., union_sideBox_update_map_eq_sideBox_update_add ..⟩
-- (sideBox k is definitionally latticeBox 0 (fun i => k i - 1)).
/-- `sideBox (update k i (a+b))` splits as `sideBox (update k i a)` and a translate of `sideBox
(update k i b)`. -/
private theorem isBoxSplit_sideBox_update_add {d : ℕ} (k : Fin d → ℕ) (i : Fin d) (a b : ℕ) :
    IsBoxSplit (sideBox (Function.update k i (a + b))) (sideBox (Function.update k i a))
      ((sideBox (Function.update k i b)).map (Equiv.addRight (Pi.single i (a : ℤ))).toEmbedding) :=
          by
  have e1 : sideBox (Function.update k i (a + b))
      = latticeBox (0 : Site d) (fun j => ((Function.update k i (a + b)) j : ℤ) - 1) := rfl
  have e2 : sideBox (Function.update k i a)
      = latticeBox (0 : Site d) (fun j => ((Function.update k i a) j : ℤ) - 1) := rfl
  have e3 : (sideBox (Function.update k i b)).map
        (Equiv.addRight (Pi.single i (a : ℤ))).toEmbedding
      = latticeBox (Pi.single i (a : ℤ))
        (Pi.single i (a : ℤ) + fun j => ((Function.update k i b) j : ℤ) - 1) :=
    sideBox_map_addRight_eq_latticeBox (Function.update k i b) (Pi.single i (a : ℤ))
  have e4 : Disjoint (sideBox (Function.update k i a))
      ((sideBox (Function.update k i b)).map
        (Equiv.addRight (Pi.single i (a : ℤ))).toEmbedding) :=
    disjoint_sideBox_update_map k i a b
  have e5 : sideBox (Function.update k i a) ∪
      (sideBox (Function.update k i b)).map
        (Equiv.addRight (Pi.single i (a : ℤ))).toEmbedding
      = sideBox (Function.update k i (a + b)) :=
    union_sideBox_update_map_eq_sideBox_update_add k i a b
  exact ⟨⟨0, _, e1⟩, ⟨0, _, e2⟩, ⟨_, _, e3⟩, e4, e5⟩


-- integral_nonneg (fun ω => (hC _ ω).1).
/-- `0 ≤ ∫ f (sideBox k)`, from the pointwise nonnegativity of `f`. -/
private theorem integral_sideBox_nonneg {d : ℕ} (μ : Measure Ω) (f : Finset (Site d) → Ω → ℝ)
    (C : ℝ)
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (k : Fin d → ℕ) :
    0 ≤ ∫ ω, f (sideBox k) ω ∂μ := by
  exact integral_nonneg fun ω => (hC (sideBox k) ω).1


-- integral_mono_of_nonneg / integral_mono (integrable_of_bound_card, integrable_const) against the
-- constant
-- C * card; integral_const, probReal_univ / measureReal_univ_eq_one, smul_eq_mul;
-- card_sideBox and Nat.cast_prod.
/-- `∫ f (sideBox k) ≤ C * ∏ i, k i`, from the pointwise bound on `f`. -/
private theorem integral_sideBox_le_mul_prod {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Finset (Site d) → Ω → ℝ) (_hmeas : ∀ A, Measurable (f A)) (C : ℝ)
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (k : Fin d → ℕ) :
    ∫ ω, f (sideBox k) ω ∂μ ≤ C * ∏ i, (k i : ℝ) := by
  have hcard : ((sideBox k).card : ℝ) = ∏ i, (k i : ℝ)
  · rw [sideBox, Pi.card_Icc, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Int.card_Icc]
    simp
  have hint : (∫ ω, (C * (sideBox k).card : ℝ) ∂μ) = C * (sideBox k).card
  · rw [integral_const, probReal_univ, one_smul]
  calc ∫ ω, f (sideBox k) ω ∂μ
      ≤ ∫ ω, (C * (sideBox k).card : ℝ) ∂μ :=
        integral_mono_of_nonneg (ae_of_all μ fun ω => (hC _ ω).1) (integrable_const _)
          (ae_of_all μ fun ω => (hC _ ω).2)
    _ = C * (sideBox k).card := hint
    _ = C * ∏ i, (k i : ℝ) := congrArg (fun x => C * x) hcard


-- integral_mono (hsub _ _ _ ω (isBoxSplit_sideBox_update_add k i a b)) with integrability
-- integrable_of_bound_card,
-- integral_add, then rewrite the translated term with integral_map_addRight_eq_integral.
/-- The mean functional `G` inherits one-coordinate subadditivity from `f`'s box-split bound. -/
private theorem integral_sideBox_update_add_le {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (f : Finset (Site d) → Ω → ℝ) (hmeas : ∀ A, Measurable (f A))
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    (C : ℝ) (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (k : Fin d → ℕ) (i : Fin d) (a b : ℕ) :
    ∫ ω, f (sideBox (Function.update k i (a + b))) ω ∂μ
      ≤ ∫ ω, f (sideBox (Function.update k i a)) ω ∂μ
        + ∫ ω, f (sideBox (Function.update k i b)) ω ∂μ := by
  have hsplit := isBoxSplit_sideBox_update_add k i a b
  have hAB := integrable_of_bound_card μ f hmeas C hC (sideBox (Function.update k i (a + b)))
  have hA := integrable_of_bound_card μ f hmeas C hC (sideBox (Function.update k i a))
  have hB := integrable_of_bound_card μ f hmeas C hC
    ((sideBox (Function.update k i b)).map (Equiv.addRight (Pi.single i (a : ℤ))).toEmbedding)
  have h2 := integral_map_addRight_eq_integral μ τ hτ f hmeas hstat
      (sideBox (Function.update k i b))
    (Pi.single i (a : ℤ))
  refine le_trans (integral_mono hAB (hA.add hB) ?_) ?_
  · intro ω
    exact hsub _ _ _ ω hsplit
  · simp only [Pi.add_apply]
    rw [integral_add hA hB, h2]


end AKMeanAux

open AKMeanAux in
/-- The mean half: the volume-normalised means converge. -/
theorem akcoglu_krengel_mean (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (f : Finset (Site d) → Ω → ℝ) (hmeas : ∀ A, Measurable (f A))
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    (hbd : ∃ C, ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (∫ ω, f (latticeCube d n) ω ∂μ) / (n : ℝ) ^ d) atTop (𝓝 L) := by
  obtain ⟨C, hC0, hC⟩ := exists_nonneg_bound_of_bound f hbd
  set G : (Fin d → ℕ) → ℝ := fun k => ∫ ω, f (sideBox k) ω ∂μ with hGdef
  have hG0 : ∀ k, 0 ≤ G k := fun k => integral_sideBox_nonneg μ f C hC k
  have hGC : ∀ k, G k ≤ C * ∏ i, (k i : ℝ) := fun k => integral_sideBox_le_mul_prod μ f hmeas C hC k
  have hGsub : ∀ k i a b, G (Function.update k i (a + b))
      ≤ G (Function.update k i a) + G (Function.update k i b) :=
    fun k i a b => integral_sideBox_update_add_le μ τ hτ f hmeas hstat C hC hsub k i a b
  have hK : 0 ≤ (d : ℝ) * C := mul_nonneg (Nat.cast_nonneg d) hC0
  obtain ⟨L, hL⟩ := exists_tendsto_of_subadditive (fun n : ℕ => G (fun _ => n) / (n : ℝ) ^ d)
    (fun n => div_nonneg (hG0 _) (pow_nonneg (Nat.cast_nonneg n) d)) ((d : ℝ) * C) hK
    (fun m n hm hmn => div_pow_le_div_pow_add_div hd G C hC0 hG0 hGC hGsub m n hm hmn)
  exact ⟨L, hL⟩


end LatticeProb
