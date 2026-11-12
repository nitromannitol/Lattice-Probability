/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20EMeet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EStrip

/-!
# DDDF Theorem 20, Step 4: a transversal crossing of a strip meets its chain (task P2-DDDFT20e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1103–1105 and 1117–1119. With `h = 2^{-K}`:
the long crossings of the chain `hChain K p q n`, `n ≤ 2(ℓ−3)`, lie in the horizontal strip
`h([p, p+ℓ] × [q, q+3])`, their union is path connected and joins the two short sides, so every
top–bottom crossing of the strip meets one of them (`T20E.hStrip_meet`); the same for the
vertical strip `h([p, p+3] × [q, q+ℓ])` and `vChain` (`T20E.vStrip_meet`). Own elementary
argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace T20E

open LFPP

lemma hChain_cases (K : ℕ) (p q : ℤ) (n : ℕ) :
    (n % 2 = 0 ∧ hChain K p q n = eH K (p + (n / 2 : ℕ)) (q + 1)) ∨
      (n % 2 = 1 ∧ hChain K p q n = eV K (p + (n / 2 : ℕ) + 2) q) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · exact Or.inl ⟨h, by simp [hChain, h]⟩
  · exact Or.inr ⟨h, by simp [hChain, h]⟩

lemma vChain_cases (K : ℕ) (p q : ℤ) (n : ℕ) :
    (n % 2 = 0 ∧ vChain K p q n = eV K (p + 2) (q + (n / 2 : ℕ))) ∨
      (n % 2 = 1 ∧ vChain K p q n = eH K p (q + (n / 2 : ℕ) + 1)) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · exact Or.inl ⟨h, by simp [vChain, h]⟩
  · exact Or.inr ⟨h, by simp [vChain, h]⟩

/-- the rectangle `h([a₀, a₁] × [b₀, b₁])` -/
def gRect (K : ℕ) (a₀ a₁ b₀ b₁ : ℤ) : Set ℂ :=
  RectCross.rect ((a₀ : ℝ) * (2 : ℝ)⁻¹ ^ K) ((a₁ : ℝ) * (2 : ℝ)⁻¹ ^ K)
    ((b₀ : ℝ) * (2 : ℝ)⁻¹ ^ K) ((b₁ : ℝ) * (2 : ℝ)⁻¹ ^ K)

lemma rH_sub {K : ℕ} {a b a₀ a₁ b₀ b₁ : ℤ} (h1 : a₀ ≤ a) (h2 : a + 3 ≤ a₁) (h3 : b₀ ≤ b)
    (h4 : b + 1 ≤ b₁) : (rH K a b).toSet ⊆ gRect K a₀ a₁ b₀ b₁ := by
  intro z hz
  rw [mem_toSet_iff] at hz
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have r1 : (a₀ : ℝ) ≤ a := by exact_mod_cast h1
  have r2 : (a : ℝ) + 3 ≤ a₁ := by exact_mod_cast h2
  have r3 : (b₀ : ℝ) ≤ b := by exact_mod_cast h3
  have r4 : (b : ℝ) + 1 ≤ b₁ := by exact_mod_cast h4
  simp only [rH, mem_Icc] at hz
  exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

lemma rV_sub {K : ℕ} {a b a₀ a₁ b₀ b₁ : ℤ} (h1 : a₀ ≤ a - 1) (h2 : a ≤ a₁) (h3 : b₀ ≤ b)
    (h4 : b + 3 ≤ b₁) : (rV K a b).toSet ⊆ gRect K a₀ a₁ b₀ b₁ := by
  intro z hz
  rw [mem_toSet_iff] at hz
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have r1 : (a₀ : ℝ) ≤ a - 1 := by exact_mod_cast h1
  have r2 : (a : ℝ) ≤ a₁ := by exact_mod_cast h2
  have r3 : (b₀ : ℝ) ≤ b := by exact_mod_cast h3
  have r4 : (b : ℝ) + 3 ≤ b₁ := by exact_mod_cast h4
  simp only [rV, mem_Icc] at hz
  exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

/-- the chain of the horizontal strip stays in the strip -/
lemma hChain_sub (K : ℕ) (p q : ℤ) (ℓ : ℕ) {n : ℕ} (hn : n ≤ 2 * (ℓ - 3)) (hℓ : 3 ≤ ℓ) :
    T20D.RL K (hChain K p q n) ⊆ gRect K p (p + ℓ) q (q + 3) := by
  rcases hChain_cases K p q n with ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e]
  · exact (RL_eH_sub K _ _).trans (rH_sub (by omega) (by omega) (by omega) (by omega))
  · exact (RL_eV_sub K _ _).trans (rV_sub (by omega) (by omega) (by omega) (by omega))

/-- the chain of the vertical strip stays in the strip -/
lemma vChain_sub (K : ℕ) (p q : ℤ) (ℓ : ℕ) {n : ℕ} (hn : n ≤ 2 * (ℓ - 3)) (hℓ : 3 ≤ ℓ) :
    T20D.RL K (vChain K p q n) ⊆ gRect K p (p + 3) q (q + ℓ) := by
  rcases vChain_cases K p q n with ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e]
  · exact (RL_eV_sub K _ _).trans (rV_sub (by omega) (by omega) (by omega) (by omega))
  · exact (RL_eH_sub K _ _).trans (rH_sub (by omega) (by omega) (by omega) (by omega))

/-- reparametrize a piece `γ|[u,v]`, forwards or backwards, on `[0,1]` -/
lemma piece_cont {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v) (hγ : ContinuousOn γ (Icc u v)) :
    ContinuousOn (fun τ => γ (u + τ * (v - u))) (Icc 0 1) ∧
      ContinuousOn (fun τ => γ (v - τ * (v - u))) (Icc 0 1) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, u + τ * (v - u) ∈ Icc u v) ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, v - τ * (v - u) ∈ Icc u v := by
  have h1 : ∀ τ ∈ Icc (0 : ℝ) 1, u + τ * (v - u) ∈ Icc u v := fun τ hτ =>
    ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  have h2 : ∀ τ ∈ Icc (0 : ℝ) 1, v - τ * (v - u) ∈ Icc u v := fun τ hτ =>
    ⟨by nlinarith [hτ.2], by nlinarith [hτ.1]⟩
  exact ⟨hγ.comp (by fun_prop) h1, hγ.comp (by fun_prop) h2, h1, h2⟩

/-- **A transversal crossing of a horizontal strip meets its chain.** -/
theorem hStrip_meet {K : ℕ} {pc : Circle × ℂ → ℝ → ℂ} (p q : ℤ) (ℓ : ℕ) (hℓ : 3 ≤ ℓ)
    (hadm : ∀ n ≤ 2 * (ℓ - 3), LAdm K (hChain K p q n) (pc (hChain K p q n)))
    {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v) (hγ : ContinuousOn γ (Icc u v))
    (hR : ∀ r ∈ Icc u v, γ r ∈ gRect K p (p + ℓ) q (q + 3))
    (hend : ((γ u).im = ((q + 3 : ℤ) : ℝ) * (2 : ℝ)⁻¹ ^ K ∧ (γ v).im = (q : ℝ) * (2 : ℝ)⁻¹ ^ K) ∨
      ((γ u).im = (q : ℝ) * (2 : ℝ)⁻¹ ^ K ∧ (γ v).im = ((q + 3 : ℤ) : ℝ) * (2 : ℝ)⁻¹ ^ K)) :
    ∃ n ≤ 2 * (ℓ - 3), ∃ r ∈ Icc u v, ∃ s ∈ Icc (0 : ℝ) 1, γ r = pc (hChain K p q n) s := by
  set N := 2 * (ℓ - 3)
  set F := ⋃ k ∈ Finset.range (N + 1), pc (hChain K p q k) '' Icc 0 1
  have hcont : ∀ k ≤ N, ContinuousOn (pc (hChain K p q k)) (Icc 0 1) := fun k hk => by
    obtain ⟨_, _, _, _, hP, _⟩ := hadm k hk; exact hP.continuousOn
  have hF : IsPathConnected F := by
    classical
    set pc' : Circle × ℂ → ℝ → ℂ := fun j =>
      if ∃ k ≤ N, hChain K p q k = j then pc j else fun _ => 0
    have e : ∀ k ≤ N, pc' (hChain K p q k) = pc (hChain K p q k) := fun k hk => by
      simp only [pc']; rw [ite_eq_left_iff.2 (fun h => absurd ⟨k, hk, rfl⟩ h)]
    have hc' : ∀ j, ContinuousOn (pc' j) (Icc 0 1) := fun j => by
      simp only [pc']
      split_ifs with h
      · obtain ⟨k, hk, rfl⟩ := h; exact hcont k hk
      · exact continuousOn_const
    have := isPathConnected_chain hc' (hChain K p q) N fun k hk => by
      rw [Meet, e k hk.le, e (k + 1) hk]
      exact hChain_meet (pc := pc) p q k (hadm k hk.le) (hadm (k + 1) hk)
    have hFe : F = ⋃ k ∈ Finset.range (N + 1), pc' (hChain K p q k) '' Icc 0 1 :=
      iUnion₂_congr fun k hk => by rw [e k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
    rw [hFe]; exact this
  have hFR : F ⊆ gRect K p (p + ℓ) q (q + 3) := by
    intro z hz
    simp only [F, mem_iUnion, Finset.mem_range] at hz
    obtain ⟨k, hk, t, ht, rfl⟩ := hz
    obtain ⟨_, _, _, _, _, hU⟩ := hadm k (by omega)
    exact hChain_sub K p q ℓ (by omega) hℓ (hU t ht)
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  -- the two ends of the chain
  have h0 : hChain K p q 0 = eH K p (q + 1) := by simp [hChain]
  have hN : hChain K p q N = eH K (p + (ℓ - 3 : ℕ)) (q + 1) := by
    have : N % 2 = 0 := by omega
    simp only [hChain, this, ite_true]
    congr 2; omega
  have ha : pc (hChain K p q 0) 0 ∈ F :=
    mem_biUnion (Finset.mem_range.2 (Nat.succ_pos N)) ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hb : pc (hChain K p q N) 1 ∈ F :=
    mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_self N)) ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  have har : (pc (hChain K p q 0) 0).re = (p : ℝ) * (2 : ℝ)⁻¹ ^ K := by
    have hA := hadm 0 (Nat.zero_le _)
    rw [h0] at hA ⊢
    obtain ⟨z, hz, _, _, hP, _⟩ := LAdm_eH hA
    rw [hP.source]
    simp only [rH, MarkedRect.side₁, ite_true, Complex.mem_reProdIm, mem_singleton_iff] at hz
    exact hz.1
  have hbr : (pc (hChain K p q N) 1).re = ((p + ℓ : ℤ) : ℝ) * (2 : ℝ)⁻¹ ^ K := by
    have hA := hadm N le_rfl
    rw [hN] at hA ⊢
    obtain ⟨_, _, w, hw, hP, _⟩ := LAdm_eH hA
    rw [hP.target]
    simp only [rH, MarkedRect.side₂, ite_true, Complex.mem_reProdIm, mem_singleton_iff] at hw
    rw [hw.1]
    have : ((ℓ - 3 : ℕ) : ℝ) = (ℓ : ℝ) - 3 := by
      rw [Nat.cast_sub hℓ]; norm_num
    push_cast; rw [this]; ring
  obtain ⟨hc1, hc2, hm1, hm2⟩ := piece_cont huv hγ
  have key : ∀ c : ℝ → ℂ, ContinuousOn c (Icc 0 1) → (∀ τ ∈ Icc (0 : ℝ) 1, ∃ r ∈ Icc u v, c τ = γ r) →
      (c 0).im = ((q + 3 : ℤ) : ℝ) * (2 : ℝ)⁻¹ ^ K → (c 1).im = (q : ℝ) * (2 : ℝ)⁻¹ ^ K →
      ∃ n ≤ N, ∃ r ∈ Icc u v, ∃ s ∈ Icc (0 : ℝ) 1, γ r = pc (hChain K p q n) s := by
    intro c hc hcγ e0 e1
    obtain ⟨τ, hτ, hτF⟩ := meet_of_joined hF ha hb hFR har hbr hc
      (fun τ hτ => by obtain ⟨r, hr, e⟩ := hcγ τ hτ; rw [e]; exact hR r hr) e0 e1
    obtain ⟨r, hr, e⟩ := hcγ τ hτ
    simp only [F, mem_iUnion, Finset.mem_range] at hτF
    obtain ⟨k, hk, s, hs, es⟩ := hτF
    exact ⟨k, by omega, r, hr, s, hs, by rw [← e, es]⟩
  rcases hend with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · exact key _ hc1 (fun τ hτ => ⟨_, hm1 τ hτ, rfl⟩) (by simpa using e0) (by simpa using e1)
  · exact key _ hc2 (fun τ hτ => ⟨_, hm2 τ hτ, rfl⟩) (by simpa using e1) (by simpa using e0)

/-- **A transversal crossing of a vertical strip meets its chain.** -/
theorem vStrip_meet {K : ℕ} {pc : Circle × ℂ → ℝ → ℂ} (p q : ℤ) (ℓ : ℕ) (hℓ : 3 ≤ ℓ)
    (hadm : ∀ n ≤ 2 * (ℓ - 3), LAdm K (vChain K p q n) (pc (vChain K p q n)))
    {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v) (hγ : ContinuousOn γ (Icc u v))
    (hR : ∀ r ∈ Icc u v, γ r ∈ gRect K p (p + 3) q (q + ℓ))
    (hend : ((γ u).re = (p : ℝ) * (2 : ℝ)⁻¹ ^ K ∧ (γ v).re = ((p + 3 : ℤ) : ℝ) * (2 : ℝ)⁻¹ ^ K) ∨
      ((γ u).re = ((p + 3 : ℤ) : ℝ) * (2 : ℝ)⁻¹ ^ K ∧ (γ v).re = (p : ℝ) * (2 : ℝ)⁻¹ ^ K)) :
    ∃ n ≤ 2 * (ℓ - 3), ∃ r ∈ Icc u v, ∃ s ∈ Icc (0 : ℝ) 1, γ r = pc (vChain K p q n) s := by
  set N := 2 * (ℓ - 3)
  set F := ⋃ k ∈ Finset.range (N + 1), pc (vChain K p q k) '' Icc 0 1
  have hcont : ∀ k ≤ N, ContinuousOn (pc (vChain K p q k)) (Icc 0 1) := fun k hk => by
    obtain ⟨_, _, _, _, hP, _⟩ := hadm k hk; exact hP.continuousOn
  have hF : IsPathConnected F := by
    classical
    set pc' : Circle × ℂ → ℝ → ℂ := fun j =>
      if ∃ k ≤ N, vChain K p q k = j then pc j else fun _ => 0
    have e : ∀ k ≤ N, pc' (vChain K p q k) = pc (vChain K p q k) := fun k hk => by
      simp only [pc']; rw [ite_eq_left_iff.2 (fun h => absurd ⟨k, hk, rfl⟩ h)]
    have hc' : ∀ j, ContinuousOn (pc' j) (Icc 0 1) := fun j => by
      simp only [pc']
      split_ifs with h
      · obtain ⟨k, hk, rfl⟩ := h; exact hcont k hk
      · exact continuousOn_const
    have := isPathConnected_chain hc' (vChain K p q) N fun k hk => by
      rw [Meet, e k hk.le, e (k + 1) hk]
      exact vChain_meet (pc := pc) p q k (hadm k hk.le) (hadm (k + 1) hk)
    have hFe : F = ⋃ k ∈ Finset.range (N + 1), pc' (vChain K p q k) '' Icc 0 1 :=
      iUnion₂_congr fun k hk => by rw [e k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
    rw [hFe]; exact this
  have hFR : F ⊆ gRect K p (p + 3) q (q + ℓ) := by
    intro z hz
    simp only [F, mem_iUnion, Finset.mem_range] at hz
    obtain ⟨k, hk, t, ht, rfl⟩ := hz
    obtain ⟨_, _, _, _, _, hU⟩ := hadm k (by omega)
    exact vChain_sub K p q ℓ (by omega) hℓ (hU t ht)
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  -- the two ends of the chain
  have h0 : vChain K p q 0 = eV K (p + 2) q := by simp [vChain]
  have hN : vChain K p q N = eV K (p + 2) (q + (ℓ - 3 : ℕ)) := by
    have : N % 2 = 0 := by omega
    simp only [vChain, this, ite_true]
    congr 2; omega
  have ha : pc (vChain K p q 0) 0 ∈ F :=
    mem_biUnion (Finset.mem_range.2 (Nat.succ_pos N)) ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hb : pc (vChain K p q N) 1 ∈ F :=
    mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_self N)) ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  have har : (pc (vChain K p q 0) 0).im = (q : ℝ) * (2 : ℝ)⁻¹ ^ K := by
    have hA := hadm 0 (Nat.zero_le _)
    rw [h0] at hA ⊢
    obtain ⟨z, hz, _, _, hP, _⟩ := LAdm_eV hA
    rw [hP.source]
    simp only [rV, MarkedRect.side₁, Bool.false_eq_true, ite_false, Complex.mem_reProdIm,
      mem_singleton_iff] at hz
    exact hz.2
  have hbr : (pc (vChain K p q N) 1).im = ((q + ℓ : ℤ) : ℝ) * (2 : ℝ)⁻¹ ^ K := by
    have hA := hadm N le_rfl
    rw [hN] at hA ⊢
    obtain ⟨_, _, w, hw, hP, _⟩ := LAdm_eV hA
    rw [hP.target]
    simp only [rV, MarkedRect.side₂, Bool.false_eq_true, ite_false, Complex.mem_reProdIm,
      mem_singleton_iff] at hw
    rw [hw.2]
    have : ((ℓ - 3 : ℕ) : ℝ) = (ℓ : ℝ) - 3 := by
      rw [Nat.cast_sub hℓ]; norm_num
    push_cast; rw [this]; ring
  obtain ⟨hc1, hc2, hm1, hm2⟩ := piece_cont huv hγ
  have key : ∀ c : ℝ → ℂ, ContinuousOn c (Icc 0 1) → (∀ τ ∈ Icc (0 : ℝ) 1, ∃ r ∈ Icc u v, c τ = γ r) →
      (c 0).re = (p : ℝ) * (2 : ℝ)⁻¹ ^ K → (c 1).re = ((p + 3 : ℤ) : ℝ) * (2 : ℝ)⁻¹ ^ K →
      ∃ n ≤ N, ∃ r ∈ Icc u v, ∃ s ∈ Icc (0 : ℝ) 1, γ r = pc (vChain K p q n) s := by
    intro c hc hcγ e0 e1
    obtain ⟨τ, hτ, hτF⟩ := meet_of_joined' hF ha hb hFR har hbr hc
      (fun τ hτ => by obtain ⟨r, hr, e⟩ := hcγ τ hτ; rw [e]; exact hR r hr) e0 e1
    obtain ⟨r, hr, e⟩ := hcγ τ hτ
    simp only [F, mem_iUnion, Finset.mem_range] at hτF
    obtain ⟨k, hk, s, hs, es⟩ := hτF
    exact ⟨k, by omega, r, hr, s, hs, by rw [← e, es]⟩
  rcases hend with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · exact key _ hc1 (fun τ hτ => ⟨_, hm1 τ hτ, rfl⟩) (by simpa using e0) (by simpa using e1)
  · exact key _ hc2 (fun τ hτ => ⟨_, hm2 τ hτ, rfl⟩) (by simpa using e1) (by simpa using e0)

end T20E
end DDDF
end LQGMetric
