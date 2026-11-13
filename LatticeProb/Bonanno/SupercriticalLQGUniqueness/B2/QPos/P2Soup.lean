/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2Soup at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib

 













set_option autoImplicit false
noncomputable section

open Filter Topology

namespace SupercriticalLQGUniqueness.B2.QPos

 
abbrev Soup (X : Type*) := Σ K : ℕ, Fin K → X

 
def soupMass {X : Type*} (w : X → ℝ) (Λ t : ℝ) (s : Soup X) : ℝ :=
  Real.exp (-(t * Λ)) / (s.1.factorial : ℝ) * ∏ i, (t * w (s.2 i))

theorem soupMass_nonneg {X : Type*} {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (Λ : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (s : Soup X) : 0 ≤ soupMass w Λ t s := by
  unfold soupMass
  refine mul_nonneg (div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) ?_
  exact Finset.prod_nonneg (fun i _ => mul_nonneg ht (hw _))

 
theorem hasSum_pi_prod {X R : Type*} [NormedCommRing R] [CompleteSpace R]
    (f : X → R) (hf : Summable fun x => ‖f x‖) (K : ℕ) :
    HasSum (fun ε : Fin K → X => ∏ i, f (ε i)) ((∑' x, f x) ^ K) ∧
      Summable (fun ε : Fin K → X => ‖∏ i, f (ε i)‖) := by
  induction K with
  | zero =>
    refine ⟨?_, ?_⟩
    · simpa using hasSum_fintype (fun ε : Fin 0 → X => ∏ i, f (ε i))
    · exact (hasSum_fintype _).summable
  | succ K ih =>
    let e := Fin.consEquiv (fun _ : Fin (K + 1) => X)
    have hcomp : (fun ε : Fin (K + 1) → X => ∏ i, f (ε i)) ∘ e =
        fun p : X × (Fin K → X) => f p.1 * ∏ i, f (p.2 i) := by
      funext p
      obtain ⟨x, ε⟩ := p
      simp only [Function.comp, e, Fin.consEquiv_apply]
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    refine ⟨?_, ?_⟩
    · have h1 : HasSum f (∑' x, f x) := hf.of_norm.hasSum
      have h3 : Summable fun p : X × (Fin K → X) => f p.1 * ∏ i, f (p.2 i) :=
        summable_mul_of_summable_norm (f := f) (g := fun ε : Fin K → X => ∏ i, f (ε i)) hf ih.2
      have key : HasSum (fun p : X × (Fin K → X) => f p.1 * ∏ i, f (p.2 i))
          ((∑' x, f x) * (∑' x, f x) ^ K) := HasSum.mul (f := f)
            (g := fun ε : Fin K → X => ∏ i, f (ε i)) h1 ih.1 h3
      have key' : HasSum ((fun ε : Fin (K + 1) → X => ∏ i, f (ε i)) ∘ e)
          ((∑' x, f x) * (∑' x, f x) ^ K) := by rw [hcomp]; exact key
      rw [pow_succ']
      exact e.hasSum_iff.mp key'
    · rw [← e.summable_iff]
      have hcompn : (fun ε : Fin (K + 1) → X => ‖∏ i, f (ε i)‖) ∘ e =
          fun p : X × (Fin K → X) => ‖f p.1 * ∏ i, f (p.2 i)‖ := by
        funext p
        exact congrArg norm (congrFun hcomp p)
      rw [hcompn]
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_mul_le _ _) ?_
      exact Summable.mul_of_nonneg (f := fun x => ‖f x‖)
        (g := fun ε : Fin K → X => ‖∏ i, f (ε i)‖) hf ih.2
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

 

theorem hasSum_soupMass_mul_prod {X : Type*} {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) {Λ : ℝ}
    (hΛ : HasSum w Λ) {t : ℝ} (ht : 0 ≤ t) (g : X → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1) :
    HasSum (fun s : Soup X => (soupMass w Λ t s : ℂ) * ∏ i, g (s.2 i))
      (Complex.exp (-(t * Λ)) * Complex.exp (t * ∑' x, (w x : ℂ) * g x)) := by
  set f : X → ℂ := fun x => (t : ℂ) * ((w x : ℂ) * g x) with hf_def
  have hwn : ∀ x, ‖f x‖ ≤ t * w x := by
    intro x
    simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
      abs_of_nonneg (hw x)]
    calc t * (w x * ‖g x‖) ≤ t * (w x * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hg x) (hw x)) ht
      _ = t * w x := by ring
  have hfs : Summable fun x => ‖f x‖ :=
    Summable.of_nonneg_of_le (fun x => norm_nonneg _) hwn (hΛ.summable.mul_left t)
  set C : ℕ → ℂ := fun K => Complex.exp (-(t * Λ)) / (K.factorial : ℂ) with hC
  have hfun : ∀ K : ℕ, (fun ε : Fin K → X => (soupMass w Λ t ⟨K, ε⟩ : ℂ) * ∏ i, g (ε i)) =
      fun ε => C K * ∏ i, f (ε i) := by
    intro K
    funext ε
    simp only [soupMass, f, C, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_prod,
      Complex.ofReal_natCast, Complex.ofReal_exp, Complex.ofReal_neg]
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 2
    funext i
    ring
  have hfib : ∀ K : ℕ, HasSum (fun ε : Fin K → X => (soupMass w Λ t ⟨K, ε⟩ : ℂ) *
      ∏ i, g (ε i)) (C K * (∑' x, f x) ^ K) := by
    intro K
    rw [hfun K]
    exact ((hasSum_pi_prod f hfs K).1).mul_left (C K)
  have hCnorm : ∀ K : ℕ, ‖C K‖ = Real.exp (-(t * Λ)) / (K.factorial : ℝ) := by
    intro K
    simp only [C, norm_div, Complex.norm_natCast]
    rw [show (-( (t : ℂ) * Λ)) = ((-(t * Λ) : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
  have hnormfib : ∀ K : ℕ, HasSum (fun ε : Fin K → X =>
      ‖(soupMass w Λ t ⟨K, ε⟩ : ℂ) * ∏ i, g (ε i)‖)
      (Real.exp (-(t * Λ)) / (K.factorial : ℝ) * (∑' x, ‖f x‖) ^ K) := by
    intro K
    have hreal := (hasSum_pi_prod (R := ℝ) (fun x => ‖f x‖) (by simpa using hfs) K).1
    have hfun' : (fun ε : Fin K → X => ‖(soupMass w Λ t ⟨K, ε⟩ : ℂ) * ∏ i, g (ε i)‖) =
        fun ε => Real.exp (-(t * Λ)) / (K.factorial : ℝ) * ∏ i, ‖f (ε i)‖ := by
      funext ε
      have := congrFun (hfun K) ε
      rw [this, norm_mul, norm_prod, hCnorm]
    rw [hfun']
    exact hreal.mul_left _
  have hsumK : Summable fun K : ℕ => Real.exp (-(t * Λ)) / (K.factorial : ℝ) *
      (∑' x, ‖f x‖) ^ K := by
    have := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (∑' x, ‖f x‖)).summable.mul_left
      (Real.exp (-(t * Λ)))
    refine this.congr fun K => ?_
    ring
  have hsigma : Summable (fun s : Soup X => ‖(soupMass w Λ t s : ℂ) * ∏ i, g (s.2 i)‖) := by
    refine (summable_sigma_of_nonneg (fun s => norm_nonneg _)).mpr
      ⟨fun K => (hnormfib K).summable, ?_⟩
    refine hsumK.congr fun K => ?_
    exact ((hnormfib K).tsum_eq).symm
  have htot : HasSum (fun K : ℕ => C K * (∑' x, f x) ^ K)
      (Complex.exp (-(t * Λ)) * Complex.exp (∑' x, f x)) := by
    have := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (∑' x, f x)).mul_left
      (Complex.exp (-(t * Λ)))
    rw [← Complex.exp_eq_exp_ℂ] at this
    refine this.congr_fun fun K => ?_
    simp only [C]
    try ring
  have hf_tsum : (∑' x, f x) = t * ∑' x, (w x : ℂ) * g x := by
    simp only [f]
    rw [tsum_mul_left]
  rw [← hf_tsum]
  have hS := (hsigma.of_norm).hasSum
  have := hS.sigma hfib
  rw [htot.unique this]
  exact hS

 
theorem hasSum_soupMass {X : Type*} {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) {Λ : ℝ}
    (hΛ : HasSum w Λ) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (soupMass w Λ t) 1 := by
  have h := hasSum_soupMass_mul_prod hw hΛ ht (fun _ => 1) (by simp)
  simp only [Finset.prod_const_one, mul_one] at h
  have hre := Complex.hasSum_re h
  simp only [Complex.ofReal_re] at hre
  have hval : (Complex.exp (-(t * Λ)) * Complex.exp (t * ∑' x, (w x : ℂ))).re = 1 := by
    rw [← Complex.exp_add, ← Complex.ofReal_tsum, hΛ.tsum_eq]
    rw [show -( (t : ℂ) * Λ) + t * Λ = 0 by ring, Complex.exp_zero, Complex.one_re]
  rw [hval] at hre
  convert hre using 1
  try (funext s; push_cast; rfl)

 
theorem hasSum_soupMass_avoid {X : Type*} {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) {Λ : ℝ}
    (hΛ : HasSum w Λ) {t : ℝ} (ht : 0 ≤ t) (A : Set X) :
    HasSum ({s : Soup X | ∀ i, s.2 i ∉ A}.indicator (soupMass w Λ t))
      (Real.exp (-(t * ∑' x, A.indicator w x))) := by
  classical
  have h := hasSum_soupMass_mul_prod hw hΛ ht (fun x => if x ∈ A then 0 else 1)
    (fun x => by by_cases hx : x ∈ A <;> simp [hx])
  have hre := Complex.hasSum_re h
  have hsA : HasSum (A.indicator w) (∑' x, A.indicator w x) :=
    (hΛ.summable.indicator A).hasSum
  have hcomp : HasSum (fun x => w x - A.indicator w x) (Λ - ∑' x, A.indicator w x) :=
    hΛ.sub hsA
  have hval : (Complex.exp (-(t * Λ)) * Complex.exp (t * ∑' x, (w x : ℂ) *
      (if x ∈ A then 0 else 1))).re = Real.exp (-(t * ∑' x, A.indicator w x)) := by
    have hts : (∑' x, (w x : ℂ) * (if x ∈ A then 0 else 1)) =
        ((Λ - ∑' x, A.indicator w x : ℝ) : ℂ) := by
      rw [← hcomp.tsum_eq, Complex.ofReal_tsum]
      congr 1
      funext x
      by_cases hx : x ∈ A <;> simp [hx, Set.indicator]
    have e1 : -((t : ℂ) * Λ) = ((-(t * Λ) : ℝ) : ℂ) := by push_cast; ring
    have e2 : (t : ℂ) * ((Λ - ∑' x, A.indicator w x : ℝ) : ℂ) =
        ((t * (Λ - ∑' x, A.indicator w x) : ℝ) : ℂ) := by push_cast; ring
    rw [hts, e1, e2, ← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
      Complex.ofReal_re, ← Real.exp_add]
    congr 1
    ring
  rw [hval] at hre
  convert hre using 1
  funext s
  by_cases hs : ∀ i, s.2 i ∉ A
  · have : ∏ i, (if s.2 i ∈ A then (0 : ℂ) else 1) = 1 :=
      Finset.prod_eq_one fun i _ => by simp [hs i]
    rw [Set.indicator_of_mem (show s ∈ {s : Soup X | ∀ i, s.2 i ∉ A} from hs), this]
    simp
  · have hs' : ∃ i, s.2 i ∈ A := by
      by_contra hcon
      exact hs fun i hi => hcon ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hs'
    have : ∏ i, (if s.2 i ∈ A then (0 : ℂ) else 1) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [Set.indicator_of_notMem (show s ∉ {s : Soup X | ∀ i, s.2 i ∉ A} from hs), this]
    simp

end SupercriticalLQGUniqueness.B2.QPos
