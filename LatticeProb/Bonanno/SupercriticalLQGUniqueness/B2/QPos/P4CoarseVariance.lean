/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4CoarseVariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4BoxIncrement

 















set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos.P4

open P3

theorem interiorSites_eq_sqBox (N : ℕ) : interiorSites N = sqBox 0 (2 ^ N) := by
  ext c
  rw [mem_interiorSites_iff, mem_sqBox]
  unfold interiorRadius
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero, abs_lt]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem shiftSet_sqBox (z w : ℤ × ℤ) (r : ℤ) : shiftSet (sqBox z r) w = sqBox (z + w) r := by
  ext c
  rw [mem_shiftSet, mem_sqBox, mem_sqBox]
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rwa [show c.1 - (z.1 + w.1) = c.1 - w.1 - z.1 by ring],
      by rwa [show c.2 - (z.2 + w.2) = c.2 - w.2 - z.2 by ring]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rwa [show c.1 - w.1 - z.1 = c.1 - (z.1 + w.1) by ring],
      by rwa [show c.2 - w.2 - z.2 = c.2 - (z.2 + w.2) by ring]⟩

theorem shiftSet_shiftSet (U : Finset (ℤ × ℤ)) (w : ℤ × ℤ) :
    shiftSet (shiftSet U (-w)) w = U := by
  ext c
  rw [mem_shiftSet, mem_shiftSet]
  simp

theorem incr_shift (U : Finset (ℤ × ℤ)) (w a b : ℤ × ℤ) :
    incr (shiftSet U w) (a + w) (b + w) = incr U a b := by
  unfold incr
  rw [green_shift, green_shift, green_shift, green_shift]

 
theorem incr_le_incr_sqBox {N : ℕ} {z : ℤ × ℤ} {V : Finset (ℤ × ℤ)}
    (hV : V ⊆ sqBox z (2 ^ N)) {x y : ℤ × ℤ} (hx : x ∈ V) (hy : y ∈ V) :
    incr V x y ≤ incr (sqBox z (2 ^ N)) x y := by
  set V' := shiftSet V (-z)
  have hV' : V' ⊆ interiorSites N := by
    intro c hc
    rw [interiorSites_eq_sqBox]
    rw [mem_shiftSet] at hc
    have := hV hc
    rw [mem_sqBox] at this ⊢
    simpa using this
  have hx' : x - z ∈ V' := by rw [mem_shiftSet]; simpa using hx
  have hy' : y - z ∈ V' := by rw [mem_shiftSet]; simpa using hy
  have h := incr_le_incr_box hV' hx' hy'
  have e1 : incr V x y = incr V' (x - z) (y - z) := by
    have := incr_shift V' z (x - z) (y - z)
    rw [shiftSet_shiftSet] at this
    simpa using this
  have e2 : incr (sqBox z (2 ^ N)) x y = incr (interiorSites N) (x - z) (y - z) := by
    have := incr_shift (interiorSites N) z (x - z) (y - z)
    have hset : shiftSet (interiorSites N) z = sqBox z (2 ^ N) := by
      rw [interiorSites_eq_sqBox, shiftSet_sqBox, zero_add]
    rw [hset] at this
    simpa using this
  rw [e1, e2]
  exact h

 
def coarseVarConst : ℝ := 4 * Real.pi * incrConst

theorem coarseVarConst_pos : 0 < coarseVarConst := by
  unfold coarseVarConst; have := incrConst_pos; positivity

 
def boxSites (n : ℕ) (z : ℤ × ℤ) (L : ℤ) : Finset (DGFFSite n) := siteFilter n (sqBox z L)

 
theorem coarse_increment_variance (n a : ℕ) (z : ℤ × ℤ)
    (hQ : sqBox z (2 ^ (a + 4)) ⊆ interiorSites n)
    (i j : {c : DGFFSite n // c ∈ boxSites n z (2 ^ (a + 4))})
    (hi1 : 8 * |i.1.1.1 - z.1| ≤ 6 * 2 ^ (a + 4)) (hi2 : 8 * |i.1.1.2 - z.2| ≤ 6 * 2 ^ (a + 4))
    (hj1 : 8 * |j.1.1.1 - z.1| ≤ 6 * 2 ^ (a + 4)) (hj2 : 8 * |j.1.1.2 - z.2| ≤ 6 * 2 ^ (a + 4))
    (d : ℕ) (hd1 : |i.1.1.1 - j.1.1.1| ≤ d) (hd2 : |i.1.1.2 - j.1.1.2| ≤ d) :
    Var[fun h : EuclideanSpace ℝ (DGFFSite n) =>
        boxHarmonicField n (boxInnerOuterEquiv n (boxSites n z (2 ^ (a + 4)))) h i -
          boxHarmonicField n (boxInnerOuterEquiv n (boxSites n z (2 ^ (a + 4)))) h j;
        boxDGFF n] ≤ coarseVarConst * d / (2 ^ (a + 4) : ℝ) := by
  set ℓ : ℕ := 2 ^ (a + 1) with hℓdef
  have hℓ : 2 ≤ ℓ := by
    rw [hℓdef, pow_succ]; have := Nat.one_le_two_pow (n := a); omega
  have hL : ((2 : ℤ) ^ (a + 4)) = 8 * (ℓ : ℤ) := by
    rw [hℓdef]; push_cast; ring
  have hinner : innerSet n (boxSites n z (2 ^ (a + 4))) = sqBox z (2 ^ (a + 4)) :=
    innerSet_siteFilter hQ
  have hvar := harmonic_increment_variance_eq_green n (boxSites n z (2 ^ (a + 4))) i j
  rw [hinner] at hvar
  rw [hvar]
  
  have e6 : (6 : ℤ) * 2 ^ (a + 4) = 8 * (6 * ℓ) := by rw [hL]; ring
  have hx1 : |i.1.1.1 - z.1| ≤ 6 * ℓ := by linarith
  have hx2 : |i.1.1.2 - z.2| ≤ 6 * ℓ := by linarith
  have hy1 : |j.1.1.1 - z.1| ≤ 6 * ℓ := by linarith
  have hy2 : |j.1.1.2 - z.2| ≤ 6 * ℓ := by linarith
  
  have hzin : z ∈ interiorSites n := hQ (by
    rw [mem_sqBox]; simp only [sub_self, abs_zero]; constructor <;> positivity)
  have hbig : interiorSites n ⊆ sqBox z (4 ^ n * (8 * ℓ)) := by
    intro c hc
    rw [mem_interiorSites_iff] at hc hzin
    unfold interiorRadius at hc hzin
    rw [mem_sqBox]
    have h4 : (2 : ℤ) ^ n * 2 ^ n ≤ 4 ^ n := by rw [← mul_pow]; norm_num
    have h1 : (1 : ℤ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hl : (2 : ℤ) ≤ ℓ := by exact_mod_cast hℓ
    have hb : (2 : ℤ) * 2 ^ n ≤ 4 ^ n * (8 * ℓ) := by nlinarith
    constructor <;> rw [abs_lt] <;> constructor <;> linarith [hc.1, hc.2.1, hc.2.2.1,
      hc.2.2.2, hzin.1, hzin.2.1, hzin.2.2.1, hzin.2.2.2]
  have hpow' : (4 : ℤ) ^ n * 2 ^ (a + 4) = 2 ^ (2 * n + (a + 4)) := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
  rw [← hL, hpow'] at hbig
  have hxD : i.1.1 ∈ interiorSites n := i.1.2
  have hyD : j.1.1 ∈ interiorSites n := j.1.2
  have hray := incr_le_incr_sqBox hbig hxD hyD
  have hconc := incr_concentric_le z ℓ hℓ n hx1 hx2 hy1 hy2 d hd1 hd2
  rw [← hL, hpow'] at hconc
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hℓR : ((2 : ℝ) ^ (a + 4)) = 8 * ℓ := by
    have := hL; exact_mod_cast this
  calc Real.pi / 2 * (incr (interiorSites n) i.1.1 j.1.1 - incr (sqBox z (2 ^ (a + 4))) i.1.1 j.1.1)
      ≤ Real.pi / 2 * (incrConst * d / ℓ) := by
        gcongr
        linarith
    _ = coarseVarConst * d / (2 ^ (a + 4) : ℝ) := by
        rw [hℓR]
        unfold coarseVarConst
        have : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
        field_simp
        ring

end SupercriticalLQGUniqueness.B2.QPos.P4
