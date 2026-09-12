/-
The Fourier layer of the local central limit theorem.

`torusBox d` is the torus `[-π,π]^d ⊆ (Fin d → ℝ)`.  This module proves the
recursion layer of the Fourier representation of the simple random-walk heat
kernel: the integral of a character of the torus over `torusBox d` is the
product of its one-dimensional integrals (`integral_box_exp_eq`), which is the
orthogonality of characters in the form the local central limit theorem needs
(the parity mode `z` contributes `2π` exactly when it vanishes, and `0`
otherwise).  The peeling lemma `integral_box_peel` reduces the `d`-dimensional
integral to the one-dimensional one coordinate at a time, which is how the
Fourier representation of `srwHeat` is built by recursion on `d`.
-/
import LatticeProb.Walk.Character
import LatticeProb.Site

namespace LatticeProb

open MeasureTheory

noncomputable section

def torusBox (d : ℕ) : Set (Fin d → ℝ) := Set.Icc (fun _ => (-Real.pi)) (fun _ => Real.pi)
theorem torusBox_image_piFinSuccAbove (d : ℕ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0) '' torusBox (d + 1)
      = Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    have hp' : (x 0, Fin.removeNth 0 x) = p := by
      simpa [MeasurableEquiv.piFinSuccAbove] using hp
    rw [← hp']
    refine Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨hx.1 0, hx.2 0⟩, ?_⟩
    refine Set.mem_Icc.mpr ⟨fun j => hx.1 j.succ, fun j => hx.2 j.succ⟩
  · rintro ⟨h1, h2⟩
    simp only [Set.mem_Icc, torusBox] at h1 h2
    refine ⟨Fin.cons p.1 p.2, ?_, ?_⟩
    · constructor
      · intro i; induction i using Fin.cases with
        | zero => simpa using h1.1
        | succ j => simpa using h2.1 j
      · intro i; induction i using Fin.cases with
        | zero => simpa using h1.2
        | succ j => simpa using h2.2 j
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]
theorem torusBox_measurable (d : ℕ) : MeasurableSet (torusBox d) := measurableSet_Icc

theorem map_restrict_measurableEquiv {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    Measure.map e (μ.restrict s) = (Measure.map e μ).restrict (e '' s) := by
  ext t ht
  have hL : Measure.map e (μ.restrict s) t = μ (s ∩ e ⁻¹' t) := by
    rw [Measure.map_apply e.measurable ht, Measure.restrict_apply (e.measurable ht)]
    exact congrArg μ (Set.inter_comm _ _)
  have hpre : e ⁻¹' (t ∩ e '' s) = s ∩ e ⁻¹' t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨h1, y, hy, heq⟩
      exact ⟨by have := e.injective heq; subst this; exact hy, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, x, h1, rfl⟩
  have hR : ((Measure.map e μ).restrict (e '' s)) t = μ (s ∩ e ⁻¹' t) := by
    rw [Measure.restrict_apply ht,
      Measure.map_apply e.measurable (MeasurableSet.inter ht ((MeasurableEquiv.measurableSet_image e).mpr hs)), hpre]
  rw [hL, hR]

theorem torusBox_symm_image_piFinSuccAbove (d : ℕ) : torusBox (d+1) = (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (d+1))).symm '' (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d) := by
  ext x
  constructor
  · intro hx
    exact ⟨(MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (d+1))) x,
      torusBox_image_piFinSuccAbove d ▸ Set.mem_image_of_mem _ hx, MeasurableEquiv.symm_apply_apply (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (d+1))) x⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨z, hz, hez⟩ := (torusBox_image_piFinSuccAbove d) ▸ hy
    have : x = z := by
      rw [← hez] at hxy
      rw [MeasurableEquiv.symm_apply_apply (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (d+1))) z] at hxy
      exact hxy.symm
    rw [this]; exact hz

theorem integral_torusBox_peel {d : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin (d + 1) → ℝ) → E) (hf : Integrable f (volume.restrict (torusBox (d + 1)))) :
    ∫ θ in torusBox (d + 1), f θ
      = ∫ t in Set.Icc (-Real.pi) Real.pi, ∫ θ in torusBox d, f (Fin.cons t θ) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (d+1)) with he
  have hmp : MeasurePreserving (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ)) volume volume :=
    MeasurePreserving.symm e (measurePreserving_piFinSuccAbove (fun _ : Fin (d+1) => volume) 0)
  have hsm : MeasurableSet (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d) :=
    MeasurableSet.prod (measurableSet_Icc : MeasurableSet (Set.Icc (-Real.pi) Real.pi)) (torusBox_measurable d)
  have h1 : torusBox (d+1) = e.symm '' (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d) := torusBox_symm_image_piFinSuccAbove d
  have hmap : Measure.map (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ)) volume = volume := hmp.map_eq
  have hv2 : volume.restrict (e.symm '' (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d))
      = Measure.map (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ)) (volume.restrict (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d)) := by
    rw [map_restrict_measurableEquiv e.symm volume _ hsm, hmap]
  have hmeas : Measure.map (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ)) (volume.restrict (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d))
      = volume.restrict (torusBox (d+1)) := by rw [map_restrict_measurableEquiv e.symm volume _ hsm, hmap, h1]
  have htriv : MeasurePreserving (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ))
      (volume.restrict (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d))
      (Measure.map (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ)) (volume.restrict (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d))) := ⟨e.symm.measurable, rfl⟩
  have h2 : ∫ θ in torusBox (d+1), f θ
      = ∫ p in Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d, f (e.symm p) := by
    rw [h1, hv2]
    exact (MeasurePreserving.integral_comp htriv (MeasurableEquiv.measurableEmbedding e.symm) f).symm
  have hrr : (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))).restrict (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d)
      = (volume.restrict (Set.Icc (-Real.pi) Real.pi)).prod (volume.restrict (torusBox d)) := by
    rw [show (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) = volume.prod volume from rfl, Measure.prod_restrict]
  have hint : Integrable (fun p : ℝ × (Fin d → ℝ) => f (e.symm p))
      ((volume.restrict (Set.Icc (-Real.pi) Real.pi)).prod (volume.restrict (torusBox d))) := by
    rw [← hrr]
    have hfm : Integrable f (Measure.map (e.symm : (ℝ × (Fin d → ℝ)) → (Fin (d+1) → ℝ)) (volume.restrict (Set.Icc (-Real.pi) Real.pi ×ˢ torusBox d))) := by rw [hmeas]; exact hf
    exact (MeasurePreserving.integrable_comp htriv hfm.aestronglyMeasurable).mpr hfm
  rw [h2, hrr, integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  have hcons : e.symm (t, θ) = Fin.cons t θ := by
    simp [he, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]
  simp only [hcons]


theorem char_integrable (d : ℕ) (z : Fin (d+1) → ℤ) :
    Integrable (fun θ : Fin (d+1) → ℝ => ∏ j, Complex.exp (Complex.ofReal (θ j * (z j : ℝ)) * Complex.I))
      (volume.restrict (torusBox (d+1))) := by
  have hfin : (MeasureTheory.volume : Measure (Fin (d+1) → ℝ)) (torusBox (d+1)) < ⊤ := by
    have h2 : Set.pi Set.univ (fun i => Set.Ioc (-Real.pi) Real.pi) =ᵐ[(MeasureTheory.volume : Measure (Fin (d+1) → ℝ))] Set.Icc (fun _ => (-Real.pi)) (fun _ => Real.pi) := by
      rw [← Set.pi_univ_Icc]
      exact MeasureTheory.Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ => volume)
    rw [show torusBox (d+1) = Set.Icc (fun _ => (-Real.pi)) (fun _ => Real.pi) from rfl, ← measure_congr h2, Real.volume_pi_Ioc]
    simp
  haveI : IsFiniteMeasure (volume.restrict (torusBox (d+1))) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
  · exact (continuous_finsetProd _ (fun j _ => by continuity)).aestronglyMeasurable
  · filter_upwards with θ
    have h1 : ‖∏ j, Complex.exp (Complex.ofReal (θ j * (z j : ℝ)) * Complex.I)‖ = 1 := by
      rw [norm_prod _ _, Finset.prod_eq_one (fun j _ => by rw [Complex.norm_exp]; simp [Complex.mul_im, Complex.ofReal_im])]
    rw [h1]

theorem integral_char_one (k : ℤ) :
    ∫ t in Set.Icc (-Real.pi) Real.pi, Complex.exp (Complex.ofReal (t * (k : ℝ)) * Complex.I)
      = if k = 0 then 2 * Real.pi else 0 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    simp
    norm_num [max_eq_left (by positivity : (0:ℝ) ≤ Real.pi + Real.pi)]
    ring
  · rw [if_neg hk]
    have heq : ∀ t : ℝ, Complex.exp (Complex.ofReal (t * (k:ℝ)) * Complex.I)
        = Complex.exp (Complex.ofReal ((k:ℝ) * t) * Complex.I) := fun t => by rw [mul_comm t (k:ℝ)]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall heq)]
    exact LatticeProb.integral_exp_int_mul_restrict k hk

/-- **Orthogonality of the characters on the torus, product form**: the integral
of the character of mode `z` over the torus `[-π,π]^d` is the product over the
coordinates of the one-dimensional integrals: `2π` in a vanishing coordinate,
`0` otherwise.  This is the base case of the Fourier representation of the
random-walk heat kernel: the kernel is the inverse Fourier transform of the
characters, and only the modes compatible with the parity of the walk survive.
-/
theorem integral_box_exp_eq (d : ℕ) (z : Fin d → ℤ) :
    ∫ θ in torusBox d, ∏ j, Complex.exp (Complex.ofReal (θ j * (z j : ℝ)) * Complex.I)
      = ∏ j, (if z j = 0 then 2 * Real.pi else 0) := by
  induction d with
    | zero =>
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      have h : (Set.Icc (fun _ : Fin 0 => (-Real.pi)) (fun _ : Fin 0 => Real.pi)) = (Set.univ : Set (Fin 0 → ℝ)) := by ext; simp
      rw [MeasureTheory.integral_const]
      simp only [torusBox]
      rw [h, Measure.restrict_univ]
      show ((Measure.pi fun _ => MeasureTheory.volume) Set.univ).toReal • (1:ℂ) = ↑1
      rw [Measure.pi_univ]
      simp
    | succ d ih =>
      rw [integral_torusBox_peel _ (char_integrable d z)]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      simp only [MeasureTheory.integral_const_mul]
      rw [ih (fun j => z j.succ)]
      rw [MeasureTheory.integral_mul_const]
      rw [integral_char_one (z 0)]
      split
      · simp
      · simp
end

/-- The volume of the torus box is `(2π)^d`. -/
theorem volume_torusBox (d : ℕ) :
    (MeasureTheory.volume : Measure (Fin d → ℝ)) (torusBox d)
      = ENNReal.ofReal ((2 * Real.pi) ^ d) := by
  have h1 : torusBox d = Set.univ.pi (fun _ : Fin d => Set.Icc (-Real.pi) Real.pi) := by
    rw [show torusBox d = Set.Icc (fun _ : Fin d => (-Real.pi)) (fun _ : Fin d => Real.pi) from rfl,
        ← Set.pi_univ_Icc]
  rw [h1]
  have h2 : Set.univ.pi (fun _ : Fin d => Set.Ioc (-Real.pi) Real.pi)
      =ᵐ[(MeasureTheory.volume : Measure (Fin d → ℝ))]
        Set.univ.pi (fun _ : Fin d => Set.Icc (-Real.pi) Real.pi) :=
    MeasureTheory.Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ : Fin d => volume)
  rw [← MeasureTheory.measure_congr h2, Real.volume_pi_Ioc]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring]
  rw [ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 2 * Real.pi)]

/-- The integral of the trivial character over the torus box is `(2π)^d`. -/
theorem integral_char_trivial (d : ℕ) :
    (∫ θ in torusBox d, ∏ j, Complex.exp (Complex.ofReal (θ j * ((0 : Fin d → ℤ) j : ℝ)) * Complex.I))
      = (2 * Real.pi) ^ d := by
  have h1 : ∀ θ : Fin d → ℝ, ∏ j, Complex.exp (Complex.ofReal (θ j * ((0 : Fin d → ℤ) j : ℝ)) * Complex.I) = 1 := by
    intro θ
    refine Finset.prod_eq_one (fun j _ => ?_)
    simp
  have h2 : (∫ θ in torusBox d, ∏ j, Complex.exp (Complex.ofReal (θ j * ((0 : Fin d → ℤ) j : ℝ)) * Complex.I))
      = ∫ θ in torusBox d, (1 : ℂ) := MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h1)
  rw [h2, integral_const]
  have h3 : (MeasureTheory.volume (torusBox d)).toReal = (2 * Real.pi) ^ d := by
    rw [volume_torusBox d, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (2 * Real.pi) ^ d)]
  have h4 : (MeasureTheory.volume.restrict (torusBox d)).real Set.univ = (2 * Real.pi) ^ d := by
    show ((MeasureTheory.volume.restrict (torusBox d)) Set.univ).toReal = (2 * Real.pi) ^ d
    rw [Measure.restrict_apply_univ]
    exact h3
  rw [h4]
  simp

/-- The normalized character integral is the Kronecker delta at the origin. -/
theorem integral_char_delta (d : ℕ) (x : Site d) :
    (∫ θ in torusBox d, ∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
      / (2 * Real.pi) ^ d
      = if x = 0 then 1 else 0 := by
  rw [integral_box_exp_eq d x]
  by_cases hx : x = 0
  · subst hx
    have h1 : ∏ j, (if (0 : Fin d → ℤ) j = 0 then 2 * Real.pi else 0) = (2 * Real.pi) ^ d := by
      simp [Finset.prod_const]
    rw [h1, if_pos rfl]
    norm_num [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_one]
  · have h0 : ∏ j, (if x j = 0 then 2 * Real.pi else 0) = 0 := by
      by_contra hne
      have hall : ∀ j, x j = 0 := by
        intro j
        by_contra hxj
        have hz : (if x j = 0 then 2 * Real.pi else 0) = 0 := if_neg hxj
        exact hne (Finset.prod_eq_zero (Finset.mem_univ j) hz)
      exact hx (funext hall)
    rw [h0, if_neg hx]
    simp

/-- The character of `x + v` factors as the character of `x` times the
character of `v`. -/
theorem char_add (d : ℕ) (x : Site d) (v : Site d) (θ : Fin d → ℝ) :
    ∏ j, Complex.exp (Complex.ofReal (θ j * ((x j + v j : ℤ) : ℝ)) * Complex.I)
      = (∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
        * (∏ j, Complex.exp (Complex.ofReal (θ j * ((v j : ℤ) : ℝ)) * Complex.I)) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem char_sub (d : ℕ) (θ : Fin d → ℝ) (x y : Site d) :
    (∏ j, Complex.exp (Complex.ofReal (θ j * ((y j : ℤ) : ℝ)) * Complex.I))
      = (∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
        * ∏ j, Complex.exp (Complex.ofReal (θ j * (((y - x) j : ℤ) : ℝ)) * Complex.I) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.sub_apply]
  push_cast
  ring

theorem char_unit (d : ℕ) (θ : Fin d → ℝ) (i : Fin d) :
    ∏ j, Complex.exp (Complex.ofReal (θ j * (((unit i) j : ℤ) : ℝ)) * Complex.I)
      = Complex.exp (Complex.ofReal (θ i) * Complex.I) := by
  have h1 : ((unit i) i : ℤ) = 1 := by simp [unit]
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin d)), j ≠ i →
      Complex.exp (Complex.ofReal (θ j * (((unit i) j : ℤ) : ℝ)) * Complex.I) = 1 := by
    intro j _ hj
    have huj : (unit i) j = 0 := by simp [unit, hj]
    simp [huj, Complex.exp_zero, mul_zero]
  rw [Finset.prod_eq_single i h0 (fun h => absurd (Finset.mem_univ i) h), h1]; norm_num

/-- The character of the negated unit vector. -/
theorem char_neg_unit (d : ℕ) (θ : Fin d → ℝ) (i : Fin d) :
    ∏ j, Complex.exp (Complex.ofReal (θ j * (((-unit i) j : ℤ) : ℝ)) * Complex.I)
      = Complex.exp (-(Complex.ofReal (θ i) * Complex.I)) := by
  have h1 : ((-unit i) i : ℤ) = -1 := by simp [unit]
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin d)), j ≠ i →
      Complex.exp (Complex.ofReal (θ j * (((-unit i) j : ℤ) : ℝ)) * Complex.I) = 1 := by
    intro j _ hj
    have huj : (-unit i) j = 0 := by
      have hu : (unit i) j = 0 := by simp [unit, hj]
      simp [Pi.neg_apply, hu]
    simp [huj, Complex.exp_zero, mul_zero]
  rw [Finset.prod_eq_single i h0 (fun h => absurd (Finset.mem_univ i) h), h1]
  congr 1
  push_cast
  ring
/-- The two-point average of the exponential is the cosine. -/
theorem exp_pair_eq_cos (z : ℂ) :
    Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I)) = 2 * Complex.cos z := by
  rw [Complex.cos]
  ring
/-- The Fourier multiplier of the simple random walk: the average of the
character over the `2d` neighbours of `x` equals the character at `x` times
the average of the cosines. -/
theorem char_neighbour_avg_eq_avg_cos (d : ℕ) (θ : Fin d → ℝ) (x : Site d) :
    (∑ i : Fin d, ((∏ j, Complex.exp (Complex.ofReal (θ j * (((x + unit i) j : ℤ) : ℝ)) * Complex.I))
      + ∏ j, Complex.exp (Complex.ofReal (θ j * (((x - unit i) j : ℤ) : ℝ)) * Complex.I))) / (2 * d)
      = (∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
        * (∑ i : Fin d, Real.cos (θ i)) / d := by
  have hsum : ∀ i : Fin d,
      (∏ j, Complex.exp (Complex.ofReal (θ j * (((x + unit i) j : ℤ) : ℝ)) * Complex.I))
      + ∏ j, Complex.exp (Complex.ofReal (θ j * (((x - unit i) j : ℤ) : ℝ)) * Complex.I)
      = (∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
        * (2 * Complex.ofReal (Real.cos (θ i))) := by
    intro i
    have hp := char_sub d θ x (x + unit i)
    have hm := char_sub d θ x (x - unit i)
    have hpx : (x + unit i) - x = unit i := by abel
    have hmx : (x - unit i) - x = -unit i := by abel
    rw [hp, hm, hpx, hmx, char_unit d θ i, char_neg_unit d θ i, ← mul_add,
      exp_pair_eq_cos, ← Complex.ofReal_cos]
  rw [Finset.sum_congr rfl (fun i _ => hsum i), ← Finset.mul_sum, ← Finset.mul_sum,
    ← Complex.ofReal_sum]
  field_simp
  have hcomm : ∀ j, Complex.exp (Complex.I * ↑(θ j * ↑(x j)))
      = Complex.exp (↑(θ j * ↑(x j)) * Complex.I) := fun j => by congr 1; ring
  rw [Finset.prod_congr rfl (fun j _ => hcomm j)]
  ring

end LatticeProb
