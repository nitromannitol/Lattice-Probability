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
import LatticeProb.Walk.Basic
import LatticeProb.Walk.SRW
import LatticeProb.Walk.Fourier
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

/-- The sum over all `2d` directions of the character at `x + dirVec a`
equals the character at `x` times twice the sum of the cosines. -/
theorem char_dir_sum (d : ℕ) (θ : Fin d → ℝ) (x : Site d) :
    ∑ a : Dir d, ∏ j, Complex.exp (Complex.ofReal (θ j * (((x + dirVec a) j : ℤ) : ℝ)) * Complex.I)
      = (∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
        * (2 * ∑ i : Fin d, Real.cos (θ i)) := by
  rw [show (Finset.univ : Finset (Dir d)) = Finset.univ ×ˢ Finset.univ from rfl, Finset.sum_product]
  have hpair : ∀ i : Fin d,
      (∏ j, Complex.exp (Complex.ofReal (θ j * (((x + dirVec (i, true)) j : ℤ) : ℝ)) * Complex.I))
      + (∏ j, Complex.exp (Complex.ofReal (θ j * (((x + dirVec (i, false)) j : ℤ) : ℝ)) * Complex.I))
      = (∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
        * (2 * Complex.ofReal (Real.cos (θ i))) := by
    intro i
    have hp := char_sub d θ x (x + dirVec (i, true))
    have hm := char_sub d θ x (x + dirVec (i, false))
    have hpt : (x + dirVec (i, true)) - x = unit i := by
      funext j; by_cases hji : j = i <;> simp [dirVec, unit, hji]
    have hmt : (x + dirVec (i, false)) - x = -unit i := by
      funext j; by_cases hji : j = i <;> simp [dirVec, unit, hji]
    rw [hp, hm, hpt, hmt, char_unit d θ i, char_neg_unit d θ i, ← mul_add, exp_pair_eq_cos, ← Complex.ofReal_cos]
  have hbool : ∀ i : Fin d, ∑ y : Bool, ∏ j, Complex.exp (Complex.ofReal (θ j * (((x + dirVec (i, y)) j : ℤ) : ℝ)) * Complex.I)
      = (∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
        * (2 * Complex.ofReal (Real.cos (θ i))) := by
    intro i; simp_rw [← hpair i]; simp
  simp_rw [hbool, Complex.ofReal_sum]
  simp only [Finset.mul_sum]

/-- Pointwise: the character at x times the (j+1)-st power of the multiplier
equals the Dir-average of the characters at x + dirVec a times the j-th
power. -/
theorem fourier_integrand_succ (d : ℕ) (j : ℕ) (x : Site d) (θ : Fin d → ℝ) :
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
        * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ (j + 1)
    = (∑ a : Dir d, (∏ k, Complex.exp (Complex.ofReal (θ k * (((x + dirVec a) k : ℤ) : ℝ)) * Complex.I))
        * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j) / (2 * d) := by
  have h := char_dir_sum d θ x
  rw [← Finset.sum_mul, h, pow_succ]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · simp [show d = 0 by omega]
  · have hd' : ((d : ℕ) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd)
    have h2d : (2 * (d : ℂ)) ≠ 0 := by
      exact mul_ne_zero two_ne_zero hd'
    field_simp
    have hcomm : ∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I)
        = ∏ k, Complex.exp (Complex.I * Complex.ofReal (θ k * ((x k : ℤ) : ℝ))) := by
      refine Finset.prod_congr rfl (fun k _ => ?_)
      congr 1; ring
    rw [hcomm]
    ring

/-- The finite Dir-sum of integrals equals the integral of the Dir-sum,
given integrability of each summand. -/
theorem fourier_swap (d : ℕ)
    (g : Dir d → (Fin d → ℝ) → ℂ)
    (hint : ∀ a : Dir d, Integrable (g a) (volume.restrict (torusBox d))) :
    (∑ a : Dir d, ∫ θ in torusBox d, g a θ) = ∫ θ in torusBox d, ∑ a : Dir d, g a θ :=
  by rw [MeasureTheory.integral_finsetSum Finset.univ (fun a _ => hint a)]

/-- The Brownian constant is nonzero as a complex number. -/
theorem two_pi_pow_ne_zero (d : ℕ) : ((2 * Real.pi) ^ d : ℂ) ≠ 0 :=
  pow_ne_zero d (mul_ne_zero two_ne_zero (by exact_mod_cast (ne_of_gt Real.pi_pos)))

/-- The final divisor algebra of the Fourier representation step. -/
theorem fourier_final_algebra (d : ℕ) (hd : 1 ≤ d) (A : ℂ) :
    (A * (2 * (d : ℂ))) / ((2 * Real.pi) ^ d * (2 * (d : ℂ))) = A / (2 * Real.pi) ^ d := by
  have hp : ((2 * Real.pi) ^ d : ℂ) ≠ 0 := two_pi_pow_ne_zero d
  have hd' : ((d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (by omega))
  have h2d : (2 * (d : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hd'
  field_simp

/-- The Fourier integrand is strongly measurable on the torus box. -/
theorem fourier_integrand_aemeasurable (d : ℕ) (j : ℕ) (x : Site d) :
    AEStronglyMeasurable (fun θ : Fin d → ℝ ↦
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
      * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j)
      (volume.restrict (torusBox d)) := by
  fun_prop

/-- The Fourier integrand is bounded by one in norm. -/
theorem fourier_integrand_norm_le_one (d : ℕ) (j : ℕ) (x : Site d)
    (θ : Fin d → ℝ) :
    ‖(∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
      * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j‖ ≤ 1 := by
  have hle : |(∑ i : Fin d, Real.cos (θ i))| ≤ (d : ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs (fun i => Real.cos (θ i)) Finset.univ) ?_
    refine le_trans (Finset.sum_le_sum (fun i _ => abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have havg : |(∑ i : Fin d, Real.cos (θ i))| / (d : ℝ) ≤ 1 :=
    div_le_one_of_le₀ hle (Nat.cast_nonneg d)
  have hd : |(d : ℝ)| = (d : ℝ) := abs_of_nonneg (Nat.cast_nonneg d)
  have h1 : ‖Complex.ofReal (∑ i : Fin d, Real.cos (θ i))‖ = |(∑ i : Fin d, Real.cos (θ i))| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖((d : ℕ) : ℂ)‖ = |(d : ℝ)| := by simp
  apply le_trans (norm_mul_le _ _)
  have ha : ‖(∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))‖ ≤ 1 := by
    rw [norm_prod]
    simp [Complex.norm_exp]
  apply mul_le_one₀
  · exact ha
  · exact norm_nonneg _
  · rw [norm_pow, norm_div, h1, h2, hd]
    exact pow_le_one₀ (div_nonneg (abs_nonneg _) (Nat.cast_nonneg d)) havg

/-- The Fourier integrand is integrable: it is bounded by one on a finite box. -/
theorem fourier_integrand_integrable (d : ℕ) (j : ℕ) (x : Site d) :
    Integrable (fun θ : Fin d → ℝ ↦
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
      * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j)
      (volume.restrict (torusBox d)) := by
  have hfin : (MeasureTheory.volume : Measure (Fin d → ℝ)) (torusBox d) < ⊤ := by
    have h2 : Set.pi Set.univ (fun i => Set.Ioc (-Real.pi) Real.pi) =ᵐ[(MeasureTheory.volume : Measure (Fin d → ℝ))] Set.Icc (fun _ => (-Real.pi)) (fun _ => Real.pi) := by
      rw [← Set.pi_univ_Icc]
      exact MeasureTheory.Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ => volume)
    rw [show torusBox d = Set.Icc (fun _ => (-Real.pi)) (fun _ => Real.pi) from rfl, ← measure_congr h2, Real.volume_pi_Ioc]
    simp
  haveI : IsFiniteMeasure (volume.restrict (torusBox d)) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
  · exact fourier_integrand_aemeasurable d j x
  · filter_upwards with θ
    exact fourier_integrand_norm_le_one d j x θ

/-- The Fourier representation of the simple random-walk heat kernel:
the kernel is the torus integral of the character times the j-th power
of the cosine-average multiplier, divided by the Brownian constant. -/
theorem srwHeat_eq_fourier {d : ℕ} (hd : 1 ≤ d)
    (j : ℕ) (x : Site d) :
    (srwHeat d j x : ℂ) =
      (∫ θ in torusBox d, (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
        * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j) / (2 * Real.pi) ^ d := by
  have hint : ∀ (j : ℕ) (x : Site d),
    Integrable (fun θ => (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
      * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j) (volume.restrict (torusBox d)) :=
    fun j x => fourier_integrand_integrable d j x
  induction j generalizing x with
  | zero =>
      rw [srwHeat_zero]
      simp only [pow_zero, mul_one]
      rw [integral_char_delta d x]
      by_cases hx : x = 0 <;> simp [hx]
  | succ j ih =>
      rw [srwHeat_succ_eq_sum_dir]
      have hsum : (((∑ a : Dir d, srwHeat d j (x + dirVec a)) / (2 * (d : ℝ)) : ℝ) : ℂ)
          = ((∑ a : Dir d, ∫ θ in torusBox d,
              (∏ k, Complex.exp (Complex.ofReal (θ k * (((x + dirVec a) k : ℤ) : ℝ)) * Complex.I))
                * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j)) / ((2 * Real.pi) ^ d * (2 * (d : ℝ))) := by
        rw [Complex.ofReal_div, Complex.ofReal_sum]
        show (∑ a : Dir d, ((srwHeat d j (x + dirVec a) : ℝ) : ℂ)) / Complex.ofReal (2 * (d : ℝ)) = _
        simp only [Finset.sum_div]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [ih (x + dirVec a), div_div]
        push_cast
        ring
      rw [hsum]
      rw [fourier_swap d (fun a θ => (∏ k, Complex.exp (Complex.ofReal (θ k * (((x + dirVec a) k : ℤ) : ℝ)) * Complex.I)) * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j) (fun a => hint j (x + dirVec a))]
      have hI : (∫ θ in torusBox d, ∑ a : Dir d,
            (∏ k, Complex.exp (Complex.ofReal (θ k * (((x + dirVec a) k : ℤ) : ℝ)) * Complex.I))
              * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j)
          = ∫ θ in torusBox d,
            (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
              * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ (j + 1) * (2 * (d : ℂ)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
        show (∑ a : Dir d, (∏ k, Complex.exp (Complex.ofReal (θ k * (((x + dirVec a) k : ℤ) : ℝ)) * Complex.I))
            * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ j)
          = (∏ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I))
            * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ (j + 1) * (2 * (d : ℂ))
        rw [fourier_integrand_succ d j x θ]
        have h2d : (2 * (d : ℂ)) ≠ 0 :=
          mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) hd)))
        field_simp
        have hcomm : ∀ k, Complex.exp (Complex.ofReal (θ k * ((x k : ℤ) : ℝ)) * Complex.I)
            = Complex.exp (Complex.I * Complex.ofReal (θ k * ((x k : ℤ) : ℝ))) := by
          intro k; congr 1; ring
        simp only [mul_comm]
        have hd' : ((d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) hd))
        rw [mul_div_cancel_left₀ _ hd']
      rw [hI, integral_mul_const]
      exact fourier_final_algebra d hd _

/-- The character at the antipodal point `θ + π` equals the character at `θ`
times the parity sign of `x`. -/
theorem char_antipode (d : ℕ) (x : Site d) (θ : Fin d → ℝ) :
    ∏ j, Complex.exp (Complex.ofReal ((θ j + Real.pi) * ((x j : ℤ) : ℝ)) * Complex.I)
      = (∏ j, Complex.exp (Complex.ofReal (θ j * ((x j : ℤ) : ℝ)) * Complex.I))
        * (∏ j, Complex.exp (Complex.ofReal (Real.pi * ((x j : ℤ) : ℝ)) * Complex.I)) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Strict contraction of the cosine away from the multiples of 2π:
for 0 < |t| < π, |cos t| < 1. -/
theorem abs_cos_lt_one (t : ℝ) (ht0 : 0 < |t|) (ht : |t| < Real.pi) :
    |Real.cos t| < 1 := by
  obtain ⟨h1, h2⟩ := abs_lt.mp ht
  rw [abs_lt]
  constructor
  · refine lt_of_le_of_ne (Real.neg_one_le_cos t) ?_
    intro hc
    have hc' : Real.cos t = -1 := hc.symm
    rw [Real.cos_eq_neg_one_iff] at hc'
    obtain ⟨k, hk⟩ := hc'
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    have hk' : ((k:ℤ) : ℝ) = (t - Real.pi) / (2 * Real.pi) := by
      field_simp
      linarith
    rcases em ((k:ℤ) < 0) with hk0 | hk0
    · have hk1 : k ≤ -1 := by omega
      have h0 : ((k:ℤ) : ℝ) ≤ -1 := by exact_mod_cast hk1
      rw [hk'] at h0
      nlinarith
    · have hk2 : 0 ≤ k := by omega
      have h0 : (0:ℝ) ≤ ((k:ℤ) : ℝ) := by exact_mod_cast hk2
      rw [hk'] at h0
      nlinarith
  · refine lt_of_le_of_ne (Real.cos_le_one t) ?_
    intro hc
    rw [Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)] at hc
    rw [hc] at ht0
    exact absurd ht0 (by simp)

/-- Near-zero cosine bound: for |t| ≤ π, cos t ≤ 1 - 2/π² · t². -/
theorem cos_le_one_sub_mul_sq (t : ℝ) (ht : |t| ≤ Real.pi) :
    Real.cos t ≤ 1 - 2 / Real.pi ^ 2 * t ^ 2 := by exact Real.cos_le_one_sub_mul_cos_sq ht

/-- The one-step characteristic function is bounded away from one when every
coordinate is at distance at least η from zero (and at most π). -/
theorem charFn_le_of_far (d : ℕ) (θ : Fin d → ℝ) (η : ℝ)
    (hd : 0 < d) (hη : 0 < η) (hθ : ∀ i, η ≤ |θ i|) (hpi : ∀ i, |θ i| ≤ Real.pi) :
    charFn d θ ≤ 1 - 2 * η ^ 2 / Real.pi ^ 2 := by
  have h1 : ∑ i : Fin d, Real.cos (θ i) ≤ (d : ℝ) * (1 - 2 * η ^ 2 / Real.pi ^ 2) := by
    refine le_trans (Finset.sum_le_sum (g := fun _ => (1 - 2 * η ^ 2 / Real.pi ^ 2 : ℝ)) (fun i _ => ?_)) ?_
    · have hle : Real.cos (θ i) ≤ 1 - 2 / Real.pi ^ 2 * (θ i) ^ 2 :=
        Real.cos_le_one_sub_mul_cos_sq (hpi i)
      have heta : η ^ 2 ≤ (θ i) ^ 2 := by
        have h2 : η ^ 2 ≤ |θ i| ^ 2 := pow_le_pow_left₀ (by linarith) (hθ i) 2
        rw [sq_abs] at h2
        exact h2
      have hkey : 2 * η ^ 2 / Real.pi ^ 2 ≤ 2 / Real.pi ^ 2 * (θ i) ^ 2 := by
        rw [div_mul_eq_mul_div]
        gcongr
      linarith
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  show (∑ i : Fin d, Real.cos (θ i)) / (d : ℝ) ≤ 1 - 2 * η ^ 2 / Real.pi ^ 2
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  linarith

/-- Near-zero cosine upper bound with the quartic remainder:
for |t| ≤ π, cos t ≤ 1 - t²/2 + t⁴/24.  This is the Gaussian-region
input to the local central limit theorem (the Fourier multiplier is bounded
by the heat multiplier up to the quartic term). -/
theorem cos_le_one_sub_half_sq_add_quartic (t : ℝ) (ht : |t| ≤ Real.pi) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  have heven : Real.cos t = Real.cos |t| := by
    rcases abs_cases t with h | h
    · rw [h.1]
    · rw [h.1, Real.cos_neg]
  rw [heven]
  have h0 : 0 ≤ |t| := abs_nonneg t
  have hpi : |t| ≤ Real.pi := ht
  have key : Real.cos |t| = 1 - 2 * Real.sin (|t| / 2) ^ 2 := by
    rw [show |t| = 2 * (|t| / 2) from by ring, Real.cos_two_mul, Real.sin_sq]
    ring
  rw [key]
  have hnn : 0 ≤ Real.sin (|t| / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin : |t| / 2 - (|t| / 2) ^ 3 / 6 ≤ Real.sin (|t| / 2) :=
    Real.sin_ge_sub_cube (by linarith)
  have hbase : 0 ≤ |t| / 2 - (|t| / 2) ^ 3 / 6 := by
    have hp2 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
    have hs2 : (|t| / 2) ^ 2 ≤ 6 := by nlinarith [hp2, hpi, h0]
    nlinarith [hs2]
  have hsq : (|t| / 2 - (|t| / 2) ^ 3 / 6) ^ 2 ≤ Real.sin (|t| / 2) ^ 2 :=
    pow_le_pow_left₀ hbase hsin 2
  have h2 : 2 * (|t| / 2 - (|t| / 2) ^ 3 / 6) ^ 2 ≤ 2 * Real.sin (|t| / 2) ^ 2 := by nlinarith [hsq]
  have h4 : 1 - 2 * (|t| / 2 - (|t| / 2) ^ 3 / 6) ^ 2 ≤ 1 - |t| ^ 2 / 2 + |t| ^ 4 / 24 := by
    have hu4 : (0 : ℝ) ≤ (|t| / 2) ^ 4 := by positivity
    have hu6 : (0 : ℝ) ≤ (|t| / 2) ^ 6 := by positivity
    nlinarith [hu4, hu6]
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have ht4 : t ^ 4 = |t| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 4)]
  rw [ht2, ht4]
  have hexp : (|t| / 2 - (|t| / 2) ^ 3 / 6) ^ 2 = |t| ^ 2 / 4 - |t| ^ 4 / 48 + |t| ^ 6 / 2304 := by ring
  nlinarith [hsq, hexp, sq_nonneg (|t| ^ 3)]




/-- The characteristic function at the antipodal point is its negative. -/
theorem charFn_antipode (d : ℕ) (θ : Fin d → ℝ) :
    charFn d (fun i => θ i + Real.pi) = - charFn d θ := by
  simp only [charFn]
  rw [← neg_div]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.cos_add]
  simp

/-- For any real x, 1 - x ≤ exp (-x). -/
theorem one_sub_le_exp_neg (x : ℝ) : 1 - x ≤ Real.exp (-x) := by
  have h := Real.add_one_le_exp (-x)
  linarith

/-- The Gaussian-region bound on the characteristic function: if every
coordinate of θ is at most π in absolute value, then with S = ∑ θ i ²,
charFn d θ ≤ 1 - S / (2d) + S ² / (24 d).  This is the quartic-remainder
form of the heat-kernel comparison, the pointwise input to the
Gaussian region of the local central limit theorem. -/
theorem charFn_le_gauss_quartic (d : ℕ) (hd : 0 < d) (θ : Fin d → ℝ)
    (hpi : ∀ i, |θ i| ≤ Real.pi) :
    charFn d θ ≤ 1 - (∑ i, θ i ^ 2) / (2 * d) + (∑ i, θ i ^ 2) ^ 2 / (24 * d) := by
  have hcos : ∑ i, Real.cos (θ i) ≤ ∑ i, (1 - θ i ^ 2 / 2 + θ i ^ 4 / 24) :=
    Finset.sum_le_sum (fun i _ => LatticeProb.cos_le_one_sub_half_sq_add_quartic _ (hpi i))
  have hA : ∑ i, θ i ^ 4 ≤ (∑ i, θ i ^ 2) ^ 2 := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ θ i ^ 2 := by intro i _; positivity
    have hconv : ∑ i, θ i ^ 4 = ∑ i, (θ i ^ 2) ^ 2 := Finset.sum_congr rfl (fun i _ => by ring)
    rw [hconv]
    exact Finset.sum_sq_le_sq_sum_of_nonneg hnn
  have hB : ∑ i, (1 - θ i ^ 2 / 2 + θ i ^ 4 / 24)
      ≤ (d : ℝ) - (∑ i, θ i ^ 2) / 2 + (∑ i, θ i ^ 2) ^ 2 / 24 := by
    have hC : ∑ i, (1 - θ i ^ 2 / 2 + θ i ^ 4 / 24)
        = (d : ℝ) - (∑ i, θ i ^ 2) / 2 + (∑ i, θ i ^ 4) / 24 := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hC]
    gcongr
  have hF : (∑ i, Real.cos (θ i)) / (d : ℝ)
      ≤ ((d : ℝ) - (∑ i, θ i ^ 2) / 2 + (∑ i, θ i ^ 2) ^ 2 / 24) / (d : ℝ) := by
    gcongr
    · exact le_trans hcos hB
  have hG : ((d : ℝ) - (∑ i, θ i ^ 2) / 2 + (∑ i, θ i ^ 2) ^ 2 / 24) / (d : ℝ)
      = 1 - (∑ i, θ i ^ 2) / (2 * d) + (∑ i, θ i ^ 2) ^ 2 / (24 * d) := by
    field_simp
  rw [hG] at hF
  exact hF

/-- For 0 ≤ u ≤ 1 and n : ℕ, (1 - u) ^ n ≤ exp (- n * u): the exponential
form of the Gaussian-region bound on the Fourier multiplier. -/
theorem one_sub_pow_le_exp (n : ℕ) (u : ℝ) (_hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 - u) ^ n ≤ Real.exp (- n * u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (1 - u) ^ (n + 1) ≤ Real.exp (-↑n * u) * (1 - u) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right ih (by linarith)
    have h2 : Real.exp (-↑n * u) * (1 - u) ≤ Real.exp (-↑(n + 1) * u) := by
      have h3 : Real.exp (-↑(n + 1) * u) = Real.exp (-↑n * u) * Real.exp (-u) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [h3]
      have h4 : 1 - u ≤ Real.exp (-u) := by
        have := Real.add_one_le_exp (-u)
        linarith
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    exact le_trans h1 h2

/-- Region-2 cosine bound: if η ≤ |t| ≤ π - η with 0 ≤ η, then
|cos t| ≤ cos η.  This is the intermediate-region input to the local
central limit theorem: away from both 0 and the antipode, the cosine is
bounded away from one in absolute value. -/
theorem abs_cos_le_cos_eta (η t : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ |t|) (ht : |t| ≤ Real.pi - η) :
    |Real.cos t| ≤ Real.cos η := by
  have heven : Real.cos t = Real.cos |t| := by
    rcases abs_cases t with h | h
    · rw [h.1]
    · rw [h.1, Real.cos_neg]
  have hu : |t| ≤ Real.pi := by linarith [Real.pi_pos]
  rcases lt_or_ge |t| (Real.pi / 2) with hmid | hmid
  · have hcospos : 0 ≤ Real.cos |t| :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
    rw [heven, abs_of_nonneg hcospos]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hη0 (by linarith) hη
  · have hcosn : Real.cos |t| ≤ 0 := by
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hmid (by linarith)
      simpa using this
    have hpi : Real.cos (Real.pi - |t|) = -Real.cos |t| := Real.cos_pi_sub |t|
    have hle : Real.cos (Real.pi - |t|) ≤ Real.cos η :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith) (by linarith)
    rw [heven, abs_of_nonpos hcosn, ← hpi]
    exact hle

/-- Gaussian-region exponential bound on the Fourier multiplier: in the
region where every |θ i| ≤ π/2, S = ∑ θ i ² ≤ 4 and S ≤ 2d, the n-th power
of the characteristic function satisfies charFn d θ ^ n ≤ exp (- n S / (3d)). -/
theorem charFn_pow_le_exp_gauss (d : ℕ) (hd : 0 < d) (n : ℕ) (θ : Fin d → ℝ)
    (hpi : ∀ i, |θ i| ≤ Real.pi / 2) (hS : (∑ i, θ i ^ 2) ≤ 4)
    (hS2 : (∑ i, θ i ^ 2) ≤ 2 * d) :
    charFn d θ ^ n ≤ Real.exp (- n * (∑ i, θ i ^ 2) / (3 * d)) := by
  have hd' : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hq : charFn d θ ≤ 1 - (∑ i, θ i ^ 2) / (2 * d) + (∑ i, θ i ^ 2) ^ 2 / (24 * d) :=
    LatticeProb.charFn_le_gauss_quartic d hd θ (fun i => (hpi i).trans (by linarith [Real.pi_pos]))
  have hunn : 0 ≤ ∑ i, θ i ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
  have hS4 : (∑ i, θ i ^ 2) ^ 2 ≤ 4 * ∑ i, θ i ^ 2 := by nlinarith [hunn, hS]
  have h1 : (∑ i, θ i ^ 2) ^ 2 / (24 * d) ≤ (∑ i, θ i ^ 2) / (6 * d) := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 24 * d) (by positivity : (0:ℝ) < 6 * d)]
    nlinarith [hS4, hd']
  have h2 : (∑ i, θ i ^ 2) / (6 * d) ≤ (∑ i, θ i ^ 2) / (2 * d) := by gcongr; nlinarith [hd']
  have hu0 : 0 ≤ (∑ i, θ i ^ 2) / (2 * d) - (∑ i, θ i ^ 2) ^ 2 / (24 * d) := by linarith
  have hBnn : (0:ℝ) ≤ (∑ i, θ i ^ 2) ^ 2 / (24 * d) := by positivity
  have hu1 : (∑ i, θ i ^ 2) / (2 * d) - (∑ i, θ i ^ 2) ^ 2 / (24 * d) ≤ 1 := by
    have hD : (∑ i, θ i ^ 2) / (2 * d) ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * d)]
      linarith
    linarith
  have hcnn : 0 ≤ charFn d θ := by
    have hcos : ∀ i, 0 ≤ Real.cos (θ i) := fun i => by
      exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (abs_le.mp (hpi i)).1 (abs_le.mp (hpi i)).2
    have hsum : 0 ≤ ∑ i, Real.cos (θ i) := Finset.sum_nonneg (fun i _ => hcos i)
    have : charFn d θ = (∑ i, Real.cos (θ i)) / (d:ℝ) := rfl
    rw [this]
    positivity
  have hkey : charFn d θ ^ n ≤ (1 - ((∑ i, θ i ^ 2) / (2 * d) - (∑ i, θ i ^ 2) ^ 2 / (24 * d))) ^ n := by
    refine pow_le_pow_left₀ hcnn ?_ n
    linarith
  have hexp := LatticeProb.one_sub_pow_le_exp n ((∑ i, θ i ^ 2) / (2 * d) - (∑ i, θ i ^ 2) ^ 2 / (24 * d)) hu0 hu1
  have hmono : Real.exp (- n * ((∑ i, θ i ^ 2) / (2 * d) - (∑ i, θ i ^ 2) ^ 2 / (24 * d))) ≤ Real.exp (- n * (∑ i, θ i ^ 2) / (3 * d)) := by
    apply Real.exp_le_exp.mpr
    have hE : (∑ i, θ i ^ 2) / (3 * d) ≤ (∑ i, θ i ^ 2) / (2 * d) - (∑ i, θ i ^ 2) ^ 2 / (24 * d) := by
      have hF : (∑ i, θ i ^ 2) / (3 * d) + (∑ i, θ i ^ 2) / (6 * d) = (∑ i, θ i ^ 2) / (2 * d) := by
        field_simp
        ring
      linarith
    have hG : (n:ℝ) * ((∑ i, θ i ^ 2) / (3 * d)) ≤ (n:ℝ) * ((∑ i, θ i ^ 2) / (2 * d) - (∑ i, θ i ^ 2) ^ 2 / (24 * d)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    rw [show (-n * (∑ i, θ i ^ 2)) / (3 * d) = -n * ((∑ i, θ i ^ 2) / (3 * d)) from by field_simp]
    linarith
  exact le_trans (le_trans hkey hexp) hmono

/-- Far-region exponential decay: for 0 < η ≤ π / √2 and n : ℕ,
(1 - 2 η ² / π ²) ^ n ≤ exp (- n η ² / π ²).  This converts the
far-region polynomial bound on the Fourier multiplier into its
exponential form. -/
theorem far_pow_le_exp (n : ℕ) (η : ℝ) (hη : 0 < η) (hηp : η ≤ Real.pi / Real.sqrt 2) :
    (1 - 2 * η ^ 2 / Real.pi ^ 2) ^ n ≤ Real.exp (- n * η ^ 2 / Real.pi ^ 2) := by
  have hpi2_pos : (0:ℝ) < Real.pi ^ 2 := by positivity
  have hu1 : 2 * η ^ 2 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_iff₀ hpi2_pos]
    have h1 : η ^ 2 ≤ (Real.pi / Real.sqrt 2) ^ 2 := pow_le_pow_left₀ (le_of_lt hη) hηp 2
    have hs : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
    have h2 : 2 * (Real.pi / Real.sqrt 2) ^ 2 = Real.pi ^ 2 := by
      rw [div_pow, hs]; ring
    nlinarith [h1, h2]
  have hnn : 0 ≤ 1 - 2 * η ^ 2 / Real.pi ^ 2 := by linarith
  have hbase : 1 - 2 * η ^ 2 / Real.pi ^ 2 ≤ Real.exp (-(2 * η ^ 2 / Real.pi ^ 2)) := by
    have := Real.add_one_le_exp (-(2 * η ^ 2 / Real.pi ^ 2))
    linarith
  have hpow : (1 - 2 * η ^ 2 / Real.pi ^ 2) ^ n ≤ (Real.exp (-(2 * η ^ 2 / Real.pi ^ 2))) ^ n :=
    pow_le_pow_left₀ hnn hbase n
  have hexp : (Real.exp (-(2 * η ^ 2 / Real.pi ^ 2))) ^ n = Real.exp (-↑n * (2 * η ^ 2 / Real.pi ^ 2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hmono : Real.exp (-↑n * (2 * η ^ 2 / Real.pi ^ 2)) ≤ Real.exp (-↑n * η ^ 2 / Real.pi ^ 2) := by
    apply Real.exp_le_exp.mpr
    have h1 : (0:ℝ) ≤ ↑n * (η ^ 2 / Real.pi ^ 2) := by positivity
    have h2 : -↑n * (2 * η ^ 2 / Real.pi ^ 2) = -2 * (↑n * (η ^ 2 / Real.pi ^ 2)) := by ring
    have h3 : -↑n * η ^ 2 / Real.pi ^ 2 = -(↑n * (η ^ 2 / Real.pi ^ 2)) := by ring
    rw [h2, h3]
    linarith
  exact le_trans hpow (le_trans hexp.le hmono)

/-- Region-2 multiplier bound: if every coordinate in F satisfies
η ≤ |θ i| ≤ π - η, then |charFn d θ| is at most
(d - |F| + |F| cos η) / d: each far coordinate costs the factor cos η. -/
theorem charFn_abs_le_of_region2 (d : ℕ) (hd : 0 < d) (θ : Fin d → ℝ) (η : ℝ)
    (hη0 : 0 ≤ η) (_hηp : η ≤ Real.pi / 2)
    (F : Finset (Fin d)) (hF : ∀ i ∈ F, η ≤ |θ i| ∧ |θ i| ≤ Real.pi - η) :
    |charFn d θ| ≤ ((d : ℝ) - F.card + F.card * Real.cos η) / d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ∑ i ∈ F, |Real.cos (θ i)| ≤ F.card * Real.cos η := by
    have h : ∑ i ∈ F, |Real.cos (θ i)| ≤ ∑ i ∈ F, Real.cos η :=
      Finset.sum_le_sum (fun i hi => LatticeProb.abs_cos_le_cos_eta η (θ i) hη0 (hF i hi).1 (hF i hi).2)
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have h2 : ∑ i ∈ Fᶜ, |Real.cos (θ i)| ≤ (d : ℝ) - F.card := by
    have h2a : ∑ i ∈ Fᶜ, |Real.cos (θ i)| ≤ ∑ i ∈ Fᶜ, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => Real.abs_cos_le_one _)
    have h2b : ∑ i ∈ Fᶜ, (1 : ℝ) = (d : ℝ) - F.card := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_compl, Fintype.card_fin]
      exact Nat.cast_sub (by simpa using Finset.card_le_univ F)
    exact le_trans h2a (le_of_eq h2b)
  show |(∑ i, Real.cos (θ i)) / (d : ℝ)| ≤ _
  rw [abs_div, abs_of_pos hd0]
  apply div_le_div_of_nonneg_right _ (le_of_lt hd0)
  calc |∑ i, Real.cos (θ i)|
      ≤ ∑ i, |Real.cos (θ i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ F, |Real.cos (θ i)| + ∑ i ∈ Fᶜ, |Real.cos (θ i)| := by
        rw [Finset.sum_add_sum_compl]
    _ ≤ F.card * Real.cos η + ((d : ℝ) - F.card) := add_le_add h1 h2
    _ = (d : ℝ) - F.card + F.card * Real.cos η := by ring

end LatticeProb
