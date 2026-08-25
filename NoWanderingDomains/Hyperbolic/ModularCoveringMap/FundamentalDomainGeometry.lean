/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.Gamma2FundamentalDomain.Surjectivity

/-! # Tiles, reduction to the half-domain, and the F_Y contour

The reflected half-fundamental domain `F^σ`, twelve explicit tiles placing the standard
`SL(2, ℤ)` domain inside `F ∪ F^σ`, and the strict fundamental-domain property
`gamma2_translate_in_F_union_F_sigma`. Reduction to the half-domain: `Im λ ≥ 0` on the
closed `F`, and every orbit with `Im λ > 0` meets `F`. Boundary nonvanishing `λ ≠ w` on
the three boundary arcs of `F` for `Im w > 0`, and the `F_Y` contour: geometric
parameter setup, analyticity of `λ − w`, and nonvanishing on the rectangle edges and
the two coupled bottom strips.
-/

namespace NoWanderingDomains
open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-! ## The reflected domain and the strict fundamental-domain property -/

/-- The reflected half-fundamental domain `F^σ := { τ : -1 ≤ Re τ ≤ 0,
|2τ + 1| ≥ 1, Im τ > 0 }`. This is `-conj(F)`: the conjugation
`τ ↦ -conj τ` maps `F` (closed) to `F^σ` (closed) homeomorphically.
Together with `F`, `F^σ` tessellates a strict `Γ(2)`-fundamental
domain of `ℍ` with hyperbolic covolume `2π`. The image of `F^σ`
under `λ` is the closed lower half of `ℂ ∖ {0, 1}` (by
`modularLambdaH_conj_symmetry`). -/
def Gamma2FundamentalDomainReflected : Set ℂ :=
  { τ : ℂ | 0 < τ.im ∧ -1 ≤ τ.re ∧ τ.re ≤ 0 ∧ 1 ≤ ‖2 * τ + 1‖ }

/-! ### Tiles of the standard fundamental domain inside `F ∪ F^σ`

For `z` in the standard `SL(2, ℤ)` fundamental domain `𝒟`
(`1 ≤ |z|²`, `|Re z| ≤ 1/2`, `Im z > 0`), the twelve lemmas below
place an explicit Möbius image of `z` into the half-fundamental
domain `F` or its reflection `F^σ`, with the image chosen by the
sign of `Re z`. Together they cover the six classes of
`SL(2, ℤ/2) ≅ S₃`: the identity class (`z` itself), `S` (`−1/z`),
`T` (`z ± 1`), the lower-unipotent class (`z/(z+1)`, `z/(1−z)`),
`ST` (`−1/(z ± 1)`), and `TS` (`±1 − 1/z`). Each membership reduces
to a `normSq` inequality of the form `‖az + b‖² − ‖cz + d‖² ≥ 0`
valid on `𝒟`. -/

/-- **Identity tile, right half.** `z ∈ 𝒟` with `Re z ≥ 0` lies in `F`:
`‖2z − 1‖² = 4|z|² − 4 Re z + 1 ≥ 4 − 2 + 1 = 3 ≥ 1`. -/
theorem gamma2_tile_id_F {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : 0 ≤ z.re) : z ∈ Gamma2FundamentalDomain := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have hn := hz_norm
  rw [Complex.normSq_apply] at hn
  simp only [Gamma2FundamentalDomain, Set.mem_ofPred_eq]
  refine ⟨hz_im, h_sign, by linarith, ?_⟩
  have hq : (1 : ℝ) ≤ Complex.normSq (2 * z - 1) := by
    rw [Complex.normSq_apply]
    have h1 : (2 * z - 1).re = 2 * z.re - 1 := by simp
    have h2 : (2 * z - 1).im = 2 * z.im := by simp
    rw [h1, h2]
    nlinarith
  have hsq := Complex.sq_norm (2 * z - 1)
  nlinarith [norm_nonneg (2 * z - 1)]

/-- **Identity tile, left half.** `z ∈ 𝒟` with `Re z ≤ 0` lies in `F^σ`:
`‖2z + 1‖² = 4|z|² + 4 Re z + 1 ≥ 4 − 2 + 1 = 3 ≥ 1`. -/
theorem gamma2_tile_id_Fsigma {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : z.re ≤ 0) : z ∈ Gamma2FundamentalDomainReflected := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have hn := hz_norm
  rw [Complex.normSq_apply] at hn
  simp only [Gamma2FundamentalDomainReflected, Set.mem_ofPred_eq]
  refine ⟨hz_im, by linarith, h_sign, ?_⟩
  have hq : (1 : ℝ) ≤ Complex.normSq (2 * z + 1) := by
    rw [Complex.normSq_apply]
    have h1 : (2 * z + 1).re = 2 * z.re + 1 := by simp
    have h2 : (2 * z + 1).im = 2 * z.im := by simp
    rw [h1, h2]
    nlinarith
  have hsq := Complex.sq_norm (2 * z + 1)
  nlinarith [norm_nonneg (2 * z + 1)]

/-- **`S`-tile, left half.** For `z ∈ 𝒟` with `Re z ≤ 0`, the image
`−1/z` lies in `F`: `Re(−1/z) = −Re z/|z|² ∈ [0, 1/2]`, and
`‖2(−1/z) − 1‖ = ‖z + 2‖/‖z‖ ≥ 1` since `‖z + 2‖² − ‖z‖² = 4 Re z + 4 ≥ 2`. -/
theorem gamma2_tile_S_F {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : z.re ≤ 0) : -1 / z ∈ Gamma2FundamentalDomain := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have hz_ne : z ≠ 0 := by
    intro h
    rw [h] at hz_im
    simp at hz_im
  have h_nsq_pos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz_ne
  have him : (-1 / z).im = z.im / Complex.normSq z := by
    rw [Complex.div_im]
    simp
    ring
  have hre : (-1 / z).re = -z.re / Complex.normSq z := by
    rw [Complex.div_re]
    simp [neg_div]
  simp only [Gamma2FundamentalDomain, Set.mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him]
    exact div_pos hz_im h_nsq_pos
  · rw [hre]
    exact div_nonneg (by linarith) h_nsq_pos.le
  · rw [hre, div_le_one h_nsq_pos]
    linarith
  · have key : 2 * (-1 / z) - 1 = -(z + 2) / z := by
      field_simp
      ring
    have hq : (1 : ℝ) ≤ Complex.normSq (2 * (-1 / z) - 1) := by
      rw [key, Complex.normSq_div, Complex.normSq_neg, le_div_iff₀ h_nsq_pos, one_mul]
      rw [Complex.normSq_apply, Complex.normSq_apply]
      have h1 : (z + 2).re = z.re + 2 := by simp
      have h2 : (z + 2).im = z.im := by simp
      rw [h1, h2]
      nlinarith
    have hsq := Complex.sq_norm (2 * (-1 / z) - 1)
    nlinarith [norm_nonneg (2 * (-1 / z) - 1)]

/-- **`S`-tile, right half.** For `z ∈ 𝒟` with `Re z ≥ 0`, the image
`−1/z` lies in `F^σ`: mirror of `gamma2_tile_S_F` using
`‖z − 2‖² − ‖z‖² = −4 Re z + 4 ≥ 2`. -/
theorem gamma2_tile_S_Fsigma {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : 0 ≤ z.re) : -1 / z ∈ Gamma2FundamentalDomainReflected := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have hz_ne : z ≠ 0 := by
    intro h
    rw [h] at hz_im
    simp at hz_im
  have h_nsq_pos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz_ne
  have him : (-1 / z).im = z.im / Complex.normSq z := by
    rw [Complex.div_im]
    simp
    ring
  have hre : (-1 / z).re = -z.re / Complex.normSq z := by
    rw [Complex.div_re]
    simp [neg_div]
  simp only [Gamma2FundamentalDomainReflected, Set.mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him]
    exact div_pos hz_im h_nsq_pos
  · rw [hre, neg_div]
    have h1 : z.re / Complex.normSq z ≤ 1 := by
      rw [div_le_one h_nsq_pos]
      linarith
    linarith
  · rw [hre]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) h_nsq_pos.le
  · have key : 2 * (-1 / z) + 1 = (z - 2) / z := by
      field_simp
      ring
    have hq : (1 : ℝ) ≤ Complex.normSq (2 * (-1 / z) + 1) := by
      rw [key, Complex.normSq_div, le_div_iff₀ h_nsq_pos, one_mul]
      rw [Complex.normSq_apply, Complex.normSq_apply]
      have h1 : (z - 2).re = z.re - 2 := by simp
      have h2 : (z - 2).im = z.im := by simp
      rw [h1, h2]
      nlinarith
    have hsq := Complex.sq_norm (2 * (-1 / z) + 1)
    nlinarith [norm_nonneg (2 * (-1 / z) + 1)]

/-- **`T`-tile, left half.** For `z ∈ 𝒟` with `Re z ≤ 0`, the translate
`z + 1` lies in `F`: `Re(z + 1) ∈ [1/2, 1]` and
`‖2(z + 1) − 1‖² = ‖2z + 1‖² = 4|z|² + 4 Re z + 1 ≥ 3`. -/
theorem gamma2_tile_T_F {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : z.re ≤ 0) : z + 1 ∈ Gamma2FundamentalDomain := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have him : (z + 1).im = z.im := by simp
  have hre : (z + 1).re = z.re + 1 := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him]; exact hz_im
  · rw [hre]; linarith
  · rw [hre]; linarith
  · have hsq : (1 : ℝ) ≤ Complex.normSq (2 * (z + 1) - 1) := by
      have hval : Complex.normSq (2 * (z + 1) - 1)
          = 4 * Complex.normSq z + 4 * z.re + 1 := by
        simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
          Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
        ring
      rw [hval]; nlinarith
    have hsq' : (1 : ℝ) ≤ ‖2 * (z + 1) - 1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; exact hsq
    nlinarith [norm_nonneg (2 * (z + 1) - 1)]

/-- **`T`-tile, right half.** For `z ∈ 𝒟` with `Re z ≥ 0`, the translate
`z − 1` lies in `F^σ`: mirror of `gamma2_tile_T_F`. -/
theorem gamma2_tile_T_Fsigma {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : 0 ≤ z.re) : z - 1 ∈ Gamma2FundamentalDomainReflected := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have him : (z - 1).im = z.im := by simp
  have hre : (z - 1).re = z.re - 1 := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him]; exact hz_im
  · rw [hre]; linarith
  · rw [hre]; linarith
  · have hsq : (1 : ℝ) ≤ Complex.normSq (2 * (z - 1) + 1) := by
      have hval : Complex.normSq (2 * (z - 1) + 1)
          = 4 * Complex.normSq z - 4 * z.re + 1 := by
        simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
          Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
        ring
      rw [hval]; nlinarith
    have hsq' : (1 : ℝ) ≤ ‖2 * (z - 1) + 1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; exact hsq
    nlinarith [norm_nonneg (2 * (z - 1) + 1)]

/-- **Lower-unipotent tile, left half.** For `z ∈ 𝒟` with `Re z ≤ 0`,
the image `z/(z + 1)` lies in `F`: `Im(z/(z+1)) = Im z/‖z+1‖² > 0`,
`Re(z/(z+1)) = (|z|² + Re z)/‖z+1‖² ∈ [0, 1]`, and
`‖2 z/(z+1) − 1‖ = ‖z − 1‖/‖z + 1‖ ≥ 1` iff `Re z ≤ 0`. -/
theorem gamma2_tile_L_F {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : z.re ≤ 0) : z / (z + 1) ∈ Gamma2FundamentalDomain := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have h' : (z + 1).im = 0 := by rw [h]; simp
    simp only [Complex.add_im, Complex.one_im, add_zero] at h'
    linarith
  have hN : 0 < Complex.normSq (z + 1) := Complex.normSq_pos.mpr hz1
  have h1re : (z + 1).re = z.re + 1 := by simp
  have h1im : (z + 1).im = z.im := by simp
  have hN_eq : Complex.normSq (z + 1) = Complex.normSq z + 2 * z.re + 1 := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have him : (z / (z + 1)).im = z.im / Complex.normSq (z + 1) := by
    rw [Complex.div_im, h1re, h1im]
    ring
  have hre : (z / (z + 1)).re
      = (Complex.normSq z + z.re) / Complex.normSq (z + 1) := by
    rw [Complex.div_re, h1re, h1im, Complex.normSq_apply z]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him]; exact div_pos hz_im hN
  · rw [hre]
    apply div_nonneg _ hN.le
    linarith
  · rw [hre, div_le_one hN]
    linarith
  · have hquot : 2 * (z / (z + 1)) - 1 = (z - 1) / (z + 1) := by
      field_simp
      ring
    rw [hquot, Complex.norm_div, one_le_div₀ (norm_pos_iff.mpr hz1)]
    have hsq : Complex.normSq (z + 1) ≤ Complex.normSq (z - 1) := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      nlinarith
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (z + 1), norm_nonneg (z - 1)]

/-- **Lower-unipotent tile, right half.** For `z ∈ 𝒟` with `Re z ≥ 0`,
the image `z/(1 − z)` lies in `F^σ`: `Re(z/(1−z)) = (Re z − |z|²)/‖1−z‖²
∈ [−1, 0]` and `‖2 z/(1−z) + 1‖ = ‖z + 1‖/‖1 − z‖ ≥ 1` iff `Re z ≥ 0`. -/
theorem gamma2_tile_L_Fsigma {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : 0 ≤ z.re) : z / (1 - z) ∈ Gamma2FundamentalDomainReflected := by
  obtain ⟨hre_lo, hre_hi⟩ := abs_le.mp hz_re
  have hz1 : (1 : ℂ) - z ≠ 0 := by
    intro h
    have h' : ((1 : ℂ) - z).im = 0 := by rw [h]; simp
    simp only [Complex.sub_im, Complex.one_im, zero_sub, neg_eq_zero] at h'
    linarith
  have hN : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hz1
  have h1re : ((1 : ℂ) - z).re = 1 - z.re := by simp
  have h1im : ((1 : ℂ) - z).im = -z.im := by simp
  have hN_eq : Complex.normSq (1 - z) = Complex.normSq z - 2 * z.re + 1 := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have him : (z / (1 - z)).im = z.im / Complex.normSq (1 - z) := by
    rw [Complex.div_im, h1re, h1im]
    ring
  have hre : (z / (1 - z)).re
      = (z.re - Complex.normSq z) / Complex.normSq (1 - z) := by
    rw [Complex.div_re, h1re, h1im, Complex.normSq_apply z]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him]; exact div_pos hz_im hN
  · rw [hre, le_div_iff₀ hN]
    nlinarith
  · rw [hre]
    apply div_nonpos_of_nonpos_of_nonneg _ hN.le
    linarith
  · have hquot : 2 * (z / (1 - z)) + 1 = (z + 1) / (1 - z) := by
      field_simp
      ring
    rw [hquot, Complex.norm_div, one_le_div₀ (norm_pos_iff.mpr hz1)]
    have hsq : Complex.normSq (1 - z) ≤ Complex.normSq (z + 1) := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      nlinarith
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (1 - z), norm_nonneg (z + 1)]

/-- **`ST`-tile, left half.** For `z ∈ 𝒟` with `Re z ≤ 0`, the image
`−1/(z + 1)` lies in `F^σ`: `Re(−1/(z+1)) = −(Re z + 1)/‖z+1‖² ∈ [−1, 0]`
and `‖2(−1/(z+1)) + 1‖ = ‖z − 1‖/‖z + 1‖ ≥ 1` iff `Re z ≤ 0`. -/
theorem gamma2_tile_ST_Fsigma {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : z.re ≤ 0) : -1 / (z + 1) ∈ Gamma2FundamentalDomainReflected := by
  obtain ⟨hre1, hre2⟩ := abs_le.mp hz_re
  have hd_ne : z + 1 ≠ 0 := by
    intro h
    have h' : (z + 1).im = 0 := by rw [h, Complex.zero_im]
    rw [Complex.add_im, Complex.one_im, add_zero] at h'
    linarith
  have hd_pos : 0 < Complex.normSq (z + 1) := Complex.normSq_pos.mpr hd_ne
  have hd_eq : Complex.normSq (z + 1) = Complex.normSq z + 2 * z.re + 1 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, add_zero]
    ring
  have hre_w : (-1 / (z + 1)).re = -(z.re + 1) / Complex.normSq (z + 1) := by
    rw [Complex.div_re]
    simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, neg_zero,
      add_zero, zero_mul, zero_div]
    ring
  have him_w : (-1 / (z + 1)).im = z.im / Complex.normSq (z + 1) := by
    rw [Complex.div_im]
    simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, neg_zero, add_zero, zero_mul, zero_div]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him_w]
    exact div_pos hz_im hd_pos
  · rw [hre_w, le_div_iff₀ hd_pos]
    nlinarith [hd_eq]
  · rw [hre_w, div_le_iff₀ hd_pos]
    nlinarith
  · have key : 2 * (-1 / (z + 1)) + 1 = (z - 1) / (z + 1) := by
      field_simp
      ring
    have h1 : Complex.normSq (z + 1) ≤ Complex.normSq (z - 1) := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.one_re, Complex.one_im, add_zero, sub_zero]
      nlinarith
    have h2 : ‖z + 1‖ ≤ ‖z - 1‖ := by
      have e1 := Complex.normSq_eq_norm_sq (z + 1)
      have e2 := Complex.normSq_eq_norm_sq (z - 1)
      nlinarith [norm_nonneg (z + 1), norm_nonneg (z - 1)]
    rw [key, norm_div, le_div_iff₀ (norm_pos_iff.mpr hd_ne), one_mul]
    exact h2

/-- **`ST`-tile, right half.** For `z ∈ 𝒟` with `Re z ≥ 0`, the image
`−1/(z − 1)` lies in `F`: `Re(−1/(z−1)) = (1 − Re z)/‖z−1‖² ∈ [0, 1]`
and `‖2(−1/(z−1)) − 1‖ = ‖z + 1‖/‖z − 1‖ ≥ 1` iff `Re z ≥ 0`. -/
theorem gamma2_tile_ST_F {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : 0 ≤ z.re) : -1 / (z - 1) ∈ Gamma2FundamentalDomain := by
  obtain ⟨hre1, hre2⟩ := abs_le.mp hz_re
  have hd_ne : z - 1 ≠ 0 := by
    intro h
    have h' : (z - 1).im = 0 := by rw [h, Complex.zero_im]
    rw [Complex.sub_im, Complex.one_im, sub_zero] at h'
    linarith
  have hd_pos : 0 < Complex.normSq (z - 1) := Complex.normSq_pos.mpr hd_ne
  have hd_eq : Complex.normSq (z - 1) = Complex.normSq z - 2 * z.re + 1 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero]
    ring
  have hre_w : (-1 / (z - 1)).re = (1 - z.re) / Complex.normSq (z - 1) := by
    rw [Complex.div_re]
    simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
      Complex.sub_re, Complex.sub_im, neg_zero, sub_zero, zero_mul, zero_div]
    ring
  have him_w : (-1 / (z - 1)).im = z.im / Complex.normSq (z - 1) := by
    rw [Complex.div_im]
    simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
      Complex.sub_re, Complex.sub_im, neg_zero, sub_zero, zero_mul, zero_div]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him_w]
    exact div_pos hz_im hd_pos
  · rw [hre_w, le_div_iff₀ hd_pos]
    nlinarith
  · rw [hre_w, div_le_iff₀ hd_pos]
    nlinarith [hd_eq]
  · have key : 2 * (-1 / (z - 1)) - 1 = -(z + 1) / (z - 1) := by
      field_simp
      ring
    have h1 : Complex.normSq (z - 1) ≤ Complex.normSq (z + 1) := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.one_re, Complex.one_im, add_zero, sub_zero]
      nlinarith
    have h2 : ‖z - 1‖ ≤ ‖z + 1‖ := by
      have e1 := Complex.normSq_eq_norm_sq (z + 1)
      have e2 := Complex.normSq_eq_norm_sq (z - 1)
      nlinarith [norm_nonneg (z + 1), norm_nonneg (z - 1)]
    rw [key, norm_div, norm_neg, le_div_iff₀ (norm_pos_iff.mpr hd_ne), one_mul]
    exact h2

/-- **`TS`-tile, right half.** For `z ∈ 𝒟` with `Re z ≥ 0`, the image
`1 − 1/z` lies in `F`: `Re(1 − 1/z) = 1 − Re z/|z|² ∈ [1/2, 1]` and
`‖2(1 − 1/z) − 1‖ = ‖z − 2‖/‖z‖ ≥ 1` since `‖z − 2‖² − ‖z‖² = 4 − 4 Re z ≥ 2`. -/
theorem gamma2_tile_TS_F {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : 0 ≤ z.re) : 1 - 1 / z ∈ Gamma2FundamentalDomain := by
  obtain ⟨hre1, hre2⟩ := abs_le.mp hz_re
  have hz_ne : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hz_im
    linarith
  have hN_pos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz_ne
  have hN_ne : Complex.normSq z ≠ 0 := ne_of_gt hN_pos
  have hre_w : (1 - 1 / z).re = (Complex.normSq z - z.re) / Complex.normSq z := by
    rw [Complex.sub_re, Complex.div_re]
    simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, zero_div, add_zero]
    field_simp
  have him_w : (1 - 1 / z).im = z.im / Complex.normSq z := by
    rw [Complex.sub_im, Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, zero_div, zero_sub]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him_w]
    exact div_pos hz_im hN_pos
  · rw [hre_w, le_div_iff₀ hN_pos]
    nlinarith
  · rw [hre_w, div_le_iff₀ hN_pos]
    nlinarith
  · have key : 2 * (1 - 1 / z) - 1 = (z - 2) / z := by
      field_simp
      ring
    have h1 : Complex.normSq z ≤ Complex.normSq (z - 2) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.re_ofNat,
        Complex.im_ofNat, sub_zero]
      nlinarith
    have h2 : ‖z‖ ≤ ‖z - 2‖ := by
      have e1 := Complex.normSq_eq_norm_sq z
      have e2 := Complex.normSq_eq_norm_sq (z - 2)
      nlinarith [norm_nonneg z, norm_nonneg (z - 2)]
    rw [key, norm_div, le_div_iff₀ (norm_pos_iff.mpr hz_ne), one_mul]
    exact h2

/-- **`TS`-tile, left half.** For `z ∈ 𝒟` with `Re z ≤ 0`, the image
`−1 − 1/z` lies in `F^σ`: `Re(−1 − 1/z) = −1 − Re z/|z|² ∈ [−1, −1/2]`
and `‖2(−1 − 1/z) + 1‖ = ‖z + 2‖/‖z‖ ≥ 1` since
`‖z + 2‖² − ‖z‖² = 4 Re z + 4 ≥ 2`. -/
theorem gamma2_tile_TS_Fsigma {z : ℂ} (hz_im : 0 < z.im)
    (hz_norm : 1 ≤ Complex.normSq z) (hz_re : |z.re| ≤ 1 / 2)
    (h_sign : z.re ≤ 0) : -1 - 1 / z ∈ Gamma2FundamentalDomainReflected := by
  obtain ⟨hre1, hre2⟩ := abs_le.mp hz_re
  have hz_ne : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hz_im
    linarith
  have hN_pos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz_ne
  have hN_ne : Complex.normSq z ≠ 0 := ne_of_gt hN_pos
  have hre_w : (-1 - 1 / z).re = -(Complex.normSq z + z.re) / Complex.normSq z := by
    rw [Complex.sub_re, Complex.neg_re, Complex.div_re]
    simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, zero_div, add_zero]
    field_simp
    ring
  have him_w : (-1 - 1 / z).im = z.im / Complex.normSq z := by
    rw [Complex.sub_im, Complex.neg_im, Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, zero_div, neg_zero,
      zero_sub]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him_w]
    exact div_pos hz_im hN_pos
  · rw [hre_w, le_div_iff₀ hN_pos]
    nlinarith
  · rw [hre_w, div_le_iff₀ hN_pos]
    nlinarith
  · have key : 2 * (-1 - 1 / z) + 1 = -(z + 2) / z := by
      field_simp
      ring
    have h1 : Complex.normSq z ≤ Complex.normSq (z + 2) := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.re_ofNat,
        Complex.im_ofNat, add_zero]
      nlinarith
    have h2 : ‖z‖ ≤ ‖z + 2‖ := by
      have e1 := Complex.normSq_eq_norm_sq z
      have e2 := Complex.normSq_eq_norm_sq (z + 2)
      nlinarith [norm_nonneg z, norm_nonneg (z + 2)]
    rw [key, norm_div, norm_neg, le_div_iff₀ (norm_pos_iff.mpr hz_ne), one_mul]
    exact h2

/-- **Coercion formula for the `SL(2, ℤ)` action on `ℍ`.** The complex
coordinate of `g • z` is the Möbius image `(az + b)/(cz + d)` with the
integer entries of `g` cast into `ℂ`. Unfolds
`UpperHalfPlane.specialLinearGroup_apply` through the cast chain
`ℤ → ℝ → ℂ`. -/
theorem sl2z_smul_coe (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (z : UpperHalfPlane) :
    ((g • z : UpperHalfPlane) : ℂ) =
      ((g 0 0 : ℤ) * (z : ℂ) + (g 0 1 : ℤ)) /
        ((g 1 0 : ℤ) * (z : ℂ) + (g 1 1 : ℤ)) := by
  rw [UpperHalfPlane.specialLinearGroup_apply]
  simp [eq_intCast, Complex.ofReal_intCast]

/-- **Existence of a `Γ(2)`-translate in `F ∪ F^σ`.** For every
`τ ∈ ℍ`, there is `γ ∈ Γ(2)` such that `γ • τ` lies in either the
half-fundamental domain `F` or its reflection `F^σ`. This is the
classical strict fundamental-domain property of `Γ(2)`: place the
orbit into the standard `SL(2, ℤ)` fundamental domain `𝒟` via the
Mathlib reduction `ModularGroup.exists_smul_mem_fd`, say `g • τ ∈ 𝒟`;
the mod-2 reduction of `g⁻¹` is one of the six elements of
`SL(2, ℤ/2) ≅ S₃`, and for each class an explicit correction matrix
`h ≡ g⁻¹ (mod 2)` — chosen between two candidates by the sign of
`Re (g • τ)` — sends `g • τ` into `F ∪ F^σ` by the twelve tile
lemmas above. Then `γ := h * g ∈ Γ(2)` and
`γ • τ = h • (g • τ) ∈ F ∪ F^σ`. -/
theorem gamma2_translate_in_F_union_F_sigma (τ : UpperHalfPlane) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2,
      ((γ • τ : UpperHalfPlane) : ℂ) ∈
        Gamma2FundamentalDomain ∪ Gamma2FundamentalDomainReflected := by
  obtain ⟨g, hg_fd⟩ := ModularGroup.exists_smul_mem_fd τ
  have hg_pair : 1 ≤ Complex.normSq ((g • τ : UpperHalfPlane) : ℂ) ∧
      |(g • τ : UpperHalfPlane).re| ≤ 1 / 2 := hg_fd
  set z : ℂ := ((g • τ : UpperHalfPlane) : ℂ) with hz_def
  have hz_norm : 1 ≤ Complex.normSq z := hg_pair.1
  have hz_re : |z.re| ≤ 1 / 2 := by
    have h2 := hg_pair.2
    rwa [← UpperHalfPlane.coe_re, ← hz_def] at h2
  have hz_im : 0 < z.im := by
    rw [hz_def, UpperHalfPlane.coe_im]
    exact (g • τ).im_pos
  have hz_ne : z ≠ 0 := by
    intro h0
    rw [h0] at hz_im
    simp at hz_im
  -- determinant of `g`
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have hp := g.2
    rwa [Matrix.det_fin_two] at hp
  -- `ZMod 2` cast helpers
  have cast1 : ∀ x : ℤ, x % 2 = 1 → ((x : ZMod 2) = 1) := by
    intro x hx
    have hcast : ((x : ℤ) : ZMod 2) = ((1 : ℤ) : ZMod 2) := by
      rw [ZMod.intCast_eq_intCast_iff]
      change x % ((2 : ℕ) : ℤ) = 1 % ((2 : ℕ) : ℤ)
      omega
    simpa using hcast
  have cast0 : ∀ x : ℤ, x % 2 = 0 → ((x : ZMod 2) = 0) := by
    intro x hx
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    omega
  -- master construction: given a correction matrix `h = !![p,q;r,s]` with
  -- `h * g ≡ 1 (mod 2)` and the Möbius image of `z` under `h` in `F ∪ F^σ`,
  -- produce the required `γ ∈ Γ(2)`.
  have main : ∀ p q r s : ℤ, ∀ u : ℂ, p * s - q * r = 1 →
      (p * g 0 0 + q * g 1 0) % 2 = 1 →
      (p * g 0 1 + q * g 1 1) % 2 = 0 →
      (r * g 0 0 + s * g 1 0) % 2 = 0 →
      (r * g 0 1 + s * g 1 1) % 2 = 1 →
      ((p : ℂ) * z + (q : ℂ)) / ((r : ℂ) * z + (s : ℂ)) = u →
      u ∈ Gamma2FundamentalDomain ∪ Gamma2FundamentalDomainReflected →
      ∃ γ ∈ CongruenceSubgroup.Gamma 2,
        ((γ • τ : UpperHalfPlane) : ℂ) ∈
          Gamma2FundamentalDomain ∪ Gamma2FundamentalDomainReflected := by
    intro p q r s u hpqrs h1 h2 h3 h4 hu hmem
    have hdet_h : (!![p, q; r, s] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
      rw [Matrix.det_fin_two_of]; exact hpqrs
    obtain ⟨hM, hM_val⟩ : ∃ hM : SL(2, ℤ), (hM : Matrix (Fin 2) (Fin 2) ℤ) = !![p, q; r, s] :=
      ⟨⟨!![p, q; r, s], hdet_h⟩, rfl⟩
    have e00 : (hM * g) 0 0 = p * g 0 0 + q * g 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hM_val]
      simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e01 : (hM * g) 0 1 = p * g 0 1 + q * g 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hM_val]
      simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e10 : (hM * g) 1 0 = r * g 0 0 + s * g 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hM_val]
      simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e11 : (hM * g) 1 1 = r * g 0 1 + s * g 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hM_val]
      simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨hM * g, ?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma_mem]
      exact ⟨by rw [e00]; exact cast1 _ h1, by rw [e01]; exact cast0 _ h2,
        by rw [e10]; exact cast0 _ h3, by rw [e11]; exact cast1 _ h4⟩
    · rw [mul_smul, sl2z_smul_coe, ← hz_def, hM_val]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hu]
      exact hmem
  -- parity obstruction: `det ≡ 1 (mod 2)` rules out ten parity patterns
  have hparity : (g 0 0 % 2) * (g 1 1 % 2) % 2 ≠ (g 0 1 % 2) * (g 1 0 % 2) % 2 := by
    rw [← Int.mul_emod, ← Int.mul_emod]
    intro hEq
    have hsub : (g 0 0 * g 1 1 - g 0 1 * g 1 0) % 2 = 0 := by
      rw [Int.sub_emod, hEq, sub_self, Int.zero_emod]
    rw [hdet] at hsub
    norm_num at hsub
  rcases Int.emod_two_eq (g 0 0) with ha | ha <;>
    rcases Int.emod_two_eq (g 0 1) with hb | hb <;>
      rcases Int.emod_two_eq (g 1 0) with hc | hc <;>
        rcases Int.emod_two_eq (g 1 1) with hd | hd
  -- (0,0,0,0): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (0,0,0,1): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (0,0,1,0): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (0,0,1,1): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (0,1,0,0): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (0,1,0,1): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (0,1,1,0): `S`-class, h = [[0,-1],[1,0]], image -1/z
  · rcases le_or_gt z.re 0 with hsign | hsign
    · exact main 0 (-1) 1 0 (-1 / z) (by norm_num) (by omega) (by omega) (by omega)
        (by omega) (by push_cast; ring)
        (Set.mem_union_left _ (gamma2_tile_S_F hz_im hz_norm hz_re hsign))
    · exact main 0 (-1) 1 0 (-1 / z) (by norm_num) (by omega) (by omega) (by omega)
        (by omega) (by push_cast; ring)
        (Set.mem_union_right _ (gamma2_tile_S_Fsigma hz_im hz_norm hz_re hsign.le))
  -- (0,1,1,1): `TS`-class, h = [[∓1,-1],[1,0]], image ∓1 - 1/z
  · rcases le_or_gt z.re 0 with hsign | hsign
    · exact main (-1) (-1) 1 0 (-1 - 1 / z) (by norm_num) (by omega) (by omega) (by omega)
        (by omega)
        (by push_cast
            rw [neg_one_mul, one_mul, add_zero, ← sub_eq_add_neg, sub_div, neg_div,
              div_self hz_ne])
        (Set.mem_union_right _ (gamma2_tile_TS_Fsigma hz_im hz_norm hz_re hsign))
    · exact main 1 (-1) 1 0 (1 - 1 / z) (by norm_num) (by omega) (by omega) (by omega)
        (by omega)
        (by push_cast
            rw [one_mul, add_zero, ← sub_eq_add_neg, sub_div, div_self hz_ne])
        (Set.mem_union_left _ (gamma2_tile_TS_F hz_im hz_norm hz_re hsign.le))
  -- (1,0,0,0): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (1,0,0,1): identity class, γ = g itself
  · rcases le_or_gt z.re 0 with hsign | hsign
    · exact main 1 0 0 1 z (by norm_num) (by omega) (by omega) (by omega) (by omega)
        (by push_cast; ring)
        (Set.mem_union_right _ (gamma2_tile_id_Fsigma hz_im hz_norm hz_re hsign))
    · exact main 1 0 0 1 z (by norm_num) (by omega) (by omega) (by omega) (by omega)
        (by push_cast; ring)
        (Set.mem_union_left _ (gamma2_tile_id_F hz_im hz_norm hz_re hsign.le))
  -- (1,0,1,0): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (1,0,1,1): lower-unipotent class, h = [[1,0],[±1,1]], image z/(z+1) or z/(1-z)
  · rcases le_or_gt z.re 0 with hsign | hsign
    · exact main 1 0 1 1 (z / (z + 1)) (by norm_num) (by omega) (by omega) (by omega)
        (by omega) (by push_cast; ring)
        (Set.mem_union_left _ (gamma2_tile_L_F hz_im hz_norm hz_re hsign))
    · exact main 1 0 (-1) 1 (z / (1 - z)) (by norm_num) (by omega) (by omega) (by omega)
        (by omega) (by push_cast; ring)
        (Set.mem_union_right _ (gamma2_tile_L_Fsigma hz_im hz_norm hz_re hsign.le))
  -- (1,1,0,0): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity
  -- (1,1,0,1): `T`-class, h = [[1,±1],[0,1]], image z ± 1
  · rcases le_or_gt z.re 0 with hsign | hsign
    · exact main 1 1 0 1 (z + 1) (by norm_num) (by omega) (by omega) (by omega) (by omega)
        (by push_cast; ring)
        (Set.mem_union_left _ (gamma2_tile_T_F hz_im hz_norm hz_re hsign))
    · exact main 1 (-1) 0 1 (z - 1) (by norm_num) (by omega) (by omega) (by omega) (by omega)
        (by push_cast; ring)
        (Set.mem_union_right _ (gamma2_tile_T_Fsigma hz_im hz_norm hz_re hsign.le))
  -- (1,1,1,0): `ST`-class, h = [[0,-1],[1,±1]], image -1/(z±1)
  · rcases le_or_gt z.re 0 with hsign | hsign
    · exact main 0 (-1) 1 1 (-1 / (z + 1)) (by norm_num) (by omega) (by omega) (by omega)
        (by omega) (by push_cast; ring)
        (Set.mem_union_right _ (gamma2_tile_ST_Fsigma hz_im hz_norm hz_re hsign))
    · exact main 0 (-1) 1 (-1) (-1 / (z - 1)) (by norm_num) (by omega) (by omega) (by omega)
        (by omega) (by push_cast; ring)
        (Set.mem_union_left _ (gamma2_tile_ST_F hz_im hz_norm hz_re hsign.le))
  -- (1,1,1,1): impossible
  · rw [ha, hb, hc, hd] at hparity; norm_num at hparity

/-! ## Reduction to the half-domain: sign of `Im λ` on `F` and orbit placement -/

/-- **`Im λ ≥ 0` on the closed half-fundamental domain `F`.**
Combines `modularLambdaH_F_im_pos` (strict positivity on the open
interior `F^o`) with the three boundary-arc lemmas
`modularLambdaH_pure_imag_real` (left edge, `λ ∈ ℝ`),
`modularLambdaH_one_add_imag_real` (right edge), and
`modularLambdaH_semicircle_real` (semicircular bottom arc). -/
theorem modularLambdaH_im_nonneg_on_closed_F
    {τ : ℂ} (hτ_F : τ ∈ Gamma2FundamentalDomain) :
    0 ≤ (modularLambdaH τ).im := by
  obtain ⟨hτ_im_pos, hτ_re_nonneg, hτ_re_le_one, hτ_semicircle⟩ := hτ_F
  -- Case split on left/right edges and semicircle vs interior.
  by_cases h_re_zero : τ.re = 0
  · -- Left edge: τ = i·y for some y > 0.
    have h_τ_eq : τ = Complex.I * τ.im := by
      apply Complex.ext
      · simp [Complex.mul_re, Complex.I_re, Complex.I_im, h_re_zero]
      · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [h_τ_eq]
    rw [modularLambdaH_pure_imag_real hτ_im_pos]
  · by_cases h_re_one : τ.re = 1
    · -- Right edge: τ = 1 + i·y for some y > 0.
      have h_τ_eq : τ = 1 + Complex.I * τ.im := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, h_re_one]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
      rw [h_τ_eq]
      rw [modularLambdaH_one_add_imag_real hτ_im_pos]
    · by_cases h_semicircle : ‖2 * τ - 1‖ = 1
      · -- Semicircle: λ ∈ ℝ.
        rw [modularLambdaH_semicircle_real hτ_im_pos h_semicircle]
      · -- Strict interior: use Step A.
        have hτ_interior : τ ∈ Gamma2FundamentalDomainInterior := by
          refine ⟨hτ_im_pos, ?_, ?_, ?_⟩
          · rcases lt_or_eq_of_le hτ_re_nonneg with h | h
            · exact h
            · exact absurd h.symm h_re_zero
          · rcases lt_or_eq_of_le hτ_re_le_one with h | h
            · exact h
            · exact absurd h h_re_one
          · rcases lt_or_eq_of_le hτ_semicircle with h | h
            · exact h
            · exact absurd h.symm h_semicircle
        exact (modularLambdaH_F_im_pos τ hτ_interior).le

/-- **Half-FD existence (upper branch).** Every `τ ∈ ℍ` with
`Im(λ τ) > 0` has a `Γ(2)`-translate in the half-fundamental domain
`F`. Proof: use the strict fundamental-domain property
`gamma2_translate_in_F_union_F_sigma` to obtain `γ ∈ Γ(2)` with
`γ • τ ∈ F ∪ F^σ`. If `γ • τ ∈ F^σ`, then `-conj(γ • τ) ∈ F`
(by definition of `F^σ` as the reflection of `F`); by
`modularLambdaH_conj_symmetry` and `modularLambdaH_im_nonneg_on_closed_F`,
`Im(λ(γ • τ)) ≤ 0`; but by `Γ(2)`-invariance of `λ`,
`Im(λ(γ • τ)) = Im(λ τ) > 0` — contradiction. So `γ • τ ∈ F`. -/
theorem gamma2_orbit_meets_F_when_im_lambda_pos (τ : UpperHalfPlane)
    (hτ_pos : 0 < (modularLambdaH (τ : ℂ)).im) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2,
      ((γ • τ : UpperHalfPlane) : ℂ) ∈ Gamma2FundamentalDomain := by
  obtain ⟨γ, hγ_in, h_in_union⟩ := gamma2_translate_in_F_union_F_sigma τ
  -- λ-invariance: λ(γ•τ) = λ(τ).
  have h_lam_inv : modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ) = modularLambdaH (τ : ℂ) :=
    modularLambdaH_gamma2_invariant γ hγ_in τ
  -- Im(λ γτ) = Im(λ τ) > 0.
  have h_im_lam_γτ : 0 < (modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ)).im := by
    rw [h_lam_inv]; exact hτ_pos
  rcases h_in_union with h_F | h_Fσ
  · exact ⟨γ, hγ_in, h_F⟩
  · -- γ • τ ∈ F^σ: derive contradiction via conjugation.
    exfalso
    -- Extract F^σ membership data.
    obtain ⟨hγτ_im, hγτ_re_ge, hγτ_re_le, hγτ_semicircle⟩ := h_Fσ
    -- -conj(γ • τ) ∈ F.
    set γτ_c : ℂ := ((γ • τ : UpperHalfPlane) : ℂ) with hγτ_c_def
    have h_neg_conj_in_F : -(starRingEnd ℂ γτ_c) ∈ Gamma2FundamentalDomain := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- Im(-conj γτ) = Im(γτ) > 0.
        simp only [Complex.neg_im, Complex.conj_im, neg_neg]
        exact hγτ_im
      · -- Re(-conj γτ) = -Re(γτ) ≥ 0 (since Re(γτ) ≤ 0).
        simp only [Complex.neg_re, Complex.conj_re]
        linarith
      · -- Re(-conj γτ) = -Re(γτ) ≤ 1 (since Re(γτ) ≥ -1).
        simp only [Complex.neg_re, Complex.conj_re]
        linarith
      · -- |2(-conj γτ) - 1| = |2γτ + 1| ≥ 1.
        have h_eq_neg_conj : (2 * (-(starRingEnd ℂ γτ_c)) - 1 : ℂ) =
            -(starRingEnd ℂ (2 * γτ_c + 1)) := by
          simp only [map_add, map_mul, Complex.conj_ofNat, map_one]
          ring
        have h_norm_eq : ‖2 * (-(starRingEnd ℂ γτ_c)) - 1‖ = ‖2 * γτ_c + 1‖ := by
          rw [h_eq_neg_conj, norm_neg, Complex.norm_conj]
        rw [h_norm_eq]
        exact hγτ_semicircle
    -- λ(-conj γτ) = conj(λ γτ) by conjugation symmetry.
    have h_lam_neg_conj : modularLambdaH (-(starRingEnd ℂ γτ_c)) =
        starRingEnd ℂ (modularLambdaH γτ_c) :=
      modularLambdaH_conj_symmetry hγτ_im
    -- Im(λ(-conj γτ)) ≥ 0 (from closed F).
    have h_im_neg_conj_nonneg : 0 ≤ (modularLambdaH (-(starRingEnd ℂ γτ_c))).im :=
      modularLambdaH_im_nonneg_on_closed_F h_neg_conj_in_F
    -- Im(conj(λ γτ)) = -Im(λ γτ).
    have h_im_conj_eq : (starRingEnd ℂ (modularLambdaH γτ_c)).im =
        -(modularLambdaH γτ_c).im := by
      simp [Complex.conj_im]
    -- Combine: Im(λ γτ) ≤ 0.
    rw [h_lam_neg_conj, h_im_conj_eq] at h_im_neg_conj_nonneg
    -- h_im_neg_conj_nonneg : 0 ≤ -(modularLambdaH γτ_c).im
    have h_im_γτ_le : (modularLambdaH γτ_c).im ≤ 0 := by linarith
    -- But h_im_lam_γτ : 0 < (modularLambdaH γτ_c).im. Contradiction.
    linarith

/-! ## Boundary nonvanishing: `λ ≠ w` on `∂F` for `Im w > 0`

The closure of `modularLambdaH_existsUnique_in_F_interior_of_im_pos`
rests on the F_Y argument principle
`cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk`.
The non-vanishing boundary conditions required by the AP decompose into
the four boundary helpers below (left edge, right edge, semicircle, top
edge). Uniqueness itself is delivered by the degree-argument bootstrap
`modularLambdaH_F_interior_preimage_unique`, which combines the AP's
divisor-count form with a δ-thickening argument bridging the AP's
shifted-disk geometry (centered at `1/2 + δ·i`) to F's actual semicircle
geometry (centered at `1/2`). -/

/-- **Boundary helper (left edge).** For `w` with `Im w > 0` and `y > 0`,
`λ(i·y) ≠ w`. Direct consequence of `modularLambdaH_pure_imag_real`
(`Im λ(i·y) = 0`) and `Im w > 0`. -/
theorem modularLambdaH_left_edge_ne_of_im_pos
    {w : ℂ} (hw : 0 < w.im) {y : ℝ} (hy : 0 < y) :
    modularLambdaH (Complex.I * y) ≠ w := by
  intro h_eq
  have h_im_lam_zero : (modularLambdaH (Complex.I * y)).im = 0 :=
    modularLambdaH_pure_imag_real hy
  rw [h_eq] at h_im_lam_zero
  linarith

/-- **Boundary helper (right edge).** For `w` with `Im w > 0` and `y > 0`,
`λ(1 + i·y) ≠ w`. Direct consequence of
`modularLambdaH_one_add_imag_real`. -/
theorem modularLambdaH_right_edge_ne_of_im_pos
    {w : ℂ} (hw : 0 < w.im) {y : ℝ} (hy : 0 < y) :
    modularLambdaH (1 + Complex.I * y) ≠ w := by
  intro h_eq
  have h_im_lam_zero : (modularLambdaH (1 + Complex.I * y)).im = 0 :=
    modularLambdaH_one_add_imag_real hy
  rw [h_eq] at h_im_lam_zero
  linarith

/-- **Boundary helper (bottom semicircle).** For `w` with `Im w > 0` and
`τ` on the upper semicircle `|2τ − 1| = 1, Im τ > 0`, `λ(τ) ≠ w`. Direct
consequence of `modularLambdaH_semicircle_real`. -/
theorem modularLambdaH_semicircle_ne_of_im_pos
    {w : ℂ} (hw : 0 < w.im) {τ : ℂ}
    (hτ_im : 0 < τ.im) (hτ_semi : ‖2 * τ - 1‖ = 1) :
    modularLambdaH τ ≠ w := by
  intro h_eq
  have h_im_lam_zero : (modularLambdaH τ).im = 0 :=
    modularLambdaH_semicircle_real hτ_im hτ_semi
  rw [h_eq] at h_im_lam_zero
  linarith

/-- **Boundary helper (top edge).** For `w` with `Im w > 0`, there exists
`Y₀` such that for all `Y ≥ Y₀` and all `x ∈ [0, 1]`,
`λ(x + Y·i) ≠ w`. Proof: `‖θ₂(τ)‖ ≤ 10·exp(−π·Im τ/4)` (from
`theta2_norm_le_of_im_ge_one`) and `‖jacobiTheta τ − 1‖ ≤ C·exp(−π·Im τ)`
(from `isBigO_at_im_infty_jacobiTheta_sub_one`) — both bounds depend
only on `Im τ`, hence uniform in `Re τ`. Combined,
`‖λ(τ)‖ ≤ 160000·exp(−π·Im τ)` for `Im τ` large, which is `< ‖w‖` for
`Im τ` large enough. -/
theorem modularLambdaH_top_edge_far_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) ≠ w := by
  have hw_ne : w ≠ 0 := fun h_eq => by rw [h_eq] at hw; simp at hw
  have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  -- Get the uniform bound on jacobiTheta - 1 (depends only on Im τ).
  obtain ⟨C, hC⟩ := isBigO_at_im_infty_jacobiTheta_sub_one.bound
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hC
  obtain ⟨Y_start, hY_start⟩ := hC
  -- Exponential decay of exp(-π·Y).
  have h_exp_decay : Filter.Tendsto (fun Y : ℝ => Real.exp (-Real.pi * Y))
      Filter.atTop (nhds 0) := by
    have h_arg : Filter.Tendsto (fun Y : ℝ => -Real.pi * Y) Filter.atTop Filter.atBot := by
      have h1 : Filter.Tendsto (fun Y : ℝ => Real.pi * Y) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop Real.pi_pos Filter.tendsto_id
      have h2 := Filter.tendsto_neg_atTop_atBot.comp h1
      refine h2.congr ?_
      intro Y
      simp only [Function.comp_apply]
      ring
    exact Real.tendsto_exp_atBot.comp h_arg
  -- C·exp(-π·Y) ≤ 1/2 eventually.
  have h_C_evt : ∀ᶠ Y in Filter.atTop, C * Real.exp (-Real.pi * Y) ≤ 1/2 := by
    have h_lim : Filter.Tendsto (fun Y : ℝ => C * Real.exp (-Real.pi * Y))
        Filter.atTop (nhds 0) := by
      have := h_exp_decay.const_mul C
      simpa using this
    have h_lt : ∀ᶠ Y in Filter.atTop, C * Real.exp (-Real.pi * Y) < 1/2 :=
      h_lim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/2))
    filter_upwards [h_lt] with Y hY using hY.le
  -- 160000·exp(-π·Y) < ‖w‖ eventually.
  have h_lambda_norm_evt :
      ∀ᶠ Y in Filter.atTop, 160000 * Real.exp (-Real.pi * Y) < ‖w‖ := by
    have h_lim : Filter.Tendsto (fun Y : ℝ => 160000 * Real.exp (-Real.pi * Y))
        Filter.atTop (nhds 0) := by
      have := h_exp_decay.const_mul 160000
      simpa using this
    exact h_lim.eventually (eventually_lt_nhds hw_norm_pos)
  -- Combine.
  have h_combined : ∀ᶠ Y in Filter.atTop,
      max 1 Y_start ≤ Y ∧
      C * Real.exp (-Real.pi * Y) ≤ 1/2 ∧
      160000 * Real.exp (-Real.pi * Y) < ‖w‖ := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨max 1 Y_start, fun Y hY => hY⟩,
      h_C_evt, h_lambda_norm_evt] with Y h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  rw [Filter.eventually_atTop] at h_combined
  obtain ⟨Y₀, hY₀⟩ := h_combined
  refine ⟨Y₀, ?_⟩
  intro Y hY_ge x hx_nn hx_le
  obtain ⟨hY_max_le, hC_half, h_lam_bound⟩ := hY₀ Y hY_ge
  have hY_start_le : Y_start ≤ Y := le_trans (le_max_right _ _) hY_max_le
  have hY_one_le : 1 ≤ Y := le_trans (le_max_left _ _) hY_max_le
  set τ : ℂ := (x : ℂ) + (Y : ℂ) * Complex.I with hτ_def
  have hτ_im : τ.im = Y := by
    simp [hτ_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_θ₂_bound : ‖theta2 τ‖ ≤ 10 * Real.exp (-Real.pi * Y / 4) := by
    have h_τ_im_ge : 1 ≤ τ.im := by rw [hτ_im]; exact hY_one_le
    have h := theta2_norm_le_of_im_ge_one h_τ_im_ge
    rw [hτ_im] at h
    exact h
  have h_jt_bound : ‖jacobiTheta τ - 1‖ ≤ C * Real.exp (-Real.pi * Y) := by
    have h_apply := hY_start Y hY_start_le τ hτ_im
    rw [hτ_im, Real.norm_of_nonneg (Real.exp_pos _).le] at h_apply
    exact h_apply
  have h_θ₃_lb : 1/2 ≤ ‖theta3 τ‖ := by
    unfold theta3
    have h1 : ‖jacobiTheta τ - 1‖ ≤ 1/2 := le_trans h_jt_bound hC_half
    have h_norm_diff :
        ‖(1 : ℂ)‖ - ‖jacobiTheta τ‖ ≤ ‖(1 : ℂ) - jacobiTheta τ‖ :=
      norm_sub_norm_le _ _
    rw [norm_one, norm_sub_rev] at h_norm_diff
    linarith
  -- Conclude λ(τ) ≠ w by norm comparison.
  intro h_eq
  -- λ(τ) = θ₂⁴ / θ₃⁴ = w, so ‖θ₂‖⁴/‖θ₃‖⁴ = ‖w‖.
  have h_θ₃_ne : theta3 τ ≠ 0 := by
    intro h_eq_zero
    rw [h_eq_zero, norm_zero] at h_θ₃_lb
    linarith
  have h_θ₃_pow_ne : theta3 τ ^ 4 ≠ 0 := pow_ne_zero _ h_θ₃_ne
  have h_lam_def : modularLambdaH τ = theta2 τ ^ 4 / theta3 τ ^ 4 := rfl
  rw [h_lam_def] at h_eq
  have h_lam_norm : ‖theta2 τ ^ 4 / theta3 τ ^ 4‖ = ‖w‖ := by rw [h_eq]
  rw [norm_div, norm_pow, norm_pow] at h_lam_norm
  have h_θ₂_nn : 0 ≤ ‖theta2 τ‖ := norm_nonneg _
  have h_θ₂_pow_le : ‖theta2 τ‖^4 ≤ (10 * Real.exp (-Real.pi * Y / 4))^4 :=
    pow_le_pow_left₀ h_θ₂_nn h_θ₂_bound 4
  have h_θ₂_pow_simp :
      (10 * Real.exp (-Real.pi * Y / 4))^4 = 10000 * Real.exp (-Real.pi * Y) := by
    rw [mul_pow]
    have h1 : (10 : ℝ)^4 = 10000 := by norm_num
    have h2 : (Real.exp (-Real.pi * Y / 4))^4 = Real.exp (-Real.pi * Y) := by
      rw [← Real.exp_nat_mul]
      congr 1; ring
    rw [h1, h2]
  have h_θ₂_pow_le_2 : ‖theta2 τ‖^4 ≤ 10000 * Real.exp (-Real.pi * Y) :=
    h_θ₂_pow_le.trans (le_of_eq h_θ₂_pow_simp)
  have h_θ₃_lb_pow : (1/16 : ℝ) ≤ ‖theta3 τ‖^4 := by
    have h_one_sixteenth : (1/2 : ℝ)^4 = 1/16 := by norm_num
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) h_θ₃_lb 4
    rw [h_one_sixteenth] at h
    exact h
  have h_θ₃_pow_pos : 0 < ‖theta3 τ‖^4 :=
    pow_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) h_θ₃_lb) 4
  have h_lam_norm_le :
      ‖theta2 τ‖^4 / ‖theta3 τ‖^4 ≤ 160000 * Real.exp (-Real.pi * Y) := by
    calc ‖theta2 τ‖^4 / ‖theta3 τ‖^4
        ≤ (10000 * Real.exp (-Real.pi * Y)) / ‖theta3 τ‖^4 :=
          div_le_div_of_nonneg_right h_θ₂_pow_le_2 h_θ₃_pow_pos.le
      _ ≤ (10000 * Real.exp (-Real.pi * Y)) / (1/16) := by
          apply div_le_div_of_nonneg_left _ (by norm_num : (0:ℝ) < 1/16) h_θ₃_lb_pow
          have h_exp_nn : 0 ≤ Real.exp (-Real.pi * Y) := (Real.exp_pos _).le
          positivity
      _ = 160000 * Real.exp (-Real.pi * Y) := by ring
  linarith [h_lam_norm_le, h_lam_bound, h_lam_norm]

/-! ## The F_Y contour: geometry, analyticity, and edge nonvanishing

The F_Y argument principle
`cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk`
from `WindingNumber/TruncatedArgumentPrinciple.lean` drives both the winding-index theorem
`modularLambdaH_F_Y_image_curve_winding_index_eq_one` and the
degree-argument bootstrap `modularLambdaH_F_interior_preimage_unique`
(uniqueness of the `λ`-preimage in `F^o`). The scaffold below
decomposes the application into sub-lemmas with explicit statements.

The F_Y region is a rectangle minus an upper half-disk on its bottom edge,
shaped to approximate the closure of `F^o ∩ {δ ≤ Im ≤ Y}` for small `δ`
and large `Y`. The chosen parameters are
`a = 0, b = 1, e = 1/2 + δ·i, R₀ = R₀'`, where `δ > 0` and `R₀' ∈ (0, 1/2)`
are picked to satisfy the strict AP hypothesis `a < e.re − R₀` (giving
`R₀' < 1/2`) while keeping `τ₁, τ₂` inside the F_Y interior. -/

/-- **F_Y geometric setup.** For `w ∈ ℍ` and any
`τ₁, τ₂ ∈ F^o`, there exists a parameter triple `(δ, Y, R₀)` with:
* `0 < δ ≤ δ_max ≤ 1/4` (rectangle bottom above the real axis);
* `δ < τᵢ.im < Y` (rectangle covers both `τᵢ`);
* `0 < R₀ < 1/2` (strict AP hypothesis `0 < 1/2 − R₀`);
* `‖τᵢ − (1/2 + δ·i)‖ > R₀` for each `τᵢ` (both `τᵢ` strictly outside
  the disk, hence in F_Y interior).

The proof picks `δ := min(τ₁.im/2, τ₂.im/2, δ_max)`,
`Y := max(τ₁.im + 1, τ₂.im + 1, 1)`, and `R₀ := 1/2 − δ`. The norm
condition follows from `|τᵢ − 1/2| > 1/2` (from `F^o`) via the reverse
triangle inequality. -/
theorem modularLambdaH_F_Y_params_exist
    {w : ℂ} (_hw : 0 < w.im)
    {τ₁ τ₂ : ℂ}
    (h₁_in : τ₁ ∈ Gamma2FundamentalDomainInterior)
    (h₂_in : τ₂ ∈ Gamma2FundamentalDomainInterior)
    {δ_max : ℝ} (hδ_max_pos : 0 < δ_max) (hδ_max_lt_quarter : δ_max ≤ 1 / 4) :
    ∃ δ Y R₀ : ℝ,
      0 < δ ∧ δ ≤ δ_max ∧ δ < τ₁.im ∧ δ < τ₂.im ∧
      δ < Y ∧ τ₁.im < Y ∧ τ₂.im < Y ∧
      0 < R₀ ∧ R₀ < 1 / 2 ∧ δ + R₀ < Y ∧
      ‖τ₁ - (1/2 + δ * Complex.I)‖ > R₀ ∧
      ‖τ₂ - (1/2 + δ * Complex.I)‖ > R₀ := by
  obtain ⟨h₁_im, _, _, h₁_semi⟩ := h₁_in
  obtain ⟨h₂_im, _, _, h₂_semi⟩ := h₂_in
  -- δ := min(τ₁.im / 2, τ₂.im / 2, δ_max).
  set δ : ℝ := min (min (τ₁.im / 2) (τ₂.im / 2)) δ_max with hδ_def
  have hδ_pos : 0 < δ := by
    refine lt_min (lt_min ?_ ?_) hδ_max_pos
    · linarith
    · linarith
  have hδ_le_δ_max : δ ≤ δ_max := min_le_right _ _
  have hδ_le_quarter : δ ≤ 1/4 := le_trans hδ_le_δ_max hδ_max_lt_quarter
  have hδ_lt_half : δ < 1/2 := by linarith
  have hδ_lt_τ₁_im : δ < τ₁.im := by
    have h₁ : δ ≤ τ₁.im / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hδ_lt_τ₂_im : δ < τ₂.im := by
    have h₂ : δ ≤ τ₂.im / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  -- Y := max(τ₁.im + 1, τ₂.im + 1, 1).
  set Y : ℝ := max (max (τ₁.im + 1) (τ₂.im + 1)) 1 with hY_def
  have hY_ge_one : (1 : ℝ) ≤ Y := le_max_right _ _
  have hY_gt_τ₁_im : τ₁.im < Y := by
    have h₁ : τ₁.im + 1 ≤ Y := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hY_gt_τ₂_im : τ₂.im < Y := by
    have h₂ : τ₂.im + 1 ≤ Y := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hY_gt_δ : δ < Y := lt_of_lt_of_le hδ_lt_half (by linarith)
  -- R₀ := 1/2 - δ.
  set R₀ : ℝ := 1/2 - δ with hR₀_def
  have hR₀_pos : 0 < R₀ := by linarith
  have hR₀_lt_half : R₀ < 1/2 := by linarith
  have h_δ_plus_R₀_eq : δ + R₀ = 1/2 := by rw [hR₀_def]; ring
  have hY_gt_δ_plus_R₀ : δ + R₀ < Y := by rw [h_δ_plus_R₀_eq]; linarith
  refine ⟨δ, Y, R₀, hδ_pos, hδ_le_δ_max, hδ_lt_τ₁_im, hδ_lt_τ₂_im, hY_gt_δ,
    hY_gt_τ₁_im, hY_gt_τ₂_im, hR₀_pos, hR₀_lt_half, hY_gt_δ_plus_R₀, ?_, ?_⟩
  · -- ‖τ₁ - (1/2 + δi)‖ > R₀.
    have h_semi_real : 1 < ‖2 * τ₁ - 1‖ := h₁_semi
    have h_eq : 2 * τ₁ - 1 = 2 * (τ₁ - 1/2) := by ring
    rw [h_eq, norm_mul] at h_semi_real
    have h_norm_2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h_norm_2] at h_semi_real
    have h_norm_τ₁_minus : 1/2 < ‖τ₁ - 1/2‖ := by linarith
    have h_norm_δ : ‖((δ : ℂ) * Complex.I)‖ = δ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hδ_pos]
    have h_sub_eq : τ₁ - (1/2 + δ * Complex.I) = (τ₁ - 1/2) - δ * Complex.I := by ring
    rw [h_sub_eq]
    have h_rtri := norm_sub_norm_le (τ₁ - 1/2) ((δ : ℂ) * Complex.I)
    rw [h_norm_δ] at h_rtri
    linarith
  · -- ‖τ₂ - (1/2 + δi)‖ > R₀.
    have h_semi_real : 1 < ‖2 * τ₂ - 1‖ := h₂_semi
    have h_eq : 2 * τ₂ - 1 = 2 * (τ₂ - 1/2) := by ring
    rw [h_eq, norm_mul] at h_semi_real
    have h_norm_2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h_norm_2] at h_semi_real
    have h_norm_τ₂_minus : 1/2 < ‖τ₂ - 1/2‖ := by linarith
    have h_norm_δ : ‖((δ : ℂ) * Complex.I)‖ = δ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hδ_pos]
    have h_sub_eq : τ₂ - (1/2 + δ * Complex.I) = (τ₂ - 1/2) - δ * Complex.I := by ring
    rw [h_sub_eq]
    have h_rtri := norm_sub_norm_le (τ₂ - 1/2) ((δ : ℂ) * Complex.I)
    rw [h_norm_δ] at h_rtri
    linarith

/-- **F_Y geometric setup adapted for the arc.**
A stronger variant of `modularLambdaH_F_Y_params_exist` that additionally
ensures `R₀ > √(1/4 − δ²)`, so the shifted-disk arc lies strictly inside
F^o (where each arc point satisfies `|τ − 1/2| > 1/2`).

This variant picks `δ` small enough relative to the buffer
`εᵢ := ‖τᵢ − 1/2‖² − 1/4 > 0` (from F^o) and the imaginary parts. The
choice `R₀ := 1/2 − δ²/4` lies in the narrow interval
`(√(1/4 − δ²), 1/2)` and admits `‖τᵢ − (1/2 + δ·i)‖ > R₀` provided
`δ ≤ εᵢ/(4 · τᵢ.im)`. -/
theorem modularLambdaH_F_Y_params_exist_arc
    {w : ℂ} (_hw : 0 < w.im)
    {τ₁ τ₂ : ℂ}
    (h₁_in : τ₁ ∈ Gamma2FundamentalDomainInterior)
    (h₂_in : τ₂ ∈ Gamma2FundamentalDomainInterior)
    {δ_max : ℝ} (hδ_max_pos : 0 < δ_max) (hδ_max_lt_quarter : δ_max ≤ 1 / 4) :
    ∃ δ Y R₀ : ℝ,
      0 < δ ∧ δ ≤ δ_max ∧ δ < τ₁.im ∧ δ < τ₂.im ∧
      δ < Y ∧ τ₁.im < Y ∧ τ₂.im < Y ∧
      0 < R₀ ∧ R₀ < 1 / 2 ∧ δ + R₀ < Y ∧
      Real.sqrt (1/4 - δ^2) < R₀ ∧
      ‖τ₁ - (1/2 + δ * Complex.I)‖ > R₀ ∧
      ‖τ₂ - (1/2 + δ * Complex.I)‖ > R₀ := by
  obtain ⟨h₁_im, _, _, h₁_semi⟩ := h₁_in
  obtain ⟨h₂_im, _, _, h₂_semi⟩ := h₂_in
  -- F^o gives ‖τᵢ - 1/2‖ > 1/2.
  have h_norm_τ₁_sub_gt : 1/2 < ‖τ₁ - 1/2‖ := by
    have h_semi : 1 < ‖2 * τ₁ - 1‖ := h₁_semi
    have h_eq : 2 * τ₁ - 1 = 2 * (τ₁ - 1/2) := by ring
    rw [h_eq, norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num] at h_semi
    linarith
  have h_norm_τ₂_sub_gt : 1/2 < ‖τ₂ - 1/2‖ := by
    have h_semi : 1 < ‖2 * τ₂ - 1‖ := h₂_semi
    have h_eq : 2 * τ₂ - 1 = 2 * (τ₂ - 1/2) := by ring
    rw [h_eq, norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num] at h_semi
    linarith
  have h_ε₁_pos : 0 < ‖τ₁ - 1/2‖^2 - 1/4 := by nlinarith [h_norm_τ₁_sub_gt]
  have h_ε₂_pos : 0 < ‖τ₂ - 1/2‖^2 - 1/4 := by nlinarith [h_norm_τ₂_sub_gt]
  -- Step 2: obtain δ as opaque value, with all needed bounds proven inside.
  have h_δ_exists : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ_max ∧ δ ≤ 1/4 ∧
      δ < τ₁.im ∧ δ < τ₂.im ∧
      2 * δ * τ₁.im ≤ (‖τ₁ - 1/2‖^2 - 1/4) / 2 ∧
      2 * δ * τ₂.im ≤ (‖τ₂ - 1/2‖^2 - 1/4) / 2 := by
    -- Pick the candidate δ as the min of five bounds.
    set b₁ : ℝ := τ₁.im / 2 with hb₁_def
    set b₂ : ℝ := τ₂.im / 2 with hb₂_def
    set bε₁ : ℝ := (‖τ₁ - 1/2‖^2 - 1/4) / (4 * τ₁.im) with hbε₁_def
    set bε₂ : ℝ := (‖τ₂ - 1/2‖^2 - 1/4) / (4 * τ₂.im) with hbε₂_def
    have hb₁_pos : 0 < b₁ := by rw [hb₁_def]; linarith
    have hb₂_pos : 0 < b₂ := by rw [hb₂_def]; linarith
    have hbε₁_pos : 0 < bε₁ := by rw [hbε₁_def]; positivity
    have hbε₂_pos : 0 < bε₂ := by rw [hbε₂_def]; positivity
    refine ⟨min (min (min b₁ b₂) δ_max) (min bε₁ bε₂), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 0 < δ.
      exact lt_min (lt_min (lt_min hb₁_pos hb₂_pos) hδ_max_pos) (lt_min hbε₁_pos hbε₂_pos)
    · -- δ ≤ δ_max.
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    · -- δ ≤ 1/4.
      exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) hδ_max_lt_quarter
    · -- δ < τ₁.im.
      have : min (min (min b₁ b₂) δ_max) (min bε₁ bε₂) ≤ b₁ :=
        le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
      rw [hb₁_def] at this
      linarith
    · -- δ < τ₂.im.
      have : min (min (min b₁ b₂) δ_max) (min bε₁ bε₂) ≤ b₂ :=
        le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
      rw [hb₂_def] at this
      linarith
    · -- 2δ·τ₁.im ≤ (‖τ₁-1/2‖²-1/4)/2.
      have h_δ_le_bε₁ : min (min (min b₁ b₂) δ_max) (min bε₁ bε₂) ≤ bε₁ :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      rw [hbε₁_def] at h_δ_le_bε₁
      have h_4τ₁_pos : 0 < 4 * τ₁.im := by linarith
      have h_mul : min (min (min b₁ b₂) δ_max) (min bε₁ bε₂) * (4 * τ₁.im) ≤
          ((‖τ₁ - 1/2‖^2 - 1/4) / (4 * τ₁.im)) * (4 * τ₁.im) :=
        mul_le_mul_of_nonneg_right h_δ_le_bε₁ (le_of_lt h_4τ₁_pos)
      rw [div_mul_cancel₀ _ (ne_of_gt h_4τ₁_pos)] at h_mul
      linarith
    · -- 2δ·τ₂.im ≤ (‖τ₂-1/2‖²-1/4)/2.
      have h_δ_le_bε₂ : min (min (min b₁ b₂) δ_max) (min bε₁ bε₂) ≤ bε₂ :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      rw [hbε₂_def] at h_δ_le_bε₂
      have h_4τ₂_pos : 0 < 4 * τ₂.im := by linarith
      have h_mul : min (min (min b₁ b₂) δ_max) (min bε₁ bε₂) * (4 * τ₂.im) ≤
          ((‖τ₂ - 1/2‖^2 - 1/4) / (4 * τ₂.im)) * (4 * τ₂.im) :=
        mul_le_mul_of_nonneg_right h_δ_le_bε₂ (le_of_lt h_4τ₂_pos)
      rw [div_mul_cancel₀ _ (ne_of_gt h_4τ₂_pos)] at h_mul
      linarith
  -- Now obtain δ as opaque.
  obtain ⟨δ, hδ_pos, hδ_le_δ_max, hδ_le_quarter, hδ_lt_τ₁_im, hδ_lt_τ₂_im,
    h_2δ_τ₁_le, h_2δ_τ₂_le⟩ := h_δ_exists
  -- Step 3: compute Y and R₀.
  set Y : ℝ := max (max (τ₁.im + 1) (τ₂.im + 1)) 1 with hY_def
  have hY_ge_one : (1 : ℝ) ≤ Y := le_max_right _ _
  have hY_gt_τ₁_im : τ₁.im < Y := by
    have : τ₁.im + 1 ≤ Y := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hY_gt_τ₂_im : τ₂.im < Y := by
    have : τ₂.im + 1 ≤ Y := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hY_gt_δ : δ < Y := by linarith
  set R₀ : ℝ := 1/2 - δ^2/4 with hR₀_def
  have h_δ_sq_pos : 0 < δ^2 := by positivity
  have h_δ_sq_le_inv16 : δ^2 ≤ 1/16 := by nlinarith
  have hR₀_pos : 0 < R₀ := by rw [hR₀_def]; linarith
  have hR₀_lt_half : R₀ < 1/2 := by rw [hR₀_def]; linarith
  have h_δ_plus_R₀_lt_Y : δ + R₀ < Y := by
    rw [hR₀_def]
    have h_δ_sq_nn : (0:ℝ) ≤ δ^2/4 := by positivity
    linarith
  -- R₀ > √(1/4 - δ²).
  have h_arg_nn : (0:ℝ) ≤ 1/4 - δ^2 := by linarith
  have h_R₀_sq_eq : R₀^2 = 1/4 - δ^2/4 + δ^4/16 := by rw [hR₀_def]; ring
  have h_R₀_sq_gt : 1/4 - δ^2 < R₀^2 := by
    rw [h_R₀_sq_eq]
    have h_3δ_sq_pos : 0 < 3 * δ^2 / 4 := by positivity
    have h_δ_4_nn : (0:ℝ) ≤ δ^4 / 16 := by positivity
    linarith
  have h_sqrt_lt_R₀ : Real.sqrt (1/4 - δ^2) < R₀ := by
    have h_sqrt_lt_sqrt : Real.sqrt (1/4 - δ^2) < Real.sqrt (R₀^2) :=
      Real.sqrt_lt_sqrt h_arg_nn h_R₀_sq_gt
    rw [Real.sqrt_sq hR₀_pos.le] at h_sqrt_lt_sqrt
    exact h_sqrt_lt_sqrt
  -- Pre-compute the shared inequality δ⁴/16 ≤ δ²/4.
  have h_δ4_le_δ2 : δ^4 / 16 ≤ δ^2 / 4 := by nlinarith [h_δ_sq_pos, h_δ_sq_le_inv16]
  -- Helper: compute the squared norm of `τ - (1/2 + δi)` for any τ : ℂ.
  -- Cast `1/2 : ℂ` as `((1/2 : ℝ) : ℂ)` so `Complex.ofReal_re`/`Complex.ofReal_im`
  -- can reduce the complex arithmetic uniformly.
  have h_half_cast : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by push_cast; ring
  have h_normSq : ∀ (z : ℂ),
      ‖z - (1/2 + (δ : ℂ) * Complex.I)‖^2 = ‖z - 1/2‖^2 - 2*δ*z.im + δ^2 := by
    intro z
    rw [h_half_cast, Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm,
      Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- Pre-compute the squared norm bounds for τ₁ and τ₂.
  have h_τ₁_normSq_gt : R₀^2 < ‖τ₁ - (1/2 + (δ : ℂ) * Complex.I)‖^2 := by
    rw [h_normSq τ₁, h_R₀_sq_eq]
    linarith [h_2δ_τ₁_le, h_ε₁_pos, h_δ_sq_pos, h_δ4_le_δ2]
  have h_τ₂_normSq_gt : R₀^2 < ‖τ₂ - (1/2 + (δ : ℂ) * Complex.I)‖^2 := by
    rw [h_normSq τ₂, h_R₀_sq_eq]
    linarith [h_2δ_τ₂_le, h_ε₂_pos, h_δ_sq_pos, h_δ4_le_δ2]
  -- Take square roots.
  have h_τ₁_norm_gt : R₀ < ‖τ₁ - (1/2 + (δ : ℂ) * Complex.I)‖ := by
    have h_sqrt_lt : Real.sqrt (R₀^2) <
        Real.sqrt (‖τ₁ - (1/2 + (δ : ℂ) * Complex.I)‖^2) :=
      Real.sqrt_lt_sqrt (sq_nonneg _) h_τ₁_normSq_gt
    rw [Real.sqrt_sq hR₀_pos.le, Real.sqrt_sq (norm_nonneg _)] at h_sqrt_lt
    exact h_sqrt_lt
  have h_τ₂_norm_gt : R₀ < ‖τ₂ - (1/2 + (δ : ℂ) * Complex.I)‖ := by
    have h_sqrt_lt : Real.sqrt (R₀^2) <
        Real.sqrt (‖τ₂ - (1/2 + (δ : ℂ) * Complex.I)‖^2) :=
      Real.sqrt_lt_sqrt (sq_nonneg _) h_τ₂_normSq_gt
    rw [Real.sqrt_sq hR₀_pos.le, Real.sqrt_sq (norm_nonneg _)] at h_sqrt_lt
    exact h_sqrt_lt
  exact ⟨δ, Y, R₀, hδ_pos, hδ_le_δ_max, hδ_lt_τ₁_im, hδ_lt_τ₂_im, hY_gt_δ,
    hY_gt_τ₁_im, hY_gt_τ₂_im, hR₀_pos, hR₀_lt_half, h_δ_plus_R₀_lt_Y, h_sqrt_lt_R₀,
    h_τ₁_norm_gt, h_τ₂_norm_gt⟩

/-- **Analyticity on the closed F_Y region.** Given F_Y
parameters with `δ > 0`, the function `g(τ) := λ(τ) − w` is analytic on
an open neighbourhood of the closed F_Y region
`(Set.Icc 0 1 ×ℂ Set.Icc δ Y) \ Metric.ball (1/2 + δ·i) R₀`.

Proof: the F_Y region is contained in the open upper half-plane (since
its bottom edge sits at `Im τ = δ > 0`), where `λ` is analytic by
`modularLambdaH_differentiableOn`. Subtracting the constant `w`
preserves analyticity. -/
theorem modularLambdaH_F_Y_analytic
    (w : ℂ) {δ Y R₀ : ℝ} (hδ : 0 < δ) (_hδY : δ < Y) (_hR₀ : 0 < R₀) :
    AnalyticOnNhd ℂ (fun τ => modularLambdaH τ - w)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀) := by
  intro τ hτ
  obtain ⟨h_box, _⟩ := hτ
  rw [Complex.mem_reProdIm] at h_box
  obtain ⟨_, h_im⟩ := h_box
  rw [Set.mem_Icc] at h_im
  have hτ_im_pos : 0 < τ.im := lt_of_lt_of_le hδ h_im.1
  have h_open_H : IsOpen ({z : ℂ | 0 < z.im} : Set ℂ) := by
    have h_set_eq : ({z : ℂ | 0 < z.im} : Set ℂ) = Complex.im ⁻¹' Set.Ioi 0 := by
      ext; simp
    rw [h_set_eq]
    exact isOpen_Ioi.preimage Complex.continuous_im
  have h_lam_an : AnalyticAt ℂ modularLambdaH τ :=
    (modularLambdaH_differentiableOn.analyticOnNhd h_open_H) τ hτ_im_pos
  exact h_lam_an.sub analyticAt_const

/-- **Left edge non-vanishing.** For `w ∈ ℍ` and any
`y > 0`, `λ(0 + i·y) − w ≠ 0`. Direct from
`modularLambdaH_left_edge_ne_of_im_pos`. -/
theorem modularLambdaH_F_Y_left_edge_ne
    {w : ℂ} (hw : 0 < w.im) {y : ℝ} (hy : 0 < y) :
    modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0 := by
  intro h_eq
  have h_lam_eq : modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) = w := by
    linear_combination h_eq
  have h_z_eq : ((0 : ℂ) + (y : ℂ) * Complex.I) = Complex.I * y := by ring
  rw [h_z_eq] at h_lam_eq
  exact modularLambdaH_left_edge_ne_of_im_pos hw hy h_lam_eq

/-- **Right edge non-vanishing.** For `w ∈ ℍ` and any
`y > 0`, `λ(1 + i·y) − w ≠ 0`. Direct from
`modularLambdaH_right_edge_ne_of_im_pos`. -/
theorem modularLambdaH_F_Y_right_edge_ne
    {w : ℂ} (hw : 0 < w.im) {y : ℝ} (hy : 0 < y) :
    modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0 := by
  intro h_eq
  have h_lam_eq : modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) = w := by
    linear_combination h_eq
  have h_z_eq : ((1 : ℂ) + (y : ℂ) * Complex.I) = 1 + Complex.I * y := by ring
  rw [h_z_eq] at h_lam_eq
  exact modularLambdaH_right_edge_ne_of_im_pos hw hy h_lam_eq

/-- **Top edge non-vanishing for `Y` sufficiently large.**
For `w ∈ ℍ`, there exists `Y₀` such that for all `Y ≥ Y₀` and
`x ∈ [0, 1]`, `λ(x + i·Y) − w ≠ 0`. Direct from
`modularLambdaH_top_edge_far_of_im_pos`. -/
theorem modularLambdaH_F_Y_top_edge_ne {w : ℂ} (hw : 0 < w.im) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0 := by
  obtain ⟨Y₀, hY₀⟩ := modularLambdaH_top_edge_far_of_im_pos hw
  refine ⟨Y₀, fun Y hY x hx_nn hx_le h_eq => ?_⟩
  have h_lam_eq : modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) = w := by
    linear_combination h_eq
  exact hY₀ Y hY x hx_nn hx_le h_lam_eq

/-- **Bot_left coupled strip non-vanishing.** For
`w ∈ ℍ`, there exists `δ_w ∈ (0, 1/2)` such that for all
`δ ∈ (0, δ_w]` and `x ∈ [0, δ]`, `λ(x + i·δ) − w ≠ 0`.

The strip width is coupled to `δ` (matching the bot_left segment of
the F_Y region when `R₀ = 1/2 − δ`). For `τ = x + δi` with `x ≤ δ`,
`|τ| ≤ δ√2`, so `Im(−1/τ) = δ/(x² + δ²) ≥ 1/(2δ)`. For `δ ≤ 1/2`,
this gives `Im(−1/τ) ≥ 1`, and
`modularLambdaH_norm_le_exp_of_im_ge_one` yields
`‖λ(−1/τ)‖ ≤ 160000·exp(−π/(2δ))`. By the S-action identity
`modularLambdaH_add_S_smul_eq_one` (`λ(τ) + λ(−1/τ) = 1`),
`‖λ(τ) − 1‖ ≤ 160000·exp(−π/(2δ))`. Since `w ∈ ℍ`, `w ≠ 1` and
`‖w − 1‖ > 0`. For `δ` sufficiently small, the exponential bound
beats `‖w − 1‖`, forcing `λ(τ) ≠ w`. -/
theorem modularLambdaH_F_Y_bot_left_strip_ne
    {w : ℂ} (hw : 0 < w.im) :
    ∃ δ_w : ℝ, 0 < δ_w ∧ δ_w < 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ_w → ∀ x : ℝ,
      0 ≤ x → x ≤ δ →
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0 := by
  have hw_ne_one : w ≠ 1 := fun h_eq => by rw [h_eq] at hw; simp at hw
  have hw_one_norm_pos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw_ne_one)
  set L : ℝ := Real.log (160000 / ‖w - 1‖) with hL_def
  set M : ℝ := max L 1 with hM_def
  have hM_ge_one : 1 ≤ M := le_max_right _ _
  have hM_pos : 0 < M := by linarith
  have hL_le_M : L ≤ M := le_max_left _ _
  set δ_w : ℝ := min (1/4) (1/(2*M)) with hδ_w_def
  have h_2M_pos : 0 < 2 * M := by linarith
  have hδ_w_pos : 0 < δ_w := lt_min (by norm_num) (by positivity)
  have hδ_w_lt_half : δ_w < 1/2 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨δ_w, hδ_w_pos, hδ_w_lt_half, ?_⟩
  intro δ hδ_pos hδ_le x hx_nn hx_le h_eq
  set τ : ℂ := (x : ℂ) + (δ : ℂ) * Complex.I with hτ_def
  have h_lam_eq : modularLambdaH τ = w := by linear_combination h_eq
  have hτ_re : τ.re = x := by
    simp [hτ_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im : τ.im = δ := by
    simp [hτ_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im_pos : 0 < τ.im := hτ_im ▸ hδ_pos
  have hδ_le_quarter : δ ≤ 1/4 := le_trans hδ_le (min_le_left _ _)
  have hδ_le_inv_2M : δ ≤ 1/(2*M) := le_trans hδ_le (min_le_right _ _)
  have h_2δ_pos : 0 < 2 * δ := by linarith
  have h_x_sq_le_δ_sq : x^2 ≤ δ^2 := by nlinarith
  have h_x_sq_plus_δ_sq_pos : 0 < x^2 + δ^2 := by nlinarith
  have h_normSq : Complex.normSq τ = x^2 + δ^2 := by
    rw [Complex.normSq_apply, hτ_re, hτ_im]; ring
  -- Im(-1/τ) = δ/(x² + δ²).
  have h_im_inv : (-(τ : ℂ)⁻¹).im = δ / (x^2 + δ^2) := by
    rw [Complex.neg_im, Complex.inv_im, hτ_im, h_normSq]; ring
  -- 1/(2δ) ≤ Im(-1/τ): equivalent to x² + δ² ≤ 2δ² (i.e., x² ≤ δ²).
  have h_im_inv_ge : 1/(2*δ) ≤ (-(τ : ℂ)⁻¹).im := by
    rw [h_im_inv, div_le_div_iff₀ h_2δ_pos h_x_sq_plus_δ_sq_pos]
    nlinarith
  -- 1/(2δ) ≥ 2 (since δ ≤ 1/4).
  have h_inv_2δ_ge_two : 2 ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]; linarith
  have h_inv_im_ge_one : 1 ≤ (-(τ : ℂ)⁻¹).im := by linarith
  -- Apply norm bound to -1/τ.
  have h_norm_lam_inv : ‖modularLambdaH (-(τ : ℂ)⁻¹)‖ ≤
      160000 * Real.exp (-Real.pi * (-(τ : ℂ)⁻¹).im) :=
    modularLambdaH_norm_le_exp_of_im_ge_one h_inv_im_ge_one
  -- Apply S-action identity: λ(τ) + λ(-1/τ) = 1.
  have h_S : modularLambdaH τ + modularLambdaH (-1/τ) = 1 :=
    modularLambdaH_add_S_smul_eq_one hτ_im_pos
  have h_neg_eq : -1/τ = -τ⁻¹ := by field_simp
  rw [h_neg_eq] at h_S
  -- ‖λ(τ) - 1‖ = ‖λ(-τ⁻¹)‖.
  have h_diff_eq : modularLambdaH τ - 1 = -modularLambdaH (-(τ : ℂ)⁻¹) := by
    linear_combination h_S
  have h_norm_diff : ‖modularLambdaH τ - 1‖ = ‖modularLambdaH (-(τ : ℂ)⁻¹)‖ := by
    rw [h_diff_eq, norm_neg]
  -- ‖λ(τ) - 1‖ ≤ 160000 · exp(-π · 1/(2δ)).
  have h_exp_mono : Real.exp (-Real.pi * (-(τ : ℂ)⁻¹).im) ≤
      Real.exp (-Real.pi * (1/(2*δ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, h_im_inv_ge]
  have h_bound : ‖modularLambdaH τ - 1‖ ≤ 160000 * Real.exp (-Real.pi * (1/(2*δ))) := by
    rw [h_norm_diff]
    refine le_trans h_norm_lam_inv ?_
    exact mul_le_mul_of_nonneg_left h_exp_mono (by norm_num)
  -- M ≤ 1/(2δ): δ ≤ 1/(2M) means 2δM ≤ 1.
  have h_M_le_inv_2δ : M ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]
    have h_step : δ * (2 * M) ≤ (1/(2*M)) * (2 * M) :=
      mul_le_mul_of_nonneg_right hδ_le_inv_2M (le_of_lt h_2M_pos)
    rw [div_mul_cancel₀ _ (ne_of_gt h_2M_pos)] at h_step
    linarith
  -- π * (1/(2δ)) > L since π > 1 and M ≥ L: π · M > M ≥ L, and π/(2δ) ≥ π·M.
  have h_pi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have h_pi_M_ge_pi_M : Real.pi * M ≤ Real.pi * (1/(2*δ)) :=
    mul_le_mul_of_nonneg_left h_M_le_inv_2δ (le_of_lt Real.pi_pos)
  have h_L_lt_pi_M : L < Real.pi * M := by
    calc L ≤ M := hL_le_M
      _ = 1 * M := by ring
      _ < Real.pi * M := by exact mul_lt_mul_of_pos_right h_pi_gt_one hM_pos
  have h_L_lt_pi_inv_2δ : L < Real.pi * (1/(2*δ)) :=
    lt_of_lt_of_le h_L_lt_pi_M h_pi_M_ge_pi_M
  -- exp(-π·(1/(2δ))) < exp(-L) = ‖w-1‖/160000.
  have h_exp_lt : Real.exp (-Real.pi * (1/(2*δ))) < Real.exp (-L) := by
    apply Real.exp_lt_exp.mpr
    linarith
  have h_quot_pos : (0 : ℝ) < 160000 / ‖w - 1‖ := by positivity
  have h_exp_neg_L : Real.exp (-L) = ‖w - 1‖ / 160000 := by
    rw [hL_def]
    rw [show -Real.log (160000 / ‖w - 1‖) = Real.log ((160000 / ‖w - 1‖)⁻¹) from
      (Real.log_inv _).symm]
    rw [Real.exp_log (by positivity : (0:ℝ) < (160000 / ‖w - 1‖)⁻¹)]
    rw [inv_div]
  have h_final_bound : 160000 * Real.exp (-Real.pi * (1/(2*δ))) < ‖w - 1‖ := by
    calc 160000 * Real.exp (-Real.pi * (1/(2*δ)))
        < 160000 * Real.exp (-L) := by
          exact mul_lt_mul_of_pos_left h_exp_lt (by norm_num)
      _ = 160000 * (‖w - 1‖ / 160000) := by rw [h_exp_neg_L]
      _ = ‖w - 1‖ := by field_simp
  have h_strict : ‖modularLambdaH τ - 1‖ < ‖w - 1‖ := lt_of_le_of_lt h_bound h_final_bound
  rw [h_lam_eq] at h_strict
  exact lt_irrefl _ h_strict

/-- **Bot_right coupled strip non-vanishing.** For
`w ∈ ℍ`, there exists `δ_w ∈ (0, 1/2)` such that for all
`δ ∈ (0, δ_w]` and `x ∈ [1 − δ, 1]`, `λ(x + i·δ) − w ≠ 0`.

The strip width is coupled to `δ` (matching the bot_right segment of
the F_Y region when `R₀ = 1/2 − δ`). For `τ = x + δi` with
`x ∈ [1 − δ, 1]`, write `τ − 1 = (x − 1) + δi` and use conjugation
symmetry `modularLambdaH_conj_symmetry` to relate to the bot_left
strip point `(1 − x) + δi`. By `modularLambdaH_F_Y_bot_left_strip_ne` applied to `(1 − x) + δi`,
`‖λ((1 − x) + δi) − 1‖` is small for `δ` small; hence
`‖λ(τ − 1) − 1‖` is small (conjugation preserves the bound).
The T-action identity `modularLambdaH_add_one_eq_div_sub_one`
(`λ(τ) = λ(τ − 1)/(λ(τ − 1) − 1)`) then gives `|λ(τ)|` large for
`λ(τ − 1)` close to 1, forcing `λ(τ) ≠ w`. -/
theorem modularLambdaH_F_Y_bot_right_strip_ne
    {w : ℂ} (_hw : 0 < w.im) :
    ∃ δ_w : ℝ, 0 < δ_w ∧ δ_w < 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ_w → ∀ x : ℝ,
      1 - δ ≤ x → x ≤ 1 →
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0 := by
  -- Target: ‖λ(τ - 1) - 1‖ < 1/(‖w‖ + 2). Then |λ(τ)| ≥ ‖w‖ + 1 > ‖w‖, so λ(τ) ≠ w.
  set L : ℝ := Real.log (160000 * (‖w‖ + 2)) with hL_def
  set M : ℝ := max L 1 with hM_def
  have hM_ge_one : 1 ≤ M := le_max_right _ _
  have hM_pos : 0 < M := by linarith
  have hL_le_M : L ≤ M := le_max_left _ _
  set δ_w : ℝ := min (1/4) (1/(2*M)) with hδ_w_def
  have h_2M_pos : 0 < 2 * M := by linarith
  have hδ_w_pos : 0 < δ_w := lt_min (by norm_num) (by positivity)
  have hδ_w_lt_half : δ_w < 1/2 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨δ_w, hδ_w_pos, hδ_w_lt_half, ?_⟩
  intro δ hδ_pos hδ_le x hx_ge hx_le h_eq
  set τ : ℂ := (x : ℂ) + (δ : ℂ) * Complex.I with hτ_def
  have h_lam_eq : modularLambdaH τ = w := by linear_combination h_eq
  have hτ_re : τ.re = x := by
    simp [hτ_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im : τ.im = δ := by
    simp [hτ_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im_pos : 0 < τ.im := hτ_im ▸ hδ_pos
  have hδ_le_quarter : δ ≤ 1/4 := le_trans hδ_le (min_le_left _ _)
  have hδ_le_inv_2M : δ ≤ 1/(2*M) := le_trans hδ_le (min_le_right _ _)
  have h_2δ_pos : 0 < 2 * δ := by linarith
  -- Define τ' := (1 - x) + δi (in bot_left strip).
  set τ' : ℂ := ((1 - x : ℝ) : ℂ) + (δ : ℂ) * Complex.I with hτ'_def
  have hτ'_re : τ'.re = 1 - x := by
    simp [hτ'_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ'_im : τ'.im = δ := by
    simp [hτ'_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ'_im_pos : 0 < τ'.im := hτ'_im ▸ hδ_pos
  have hτ'_re_nn : 0 ≤ τ'.re := by rw [hτ'_re]; linarith
  have hτ'_re_le_δ : τ'.re ≤ δ := by rw [hτ'_re]; linarith
  -- σ := τ - 1.
  set σ : ℂ := τ - 1 with hσ_def
  have hσ_im : σ.im = δ := by simp [hσ_def, hτ_im]
  have hσ_im_pos : 0 < σ.im := hσ_im ▸ hδ_pos
  -- -conj σ = τ', so λ(τ') = conj(λ(σ)).
  have h_neg_conj_σ : -(starRingEnd ℂ σ) = τ' := by
    apply Complex.ext
    · simp [hσ_def, hτ_def, hτ'_def, Complex.neg_re,
        Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    · simp [hσ_def, hτ_def, hτ'_def, Complex.neg_im,
        Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
  have h_conj_lam : modularLambdaH τ' = starRingEnd ℂ (modularLambdaH σ) := by
    rw [← h_neg_conj_σ]
    exact modularLambdaH_conj_symmetry hσ_im_pos
  -- Cusp-0 bound on τ' (in bot_left strip):
  -- For τ' = (1-x) + δi with (1-x) ∈ [0, δ] and δ ∈ (0, 1/4]:
  -- Compute Im(-1/τ'), apply norm bound, apply S-action identity.
  have h_x_sq_le_δ_sq : (1 - x)^2 ≤ δ^2 := by nlinarith
  have h_x_sq_plus_δ_sq_pos : 0 < (1 - x)^2 + δ^2 := by nlinarith
  have h_normSq_τ' : Complex.normSq τ' = (1 - x)^2 + δ^2 := by
    rw [Complex.normSq_apply, hτ'_re, hτ'_im]; ring
  have h_im_inv_τ' : (-(τ' : ℂ)⁻¹).im = δ / ((1 - x)^2 + δ^2) := by
    rw [Complex.neg_im, Complex.inv_im, hτ'_im, h_normSq_τ']; ring
  have h_im_inv_τ'_ge : 1/(2*δ) ≤ (-(τ' : ℂ)⁻¹).im := by
    rw [h_im_inv_τ', div_le_div_iff₀ h_2δ_pos h_x_sq_plus_δ_sq_pos]
    nlinarith
  have h_inv_2δ_ge_two : 2 ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]; linarith
  have h_inv_im_τ'_ge_one : 1 ≤ (-(τ' : ℂ)⁻¹).im := by linarith
  have h_norm_lam_inv_τ' : ‖modularLambdaH (-(τ' : ℂ)⁻¹)‖ ≤
      160000 * Real.exp (-Real.pi * (-(τ' : ℂ)⁻¹).im) :=
    modularLambdaH_norm_le_exp_of_im_ge_one h_inv_im_τ'_ge_one
  have h_S_τ' : modularLambdaH τ' + modularLambdaH (-1/τ') = 1 :=
    modularLambdaH_add_S_smul_eq_one hτ'_im_pos
  have h_neg_eq_τ' : -1/τ' = -τ'⁻¹ := by field_simp
  rw [h_neg_eq_τ'] at h_S_τ'
  have h_diff_τ' : modularLambdaH τ' - 1 = -modularLambdaH (-(τ' : ℂ)⁻¹) := by
    linear_combination h_S_τ'
  have h_norm_diff_τ' : ‖modularLambdaH τ' - 1‖ = ‖modularLambdaH (-(τ' : ℂ)⁻¹)‖ := by
    rw [h_diff_τ', norm_neg]
  have h_exp_mono_τ' : Real.exp (-Real.pi * (-(τ' : ℂ)⁻¹).im) ≤
      Real.exp (-Real.pi * (1/(2*δ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, h_im_inv_τ'_ge]
  have h_bound_τ' : ‖modularLambdaH τ' - 1‖ ≤ 160000 * Real.exp (-Real.pi * (1/(2*δ))) := by
    rw [h_norm_diff_τ']
    exact le_trans h_norm_lam_inv_τ' (mul_le_mul_of_nonneg_left h_exp_mono_τ' (by norm_num))
  -- M ≤ 1/(2δ), so π·M ≤ π/(2δ).
  have h_M_le_inv_2δ : M ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]
    have h_step : δ * (2 * M) ≤ (1/(2*M)) * (2 * M) :=
      mul_le_mul_of_nonneg_right hδ_le_inv_2M (le_of_lt h_2M_pos)
    rw [div_mul_cancel₀ _ (ne_of_gt h_2M_pos)] at h_step
    linarith
  have h_pi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have h_pi_inv_2δ_ge_pi_M : Real.pi * M ≤ Real.pi * (1/(2*δ)) :=
    mul_le_mul_of_nonneg_left h_M_le_inv_2δ (le_of_lt Real.pi_pos)
  have h_L_lt_pi_M : L < Real.pi * M := by
    calc L ≤ M := hL_le_M
      _ = 1 * M := by ring
      _ < Real.pi * M := mul_lt_mul_of_pos_right h_pi_gt_one hM_pos
  have h_L_lt_pi_inv_2δ : L < Real.pi * (1/(2*δ)) :=
    lt_of_lt_of_le h_L_lt_pi_M h_pi_inv_2δ_ge_pi_M
  have h_exp_lt : Real.exp (-Real.pi * (1/(2*δ))) < Real.exp (-L) := by
    apply Real.exp_lt_exp.mpr; linarith
  have h_w_norm_plus_two_pos : (0 : ℝ) < ‖w‖ + 2 := by
    have : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
    linarith
  have h_exp_neg_L : Real.exp (-L) = 1 / (160000 * (‖w‖ + 2)) := by
    rw [hL_def]
    rw [show -Real.log (160000 * (‖w‖ + 2)) = Real.log ((160000 * (‖w‖ + 2))⁻¹) from
      (Real.log_inv _).symm]
    rw [Real.exp_log (by positivity : (0:ℝ) < (160000 * (‖w‖ + 2))⁻¹)]
    rw [one_div]
  have h_final_bound : 160000 * Real.exp (-Real.pi * (1/(2*δ))) < 1 / (‖w‖ + 2) := by
    calc 160000 * Real.exp (-Real.pi * (1/(2*δ)))
        < 160000 * Real.exp (-L) := mul_lt_mul_of_pos_left h_exp_lt (by norm_num)
      _ = 160000 * (1 / (160000 * (‖w‖ + 2))) := by rw [h_exp_neg_L]
      _ = 1 / (‖w‖ + 2) := by field_simp
  have h_strict_τ' : ‖modularLambdaH τ' - 1‖ < 1 / (‖w‖ + 2) :=
    lt_of_le_of_lt h_bound_τ' h_final_bound
  -- Transfer to σ via conjugation.
  have h_norm_diff_σ : ‖modularLambdaH σ - 1‖ = ‖modularLambdaH τ' - 1‖ := by
    rw [h_conj_lam]
    rw [show starRingEnd ℂ (modularLambdaH σ) - 1 = starRingEnd ℂ (modularLambdaH σ - 1) by
      rw [map_sub, map_one]]
    rw [norm_conj]
  have h_strict_σ : ‖modularLambdaH σ - 1‖ < 1 / (‖w‖ + 2) := by
    rw [h_norm_diff_σ]; exact h_strict_τ'
  -- T-action: λ(τ) = λ(σ + 1) = λ(σ)/(λ(σ) - 1).
  have h_T : modularLambdaH (σ + 1) = modularLambdaH σ / (modularLambdaH σ - 1) :=
    modularLambdaH_add_one_eq_div_sub_one hσ_im_pos
  have h_σ_plus_one : σ + 1 = τ := by simp [hσ_def]
  rw [h_σ_plus_one] at h_T
  -- λ(σ) - 1 ≠ 0 from λ(σ) ≠ 1.
  have h_lam_σ_sub_one_ne : modularLambdaH σ - 1 ≠ 0 :=
    sub_ne_zero.mpr (modularLambdaH_ne_one hσ_im_pos)
  -- |λ(σ)| ≥ 1 - ‖λ(σ) - 1‖.
  have h_lam_σ_norm_ge : 1 - ‖modularLambdaH σ - 1‖ ≤ ‖modularLambdaH σ‖ := by
    have h_rtri : ‖(1 : ℂ)‖ - ‖modularLambdaH σ‖ ≤ ‖(1 : ℂ) - modularLambdaH σ‖ :=
      norm_sub_norm_le (1 : ℂ) (modularLambdaH σ)
    have h_simp : (1 : ℂ) - modularLambdaH σ = -(modularLambdaH σ - 1) := by ring
    rw [norm_one, h_simp, norm_neg] at h_rtri
    linarith
  -- Now: |λ(τ)| = |λ(σ)| / |λ(σ) - 1|.
  have h_norm_lam_τ : ‖modularLambdaH τ‖ = ‖modularLambdaH σ‖ / ‖modularLambdaH σ - 1‖ := by
    rw [h_T, norm_div]
  -- We want |λ(τ)| > ‖w‖.
  -- |λ(σ)| ≥ 1 - c, |λ(σ) - 1| < 1/(‖w‖ + 2) where c = ‖λ(σ) - 1‖.
  -- |λ(σ)| / |λ(σ) - 1| ≥ (1 - c)/c > ‖w‖ + 1 > ‖w‖.
  set c : ℝ := ‖modularLambdaH σ - 1‖ with hc_def
  have hc_lt : c < 1 / (‖w‖ + 2) := h_strict_σ
  have hc_pos : 0 < c := by
    rw [hc_def, norm_pos_iff]; exact h_lam_σ_sub_one_ne
  have h_one_minus_c_pos : 0 < 1 - c := by
    have : c < 1 := by
      have h_inv_pos : (0 : ℝ) < 1 / (‖w‖ + 2) := by positivity
      have h_inv_lt_one : 1 / (‖w‖ + 2) ≤ 1 := by
        rw [div_le_iff₀ h_w_norm_plus_two_pos]; linarith [norm_nonneg w]
      linarith
    linarith
  have h_lam_σ_norm_pos : 0 < ‖modularLambdaH σ‖ := by linarith [h_lam_σ_norm_ge]
  -- (1 - c)/c > ‖w‖: equiv to (1 - c) > c·‖w‖, i.e., 1 > c·(‖w‖ + 1), i.e., c < 1/(‖w‖ + 1).
  have h_w_plus_one_pos : (0 : ℝ) < ‖w‖ + 1 := by linarith [norm_nonneg w]
  have hc_lt_inv : c < 1 / (‖w‖ + 1) := by
    calc c < 1 / (‖w‖ + 2) := hc_lt
      _ ≤ 1 / (‖w‖ + 1) := by
        apply one_div_le_one_div_of_le h_w_plus_one_pos
        linarith
  have h_c_w_plus_one_lt_one : c * (‖w‖ + 1) < 1 := by
    have := hc_lt_inv
    rw [lt_div_iff₀ h_w_plus_one_pos] at this
    linarith
  have h_norm_lam_τ_gt : ‖w‖ < ‖modularLambdaH τ‖ := by
    rw [h_norm_lam_τ]
    rw [lt_div_iff₀ hc_pos]
    calc ‖w‖ * c = c * ‖w‖ := by ring
      _ < c * ‖w‖ + (1 - c * (‖w‖ + 1)) := by linarith [h_c_w_plus_one_lt_one]
      _ = 1 - c := by ring
      _ ≤ ‖modularLambdaH σ‖ := h_lam_σ_norm_ge
  -- λ(τ) = w would give ‖λ(τ)‖ = ‖w‖. Contradiction.
  rw [h_lam_eq] at h_norm_lam_τ_gt
  exact lt_irrefl _ h_norm_lam_τ_gt

end NoWanderingDomains
