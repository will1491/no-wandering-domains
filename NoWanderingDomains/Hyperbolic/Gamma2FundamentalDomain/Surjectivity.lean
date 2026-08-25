/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.Gamma2FundamentalDomain.CuspAsymptotics

/-! # The biholomorphism on `F°` and surjectivity of `λ`

The strip claim `Im λ ≥ 0` on `{0 < Re < 1, Im ≥ 1}`, its cusp-neighbourhood
transports to `B(0, 1/3)` and `B(1, 1/3)` inside `F°`, and the Phragmén–Lindelöf-style
closure `Im λ ≥ 0` on all of `F°` via the maximum modulus principle applied to
`exp (I • λ)`. These combine with the open-mapping theorem and a sequential-compactness
properness argument to establish the biholomorphism `λ(F°) = {Im w > 0}`. Surjectivity
of `λ` onto the triply-punctured plane `ℂ ∖ {0, 1}` follows, both on `ℍ`
(`modularLambdaH_image`) and on the unit disk (`modularLambda_image`).
-/

namespace NoWanderingDomains
open Complex Filter Topology Set

/-- **Strip claim for `λ`: `Im λ ≥ 0` on `{Re ∈ (0, 1), Im ≥ 1}`.**

The strip `{w ∈ ℂ : 0 < w.re < 1, 1 ≤ w.im}` is contained in `F^o`
(the F^o constraint `‖2w − 1‖ > 1` is automatic for `Im w ≥ 1` since
`‖2w − 1‖² = (2 Re w − 1)² + (2 Im w)² ≥ 0 + 4 > 1`), so this is a
sub-region of Step A. The closure is independent of
`modularLambdaH_im_nonneg_on_F` to avoid the cyclic dependency
strip → F^o → cusp-1 → strip.

The proof is a case split on `Re w`:
* `Re w ∈ [1/8, 7/8]`: three-term q-expansion bound
  (`modularLambdaH_im_nonneg_strip_interior_band`).
* `Re w ∈ (0, 1/8)`: linearization at `Re w = 0`
  (`modularLambdaH_im_nonneg_strip_left_edge`).
* `Re w ∈ (7/8, 1)`: reduction to the left edge via T-shift +
  conjugation symmetry (`modularLambdaH_im_nonneg_strip_right_edge`). -/
theorem modularLambdaH_im_nonneg_strip (w : ℂ) (hw_re_pos : 0 < w.re)
    (hw_re_lt : w.re < 1) (hw_im_ge : 1 ≤ w.im) :
    0 ≤ (modularLambdaH w).im := by
  rcases lt_or_ge w.re ((1 : ℝ) / 8) with h1 | h1
  · exact modularLambdaH_im_nonneg_strip_left_edge w hw_re_pos h1 hw_im_ge
  · rcases le_or_gt w.re ((7 : ℝ) / 8) with h2 | h2
    · exact modularLambdaH_im_nonneg_strip_interior_band w h1 h2 hw_im_ge
    · exact modularLambdaH_im_nonneg_strip_right_edge w h2 hw_re_lt hw_im_ge

/-- **Cusp 1 asymptotic in `F^o` (the deep step).** There is a
neighbourhood of `1` in which every point of `F^o` has `Im λ ≥ 0`.

The proof uses the T-shift identity
`λ(τ) = λ(τ − 1)/(λ(τ − 1) − 1)`, the cusp-0 limit `λ(τ−1) → 1` for
`τ − 1` approaching `0` from the `F^o`-shifted region (i.e., from the
upper-left quadrant minus the reflected semicircle), and the
q'-expansion `δ := λ(τ−1) − 1 = −λ(−1/(τ−1)) ≈ −16 q'` where
`q' := exp(πi · (−1/(τ−1)))`. The `F^o`-shifted constraint
`‖2(τ−1) + 1‖ > 1` forces `arg(q') ∈ (0, π)` (equivalently,
`Re(−1/(τ−1)) ∈ (0, 1)`), so `Im(q') > 0` in the leading order.

**Available infrastructure.** Two Schwarz reflection identities for
`λ` are now closed axiom-clean:

* `modularLambdaH_schwarz_reflect_re_one`: `λ(2 − conj τ) = conj(λ τ)`,
  Schwarz reflection through the line `Re τ = 1` (composition of
  `modularLambdaH_conj_symmetry` and `modularLambdaH_sub_two`).
* `modularLambdaH_schwarz_reflect_semicircle`:
  `λ(conj τ/(2·conj τ − 1)) = conj(λ τ)`, Schwarz reflection through
  the F^o boundary semicircle `|τ − 1/2| = 1/2` (composition of
  `modularLambdaH_div_two_tau_add_one` inverted and
  `modularLambdaH_conj_symmetry`).

**Reduction to the strip claim.** The combined T-shift and S-shift
give the algebraic identity `λ(τ) = 1 − 1/λ(w)` where `w := −1/(τ−1)`.
Hence `Im λ(τ) = Im λ(w)/|λ(w)|²`, so `Im λ(τ) ≥ 0 ⟺ Im λ(w) ≥ 0`.

For `τ ∈ F^o ∩ B(1, 1/3)`, the image `w = −1/(τ−1)` satisfies
`Re w ∈ (0, 1)` (F^o constraint) and `Im w > 2√2 > 1` (from
`‖w‖ ≥ 3` and `Re²w + Im²w = ‖w‖² ≥ 9` with `Re w < 1`). The cusp-1
lemma thus reduces to the strip claim
`modularLambdaH_im_nonneg_strip`. -/
theorem modularLambdaH_cusp_one_im_nonneg_nbhd_in_F :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Gamma2FundamentalDomainInterior,
      ‖τ - 1‖ ≤ δ → 0 ≤ (modularLambdaH τ).im := by
  refine ⟨1/3, by norm_num, ?_⟩
  intro τ hτ_F hτ_dist
  obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτ_F
  -- Step 1: σ := τ - 1 has σ.im > 0 and ‖σ‖ ≤ 1/3.
  set σ := τ - 1 with hσ_def
  have hσ_im_pos : 0 < σ.im := by
    change 0 < (τ - 1).im
    simp only [Complex.sub_im, Complex.one_im, sub_zero]; exact hτ_im_pos
  have hσ_re_neg : σ.re < 0 := by
    change (τ - 1).re < 0
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hσ_re_gt_neg_one : -1 < σ.re := by
    change -1 < (τ - 1).re
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hσ_norm_le : ‖σ‖ ≤ 1/3 := hτ_dist
  -- σ ≠ 0 since σ.im > 0.
  have hσ_ne : σ ≠ 0 := by
    intro h
    rw [h] at hσ_im_pos
    simp at hσ_im_pos
  have hσ_norm_pos : 0 < ‖σ‖ := norm_pos_iff.mpr hσ_ne
  -- |σ|² = ‖σ‖² ≤ 1/9.
  have hσ_normSq_eq : Complex.normSq σ = ‖σ‖^2 := by
    rw [← Complex.sq_norm]
  have hσ_normSq_pos : 0 < Complex.normSq σ := Complex.normSq_pos.mpr hσ_ne
  have hσ_normSq_le : Complex.normSq σ ≤ 1/9 := by
    rw [hσ_normSq_eq]
    have h_sq : ‖σ‖^2 ≤ (1/3)^2 := by
      apply sq_le_sq' _ hσ_norm_le
      · linarith [norm_nonneg σ]
    nlinarith
  -- F^o constraint translates to |σ|² > -σ.re.
  have hτ_semicircle_norm : 1 < Complex.normSq (2 * τ - 1) := by
    have h := hτ_semicircle
    have h_sq : 1 < ‖2 * τ - 1‖^2 := by
      have h_norm_nn : 0 ≤ ‖2 * τ - 1‖ := norm_nonneg _
      nlinarith
    have h_eq : ‖2 * τ - 1‖^2 = Complex.normSq (2 * τ - 1) := Complex.sq_norm _
    linarith [h_eq ▸ h_sq]
  have h_2tau_minus_one : (2 * τ - 1) = 2 * σ + 1 := by
    rw [hσ_def]; ring
  rw [h_2tau_minus_one] at hτ_semicircle_norm
  have hσ_F_constraint : -σ.re < Complex.normSq σ := by
    have h_eq : Complex.normSq (2 * σ + 1) = 4 * Complex.normSq σ + 4 * σ.re + 1 := by
      simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.one_re, Complex.one_im]
      ring
    rw [h_eq] at hτ_semicircle_norm
    linarith
  -- Step 2: Set w := -1/σ. Show w.im > 1, 0 < w.re < 1.
  set w := -1/σ with hw_def
  have hw_eq_neg_inv : w = -σ⁻¹ := by
    rw [hw_def, neg_div, one_div]
  have hw_re : w.re = -σ.re / Complex.normSq σ := by
    rw [hw_eq_neg_inv, Complex.neg_re, Complex.inv_re]
    ring
  have hw_im : w.im = σ.im / Complex.normSq σ := by
    rw [hw_eq_neg_inv, Complex.neg_im, Complex.inv_im]
    ring
  have hw_re_pos : 0 < w.re := by
    rw [hw_re]
    apply div_pos _ hσ_normSq_pos
    linarith
  have hw_re_lt_one : w.re < 1 := by
    rw [hw_re]
    rw [div_lt_one hσ_normSq_pos]
    linarith
  have hw_im_pos : 0 < w.im := by
    rw [hw_im]
    exact div_pos hσ_im_pos hσ_normSq_pos
  -- Im w ≥ 1: from |w|² ≥ 9 and Re w < 1.
  have hw_normSq_eq : Complex.normSq w = 1 / Complex.normSq σ := by
    have h1 : ‖w‖^2 = Complex.normSq w := Complex.sq_norm _
    have h2 : ‖σ‖^2 = Complex.normSq σ := Complex.sq_norm _
    have h3 : ‖w‖ = ‖σ‖⁻¹ := by
      rw [hw_eq_neg_inv, norm_neg, norm_inv]
    rw [← h1, h3]
    rw [inv_pow, h2]
    rw [one_div]
  have hw_normSq_ge : 9 ≤ Complex.normSq w := by
    rw [hw_normSq_eq]
    rw [le_div_iff₀ hσ_normSq_pos]
    nlinarith
  have hw_im_sq_ge : 1 ≤ w.im^2 := by
    have h_normSq_eq : Complex.normSq w = w.re^2 + w.im^2 := by
      simp [Complex.normSq_apply]; ring
    have h_re_sq_lt : w.re^2 < 1 := by
      have h := hw_re_lt_one
      have h_pos := hw_re_pos
      nlinarith
    have h_sum : w.re^2 + w.im^2 ≥ 9 := h_normSq_eq ▸ hw_normSq_ge
    linarith
  have hw_im_ge : 1 ≤ w.im := by
    have h_sq : (1:ℝ)^2 ≤ w.im^2 := by simpa using hw_im_sq_ge
    nlinarith [hw_im_pos]
  -- Step 3: λ ≠ 0 at w.
  have hw_im_pos' : 0 < w.im := hw_im_pos
  have hlamw_ne_zero : modularLambdaH w ≠ 0 := modularLambdaH_ne_zero hw_im_pos'
  -- Step 4: Identity λ(τ) = 1 - 1/λ(w).
  -- From T-shift: λ(σ + 1) = -(θ₂(σ)⁴/θ₄(σ)⁴) = λ(σ)/(λ(σ) - 1).
  -- From S-shift: λ(σ) + λ(w) = 1, so λ(σ) = 1 - λ(w).
  -- Combine: λ(τ) = (1 - λ(w))/((1 - λ(w)) - 1) = (1 - λ(w))/(-λ(w)) = 1 - 1/λ(w).
  have hσ_im_for_S : 0 < σ.im := hσ_im_pos
  have h_S : modularLambdaH σ + modularLambdaH w = 1 := by
    have := modularLambdaH_add_S_smul_eq_one hσ_im_for_S
    rw [hw_def]
    exact this
  have hlamσ_eq : modularLambdaH σ = 1 - modularLambdaH w := by linear_combination h_S
  -- T-shift: σ + 1 = τ.
  have hστ_eq : σ + 1 = τ := by rw [hσ_def]; ring
  have hlam_Tshift : modularLambdaH τ = -(theta2 σ ^ 4 / theta4 σ ^ 4) := by
    rw [← hστ_eq]
    exact modularLambdaH_T_smul σ
  have hθ_ne : theta3 σ ≠ 0 := theta3_ne_zero hσ_im_for_S
  have hθ4_ne : theta4 σ ≠ 0 := theta4_ne_zero hσ_im_for_S
  have h_jacobi : theta2 σ ^ 4 + theta4 σ ^ 4 = theta3 σ ^ 4 := jacobi_identity hσ_im_for_S
  have hlamσ_minus_one_ne : modularLambdaH σ - 1 ≠ 0 := by
    have hlamσ_ne_one : modularLambdaH σ ≠ 1 := modularLambdaH_ne_one hσ_im_for_S
    exact sub_ne_zero.mpr hlamσ_ne_one
  have hlam_via_lamσ : modularLambdaH τ = modularLambdaH σ / (modularLambdaH σ - 1) := by
    rw [hlam_Tshift]
    unfold modularLambdaH
    have hθ4_pow_ne : theta4 σ ^ 4 ≠ 0 := pow_ne_zero 4 hθ4_ne
    have hθ3_pow_ne : theta3 σ ^ 4 ≠ 0 := pow_ne_zero 4 hθ_ne
    -- (θ₂⁴/θ₃⁴) / (θ₂⁴/θ₃⁴ - 1) = (θ₂⁴/θ₃⁴) · θ₃⁴/(θ₂⁴ - θ₃⁴) = θ₂⁴/(θ₂⁴ - θ₃⁴)
    -- = θ₂⁴/(-θ₄⁴) = -θ₂⁴/θ₄⁴.
    have h_step : theta2 σ ^ 4 / theta3 σ ^ 4 / (theta2 σ ^ 4 / theta3 σ ^ 4 - 1) =
        theta2 σ ^ 4 / (theta2 σ ^ 4 - theta3 σ ^ 4) := by
      rw [div_sub_one hθ3_pow_ne, div_div_div_cancel_right₀]
      exact hθ3_pow_ne
    rw [h_step]
    have h_denom : theta2 σ ^ 4 - theta3 σ ^ 4 = -theta4 σ ^ 4 := by linear_combination h_jacobi
    rw [h_denom, div_neg]
  -- Substitute λ(σ) = 1 - λ(w).
  have hlamτ_via_lamw : modularLambdaH τ = (1 - modularLambdaH w) / (-modularLambdaH w) := by
    rw [hlam_via_lamσ, hlamσ_eq]
    have h_denom : (1 - modularLambdaH w) - 1 = -modularLambdaH w := by ring
    rw [h_denom]
  -- Simplify: λ(τ) = 1 - 1/λ(w).
  have hlamτ_simplified : modularLambdaH τ = 1 - 1 / modularLambdaH w := by
    rw [hlamτ_via_lamw]
    field_simp
    ring
  -- Step 5: Apply strip claim to get Im λ(w) ≥ 0.
  have h_strip : 0 ≤ (modularLambdaH w).im :=
    modularLambdaH_im_nonneg_strip w hw_re_pos hw_re_lt_one hw_im_ge
  -- Step 6: Conclude Im λ(τ) = Im λ(w)/|λ(w)|² ≥ 0.
  rw [hlamτ_simplified]
  -- Goal: 0 ≤ (1 - 1/modularLambdaH w).im.
  simp only [Complex.sub_im, Complex.one_im, zero_sub, neg_nonneg]
  -- Goal: (1/modularLambdaH w).im ≤ 0.
  -- 1/z = z̄/|z|², so Im(1/z) = -Im(z)/|z|².
  have hlamw_normSq_pos : 0 < Complex.normSq (modularLambdaH w) :=
    Complex.normSq_pos.mpr hlamw_ne_zero
  rw [show (1 : ℂ) / modularLambdaH w = (modularLambdaH w)⁻¹ from by rw [one_div]]
  rw [Complex.inv_im]
  -- Goal: -(modularLambdaH w).im / |λ(w)|² ≤ 0.
  rw [neg_div]
  rw [neg_nonpos]
  exact div_nonneg h_strip hlamw_normSq_pos.le

/-- **Cusp 0 nbhd in `F^o`.** Mirror of `modularLambdaH_cusp_one_im_nonneg_nbhd_in_F`
under the S-shift + conjugation symmetry. For `τ ∈ F^o ∩ B(0, 1/3)`,
set `w := -1/τ`. The S-shift identity `λ(τ) + λ(w) = 1` gives
`Im λ(τ) = -Im λ(w)`. Apply conjugation symmetry
`λ(-conj w) = conj(λ w)` with `w' := -conj w`: then
`Im λ(w') = -Im λ(w)`, so `Im λ(τ) = Im λ(w')`. The `F^o`-translation
on `τ` (equivalently `‖2τ - 1‖ > 1`, equivalently `Re²τ + Im²τ > Re τ`)
gives `Re w' = Re τ / |τ|² < 1`. Combined with `|w'|² = 1/|τ|² ≥ 9`
(from `‖τ‖ ≤ 1/3`) and `Im w' > 0`, this gives `Im w' ≥ 2√2 > 1`,
placing `w'` in the strip `{0 < Re < 1, Im ≥ 1}` where the strip claim
applies. -/
theorem modularLambdaH_cusp_zero_im_nonneg_nbhd_in_F :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Gamma2FundamentalDomainInterior,
      ‖τ‖ ≤ δ → 0 ≤ (modularLambdaH τ).im := by
  refine ⟨1/3, by norm_num, ?_⟩
  intro τ hτ_F hτ_dist
  obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτ_F
  -- τ ≠ 0.
  have hτ_ne : τ ≠ 0 := by
    intro h
    rw [h] at hτ_im_pos
    simp at hτ_im_pos
  have hτ_norm_pos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ_ne
  have hτ_normSq_eq : Complex.normSq τ = ‖τ‖^2 := by rw [← Complex.sq_norm]
  have hτ_normSq_pos : 0 < Complex.normSq τ := Complex.normSq_pos.mpr hτ_ne
  have hτ_normSq_le : Complex.normSq τ ≤ 1/9 := by
    rw [hτ_normSq_eq]
    have h_sq : ‖τ‖^2 ≤ (1/3)^2 := by
      apply sq_le_sq' _ hτ_dist
      · linarith [norm_nonneg τ]
    nlinarith
  -- F^o constraint: ‖2τ - 1‖ > 1 ⟹ Re τ < |τ|².
  have hτ_F_constraint : τ.re < Complex.normSq τ := by
    have h_sq : 1 < ‖2 * τ - 1‖^2 := by
      have h_norm_nn : 0 ≤ ‖2 * τ - 1‖ := norm_nonneg _
      nlinarith
    have h_normSq_eq : ‖2 * τ - 1‖^2 = Complex.normSq (2 * τ - 1) := Complex.sq_norm _
    have h_expand : Complex.normSq (2 * τ - 1) = 4 * Complex.normSq τ - 4 * τ.re + 1 := by
      simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.one_re, Complex.one_im]
      ring
    have h_lt : 1 < 4 * Complex.normSq τ - 4 * τ.re + 1 := by
      rw [← h_expand, ← h_normSq_eq]; exact h_sq
    linarith
  -- Set w := -1/τ.
  set w : ℂ := -1 / τ with hw_def
  have hw_eq_neg_inv : w = -τ⁻¹ := by rw [hw_def, neg_div, one_div]
  have hw_re : w.re = -τ.re / Complex.normSq τ := by
    rw [hw_eq_neg_inv, Complex.neg_re, Complex.inv_re]; ring
  have hw_im : w.im = τ.im / Complex.normSq τ := by
    rw [hw_eq_neg_inv, Complex.neg_im, Complex.inv_im]; ring
  have hw_im_pos : 0 < w.im := by
    rw [hw_im]; exact div_pos hτ_im_pos hτ_normSq_pos
  -- Set w' := -conj w (Schwarz reflection through Re = 0).
  set w' : ℂ := -(starRingEnd ℂ w) with hw'_def
  have hw'_re : w'.re = -w.re := by
    rw [hw'_def, Complex.neg_re, Complex.conj_re]
  have hw'_im : w'.im = w.im := by
    rw [hw'_def, Complex.neg_im, Complex.conj_im]; ring
  have hw'_re_pos : 0 < w'.re := by
    rw [hw'_re, hw_re, neg_div, neg_neg]
    exact div_pos hτ_re_pos hτ_normSq_pos
  have hw'_re_lt_one : w'.re < 1 := by
    rw [hw'_re, hw_re, neg_div, neg_neg]
    rw [div_lt_one hτ_normSq_pos]
    exact hτ_F_constraint
  have hw'_im_pos : 0 < w'.im := by rw [hw'_im]; exact hw_im_pos
  -- |w'|² = |w|² = 1/|τ|² ≥ 9.
  have hw_normSq_eq : Complex.normSq w = 1 / Complex.normSq τ := by
    have h1 : ‖w‖^2 = Complex.normSq w := Complex.sq_norm _
    have h2 : ‖τ‖^2 = Complex.normSq τ := Complex.sq_norm _
    have h3 : ‖w‖ = ‖τ‖⁻¹ := by rw [hw_eq_neg_inv, norm_neg, norm_inv]
    rw [← h1, h3, inv_pow, h2, one_div]
  have hw'_normSq_eq : Complex.normSq w' = Complex.normSq w := by
    rw [hw'_def, Complex.normSq_neg, Complex.normSq_conj]
  have hw'_normSq_ge : 9 ≤ Complex.normSq w' := by
    rw [hw'_normSq_eq, hw_normSq_eq]
    rw [le_div_iff₀ hτ_normSq_pos]
    nlinarith
  -- Im w' ≥ 1 from |w'|² ≥ 9 and Re w' < 1.
  have hw'_im_sq_ge : 1 ≤ w'.im^2 := by
    have h_normSq_eq : Complex.normSq w' = w'.re^2 + w'.im^2 := by
      simp [Complex.normSq_apply]; ring
    have h_re_sq_lt : w'.re^2 < 1 := by
      have h := hw'_re_lt_one
      have h_pos := hw'_re_pos
      nlinarith
    have h_sum : w'.re^2 + w'.im^2 ≥ 9 := h_normSq_eq ▸ hw'_normSq_ge
    linarith
  have hw'_im_ge : 1 ≤ w'.im := by
    have h_sq : (1:ℝ)^2 ≤ w'.im^2 := by simpa using hw'_im_sq_ge
    nlinarith [hw'_im_pos]
  -- S-shift: λ(τ) + λ(w) = 1.
  have h_S : modularLambdaH τ + modularLambdaH w = 1 := by
    have := modularLambdaH_add_S_smul_eq_one hτ_im_pos
    rw [hw_def]; exact this
  have hlamτ_eq : modularLambdaH τ = 1 - modularLambdaH w := by linear_combination h_S
  -- Conjugation symmetry: λ(w') = conj(λ(w)).
  have h_conj : modularLambdaH w' = starRingEnd ℂ (modularLambdaH w) := by
    rw [hw'_def]; exact modularLambdaH_conj_symmetry hw_im_pos
  -- Apply strip lemma to w'.
  have h_strip : 0 ≤ (modularLambdaH w').im :=
    modularLambdaH_im_nonneg_strip w' hw'_re_pos hw'_re_lt_one hw'_im_ge
  -- Im λ(w') = -Im λ(w), so Im λ(w) ≤ 0.
  have hlamw_im_eq : (modularLambdaH w').im = -(modularLambdaH w).im := by
    rw [h_conj, Complex.conj_im]
  have hlamw_im_le : (modularLambdaH w).im ≤ 0 := by linarith [hlamw_im_eq ▸ h_strip]
  -- Conclude Im λ(τ) = -Im λ(w) ≥ 0.
  rw [hlamτ_eq, Complex.sub_im, Complex.one_im, zero_sub]
  linarith

/-- **Sub-lemma for Step A (Phragmén–Lindelöf statement): `Im(λ) ≥ 0`
on `F^o`.**

`Im λ` is harmonic on `F^o`, vanishes on the three boundary arcs
(`modularLambdaH_pure_imag_real`, `modularLambdaH_one_add_imag_real`,
`modularLambdaH_semicircle_real`), and tends to `0` at the cusps
`i∞` and `0`. The four sub-regions of F^o tile it as:

* `F^o ∩ {Im τ ≥ 1}`: strip lemma `modularLambdaH_im_nonneg_strip`.
* `F^o ∩ B(0, 1/3)`: cusp-0 nbhd
  `modularLambdaH_cusp_zero_im_nonneg_nbhd_in_F`.
* `F^o ∩ B(1, 1/3)`: cusp-1 nbhd
  `modularLambdaH_cusp_one_im_nonneg_nbhd_in_F`.
* "Middle region" `F^o ∩ {Im τ < 1, ‖τ‖ > 1/3, ‖τ - 1‖ > 1/3}`:
  bounded, with all frontier conditions giving `Im λ ≥ 0` (the F^o
  boundary arcs being real, the upper edge handled by the strip lemma,
  and the cusp-truncation arcs by the cusp nbhd lemmas). Apply the
  maximum modulus principle to `g(z) := exp(i·λ(z))` (whose norm is
  `exp(-Im λ z)`) on this bounded open set to conclude `‖g‖ ≤ 1`,
  i.e. `Im λ ≥ 0`. -/
theorem modularLambdaH_im_nonneg_on_F :
    ∀ τ ∈ Gamma2FundamentalDomainInterior, 0 ≤ (modularLambdaH τ).im := by
  obtain ⟨δ₀, hδ₀_pos, h_cusp0⟩ := modularLambdaH_cusp_zero_im_nonneg_nbhd_in_F
  obtain ⟨δ₁, hδ₁_pos, h_cusp1⟩ := modularLambdaH_cusp_one_im_nonneg_nbhd_in_F
  intro τ hτ_F
  obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτ_F
  by_cases h_im_case : 1 ≤ τ.im
  · exact modularLambdaH_im_nonneg_strip τ hτ_re_pos hτ_re_lt_one h_im_case
  push Not at h_im_case
  by_cases h_c0_case : ‖τ‖ ≤ δ₀
  · exact h_cusp0 τ ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ h_c0_case
  push Not at h_c0_case
  by_cases h_c1_case : ‖τ - 1‖ ≤ δ₁
  · exact h_cusp1 τ ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ h_c1_case
  push Not at h_c1_case
  -- Middle region: apply maximum modulus to g(z) := exp(i·λ(z)).
  set M : Set ℂ := { z : ℂ | 0 < z.im ∧ 0 < z.re ∧ z.re < 1 ∧ 1 < ‖2 * z - 1‖ ∧
    z.im < 1 ∧ δ₀ < ‖z‖ ∧ δ₁ < ‖z - 1‖ } with hM_def
  have hτ_in_M : τ ∈ M :=
    ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle, h_im_case, h_c0_case, h_c1_case⟩
  set g : ℂ → ℂ := fun z => Complex.exp (Complex.I * modularLambdaH z) with hg_def
  have h_g_norm : ∀ z : ℂ, ‖g z‖ = Real.exp (-(modularLambdaH z).im) := by
    intro z
    rw [hg_def, Complex.norm_exp]
    congr 1
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  have h2zm1_cont : Continuous (fun z : ℂ => 2 * z - 1) :=
    (continuous_const.mul continuous_id).sub continuous_const
  have hzm1_cont : Continuous (fun z : ℂ => z - 1) :=
    continuous_id.sub continuous_const
  have hM_open : IsOpen M := by
    refine (isOpen_lt continuous_const Complex.continuous_im).inter ?_
    refine (isOpen_lt continuous_const Complex.continuous_re).inter ?_
    refine (isOpen_lt Complex.continuous_re continuous_const).inter ?_
    refine (isOpen_lt continuous_const h2zm1_cont.norm).inter ?_
    refine (isOpen_lt Complex.continuous_im continuous_const).inter ?_
    refine (isOpen_lt continuous_const continuous_norm).inter ?_
    exact isOpen_lt continuous_const hzm1_cont.norm
  have hM_bdd : Bornology.IsBounded M := by
    refine Bornology.IsBounded.subset (Metric.isBounded_ball (x := (0 : ℂ)) (r := 2)) ?_
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    obtain ⟨h_im_pos, h_re_pos, h_re_lt, _, h_im_lt, _, _⟩ := hz
    have h_sq : ‖z‖ ^ 2 < 4 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith
    nlinarith [norm_nonneg z, sq_nonneg (2 - ‖z‖)]
  have h_im_nn_cl : closure M ⊆ { z : ℂ | 0 ≤ z.im } :=
    closure_minimal (fun z hz => le_of_lt hz.1)
      (isClosed_le continuous_const Complex.continuous_im)
  have h_re_nn_cl : closure M ⊆ { z : ℂ | 0 ≤ z.re } :=
    closure_minimal (fun z hz => le_of_lt hz.2.1)
      (isClosed_le continuous_const Complex.continuous_re)
  have h_re_le_cl : closure M ⊆ { z : ℂ | z.re ≤ 1 } :=
    closure_minimal (fun z hz => le_of_lt hz.2.2.1)
      (isClosed_le Complex.continuous_re continuous_const)
  have h_sc_cl : closure M ⊆ { z : ℂ | 1 ≤ ‖2 * z - 1‖ } :=
    closure_minimal (fun z hz => le_of_lt hz.2.2.2.1)
      (isClosed_le continuous_const h2zm1_cont.norm)
  have h_im_le_cl : closure M ⊆ { z : ℂ | z.im ≤ 1 } :=
    closure_minimal (fun z hz => le_of_lt hz.2.2.2.2.1)
      (isClosed_le Complex.continuous_im continuous_const)
  have h_n_ge_cl : closure M ⊆ { z : ℂ | δ₀ ≤ ‖z‖ } :=
    closure_minimal (fun z hz => le_of_lt hz.2.2.2.2.2.1)
      (isClosed_le continuous_const continuous_norm)
  have h_n1_ge_cl : closure M ⊆ { z : ℂ | δ₁ ≤ ‖z - 1‖ } :=
    closure_minimal (fun z hz => le_of_lt hz.2.2.2.2.2.2)
      (isClosed_le continuous_const hzm1_cont.norm)
  have hM_cl_in_H : ∀ z ∈ closure M, 0 < z.im := by
    intro z hz_cl
    by_contra h_neg
    push Not at h_neg
    have h_im_z_nn : 0 ≤ z.im := h_im_nn_cl hz_cl
    have h_im_zero : z.im = 0 := le_antisymm h_neg h_im_z_nn
    have h_sc : 1 ≤ ‖2 * z - 1‖ := h_sc_cl hz_cl
    have h_sc_sq : 1 ≤ ‖2 * z - 1‖ ^ 2 := by
      have h_nn : 0 ≤ ‖2 * z - 1‖ := norm_nonneg _
      nlinarith
    have h_2zm1_sq : ‖2 * z - 1‖ ^ 2 = (2 * z.re - 1) ^ 2 + (2 * z.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.one_re, Complex.one_im]
      ring
    rw [h_2zm1_sq, h_im_zero] at h_sc_sq
    have h_re_sq : 1 ≤ (2 * z.re - 1) ^ 2 := by linarith
    have h_re_nn : 0 ≤ z.re := h_re_nn_cl hz_cl
    have h_re_le : z.re ≤ 1 := h_re_le_cl hz_cl
    have h_re_outside : z.re ≤ 0 ∨ 1 ≤ z.re := by
      rcases le_or_gt (2 * z.re - 1) 0 with h | h
      · left; nlinarith [sq_nonneg (2 * z.re - 1)]
      · right; nlinarith [sq_nonneg (2 * z.re - 1)]
    rcases h_re_outside with h_re_le_0 | h_re_ge_1
    · have h_re_zero : z.re = 0 := le_antisymm h_re_le_0 h_re_nn
      have h_n_ge : δ₀ ≤ ‖z‖ := h_n_ge_cl hz_cl
      have h_norm_sq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [h_re_zero, h_im_zero] at h_norm_sq
      have h_norm_sq_zero : ‖z‖ ^ 2 = 0 := by linarith
      have h_nn : 0 ≤ ‖z‖ := norm_nonneg z
      have h_norm_zero : ‖z‖ = 0 := by nlinarith
      linarith
    · have h_re_one : z.re = 1 := le_antisymm h_re_le h_re_ge_1
      have h_n1_ge : δ₁ ≤ ‖z - 1‖ := h_n1_ge_cl hz_cl
      have h_zm1_sq : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
        ring
      rw [h_re_one, h_im_zero] at h_zm1_sq
      have h_zm1_sq_zero : ‖z - 1‖ ^ 2 = 0 := by linarith
      have h_nn : 0 ≤ ‖z - 1‖ := norm_nonneg _
      have h_zm1_zero : ‖z - 1‖ = 0 := by nlinarith
      linarith
  have hg_diff_at : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ g z := by
    intro z h_im_pos
    have h_lam_diff : DifferentiableAt ℂ modularLambdaH z :=
      modularLambdaH_differentiableAt_of_im_pos h_im_pos
    have h_mul : DifferentiableAt ℂ (fun w => Complex.I * modularLambdaH w) z :=
      (differentiableAt_const _).mul h_lam_diff
    exact h_mul.cexp
  have hg_DCOC : DiffContOnCl ℂ g M := by
    refine ⟨?_, ?_⟩
    · intro z hz_M
      exact (hg_diff_at z hz_M.1).differentiableWithinAt
    · intro z hz_cl
      exact (hg_diff_at z (hM_cl_in_H z hz_cl)).continuousAt.continuousWithinAt
  have hg_frontier_bound : ∀ z ∈ frontier M, ‖g z‖ ≤ 1 := by
    intro z hz_fr
    have hz_cl : z ∈ closure M := hz_fr.1
    have h_im_pos : 0 < z.im := hM_cl_in_H z hz_cl
    have h_re_nn : 0 ≤ z.re := h_re_nn_cl hz_cl
    have h_re_le : z.re ≤ 1 := h_re_le_cl hz_cl
    have h_sc_ge : 1 ≤ ‖2 * z - 1‖ := h_sc_cl hz_cl
    have h_im_le : z.im ≤ 1 := h_im_le_cl hz_cl
    have hz_not_M : z ∉ M := by
      rw [← hM_open.interior_eq]; exact hz_fr.2
    rw [h_g_norm z]
    suffices h_im_lam : 0 ≤ (modularLambdaH z).im by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_le_exp]
      linarith
    by_cases h_re_z : z.re ≤ 0
    · have h_re_z_eq : z.re = 0 := le_antisymm h_re_z h_re_nn
      have h_z_eq : z = Complex.I * ((z.im : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, h_re_z_eq]
        · simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im]
      rw [h_z_eq]
      exact le_of_eq (modularLambdaH_pure_imag_real h_im_pos).symm
    push Not at h_re_z
    by_cases h_re_z_1 : 1 ≤ z.re
    · have h_re_z_eq : z.re = 1 := le_antisymm h_re_le h_re_z_1
      have h_z_eq : z = 1 + Complex.I * ((z.im : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, h_re_z_eq]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [h_z_eq]
      exact le_of_eq (modularLambdaH_one_add_imag_real h_im_pos).symm
    push Not at h_re_z_1
    by_cases h_sc_eq : ‖2 * z - 1‖ ≤ 1
    · have h_sc_eq' : ‖2 * z - 1‖ = 1 := le_antisymm h_sc_eq h_sc_ge
      exact le_of_eq (modularLambdaH_semicircle_real h_im_pos h_sc_eq').symm
    push Not at h_sc_eq
    have hz_in_F : z ∈ Gamma2FundamentalDomainInterior :=
      ⟨h_im_pos, h_re_z, h_re_z_1, h_sc_eq⟩
    by_cases h_im_z_1 : 1 ≤ z.im
    · exact modularLambdaH_im_nonneg_strip z h_re_z h_re_z_1 h_im_z_1
    push Not at h_im_z_1
    by_cases h_norm_z : ‖z‖ ≤ δ₀
    · exact h_cusp0 z hz_in_F h_norm_z
    push Not at h_norm_z
    by_cases h_norm_z_1 : ‖z - 1‖ ≤ δ₁
    · exact h_cusp1 z hz_in_F h_norm_z_1
    push Not at h_norm_z_1
    exfalso
    exact hz_not_M ⟨h_im_pos, h_re_z, h_re_z_1, h_sc_eq, h_im_z_1, h_norm_z, h_norm_z_1⟩
  have hg_τ_bound : ‖g τ‖ ≤ 1 :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hM_bdd hg_DCOC hg_frontier_bound
      (subset_closure hτ_in_M)
  rw [h_g_norm τ] at hg_τ_bound
  have h_le : -(modularLambdaH τ).im ≤ 0 := by
    rwa [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_le_exp] at hg_τ_bound
  linarith

/-- **Sub-lemma for Step A: `Im(λ) ≠ 0` on `F^o`.** The modular
function `λ` takes no real values on the open fundamental domain.
Derived from `modularLambdaH_im_nonneg_on_F` (`Im λ ≥ 0`) together
with the open-mapping theorem: if `λ(τ_*)` were real for some
`τ_* ∈ F^o`, then `λ(F^o)` is open and `λ(τ_*) ∈ λ(F^o)` would
admit a small ball, so some interior point `τ'` would have
`Im(λ(τ')) < 0`, contradicting `Im λ ≥ 0`. -/
theorem modularLambdaH_im_ne_zero_on_F :
    ∀ τ ∈ Gamma2FundamentalDomainInterior, (modularLambdaH τ).im ≠ 0 := by
  intro τstar hτstar h_im_zero
  -- Setup ℍ.
  set ℍ : Set ℂ := { τ : ℂ | 0 < τ.im }
  have hℍ_open : IsOpen ℍ := isOpen_lt continuous_const Complex.continuous_im
  -- λ is analytic on ℍ.
  have h_lam_an : AnalyticOnNhd ℂ modularLambdaH ℍ :=
    modularLambdaH_differentiableOn.analyticOnNhd hℍ_open
  -- ℍ is preconnected (convex).
  have hℍ_preconn : IsPreconnected ℍ := by
    have hconv : Convex ℝ ℍ := by
      intro w₁ hw₁ w₂ hw₂ s t hs ht hst
      change 0 < (s • w₁ + t • w₂).im
      rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
      rcases lt_or_eq_of_le hs with hs_pos | hs_zero
      · have h1 : 0 < s * w₁.im := mul_pos hs_pos hw₁
        have h2 : 0 ≤ t * w₂.im := mul_nonneg ht hw₂.le
        linarith
      · have ht_pos : 0 < t := by linarith
        have h1 : 0 ≤ s * w₁.im := mul_nonneg hs hw₁.le
        have h2 : 0 < t * w₂.im := mul_pos ht_pos hw₂
        linarith
    exact hconv.isPreconnected
  -- λ is non-constant on ℍ (cusp limits give two different values).
  have h_lam_not_const : ¬ (∃ w, ∀ z ∈ ℍ, modularLambdaH z = w) := by
    rintro ⟨w, hconst⟩
    have h_mul_in : ∀ y : ℝ, 0 < y → (Complex.I * (y : ℂ)) ∈ ℍ := by
      intro y hy_pos
      change 0 < (Complex.I * (y : ℂ)).im
      rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      simpa using hy_pos
    have hlim_zero := modularLambdaH_iy_tendsto_zero_atTop
    have hlim_one := modularLambdaH_iy_tendsto_one_atZeroPos
    have hw_zero : w = 0 := by
      have hcst :
          Tendsto (fun y : ℝ => modularLambdaH (Complex.I * (y : ℂ))) atTop (𝓝 w) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with y hy_pos
        exact (hconst (Complex.I * (y : ℂ)) (h_mul_in y hy_pos)).symm
      exact tendsto_nhds_unique hcst hlim_zero
    have hw_one : w = 1 := by
      have hcst :
          Tendsto (fun y : ℝ => modularLambdaH (Complex.I * (y : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with y hy_pos
        exact (hconst (Complex.I * (y : ℂ)) (h_mul_in y hy_pos)).symm
      exact tendsto_nhds_unique hcst hlim_one
    have h_eq : (0 : ℂ) = 1 := hw_zero.symm.trans hw_one
    exact one_ne_zero h_eq.symm
  -- Open mapping on F^o: λ(F^o) is open.
  rcases h_lam_an.is_constant_or_isOpen hℍ_preconn with h_const | h_open
  · exact absurd h_const h_lam_not_const
  have hF_sub_ℍ : Gamma2FundamentalDomainInterior ⊆ ℍ :=
    Gamma2FundamentalDomainInterior_subset_upperHalf
  have hF_open : IsOpen Gamma2FundamentalDomainInterior :=
    Gamma2FundamentalDomainInterior_isOpen
  have h_image_open : IsOpen (modularLambdaH '' Gamma2FundamentalDomainInterior) :=
    h_open _ hF_sub_ℍ hF_open
  -- λ(τstar) ∈ image.
  have h_lam_in : modularLambdaH τstar ∈ modularLambdaH '' Gamma2FundamentalDomainInterior :=
    ⟨τstar, hτstar, rfl⟩
  -- Get a ball around λ(τstar) inside the image.
  rcases Metric.isOpen_iff.mp h_image_open _ h_lam_in with ⟨ε, hε_pos, hball⟩
  -- Choose w = λ(τstar) − i·ε/2.
  set w : ℂ := modularLambdaH τstar - Complex.I * ((ε / 2 : ℝ) : ℂ) with hw_def
  have h_eps_half_pos : (0 : ℝ) < ε / 2 := by linarith
  have hw_in_ball : w ∈ Metric.ball (modularLambdaH τstar) ε := by
    rw [Metric.mem_ball, dist_eq_norm, hw_def]
    have h_simplify :
        modularLambdaH τstar - Complex.I * ((ε / 2 : ℝ) : ℂ) - modularLambdaH τstar =
          -(Complex.I * ((ε / 2 : ℝ) : ℂ)) := by ring
    rw [h_simplify, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_pos h_eps_half_pos]
    linarith
  -- Get preimage τ' ∈ F^o.
  obtain ⟨τ', hτ'_F, hτ'_eq⟩ := hball hw_in_ball
  -- Compute Im(λ(τ')) = −ε/2 < 0.
  have h_im_τ' : (modularLambdaH τ').im = -(ε / 2) := by
    rw [hτ'_eq, hw_def]
    rw [Complex.sub_im, h_im_zero, zero_sub]
    rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- But Im(λ(τ')) ≥ 0 by modularLambdaH_im_nonneg_on_F. Contradiction.
  have h_nonneg' := modularLambdaH_im_nonneg_on_F τ' hτ'_F
  linarith

/-- **Step A: `λ(F^o) ⊆ {Im w > 0}`.** The image of `F^o` under `λ` lies
in the open upper half-plane. Combines the witness
`modularLambdaH_im_pos_at_witness` with the "Im(λ) ≠ 0 on F^o" claim
via preconnectedness of F^o. The set
`U := F^o ∩ {Im(λ z) > 0}` is open and non-empty (by the witness); the
set `V := F^o ∩ {Im(λ z) < 0}` is open and disjoint from `U`. By
`modularLambdaH_im_ne_zero_on_F`, the two sets cover F^o. By
`IsPreconnected.subset_left_of_subset_union`, F^o ⊆ U. -/
theorem modularLambdaH_F_im_pos :
    ∀ τ ∈ Gamma2FundamentalDomainInterior, 0 < (modularLambdaH τ).im := by
  -- Set up the "good" set U and "bad" set V.
  set U : Set ℂ := Gamma2FundamentalDomainInterior ∩ {z : ℂ | 0 < (modularLambdaH z).im}
    with hU_def
  set V : Set ℂ := Gamma2FundamentalDomainInterior ∩ {z : ℂ | (modularLambdaH z).im < 0}
    with hV_def
  -- U and V are open in ℂ.
  have hF_open : IsOpen Gamma2FundamentalDomainInterior :=
    Gamma2FundamentalDomainInterior_isOpen
  have hF_sub_H : Gamma2FundamentalDomainInterior ⊆ { z : ℂ | 0 < z.im } :=
    Gamma2FundamentalDomainInterior_subset_upperHalf
  have h_cont_lam :
      ContinuousOn modularLambdaH Gamma2FundamentalDomainInterior :=
    modularLambdaH_differentiableOn.continuousOn.mono hF_sub_H
  have h_cont_im :
      ContinuousOn (fun z => (modularLambdaH z).im) Gamma2FundamentalDomainInterior :=
    Complex.continuous_im.continuousOn.comp h_cont_lam (Set.mapsTo_univ _ _)
  have hU_open : IsOpen U :=
    h_cont_im.isOpen_inter_preimage hF_open isOpen_Ioi
  have hV_open : IsOpen V :=
    h_cont_im.isOpen_inter_preimage hF_open isOpen_Iio
  -- U and V are disjoint.
  have hUV_disj : Disjoint U V := by
    rw [Set.disjoint_iff_inter_eq_empty]
    apply Set.eq_empty_of_forall_notMem
    intro z hz
    have h1 : 0 < (modularLambdaH z).im := hz.1.2
    have h2 : (modularLambdaH z).im < 0 := hz.2.2
    linarith
  -- F^o ⊆ U ∪ V (using Im(λ) ≠ 0 on F^o).
  have hF_sub_UV : Gamma2FundamentalDomainInterior ⊆ U ∪ V := by
    intro z hz
    have h_ne := modularLambdaH_im_ne_zero_on_F z hz
    rcases lt_or_gt_of_ne h_ne with h_neg | h_pos
    · right; exact ⟨hz, h_neg⟩
    · left; exact ⟨hz, h_pos⟩
  -- F^o ∩ U is non-empty (witness (1+4i)/2 ∈ F^o with Im(λ) > 0).
  have h_witness_in_F : ((1 + 4 * Complex.I) / 2) ∈ Gamma2FundamentalDomainInterior := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re]
    · simp [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re]
    · rw [show ((1 + 4 * Complex.I) / 2 : ℂ) = (1 : ℂ) / 2 + 2 * Complex.I from by ring]
      simp [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re,
        Complex.normSq_ofNat]
      norm_num
    · have heq : 2 * (((1 : ℂ) + 4 * Complex.I) / 2) - 1 = 4 * Complex.I := by ring
      rw [heq]
      simp
  have hF_inter_U_nonempty : (Gamma2FundamentalDomainInterior ∩ U).Nonempty := by
    refine ⟨((1 + 4 * Complex.I) / 2), h_witness_in_F, h_witness_in_F, ?_⟩
    exact modularLambdaH_im_pos_at_witness
  -- F^o is preconnected.
  have hF_preconn := Gamma2FundamentalDomainInterior_isPreconnected
  -- By IsPreconnected.subset_left_of_subset_union, F^o ⊆ U.
  have hF_sub_U : Gamma2FundamentalDomainInterior ⊆ U :=
    hF_preconn.subset_left_of_subset_union hU_open hV_open hUV_disj hF_sub_UV
      hF_inter_U_nonempty
  -- Hence for any τ ∈ F^o, 0 < (modularLambdaH τ).im.
  intro τ hτ
  exact (hF_sub_U hτ).2

/-- **Step B: `λ(F^o)` is open.** By the open-mapping theorem for
non-constant analytic functions on the preconnected open set `F^o`. -/
theorem modularLambdaH_F_image_isOpen :
    IsOpen (modularLambdaH '' Gamma2FundamentalDomainInterior) := by
  -- Apply the open-mapping theorem globally on the upper half-plane ℍ.
  set ℍ : Set ℂ := { τ : ℂ | 0 < τ.im }
  -- λ is analytic on ℍ.
  have hℍ_open : IsOpen ℍ := by
    have : ℍ = Complex.im ⁻¹' Set.Ioi 0 := by ext τ; simp [ℍ]
    rw [this]
    exact isOpen_Ioi.preimage Complex.continuous_im
  have h_lam_an : AnalyticOnNhd ℂ modularLambdaH ℍ :=
    modularLambdaH_differentiableOn.analyticOnNhd hℍ_open
  -- ℍ is preconnected (convex).
  have hℍ_preconn : IsPreconnected ℍ := by
    have hconv : Convex ℝ ℍ := by
      intro w₁ hw₁ w₂ hw₂ s t hs ht hst
      change 0 < (s • w₁ + t • w₂).im
      rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
      rcases lt_or_eq_of_le hs with hs_pos | hs_zero
      · have h1 : 0 < s * w₁.im := mul_pos hs_pos hw₁
        have h2 : 0 ≤ t * w₂.im := mul_nonneg ht hw₂.le
        linarith
      · have ht_pos : 0 < t := by linarith
        have h1 : 0 ≤ s * w₁.im := mul_nonneg hs hw₁.le
        have h2 : 0 < t * w₂.im := mul_pos ht_pos hw₂
        linarith
    exact hconv.isPreconnected
  -- λ is not constant on ℍ (cusp limits force two different values).
  have h_lam_not_const : ¬ (∃ w, ∀ z ∈ ℍ, modularLambdaH z = w) := by
    rintro ⟨w, hconst⟩
    have hI_im : Complex.I.im = 1 := Complex.I_im
    -- λ(iy) → 0 as y → ∞ but λ(iy) → 1 as y → 0+. If λ ≡ w, then w = 0 = 1.
    have h_mul_in : ∀ y : ℝ, 0 < y → (Complex.I * (y : ℂ)) ∈ ℍ := by
      intro y hy_pos
      change 0 < (Complex.I * (y : ℂ)).im
      rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im]
      simpa using hy_pos
    have hlim_zero := modularLambdaH_iy_tendsto_zero_atTop
    have hlim_one := modularLambdaH_iy_tendsto_one_atZeroPos
    have hw_zero : w = 0 := by
      have hcst :
          Tendsto (fun y : ℝ => modularLambdaH (Complex.I * (y : ℂ))) atTop (𝓝 w) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with y hy_pos
        exact (hconst (Complex.I * (y : ℂ)) (h_mul_in y hy_pos)).symm
      exact tendsto_nhds_unique hcst hlim_zero
    have hw_one : w = 1 := by
      have hcst :
          Tendsto (fun y : ℝ => modularLambdaH (Complex.I * (y : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with y hy_pos
        exact (hconst (Complex.I * (y : ℂ)) (h_mul_in y hy_pos)).symm
      exact tendsto_nhds_unique hcst hlim_one
    -- 0 = w = 1, contradiction.
    have : (0 : ℂ) = 1 := hw_zero.symm.trans hw_one
    exact one_ne_zero this.symm
  -- Apply open-mapping.
  rcases AnalyticOnNhd.is_constant_or_isOpen h_lam_an hℍ_preconn with h_const | h_open
  · exact absurd h_const h_lam_not_const
  · apply h_open
    · intro τ hτ
      exact hτ.1
    · exact Gamma2FundamentalDomainInterior_isOpen

/-- **Step C: `λ(F^o)` is closed in the upper half-plane.** Properness
of `λ|F^o → {Im w > 0}`: as `τ` approaches the boundary of `F^o`, the
image `λ(τ)` tends to `ℝ ∪ {∞}` (combined from the four cusp
asymptotic lemmas and the three boundary-real arc theorems), so the
preimage of any compact set in `{Im w > 0}` is compact in `F^o`.

**Proof strategy (sequential).** Suppose `wₙ → w` in `{Im w > 0}`,
with `wₙ = λ(τₙ)` for some `τₙ ∈ F^o`. Show `w ∈ λ(F^o)`. Case-split
on the sequence `(τₙ)`:

* **Bounded with limit in `F^o`**: by continuity, `λ(τ) = w ∈ λ(F^o)`.
* **Bounded with limit `τ* ∈ ∂F^o ∩ ℍ`** (on a boundary arc):
  `λ(τ*) ∈ ℝ` by the boundary-real lemmas; but `wₙ → w` with
  `Im w > 0`, contradicting `w = λ(τ*) ∈ ℝ`.
* **Bounded with limit `τ* = 0`** (cusp 0): need `λ(τₙ) → 1` for any
  approach to `0` in `F^o`. Uses the S-shift identity `λ(τ) + λ(-1/τ) = 1`
  plus `Im(-1/τₙ) → ∞` (which holds because the constraint
  `|2τ−1| > 1` in `F^o` forces `|τ|² > Re τ`, giving `|τ|² < 2 (Im τ)²`
  for `τ` near `0`, hence `Im(-1/τ) = Im τ / |τ|² > 1/(2 Im τ) → ∞`).
* **Bounded with limit `τ* = 1`** (cusp 1): need `|λ(τₙ)| → ∞`. Use
  the T-shift identity `λ(τ+1) = λ(τ)/(λ(τ)−1)` to reduce to cusp 0
  case (since `λ(τₙ - 1) → 1` as `τₙ → 1`, then
  `λ(τₙ) → 1/0 = ∞`); contradicts `wₙ → w ∈ ℂ` finite.
* **Unbounded** (`τₙ.im → ∞`, since `Re τₙ ∈ (0,1)` is bounded):
  need uniform cusp ∞ bound `|λ(τ)| ≤ C exp(-π τ.im)` on
  `{τ : τ.im ≥ 1}`. Follows from existing
  `theta2_norm_le_of_im_ge_one : ‖θ₂(τ)‖ ≤ 10 exp(-π τ.im/4)`
  and the implicit lower bound `‖θ₃(τ)‖ ≥ 1/2` (derivable from
  `‖θ₃ - 1‖ ≤ 4 exp(-π τ.im) ≤ 4 exp(-π) < 1/2` for `τ.im ≥ 1`).
  Gives `λ(τₙ) → 0`, contradicting `w ∈ {Im w > 0}`.

All four contradictions rule out the "limit outside `F^o`" cases,
leaving only the "limit in `F^o`" case, which gives `w ∈ λ(F^o)`. -/
theorem modularLambdaH_F_image_isClosed_in_upperHalf :
    IsClosed (((↑) : { w : ℂ // 0 < w.im } → ℂ) ⁻¹'
      (modularLambdaH '' Gamma2FundamentalDomainInterior)) := by
  refine IsSeqClosed.isClosed ?_
  intro xn x_target hxn_in hxn_tendsto
  -- Choose τₙ ∈ F^o with λ(τₙ) = (xn n).val.
  have h_exists : ∀ n, ∃ τ, τ ∈ Gamma2FundamentalDomainInterior ∧
      modularLambdaH τ = (xn n).val := fun n => hxn_in n
  choose τ hτ_pair using h_exists
  have hτF : ∀ n, τ n ∈ Gamma2FundamentalDomainInterior := fun n => (hτ_pair n).1
  have hτlam : ∀ n, modularLambdaH (τ n) = (xn n).val := fun n => (hτ_pair n).2
  -- λ(τₙ) → x_target.val in ℂ.
  have h_xn_C : Filter.Tendsto (fun n => (xn n).val) Filter.atTop (nhds x_target.val) :=
    (continuous_subtype_val.tendsto _).comp hxn_tendsto
  have h_lamτ_C : Filter.Tendsto (fun n => modularLambdaH (τ n)) Filter.atTop
      (nhds x_target.val) := by
    have h_eq : (fun n => modularLambdaH (τ n)) = (fun n => (xn n).val) := funext hτlam
    rw [h_eq]; exact h_xn_C
  have h_x_im_pos : 0 < x_target.val.im := x_target.property
  have h_x_norm_pos : 0 < ‖x_target.val‖ := by
    calc 0 < x_target.val.im := h_x_im_pos
      _ ≤ |x_target.val.im| := le_abs_self _
      _ ≤ ‖x_target.val‖ := Complex.abs_im_le_norm _
  -- ‖λ(τₙ)‖ → ‖x_target.val‖.
  have h_norm_lamτ : Filter.Tendsto (fun n => ‖modularLambdaH (τ n)‖) Filter.atTop
      (nhds ‖x_target.val‖) :=
    (continuous_norm.tendsto _).comp h_lamτ_C
  -- Pick Y so that for Im τ ≥ Y, ‖λ τ‖ ≤ ‖x_target.val‖/2.
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  set Y : ℝ := max 1 (Real.log (320000 / ‖x_target.val‖) / Real.pi) with hY_def
  have hY_ge_one : 1 ≤ Y := le_max_left _ _
  have hY_log_le : Real.log (320000 / ‖x_target.val‖) / Real.pi ≤ Y := le_max_right _ _
  have h_quot_pos : 0 < 320000 / ‖x_target.val‖ := by positivity
  have h_exp_Y : 320000 / ‖x_target.val‖ ≤ Real.exp (Real.pi * Y) := by
    have h_step : Real.log (320000 / ‖x_target.val‖) ≤ Real.pi * Y := by
      rw [div_le_iff₀ hπ_pos] at hY_log_le; linarith
    have := Real.exp_le_exp.mpr h_step
    rwa [Real.exp_log h_quot_pos] at this
  -- For Im τ ≥ Y: 160000 * exp(-π·Im τ) ≤ ‖x_target.val‖/2.
  have h_bound_at_Y : 160000 * Real.exp (-Real.pi * Y) ≤ ‖x_target.val‖ / 2 := by
    rw [show -Real.pi * Y = -(Real.pi * Y) from by ring, Real.exp_neg]
    have h_exp_pos : 0 < Real.exp (Real.pi * Y) := Real.exp_pos _
    have h_320 : 320000 ≤ Real.exp (Real.pi * Y) * ‖x_target.val‖ := by
      have h := h_exp_Y
      rw [div_le_iff₀ h_x_norm_pos] at h
      linarith
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [show (160000 * (Real.exp (Real.pi * Y))⁻¹ * 2 : ℝ) =
      320000 / Real.exp (Real.pi * Y) from by field_simp; ring]
    rw [div_le_iff₀ h_exp_pos]
    linarith
  -- Eventually ‖λ τₙ‖ > ‖x_target.val‖ / 2.
  have h_eventually_large : ∀ᶠ n in Filter.atTop, ‖x_target.val‖ / 2 < ‖modularLambdaH (τ n)‖ := by
    have h_half_lt : ‖x_target.val‖ / 2 < ‖x_target.val‖ := by linarith
    exact h_norm_lamτ.eventually_const_lt h_half_lt
  -- Define K (eventually contains τₙ).
  set K : Set ℂ := { z : ℂ | 0 ≤ z.im ∧ z.im ≤ Y ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ ‖2 * z - 1‖ }
    with hK_def
  -- Continuity helpers.
  have h2zm1_cont : Continuous (fun z : ℂ => 2 * z - 1) :=
    (continuous_const.mul continuous_id).sub continuous_const
  -- K is closed.
  have hK_closed : IsClosed K := by
    refine (isClosed_le continuous_const Complex.continuous_im).inter ?_
    refine (isClosed_le Complex.continuous_im continuous_const).inter ?_
    refine (isClosed_le continuous_const Complex.continuous_re).inter ?_
    refine (isClosed_le Complex.continuous_re continuous_const).inter ?_
    exact isClosed_le continuous_const h2zm1_cont.norm
  -- K is bounded.
  have hK_bdd : Bornology.IsBounded K := by
    refine Bornology.IsBounded.subset (Metric.isBounded_ball (x := (0 : ℂ)) (r := Y + 2)) ?_
    intro z hz
    obtain ⟨h_im_nn, h_im_le, h_re_nn, h_re_le, _⟩ := hz
    rw [Metric.mem_ball, dist_zero_right]
    have h_sq : ‖z‖^2 < (Y + 2)^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [hY_ge_one]
    nlinarith [norm_nonneg z, sq_nonneg (Y + 2 - ‖z‖)]
  -- K is compact.
  have hK_compact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_closed hK_bdd
  -- Eventually τₙ ∈ K.
  have h_eventually_in_K : ∀ᶠ n in Filter.atTop, τ n ∈ K := by
    filter_upwards [h_eventually_large] with n hn_large
    obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτF n
    refine ⟨hτ_im_pos.le, ?_, hτ_re_pos.le, hτ_re_lt_one.le, hτ_semicircle.le⟩
    -- Im τₙ ≤ Y. Otherwise ‖λ τₙ‖ ≤ 160000 exp(-π Im τₙ) ≤ 160000 exp(-π Y) ≤ ‖x‖/2.
    by_contra h_im_gt
    push Not at h_im_gt
    have h_im_ge_Y : Y ≤ (τ n).im := h_im_gt.le
    have h_im_ge_one : 1 ≤ (τ n).im := le_trans hY_ge_one h_im_ge_Y
    have h_bound : ‖modularLambdaH (τ n)‖ ≤ 160000 * Real.exp (-Real.pi * (τ n).im) :=
      modularLambdaH_norm_le_exp_of_im_ge_one h_im_ge_one
    have h_exp_le : Real.exp (-Real.pi * (τ n).im) ≤ Real.exp (-Real.pi * Y) := by
      apply Real.exp_le_exp.mpr
      have h_pi_Y_le : Real.pi * Y ≤ Real.pi * (τ n).im :=
        mul_le_mul_of_nonneg_left h_im_ge_Y hπ_pos.le
      linarith
    have h_chain : ‖modularLambdaH (τ n)‖ ≤ ‖x_target.val‖ / 2 := by
      calc ‖modularLambdaH (τ n)‖
          ≤ 160000 * Real.exp (-Real.pi * (τ n).im) := h_bound
        _ ≤ 160000 * Real.exp (-Real.pi * Y) :=
            mul_le_mul_of_nonneg_left h_exp_le (by norm_num)
        _ ≤ ‖x_target.val‖ / 2 := h_bound_at_Y
    linarith
  -- Extract n₀ such that τₙ ∈ K for n ≥ n₀.
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp h_eventually_in_K
  -- Shifted sequence τ' n := τ (n + n₀).
  set τ' : ℕ → ℂ := fun n => τ (n + n₀) with hτ'_def
  have hτ'_in_K : ∀ n, τ' n ∈ K := fun n => hn₀ (n + n₀) (Nat.le_add_left n₀ n)
  -- Bolzano-Weierstrass on K.
  obtain ⟨τStar, hτStar_in_K, φ, hφ_mono, hφ_tendsto⟩ :=
    hK_compact.tendsto_subseq hτ'_in_K
  -- τStar ∈ K. λ ∘ τ' ∘ φ → x_target.val.
  have h_lamτ'_tendsto : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
      (nhds x_target.val) := by
    have h_lamτ' : Filter.Tendsto (fun n => modularLambdaH (τ' n)) Filter.atTop
        (nhds x_target.val) := by
      have h_shift : (fun n => modularLambdaH (τ' n)) =
          (fun n => modularLambdaH (τ n)) ∘ (fun n => n + n₀) := by
        funext n; rfl
      rw [h_shift]
      exact h_lamτ_C.comp (Filter.tendsto_add_atTop_nat n₀)
    exact h_lamτ'.comp hφ_mono.tendsto_atTop
  -- Extract closure constraints on τStar.
  obtain ⟨hτs_im_nn, hτs_im_le_Y, hτs_re_nn, hτs_re_le, hτs_sc⟩ := hτStar_in_K
  -- Case split on τStar.
  by_cases h_τs_im_pos : 0 < τStar.im
  · -- τStar.im > 0: cases on which boundary condition (Re, semicircle) is active.
    by_cases h_re_zero : τStar.re ≤ 0
    · -- Re τStar = 0. λ(τStar) is real. Contradicts x_target.val.im > 0.
      exfalso
      have h_re_eq : τStar.re = 0 := le_antisymm h_re_zero hτs_re_nn
      have h_z_eq : τStar = Complex.I * ((τStar.im : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, h_re_eq]
        · simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im]
      have h_lamτs_real : (modularLambdaH τStar).im = 0 := by
        rw [h_z_eq]; exact modularLambdaH_pure_imag_real h_τs_im_pos
      -- λ(τ'_{φ n}) → λ(τStar) by continuity.
      have h_τs_im_pos' : 0 < τStar.im := h_τs_im_pos
      have h_lam_cont : ContinuousAt modularLambdaH τStar :=
        (modularLambdaH_differentiableAt_of_im_pos h_τs_im_pos').continuousAt
      have h_lamτ'φ_to_τs : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
          (nhds (modularLambdaH τStar)) := h_lam_cont.tendsto.comp hφ_tendsto
      have h_lamτs_eq : modularLambdaH τStar = x_target.val :=
        tendsto_nhds_unique h_lamτ'φ_to_τs h_lamτ'_tendsto
      have : x_target.val.im = 0 := by rw [← h_lamτs_eq]; exact h_lamτs_real
      linarith
    push Not at h_re_zero
    by_cases h_re_one : 1 ≤ τStar.re
    · -- Re τStar = 1. λ real. Contradiction.
      exfalso
      have h_re_eq : τStar.re = 1 := le_antisymm hτs_re_le h_re_one
      have h_z_eq : τStar = 1 + Complex.I * ((τStar.im : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, h_re_eq]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
      have h_lamτs_real : (modularLambdaH τStar).im = 0 := by
        rw [h_z_eq]; exact modularLambdaH_one_add_imag_real h_τs_im_pos
      have h_τs_im_pos' : 0 < τStar.im := h_τs_im_pos
      have h_lam_cont : ContinuousAt modularLambdaH τStar :=
        (modularLambdaH_differentiableAt_of_im_pos h_τs_im_pos').continuousAt
      have h_lamτ'φ_to_τs : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
          (nhds (modularLambdaH τStar)) := h_lam_cont.tendsto.comp hφ_tendsto
      have h_lamτs_eq : modularLambdaH τStar = x_target.val :=
        tendsto_nhds_unique h_lamτ'φ_to_τs h_lamτ'_tendsto
      have : x_target.val.im = 0 := by rw [← h_lamτs_eq]; exact h_lamτs_real
      linarith
    push Not at h_re_one
    by_cases h_sc_eq : ‖2 * τStar - 1‖ ≤ 1
    · -- ‖2τStar - 1‖ = 1: semicircle. λ real. Contradiction.
      exfalso
      have h_sc_eq' : ‖2 * τStar - 1‖ = 1 := le_antisymm h_sc_eq hτs_sc
      have h_lamτs_real : (modularLambdaH τStar).im = 0 :=
        modularLambdaH_semicircle_real h_τs_im_pos h_sc_eq'
      have h_lam_cont : ContinuousAt modularLambdaH τStar :=
        (modularLambdaH_differentiableAt_of_im_pos h_τs_im_pos).continuousAt
      have h_lamτ'φ_to_τs : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
          (nhds (modularLambdaH τStar)) := h_lam_cont.tendsto.comp hφ_tendsto
      have h_lamτs_eq : modularLambdaH τStar = x_target.val :=
        tendsto_nhds_unique h_lamτ'φ_to_τs h_lamτ'_tendsto
      have : x_target.val.im = 0 := by rw [← h_lamτs_eq]; exact h_lamτs_real
      linarith
    push Not at h_sc_eq
    -- τStar ∈ F^o.
    have hτStar_in_F : τStar ∈ Gamma2FundamentalDomainInterior :=
      ⟨h_τs_im_pos, h_re_zero, h_re_one, h_sc_eq⟩
    have h_lam_cont : ContinuousAt modularLambdaH τStar :=
      (modularLambdaH_differentiableAt_of_im_pos h_τs_im_pos).continuousAt
    have h_lamτ'φ_to_τs : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
        (nhds (modularLambdaH τStar)) := h_lam_cont.tendsto.comp hφ_tendsto
    have h_lamτs_eq : modularLambdaH τStar = x_target.val :=
      tendsto_nhds_unique h_lamτ'φ_to_τs h_lamτ'_tendsto
    -- x_target.val ∈ λ(F^o).
    exact ⟨τStar, hτStar_in_F, h_lamτs_eq⟩
  · -- τStar.im = 0. So τStar is on the real axis. K constraints force τStar = 0 or 1.
    push Not at h_τs_im_pos
    have h_τs_im_zero : τStar.im = 0 := le_antisymm h_τs_im_pos hτs_im_nn
    -- ‖2τStar - 1‖² ≥ 1 with Im τStar = 0 gives (2 Re τStar - 1)² ≥ 1.
    have h_sc_sq : 1 ≤ ‖2 * τStar - 1‖^2 := by
      have h_nn : 0 ≤ ‖2 * τStar - 1‖ := norm_nonneg _
      nlinarith [hτs_sc]
    have h_2zm1_sq : ‖2 * τStar - 1‖^2 = (2 * τStar.re - 1)^2 + (2 * τStar.im)^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.one_re, Complex.one_im]
      ring
    rw [h_2zm1_sq, h_τs_im_zero] at h_sc_sq
    have h_re_sq : 1 ≤ (2 * τStar.re - 1)^2 := by linarith
    have h_re_outside : τStar.re ≤ 0 ∨ 1 ≤ τStar.re := by
      rcases le_or_gt (2 * τStar.re - 1) 0 with h | h
      · left; nlinarith [sq_nonneg (2 * τStar.re - 1)]
      · right; nlinarith [sq_nonneg (2 * τStar.re - 1)]
    rcases h_re_outside with h_re_le_0 | h_re_ge_1
    · -- τStar = 0 (cusp 0).
      exfalso
      have h_re_zero : τStar.re = 0 := le_antisymm h_re_le_0 hτs_re_nn
      have h_τStar_eq_zero : τStar = 0 := by
        apply Complex.ext
        · simp [h_re_zero]
        · simp [h_τs_im_zero]
      -- τ' ∘ φ → 0 in F^o. So λ(τ' ∘ φ) → 1 by cusp-0 limit.
      have hτ'φ_tendsto : Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop (nhds (0 : ℂ)) := by
        rw [← h_τStar_eq_zero]; exact hφ_tendsto
      have hτ'φ_in_F : ∀ n, τ' (φ n) ∈ Gamma2FundamentalDomainInterior :=
        fun n => hτF (φ n + n₀)
      have hτ'φ_tendsto_in_F :
          Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop
            (nhdsWithin (0 : ℂ) Gamma2FundamentalDomainInterior) := by
        rw [nhdsWithin, Filter.tendsto_inf]
        refine ⟨hτ'φ_tendsto, ?_⟩
        rw [Filter.tendsto_principal]
        exact Filter.Eventually.of_forall hτ'φ_in_F
      have h_cusp0 :
          Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop (nhds 1) :=
        modularLambdaH_cusp_zero_tendsto_one_in_F.comp hτ'φ_tendsto_in_F
      have h_x_eq_one : x_target.val = 1 := tendsto_nhds_unique h_lamτ'_tendsto h_cusp0
      have : x_target.val.im = 0 := by rw [h_x_eq_one]; rfl
      linarith
    · -- τStar = 1 (cusp 1).
      exfalso
      have h_re_one : τStar.re = 1 := le_antisymm hτs_re_le h_re_ge_1
      have h_τStar_eq_one : τStar = 1 := by
        apply Complex.ext
        · simp [h_re_one]
        · simp [h_τs_im_zero]
      have hτ'φ_tendsto : Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop (nhds (1 : ℂ)) := by
        rw [← h_τStar_eq_one]; exact hφ_tendsto
      have hτ'φ_in_F : ∀ n, τ' (φ n) ∈ Gamma2FundamentalDomainInterior :=
        fun n => hτF (φ n + n₀)
      have hτ'φ_tendsto_in_F :
          Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop
            (nhdsWithin (1 : ℂ) Gamma2FundamentalDomainInterior) := by
        rw [nhdsWithin, Filter.tendsto_inf]
        refine ⟨hτ'φ_tendsto, ?_⟩
        rw [Filter.tendsto_principal]
        exact Filter.Eventually.of_forall hτ'φ_in_F
      have h_cusp1 :
          Filter.Tendsto (fun n => ‖modularLambdaH (τ' (φ n))‖) Filter.atTop Filter.atTop :=
        modularLambdaH_cusp_one_tendsto_norm_atTop_in_F.comp hτ'φ_tendsto_in_F
      have h_norm_lamτ'φ_tendsto :
          Filter.Tendsto (fun n => ‖modularLambdaH (τ' (φ n))‖) Filter.atTop
            (nhds ‖x_target.val‖) := (continuous_norm.tendsto _).comp h_lamτ'_tendsto
      -- Cannot tend to both atTop and to a finite value: pick conflicting witnesses.
      have h_at1 := h_cusp1
      rw [Filter.tendsto_atTop] at h_at1
      have h_at1_event := h_at1 (‖x_target.val‖ + 1)
      rw [Metric.tendsto_atTop] at h_norm_lamτ'φ_tendsto
      obtain ⟨N₂, hN₂⟩ := h_norm_lamτ'φ_tendsto 1 (by norm_num)
      obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h_at1_event
      set N := max N₁ N₂
      have h_ge : ‖x_target.val‖ + 1 ≤ ‖modularLambdaH (τ' (φ N))‖ :=
        hN₁ N (le_max_left _ _)
      have h_close : dist (‖modularLambdaH (τ' (φ N))‖) (‖x_target.val‖) < 1 :=
        hN₂ N (le_max_right _ _)
      rw [Real.dist_eq] at h_close
      have h_lt : ‖modularLambdaH (τ' (φ N))‖ - ‖x_target.val‖ < 1 :=
        (abs_lt.mp h_close).2
      linarith

/-- **Step D — biholomorphism of `λ` on `F^o`.** Combining Steps A, B,
C and the connectedness of the upper half-plane: `λ(F^o)` is a
nonempty clopen subset of the connected upper half-plane, hence
equals the entire upper half-plane. -/
theorem modularLambdaH_image_fundamentalDomainInterior :
    modularLambdaH '' Gamma2FundamentalDomainInterior = { w : ℂ | 0 < w.im } := by
  -- Set up the subset and the connected ambient space.
  set U : Set ℂ := { w : ℂ | 0 < w.im } with hU_def
  set S : Set ℂ := modularLambdaH '' Gamma2FundamentalDomainInterior with hS_def
  -- Step A: S ⊆ U.
  have hSU : S ⊆ U := by
    rintro w ⟨τ, hτ, rfl⟩
    exact modularLambdaH_F_im_pos τ hτ
  -- Step B: S is open in ℂ.
  have hS_open : IsOpen S := modularLambdaH_F_image_isOpen
  -- Step C: S is closed in U (subspace topology).
  have hS_closed_in_U :
      IsClosed (((↑) : U → ℂ) ⁻¹' S) := modularLambdaH_F_image_isClosed_in_upperHalf
  -- S is open in U (from S open in ℂ, restrict).
  have hS_open_in_U :
      IsOpen (((↑) : U → ℂ) ⁻¹' S) := hS_open.preimage continuous_subtype_val
  -- U is preconnected (the upper half-plane is convex).
  have hU_preconn : IsPreconnected U := by
    have hconv : Convex ℝ U := by
      intro w₁ hw₁ w₂ hw₂ s t hs ht hst
      simp only [hU_def, Set.mem_ofPred_eq] at hw₁ hw₂ ⊢
      change 0 < (s • w₁ + t • w₂).im
      rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
      rcases lt_or_eq_of_le hs with hs_pos | hs_zero
      · have h1 : 0 < s * w₁.im := mul_pos hs_pos hw₁
        have h2 : 0 ≤ t * w₂.im := mul_nonneg ht hw₂.le
        linarith
      · have ht_pos : 0 < t := by linarith
        have h1 : 0 ≤ s * w₁.im := mul_nonneg hs hw₁.le
        have h2 : 0 < t * w₂.im := mul_pos ht_pos hw₂
        linarith
    exact hconv.isPreconnected
  -- S is nonempty: pick the explicit witness (1 + 4i)/2 ∈ F^o.
  have hS_nonempty : S.Nonempty := by
    have hw_in_F : (((1 : ℂ) + 4 * Complex.I) / 2) ∈ Gamma2FundamentalDomainInterior := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re]
      · simp [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re]
      · rw [show ((1 + 4 * Complex.I) / 2 : ℂ) = (1 : ℂ) / 2 + 2 * Complex.I from by ring]
        simp [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re,
          Complex.normSq_ofNat]
        norm_num
      · have heq : 2 * (((1 : ℂ) + 4 * Complex.I) / 2) - 1 = 4 * Complex.I := by ring
        rw [heq]
        simp
    exact ⟨modularLambdaH _, _, hw_in_F, rfl⟩
  -- The preimage of S in U is nonempty.
  have hSU_pre_nonempty : (((↑) : U → ℂ) ⁻¹' S).Nonempty := by
    obtain ⟨w, hw⟩ := hS_nonempty
    exact ⟨⟨w, hSU hw⟩, hw⟩
  -- Extract a closed set `C` in ℂ such that `C ∩ U = S` (from `hS_closed_in_U`
  -- via the subspace topology induced by `Subtype.val`).
  rw [isClosed_induced_iff] at hS_closed_in_U
  obtain ⟨C, hC_closed, hC_eq⟩ := hS_closed_in_U
  have hCU_eq_S : ∀ w ∈ U, w ∈ C ↔ w ∈ S := by
    intro w hw
    exact iff_of_eq (congrArg (· (⟨w, hw⟩ : U)) hC_eq)
  -- The open complement `Cᶜ` together with `S` covers `U` disjointly.
  have hSC : S ⊆ C := fun w hw => (hCU_eq_S w (hSU hw)).mpr hw
  have hUSC : U ⊆ S ∪ Cᶜ := by
    intro w hwU
    by_cases hwC : w ∈ C
    · exact Or.inl ((hCU_eq_S w hwU).mp hwC)
    · exact Or.inr hwC
  have hSC_disj : Disjoint S Cᶜ := by
    rw [Set.disjoint_iff_inter_eq_empty]
    apply Set.eq_empty_of_forall_notMem
    intro w hw
    exact hw.2 (hSC hw.1)
  -- Apply IsPreconnected.subset_left_of_subset_union to conclude U ⊆ S.
  have hU_sub_S : U ⊆ S :=
    hU_preconn.subset_left_of_subset_union hS_open hC_closed.isOpen_compl
      hSC_disj hUSC ((Set.inter_eq_self_of_subset_right hSU).symm ▸ hS_nonempty)
  exact Set.eq_of_subset_of_subset hSU hU_sub_S

/-- **`⊆` direction of the biholomorphism:** the image of `F^o` under
`λ` lies in the upper half-plane. Derived from
`modularLambdaH_image_fundamentalDomainInterior`. -/
theorem modularLambdaH_image_F_subset_upperHalf :
    modularLambdaH '' Gamma2FundamentalDomainInterior ⊆ { w : ℂ | 0 < w.im } :=
  modularLambdaH_image_fundamentalDomainInterior.subset

/-- **`⊇` direction of the biholomorphism:** every point `w` with
`Im w > 0` is in `λ(F^o)`. Derived from
`modularLambdaH_image_fundamentalDomainInterior`. -/
theorem modularLambdaH_image_F_supset_upperHalf :
    { w : ℂ | 0 < w.im } ⊆ modularLambdaH '' Gamma2FundamentalDomainInterior :=
  modularLambdaH_image_fundamentalDomainInterior.superset

/-! ## Surjectivity of `λ` onto the triply-punctured plane -/

/-- **Surjectivity of `λ : ℍ → ℂ ∖ {0, 1}`.** The image of `λ` on `ℍ`
is exactly the triply-punctured plane.

The `⊆` direction is direct from `modularLambdaH_ne_zero` and
`modularLambdaH_ne_one`. The `⊇` direction reduces to Step D
`modularLambdaH_image_fundamentalDomainInterior`
(`λ(F^o) = {Im w > 0}`) plus the conjugation symmetry
`modularLambdaH_conj_symmetry` (which provides the Schwarz-reflection
across the imaginary axis covering `{Im w < 0}`), and a sequential
compactness extraction for `w ∈ ℝ ∖ {0, 1}` that lifts any
sequence `wₙ = w + i/n ∈ λ(F^o)` to `τₙ ∈ F^o`, then uses the cusp
asymptotics
`modularLambdaH_cusp_zero_tendsto_one_in_F`,
`modularLambdaH_cusp_one_tendsto_norm_atTop_in_F`, and
`modularLambdaH_norm_le_exp_of_im_ge_one` to rule out the three
cusps `{0, 1, ∞}` as accumulation points. -/
theorem modularLambdaH_image :
    modularLambdaH '' { τ : ℂ | 0 < τ.im } = { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro w ⟨τ, hτ, rfl⟩
    exact ⟨modularLambdaH_ne_zero hτ, modularLambdaH_ne_one hτ⟩
  · rintro w ⟨hw0, hw1⟩
    by_cases h_im_neg : w.im < 0
    · -- `w.im < 0`: use conjugation symmetry `λ(-conj τ) = conj(λ τ)`.
      have hconj_im_pos : 0 < (starRingEnd ℂ w).im := by
        rw [Complex.conj_im]; linarith
      have hconj_in : starRingEnd ℂ w ∈ modularLambdaH '' Gamma2FundamentalDomainInterior := by
        rw [modularLambdaH_image_fundamentalDomainInterior]
        exact hconj_im_pos
      obtain ⟨τ', hτ'_in_F, hτ'_lambda⟩ := hconj_in
      have hτ'_im_pos : 0 < τ'.im :=
        Gamma2FundamentalDomainInterior_subset_upperHalf hτ'_in_F
      refine ⟨-(starRingEnd ℂ τ'), ?_, ?_⟩
      · change 0 < (-(starRingEnd ℂ τ')).im
        rw [Complex.neg_im, Complex.conj_im]; linarith
      · rw [modularLambdaH_conj_symmetry hτ'_im_pos, hτ'_lambda, Complex.conj_conj]
    · -- `w.im ≥ 0`: sequential compactness in F^o via Step D.
      have hw_im_nn : 0 ≤ w.im := not_lt.mp h_im_neg
      -- Sequence `wn = w + i / (n + 1)`, all in the open upper half-plane.
      set wn : ℕ → ℂ := fun n => w + Complex.I * ((1 / (n + 1 : ℝ) : ℝ) : ℂ) with hwn_def
      have hwn_im : ∀ n, (wn n).im = w.im + 1 / (n + 1 : ℝ) := by
        intro n
        change (w + Complex.I * ((1 / (n + 1 : ℝ) : ℝ) : ℂ)).im = w.im + 1 / (n + 1 : ℝ)
        rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      have hwn_im_pos : ∀ n, 0 < (wn n).im := by
        intro n
        rw [hwn_im n]
        have h_div_pos : 0 < (1 : ℝ) / (n + 1) := by positivity
        linarith
      -- `wn → w` in `ℂ`.
      have hwn_tendsto : Filter.Tendsto wn Filter.atTop (nhds w) := by
        have h_inner : Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ) : ℝ)) Filter.atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h_inner_C : Filter.Tendsto
            (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) Filter.atTop (nhds 0) := by
          have h_zero : ((0 : ℝ) : ℂ) = (0 : ℂ) := Complex.ofReal_zero
          rw [← h_zero]
          exact (Complex.continuous_ofReal.tendsto _).comp h_inner
        have h_mul : Filter.Tendsto (fun n : ℕ => Complex.I * ((1 / (n + 1 : ℝ) : ℝ) : ℂ))
            Filter.atTop (nhds (Complex.I * 0)) :=
          tendsto_const_nhds.mul h_inner_C
        rw [mul_zero] at h_mul
        have h_add : Filter.Tendsto (fun n : ℕ => w + Complex.I * ((1 / (n + 1 : ℝ) : ℝ) : ℂ))
            Filter.atTop (nhds (w + 0)) := tendsto_const_nhds.add h_mul
        rw [add_zero] at h_add
        exact h_add
      -- Each `wn` lifts to `τn ∈ F^o` by Step D.
      have h_exists : ∀ n, ∃ τ ∈ Gamma2FundamentalDomainInterior,
          modularLambdaH τ = wn n := by
        intro n
        have h_in : wn n ∈ modularLambdaH '' Gamma2FundamentalDomainInterior := by
          rw [modularLambdaH_image_fundamentalDomainInterior]
          exact hwn_im_pos n
        obtain ⟨τ, hτ, hlamτ⟩ := h_in
        exact ⟨τ, hτ, hlamτ⟩
      choose τ hτF hτlam using h_exists
      -- `‖w‖ > 0` since `w ≠ 0`.
      have h_w_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      -- `λ(τn) → w` in `ℂ`.
      have h_lamτ_C : Filter.Tendsto (fun n => modularLambdaH (τ n)) Filter.atTop (nhds w) := by
        have h_eq : (fun n => modularLambdaH (τ n)) = wn := funext hτlam
        rw [h_eq]; exact hwn_tendsto
      have h_norm_lamτ : Filter.Tendsto (fun n => ‖modularLambdaH (τ n)‖) Filter.atTop
          (nhds ‖w‖) := (continuous_norm.tendsto _).comp h_lamτ_C
      -- Truncation `Y` of imaginary part via cusp-∞ bound.
      have hπ_pos : 0 < Real.pi := Real.pi_pos
      set Y : ℝ := max 1 (Real.log (320000 / ‖w‖) / Real.pi) with hY_def
      have hY_ge_one : 1 ≤ Y := le_max_left _ _
      have hY_log_le : Real.log (320000 / ‖w‖) / Real.pi ≤ Y := le_max_right _ _
      have h_quot_pos : 0 < 320000 / ‖w‖ := by positivity
      have h_exp_Y : 320000 / ‖w‖ ≤ Real.exp (Real.pi * Y) := by
        have h_step : Real.log (320000 / ‖w‖) ≤ Real.pi * Y := by
          rw [div_le_iff₀ hπ_pos] at hY_log_le; linarith
        have := Real.exp_le_exp.mpr h_step
        rwa [Real.exp_log h_quot_pos] at this
      have h_bound_at_Y : 160000 * Real.exp (-Real.pi * Y) ≤ ‖w‖ / 2 := by
        rw [show -Real.pi * Y = -(Real.pi * Y) from by ring, Real.exp_neg]
        have h_exp_pos : 0 < Real.exp (Real.pi * Y) := Real.exp_pos _
        have h_320 : 320000 ≤ Real.exp (Real.pi * Y) * ‖w‖ := by
          have h := h_exp_Y
          rw [div_le_iff₀ h_w_norm_pos] at h
          linarith
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        rw [show (160000 * (Real.exp (Real.pi * Y))⁻¹ * 2 : ℝ) =
          320000 / Real.exp (Real.pi * Y) from by field_simp; ring]
        rw [div_le_iff₀ h_exp_pos]
        linarith
      have h_eventually_large : ∀ᶠ n in Filter.atTop, ‖w‖ / 2 < ‖modularLambdaH (τ n)‖ := by
        have h_half_lt : ‖w‖ / 2 < ‖w‖ := by linarith
        exact h_norm_lamτ.eventually_const_lt h_half_lt
      -- Compact truncation `K` of `F^o`.
      set K : Set ℂ := { z : ℂ | 0 ≤ z.im ∧ z.im ≤ Y ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ ‖2 * z - 1‖ }
        with hK_def
      have h2zm1_cont : Continuous (fun z : ℂ => 2 * z - 1) :=
        (continuous_const.mul continuous_id).sub continuous_const
      have hK_closed : IsClosed K := by
        refine (isClosed_le continuous_const Complex.continuous_im).inter ?_
        refine (isClosed_le Complex.continuous_im continuous_const).inter ?_
        refine (isClosed_le continuous_const Complex.continuous_re).inter ?_
        refine (isClosed_le Complex.continuous_re continuous_const).inter ?_
        exact isClosed_le continuous_const h2zm1_cont.norm
      have hK_bdd : Bornology.IsBounded K := by
        refine Bornology.IsBounded.subset (Metric.isBounded_ball (x := (0 : ℂ)) (r := Y + 2)) ?_
        intro z hz
        obtain ⟨h_im_nn, h_im_le, h_re_nn, h_re_le, _⟩ := hz
        rw [Metric.mem_ball, dist_zero_right]
        have h_sq : ‖z‖^2 < (Y + 2)^2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          nlinarith [hY_ge_one]
        nlinarith [norm_nonneg z, sq_nonneg (Y + 2 - ‖z‖)]
      have hK_compact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_closed hK_bdd
      -- Eventually `τn ∈ K`.
      have h_eventually_in_K : ∀ᶠ n in Filter.atTop, τ n ∈ K := by
        filter_upwards [h_eventually_large] with n hn_large
        obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτF n
        refine ⟨hτ_im_pos.le, ?_, hτ_re_pos.le, hτ_re_lt_one.le, hτ_semicircle.le⟩
        by_contra h_im_gt
        have h_im_ge_Y : Y ≤ (τ n).im := (not_le.mp h_im_gt).le
        have h_im_ge_one : 1 ≤ (τ n).im := le_trans hY_ge_one h_im_ge_Y
        have h_bound : ‖modularLambdaH (τ n)‖ ≤ 160000 * Real.exp (-Real.pi * (τ n).im) :=
          modularLambdaH_norm_le_exp_of_im_ge_one h_im_ge_one
        have h_exp_le : Real.exp (-Real.pi * (τ n).im) ≤ Real.exp (-Real.pi * Y) := by
          apply Real.exp_le_exp.mpr
          have h_pi_Y_le : Real.pi * Y ≤ Real.pi * (τ n).im :=
            mul_le_mul_of_nonneg_left h_im_ge_Y hπ_pos.le
          linarith
        have h_chain : ‖modularLambdaH (τ n)‖ ≤ ‖w‖ / 2 := by
          calc ‖modularLambdaH (τ n)‖
              ≤ 160000 * Real.exp (-Real.pi * (τ n).im) := h_bound
            _ ≤ 160000 * Real.exp (-Real.pi * Y) :=
                mul_le_mul_of_nonneg_left h_exp_le (by norm_num)
            _ ≤ ‖w‖ / 2 := h_bound_at_Y
        linarith
      obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp h_eventually_in_K
      set τ' : ℕ → ℂ := fun n => τ (n + n₀) with hτ'_def
      have hτ'_in_K : ∀ n, τ' n ∈ K := fun n => hn₀ (n + n₀) (Nat.le_add_left n₀ n)
      obtain ⟨τStar, hτStar_in_K, φ, hφ_mono, hφ_tendsto⟩ :=
        hK_compact.tendsto_subseq hτ'_in_K
      have h_lamτ'_tendsto : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
          (nhds w) := by
        have h_lamτ' : Filter.Tendsto (fun n => modularLambdaH (τ' n)) Filter.atTop (nhds w) := by
          have h_shift : (fun n => modularLambdaH (τ' n)) =
              (fun n => modularLambdaH (τ n)) ∘ (fun n => n + n₀) := by
            funext n; rfl
          rw [h_shift]
          exact h_lamτ_C.comp (Filter.tendsto_add_atTop_nat n₀)
        exact h_lamτ'.comp hφ_mono.tendsto_atTop
      obtain ⟨hτs_im_nn, _hτs_im_le_Y, hτs_re_nn, hτs_re_le, hτs_sc⟩ := hτStar_in_K
      by_cases h_τs_im_pos : 0 < τStar.im
      · -- `τStar ∈ ℍ`. Continuity of `λ` gives `λ(τStar) = w`.
        refine ⟨τStar, h_τs_im_pos, ?_⟩
        have h_lam_cont : ContinuousAt modularLambdaH τStar :=
          (modularLambdaH_differentiableAt_of_im_pos h_τs_im_pos).continuousAt
        have h_lamτ'φ_to_τs : Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop
            (nhds (modularLambdaH τStar)) := h_lam_cont.tendsto.comp hφ_tendsto
        exact tendsto_nhds_unique h_lamτ'φ_to_τs h_lamτ'_tendsto
      · -- `τStar.im = 0`. Membership in `K` and `1 ≤ ‖2τ−1‖` forces τStar ∈ {0, 1};
        -- the cusp lemmas then contradict `w ≠ 0, w ≠ 1`.
        have h_τs_im_le : τStar.im ≤ 0 := not_lt.mp h_τs_im_pos
        have h_τs_im_zero : τStar.im = 0 := le_antisymm h_τs_im_le hτs_im_nn
        have h_sc_sq : 1 ≤ ‖2 * τStar - 1‖^2 := by
          have h_nn : 0 ≤ ‖2 * τStar - 1‖ := norm_nonneg _
          nlinarith [hτs_sc]
        have h_2zm1_sq : ‖2 * τStar - 1‖^2 = (2 * τStar.re - 1)^2 + (2 * τStar.im)^2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
            Complex.one_re, Complex.one_im]
          ring
        rw [h_2zm1_sq, h_τs_im_zero] at h_sc_sq
        have h_re_sq : 1 ≤ (2 * τStar.re - 1)^2 := by linarith
        have h_re_outside : τStar.re ≤ 0 ∨ 1 ≤ τStar.re := by
          rcases le_or_gt (2 * τStar.re - 1) 0 with h | h
          · left; nlinarith [sq_nonneg (2 * τStar.re - 1)]
          · right; nlinarith [sq_nonneg (2 * τStar.re - 1)]
        rcases h_re_outside with h_re_le_0 | h_re_ge_1
        · -- τStar = 0 (cusp 0). λ(τn) → 1 ⟹ w = 1 ⟹ contradiction.
          exfalso
          have h_re_zero : τStar.re = 0 := le_antisymm h_re_le_0 hτs_re_nn
          have h_τStar_eq_zero : τStar = 0 := by
            apply Complex.ext
            · simp [h_re_zero]
            · simp [h_τs_im_zero]
          have hτ'φ_tendsto : Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop (nhds (0 : ℂ)) := by
            rw [← h_τStar_eq_zero]; exact hφ_tendsto
          have hτ'φ_in_F : ∀ n, τ' (φ n) ∈ Gamma2FundamentalDomainInterior :=
            fun n => hτF (φ n + n₀)
          have hτ'φ_tendsto_in_F :
              Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop
                (nhdsWithin (0 : ℂ) Gamma2FundamentalDomainInterior) := by
            rw [nhdsWithin, Filter.tendsto_inf]
            refine ⟨hτ'φ_tendsto, ?_⟩
            rw [Filter.tendsto_principal]
            exact Filter.Eventually.of_forall hτ'φ_in_F
          have h_cusp0 :
              Filter.Tendsto (fun n => modularLambdaH (τ' (φ n))) Filter.atTop (nhds 1) :=
            modularLambdaH_cusp_zero_tendsto_one_in_F.comp hτ'φ_tendsto_in_F
          have h_w_eq_one : w = 1 := tendsto_nhds_unique h_lamτ'_tendsto h_cusp0
          exact hw1 h_w_eq_one
        · -- τStar = 1 (cusp 1). ‖λ(τn)‖ → ∞ while wn → w finite ⟹ contradiction.
          exfalso
          have h_re_one : τStar.re = 1 := le_antisymm hτs_re_le h_re_ge_1
          have h_τStar_eq_one : τStar = 1 := by
            apply Complex.ext
            · simp [h_re_one]
            · simp [h_τs_im_zero]
          have hτ'φ_tendsto : Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop (nhds (1 : ℂ)) := by
            rw [← h_τStar_eq_one]; exact hφ_tendsto
          have hτ'φ_in_F : ∀ n, τ' (φ n) ∈ Gamma2FundamentalDomainInterior :=
            fun n => hτF (φ n + n₀)
          have hτ'φ_tendsto_in_F :
              Filter.Tendsto (fun n => τ' (φ n)) Filter.atTop
                (nhdsWithin (1 : ℂ) Gamma2FundamentalDomainInterior) := by
            rw [nhdsWithin, Filter.tendsto_inf]
            refine ⟨hτ'φ_tendsto, ?_⟩
            rw [Filter.tendsto_principal]
            exact Filter.Eventually.of_forall hτ'φ_in_F
          have h_cusp1 :
              Filter.Tendsto (fun n => ‖modularLambdaH (τ' (φ n))‖) Filter.atTop Filter.atTop :=
            modularLambdaH_cusp_one_tendsto_norm_atTop_in_F.comp hτ'φ_tendsto_in_F
          have h_norm_lamτ'φ_tendsto :
              Filter.Tendsto (fun n => ‖modularLambdaH (τ' (φ n))‖) Filter.atTop
                (nhds ‖w‖) := (continuous_norm.tendsto _).comp h_lamτ'_tendsto
          rw [Filter.tendsto_atTop] at h_cusp1
          have h_at1_event := h_cusp1 (‖w‖ + 1)
          rw [Metric.tendsto_atTop] at h_norm_lamτ'φ_tendsto
          obtain ⟨N₂, hN₂⟩ := h_norm_lamτ'φ_tendsto 1 (by norm_num)
          obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h_at1_event
          set N := max N₁ N₂
          have h_ge : ‖w‖ + 1 ≤ ‖modularLambdaH (τ' (φ N))‖ :=
            hN₁ N (le_max_left _ _)
          have h_close : dist (‖modularLambdaH (τ' (φ N))‖) ‖w‖ < 1 :=
            hN₂ N (le_max_right _ _)
          rw [Real.dist_eq] at h_close
          have h_lt : ‖modularLambdaH (τ' (φ N))‖ - ‖w‖ < 1 :=
            (abs_lt.mp h_close).2
          linarith

/-- The image of `modularLambda` on `𝔻` is exactly `ℂ ∖ {0, 1}`.
Combines `cayleyToHalfPlane_image_ball` (Cayley sends `𝔻` onto `ℍ`)
with `modularLambdaH_image` (surjectivity of `λ` onto the
triply-punctured plane). -/
theorem modularLambda_image :
    modularLambda '' Metric.ball (0 : ℂ) 1 = { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  unfold modularLambda
  rw [show (fun z => modularLambdaH (cayleyToHalfPlane z))
        = modularLambdaH ∘ cayleyToHalfPlane from rfl,
      Set.image_comp, cayleyToHalfPlane_image_ball]
  exact modularLambdaH_image

end NoWanderingDomains
