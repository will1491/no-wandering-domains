/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.ModularFunction.JacobiIdentity

/-!
# Cusp asymptotics + argument-principle for `λ`

Two pieces of complex-analytic infrastructure for the modular
function `λ`:

* **Cusp asymptotics** (`modularLambdaH_*_tendsto_*`): `λ(iy) → 0`
  as `y → ∞`, `λ(iy) → 1` as `y → 0⁺`, and `λ(1 + iy) → 0` as
  `y → ∞`, along the natural vertical lines of approach to the
  three cusps `i∞`, `0`, and the right edge approach to `i∞`.
* **Argument-principle preimage finiteness**
  (`argumentPrinciple_rectangle_preimage_finite`): for a function
  analytic on a neighborhood of a closed rectangle, with `f` not
  identically `w` somewhere in the open rectangle, the set of
  preimages of `w` inside the open rectangle is finite.
-/

namespace NoWanderingDomains

open Complex Filter Topology Set

/-! ## Cusp asymptotics of `λ`

The three cusps of the `Γ(2)` action on `ℍ` are `i∞`, `0`, `1`. The
modular function `λ` takes the values `0`, `1`, `∞` respectively. We
state each limit as `y → ∞` (cusp `i∞`) or `y → 0⁺` (cusps `0`, `1`)
along the natural vertical line of approach. -/

/-- **Cusp `i∞`:** `λ(iy) → 0` as `y → ∞`. Combines
`theta2_norm_le_of_im_ge_one` (giving `‖θ₂(iy)‖ ≤ 10·exp(−π·y/4)`
for `y ≥ 1`) with Mathlib's `isBigO_at_im_infty_jacobiTheta_sub_one`
(giving `θ₃(iy) → 1`). Then `λ = (θ₂/θ₃)⁴ → 0`. -/
theorem modularLambdaH_iy_tendsto_zero_atTop :
    Tendsto (fun y : ℝ => modularLambdaH (Complex.I * y)) atTop (𝓝 0) := by
  -- Helper: Im(I·y) = y for y : ℝ.
  have h_im : ∀ y : ℝ, (Complex.I * (y : ℂ)).im = y := by
    intro y; simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  -- Step 1: θ₂(iy) → 0 via the norm bound.
  have h_exp_neg : Tendsto (fun y : ℝ => Real.exp (-Real.pi * y / 4)) atTop (𝓝 0) := by
    have h_arg : Tendsto (fun y : ℝ => -Real.pi * y / 4) atTop atBot := by
      have h1 : Tendsto (fun y : ℝ => (Real.pi / 4) * y) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity) tendsto_id
      have h2 : Tendsto (fun y : ℝ => -((Real.pi / 4) * y)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp h1
      refine h2.congr ?_
      intro y; ring
    exact Real.tendsto_exp_atBot.comp h_arg
  have h_10exp : Tendsto (fun y : ℝ => 10 * Real.exp (-Real.pi * y / 4)) atTop (𝓝 0) := by
    have := h_exp_neg.const_mul 10
    simpa using this
  have h2_norm_le : ∀ᶠ y : ℝ in atTop,
      ‖theta2 (Complex.I * y)‖ ≤ 10 * Real.exp (-Real.pi * y / 4) := by
    refine eventually_atTop.mpr ⟨1, fun y hy => ?_⟩
    have hτ_im : 1 ≤ (Complex.I * (y : ℂ)).im := by rw [h_im]; exact hy
    have h_bound := theta2_norm_le_of_im_ge_one hτ_im
    rwa [h_im] at h_bound
  have h2_norm_to_zero : Tendsto (fun y : ℝ => ‖theta2 (Complex.I * y)‖) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) h2_norm_le h_10exp
  have h2 : Tendsto (fun y : ℝ => theta2 (Complex.I * y)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr h2_norm_to_zero
  -- Step 2: θ₃(iy) → 1 via `isBigO_at_im_infty_jacobiTheta_sub_one`.
  have h3 : Tendsto (fun y : ℝ => theta3 (Complex.I * y)) atTop (𝓝 1) := by
    unfold theta3
    -- jacobiTheta τ → 1 as τ.im → ∞.
    have h_big_o := isBigO_at_im_infty_jacobiTheta_sub_one
    -- Compose with y ↦ I·y.
    have h_map : Tendsto (fun y : ℝ => (Complex.I * (y : ℂ))) atTop (comap Complex.im atTop) := by
      refine tendsto_comap_iff.mpr ?_
      refine (tendsto_atTop_atTop.mpr ?_)
      intro N
      refine ⟨N, fun y hy => ?_⟩
      rw [Function.comp_apply, h_im]
      exact hy
    have h_jt_sub : Tendsto (fun y : ℝ => jacobiTheta (Complex.I * y) - 1) atTop (𝓝 0) := by
      have h_rhs_to_zero : Tendsto (fun y : ℝ => Real.exp (-Real.pi * y)) atTop (𝓝 0) := by
        have h_arg : Tendsto (fun y : ℝ => -Real.pi * y) atTop atBot := by
          have h1 : Tendsto (fun y : ℝ => Real.pi * y) atTop atTop :=
            Tendsto.const_mul_atTop Real.pi_pos tendsto_id
          have h2 := tendsto_neg_atTop_atBot.comp h1
          refine h2.congr ?_
          intro y
          change -(Real.pi * y) = -Real.pi * y
          ring
        exact Real.tendsto_exp_atBot.comp h_arg
      have h_comp : Tendsto (fun y : ℝ => (jacobiTheta (Complex.I * y) - 1)) atTop
          (𝓝 0) := by
        have h_pull := h_big_o.comp_tendsto h_map
        -- h_pull : (fun y => jacobiTheta (I·y) - 1) =O[atTop] (fun y => exp(-π · (I·y).im))
        have h_pull' : (fun y : ℝ => jacobiTheta (Complex.I * y) - 1) =O[atTop]
            (fun y : ℝ => Real.exp (-Real.pi * y)) := by
          refine h_pull.congr_right ?_
          intro y
          change Real.exp (-Real.pi * (Complex.I * (y : ℂ)).im) = Real.exp (-Real.pi * y)
          rw [h_im]
        exact h_pull'.trans_tendsto h_rhs_to_zero
      exact h_comp
    have : Tendsto (fun y : ℝ => jacobiTheta (Complex.I * y)) atTop (𝓝 1) := by
      have := h_jt_sub.add_const 1
      simpa using this
    exact this
  -- Step 3: λ = (θ₂)⁴ / (θ₃)⁴ → 0⁴ / 1⁴ = 0.
  unfold modularLambdaH
  have h2_pow : Tendsto (fun y : ℝ => (theta2 (Complex.I * y))^4) atTop (𝓝 (0 ^ 4)) := h2.pow 4
  have h3_pow : Tendsto (fun y : ℝ => (theta3 (Complex.I * y))^4) atTop (𝓝 (1 ^ 4)) := h3.pow 4
  have h3_pow_ne : (1 : ℂ) ^ 4 ≠ 0 := by norm_num
  have h_div := h2_pow.div h3_pow h3_pow_ne
  simpa using! h_div

/-- **Cusp `0`:** `λ(iy) → 1` as `y → 0⁺` (along the imaginary axis).
Proof via the Jacobi sum identity `λ(τ) + λ(−1/τ) = 1` (derived inline
from `jacobi_identity` + `modularLambdaH_S_smul`) and the cusp-`i∞`
limit: `−1/(iy) = i/y → i∞` as `y → 0⁺`, so `λ(i/y) → 0`, hence
`λ(iy) = 1 − λ(i/y) → 1`. -/
theorem modularLambdaH_iy_tendsto_one_atZeroPos :
    Tendsto (fun y : ℝ => modularLambdaH (Complex.I * y)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  -- 1/y → +∞ as y → 0⁺ in ℝ.
  have h_inv : Tendsto (fun y : ℝ => y⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  -- Compose with cusp-`i∞` to get λ(I · y⁻¹) → 0.
  have h_comp : Tendsto (fun y : ℝ => modularLambdaH (Complex.I * ((y⁻¹ : ℝ) : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    modularLambdaH_iy_tendsto_zero_atTop.comp h_inv
  -- For y > 0: λ(iy) = 1 − λ(I · y⁻¹).
  have h_eq : (fun y : ℝ => modularLambdaH (Complex.I * (y : ℂ))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun y : ℝ => 1 - modularLambdaH (Complex.I * ((y⁻¹ : ℝ) : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy_pos : (0 : ℝ) < y := hy
    have hy_ne : (y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hy_pos
    have hτ_im : 0 < (Complex.I * (y : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
        Complex.I_im, Complex.ofReal_re, one_mul, zero_add]
      exact hy_pos
    -- Derive the sum identity `λ(τ) + λ(−1/τ) = 1` inline.
    have h_sum : modularLambdaH (Complex.I * (y : ℂ)) +
        modularLambdaH (-1 / (Complex.I * (y : ℂ))) = 1 := by
      rw [modularLambdaH_S_smul hτ_im]
      unfold modularLambdaH
      have h_jac : theta2 (Complex.I * (y : ℂ)) ^ 4 + theta4 (Complex.I * (y : ℂ)) ^ 4 =
          theta3 (Complex.I * (y : ℂ)) ^ 4 := jacobi_identity hτ_im
      have hne : theta3 (Complex.I * (y : ℂ)) ≠ 0 := theta3_ne_zero hτ_im
      field_simp
      linear_combination h_jac
    have h_neg_inv : (-1 / (Complex.I * (y : ℂ))) = Complex.I * ((y⁻¹ : ℝ) : ℂ) := by
      push_cast
      field_simp
      have hII : Complex.I * Complex.I = -1 := by rw [← sq]; exact Complex.I_sq
      linear_combination -hII
    rw [h_neg_inv] at h_sum
    linear_combination h_sum
  -- 1 − λ(I · y⁻¹) → 1 − 0 = 1.
  have h_target : Tendsto (fun y : ℝ => 1 - modularLambdaH (Complex.I * ((y⁻¹ : ℝ) : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 - 0)) := h_comp.const_sub 1
  simp only [sub_zero] at h_target
  exact h_target.congr' h_eq.symm

/-- **Right edge approaching `i∞`:** `λ(1 + iy) → 0` as `y → ∞`.
Uses `modularLambdaH_T_smul` (`λ(τ + 1) = −(θ₂(τ)/θ₄(τ))⁴`) together
with `θ₂(iy) → 0` (via `theta2_norm_le_of_im_ge_one`) and
`θ₄(iy) → 1` (via `isBigO_at_im_infty_jacobiTheta_sub_one` applied
at `iy + 1`). -/
theorem modularLambdaH_one_add_iy_tendsto_zero_atTop :
    Tendsto (fun y : ℝ => modularLambdaH (1 + Complex.I * y)) atTop (𝓝 0) := by
  have h_im : ∀ y : ℝ, (Complex.I * (y : ℂ)).im = y := by
    intro y; simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  -- Step 1: θ₂(iy) → 0 via the norm bound (same as in the cusp-`i∞` proof for λ).
  have h_exp_neg : Tendsto (fun y : ℝ => Real.exp (-Real.pi * y / 4)) atTop (𝓝 0) := by
    have h_arg : Tendsto (fun y : ℝ => -Real.pi * y / 4) atTop atBot := by
      have h1 : Tendsto (fun y : ℝ => (Real.pi / 4) * y) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity) tendsto_id
      have h2 := tendsto_neg_atTop_atBot.comp h1
      refine h2.congr ?_
      intro y
      change -(Real.pi / 4 * y) = -Real.pi * y / 4
      ring
    exact Real.tendsto_exp_atBot.comp h_arg
  have h_10exp : Tendsto (fun y : ℝ => 10 * Real.exp (-Real.pi * y / 4)) atTop (𝓝 0) := by
    have := h_exp_neg.const_mul 10
    simpa using this
  have h_t2_norm_le : ∀ᶠ y : ℝ in atTop,
      ‖theta2 (Complex.I * y)‖ ≤ 10 * Real.exp (-Real.pi * y / 4) := by
    refine eventually_atTop.mpr ⟨1, fun y hy => ?_⟩
    have hτ_im : 1 ≤ (Complex.I * (y : ℂ)).im := by rw [h_im]; exact hy
    have h_bound := theta2_norm_le_of_im_ge_one hτ_im
    rwa [h_im] at h_bound
  have h_t2_norm_to_zero :
      Tendsto (fun y : ℝ => ‖theta2 (Complex.I * y)‖) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) h_t2_norm_le h_10exp
  have h_t2_to_zero : Tendsto (fun y : ℝ => theta2 (Complex.I * y)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr h_t2_norm_to_zero
  -- Step 2: θ₄(iy) → 1. Since θ₄ τ = jacobiTheta(τ + 1), evaluate at τ = iy.
  have h_t4_to_one : Tendsto (fun y : ℝ => theta4 (Complex.I * y)) atTop (𝓝 1) := by
    have h_big_o := isBigO_at_im_infty_jacobiTheta_sub_one
    have h_map : Tendsto (fun y : ℝ => (Complex.I * (y : ℂ) + 1)) atTop
        (comap Complex.im atTop) := by
      refine tendsto_comap_iff.mpr ?_
      refine tendsto_atTop_atTop.mpr ?_
      intro N
      refine ⟨N, fun y hy => ?_⟩
      rw [Function.comp_apply]
      change (Complex.I * (y : ℂ) + 1).im ≥ N
      rw [Complex.add_im, h_im, Complex.one_im]
      linarith
    have h_pull := h_big_o.comp_tendsto h_map
    have h_rhs_to_zero : Tendsto (fun y : ℝ => Real.exp (-Real.pi * y)) atTop (𝓝 0) := by
      have h_arg : Tendsto (fun y : ℝ => -Real.pi * y) atTop atBot := by
        have h1 : Tendsto (fun y : ℝ => Real.pi * y) atTop atTop :=
          Tendsto.const_mul_atTop Real.pi_pos tendsto_id
        have h2 := tendsto_neg_atTop_atBot.comp h1
        refine h2.congr ?_
        intro y
        change -(Real.pi * y) = -Real.pi * y
        ring
      exact Real.tendsto_exp_atBot.comp h_arg
    have h_pull' : (fun y : ℝ => jacobiTheta (Complex.I * (y : ℂ) + 1) - 1) =O[atTop]
        (fun y : ℝ => Real.exp (-Real.pi * y)) := by
      refine h_pull.congr_right ?_
      intro y
      change Real.exp (-Real.pi * (Complex.I * (y : ℂ) + 1).im) = Real.exp (-Real.pi * y)
      rw [Complex.add_im, h_im, Complex.one_im, add_zero]
    have h_sub_to_zero :
        Tendsto (fun y : ℝ => jacobiTheta (Complex.I * (y : ℂ) + 1) - 1) atTop (𝓝 0) :=
      h_pull'.trans_tendsto h_rhs_to_zero
    have h_jt_to_one : Tendsto (fun y : ℝ => jacobiTheta (Complex.I * (y : ℂ) + 1)) atTop
        (𝓝 1) := by
      have := h_sub_to_zero.add_const 1
      simpa using this
    unfold theta4
    exact h_jt_to_one
  -- Step 3: λ(1 + iy) = -(θ₂/θ₄)⁴ → -(0/1)⁴ = 0.
  have h_id : (fun y : ℝ => modularLambdaH (1 + Complex.I * y)) =ᶠ[atTop]
      (fun y : ℝ => -(theta2 (Complex.I * y) ^ 4 / theta4 (Complex.I * y) ^ 4)) := by
    refine Filter.Eventually.of_forall ?_
    intro y
    change modularLambdaH (1 + Complex.I * (y : ℂ)) =
      -(theta2 (Complex.I * (y : ℂ)) ^ 4 / theta4 (Complex.I * (y : ℂ)) ^ 4)
    rw [show (1 + Complex.I * (y : ℂ) : ℂ) = Complex.I * (y : ℂ) + 1 from by ring]
    exact modularLambdaH_T_smul _
  have h_t2_pow : Tendsto (fun y : ℝ => theta2 (Complex.I * y) ^ 4) atTop (𝓝 (0 ^ 4)) :=
    h_t2_to_zero.pow 4
  have h_t4_pow : Tendsto (fun y : ℝ => theta4 (Complex.I * y) ^ 4) atTop (𝓝 (1 ^ 4)) :=
    h_t4_to_one.pow 4
  have h_t4_pow_ne : (1 : ℂ) ^ 4 ≠ 0 := by norm_num
  have h_div : Tendsto (fun y : ℝ => theta2 (Complex.I * y) ^ 4 /
      theta4 (Complex.I * y) ^ 4) atTop (𝓝 (0 ^ 4 / 1 ^ 4)) :=
    h_t2_pow.div h_t4_pow h_t4_pow_ne
  have h_neg : Tendsto (fun y : ℝ => -(theta2 (Complex.I * y) ^ 4 /
      theta4 (Complex.I * y) ^ 4)) atTop (𝓝 (-(0 ^ 4 / 1 ^ 4))) := h_div.neg
  have h_simp : -((0 : ℂ) ^ 4 / 1 ^ 4) = 0 := by norm_num
  rw [h_simp] at h_neg
  exact h_neg.congr' h_id.symm

/-- **Argument-principle preimage finiteness.** For a function `f`
analytic on a neighborhood of a closed rectangle `[a, b] × [c, d]`,
the set of preimages of `w` inside the open rectangle is finite
(provided `f` is not identically `w` somewhere in the open rectangle).

Proof: `g(z) := f(z) − w` is analytic on a neighborhood of the closed
rectangle, which is convex (hence preconnected). By the identity
theorem (`AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`),
either `g ≡ 0` on the closed rectangle (contradicting the hypothesis)
or the zero set is codiscrete; via `isDiscrete_of_codiscreteWithin`
the intersection with the closed rectangle has `IsDiscrete`. The
closed rectangle is compact and `f⁻¹{w} ∩ rect` is closed inside it
(continuous preimage of a closed singleton restricted to a closed
set), so `IsCompact.finite` gives finiteness in the closed rectangle;
finiteness on the open subset follows. -/
theorem argumentPrinciple_rectangle_preimage_finite
    (f : ℂ → ℂ) (w : ℂ) (a b c d : ℝ) (_hab : a < b) (_hcd : c < d)
    (hf : AnalyticOnNhd ℂ f (Set.Icc a b ×ℂ Set.Icc c d))
    (hf_ne_const : ∃ z ∈ Set.Ioo a b ×ℂ Set.Ioo c d, f z ≠ w) :
    (f ⁻¹' {w} ∩ (Set.Ioo a b ×ℂ Set.Ioo c d)).Finite := by
  -- g := f - w is analytic on a neighborhood of the closed rectangle.
  have hg : AnalyticOnNhd ℂ (fun z => f z - w) (Set.Icc a b ×ℂ Set.Icc c d) :=
    fun z hz => (hf z hz).sub analyticAt_const
  -- The closed rectangle is convex (hence preconnected).
  have h_convex : Convex ℝ (Set.Icc a b ×ℂ Set.Icc c d) := by
    intro z₀ hz₀ z₁ hz₁ s t hs ht hst
    rw [Complex.mem_reProdIm] at hz₀ hz₁ ⊢
    refine ⟨?_, ?_⟩
    · have hre : (s • z₀ + t • z₁).re = s * z₀.re + t * z₁.re := by
        simp [Complex.add_re]
      rw [hre]
      exact convex_Icc a b hz₀.1 hz₁.1 hs ht hst
    · have him : (s • z₀ + t • z₁).im = s * z₀.im + t * z₁.im := by
        simp [Complex.add_im]
      rw [him]
      exact convex_Icc c d hz₀.2 hz₁.2 hs ht hst
  have h_preconn : IsPreconnected (Set.Icc a b ×ℂ Set.Icc c d) :=
    h_convex.isPreconnected
  -- Identity theorem: either g ≡ 0 on closed rect or zeros codiscrete.
  rcases hg.eqOn_zero_or_eventually_ne_zero_of_preconnected h_preconn with h_zero | h_codisc
  · -- g ≡ 0 contradicts hf_ne_const.
    exfalso
    obtain ⟨z, hz_Ioo, hfz⟩ := hf_ne_const
    have hz_Icc : z ∈ Set.Icc a b ×ℂ Set.Icc c d := by
      rw [Complex.mem_reProdIm] at hz_Ioo ⊢
      exact ⟨Set.Ioo_subset_Icc_self hz_Ioo.1, Set.Ioo_subset_Icc_self hz_Ioo.2⟩
    have h_zero_z : f z - w = 0 := h_zero hz_Icc
    exact hfz (sub_eq_zero.mp h_zero_z)
  -- Zeros are codiscrete: extract discreteness.
  have h_eq_set : {x | f x - w = 0} = f ⁻¹' {w} := by
    ext x; simp [sub_eq_zero]
  have h_codisc' :
      ({x | f x - w = 0})ᶜ ∈ codiscreteWithin (Set.Icc a b ×ℂ Set.Icc c d) := h_codisc
  have h_disc :
      IsDiscrete ({x | f x - w = 0} ∩ (Set.Icc a b ×ℂ Set.Icc c d)) :=
    isDiscrete_of_codiscreteWithin h_codisc'
  rw [h_eq_set] at h_disc
  -- f is continuous on the closed rectangle (from analyticity).
  have h_cont : ContinuousOn f (Set.Icc a b ×ℂ Set.Icc c d) :=
    fun z hz => (hf z hz).continuousAt.continuousWithinAt
  have h_rect_closed : IsClosed (Set.Icc a b ×ℂ Set.Icc c d) :=
    IsClosed.reProdIm isClosed_Icc isClosed_Icc
  have h_rect_compact : IsCompact (Set.Icc a b ×ℂ Set.Icc c d) :=
    IsCompact.reProdIm isCompact_Icc isCompact_Icc
  -- f⁻¹{w} ∩ closed rect is closed in ℂ.
  have h_inter_closed :
      IsClosed ((Set.Icc a b ×ℂ Set.Icc c d) ∩ f ⁻¹' {w}) :=
    h_cont.preimage_isClosed_of_isClosed h_rect_closed isClosed_singleton
  -- Hence compact (closed subset of compact rectangle).
  have h_inter_compact :
      IsCompact (f ⁻¹' {w} ∩ (Set.Icc a b ×ℂ Set.Icc c d)) := by
    rw [Set.inter_comm]
    exact h_rect_compact.of_isClosed_subset h_inter_closed Set.inter_subset_left
  -- Compact + discrete = finite.
  have h_finite : (f ⁻¹' {w} ∩ (Set.Icc a b ×ℂ Set.Icc c d)).Finite :=
    h_inter_compact.finite h_disc
  -- Restrict to the open subrectangle.
  refine h_finite.subset ?_
  intro x ⟨hxf, hx_Ioo⟩
  refine ⟨hxf, ?_⟩
  rw [Complex.mem_reProdIm] at hx_Ioo ⊢
  exact ⟨Set.Ioo_subset_Icc_self hx_Ioo.1, Set.Ioo_subset_Icc_self hx_Ioo.2⟩

end NoWanderingDomains
