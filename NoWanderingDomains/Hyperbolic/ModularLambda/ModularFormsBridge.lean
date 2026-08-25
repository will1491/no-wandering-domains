/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Modular forms bridge: from generator-level data to `Mathlib.CuspForm`

The Mathlib `CuspForm Γ(1) k` structure carries slash invariance under
every `γ ∈ SL(2, ℤ)`, manifold differentiability, and zero-at-cusp.
Our project's "weight-`k` cusp form" data — coming from work on the
modular function `λ` and Jacobi's identity — naturally surfaces only
the two generator-level slash relations (under `S` and `T`), the
standard `DifferentiableOn ℂ` holomorphy on the upper half-plane, and
an explicit exponential decay at `+i∞`. This file bridges the two
APIs.

The endpoint `dim S_4(SL(2, ℤ)) = 0` is captured here as
`weight4_levelOne_cuspForm_vanishes`, via the `Δ`-division route:
construct `F²/Δ` as a negative-weight modular form (which must vanish
by Mathlib's `ModularFormClass.levelOne_neg_weight_eq_zero`), then
deduce `F = 0` from `discriminant_ne_zero`.
-/

namespace NoWanderingDomains

open ModularForm UpperHalfPlane CongruenceSubgroup Complex Matrix.SpecialLinearGroup
open scoped MatrixGroups Manifold

/-- **Slash invariance from the generators `S, T`.** Since
`SpecialLinearGroup.SL2Z_generators` shows `Subgroup.closure {S, T} = ⊤`
in `SL(2, ℤ)`, any weight-`k` slash invariance under both `S` and `T`
propagates by `Subgroup.closure_induction` to every `γ ∈ SL(2, ℤ)`. -/
theorem slashInvariant_via_S_T_in_SL2Z {f : ℍ → ℂ} {k : ℤ}
    (h_S : f ∣[k] ModularGroup.S = f)
    (h_T : f ∣[k] ModularGroup.T = f)
    (γ : SL(2, ℤ)) :
    f ∣[k] γ = f := by
  have hmem : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | one => exact SlashAction.slash_one _ _
  | mem g hg =>
    rcases hg with h1 | h2
    · rw [h1]; exact h_S
    · rw [h2]; exact h_T
  | mul g h _ _ ig ih =>
    rw [SlashAction.slash_mul, ig, ih]
  | inv g _ ig =>
    have key : (f ∣[k] g) ∣[k] g⁻¹ = f ∣[k] g⁻¹ := by rw [ig]
    rwa [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one, eq_comm] at key

/-- **`T`-slash of a `T`-invariant function on `ℍ`.** If `g : ℂ → ℂ`
satisfies `g(τ + 1) = g(τ)` on the upper half-plane, then the
restriction `g_H σ = g σ` satisfies `g_H ∣[k] T = g_H` as a function
`ℍ → ℂ`. -/
theorem slash_T_eq_of_T_invariant {g : ℂ → ℂ} {k : ℤ}
    (h_T : ∀ τ : ℂ, 0 < τ.im → g (τ + 1) = g τ) :
    (fun σ : ℍ => g (↑σ : ℂ)) ∣[k] ModularGroup.T
      = (fun σ : ℍ => g (↑σ : ℂ)) := by
  funext σ
  rw [ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_smul,
      UpperHalfPlane.coe_vadd]
  -- Goal: g (↑(1 : ℝ) + ↑σ) * denom T σ ^ (-k) = g ↑σ.
  -- denom T σ = 1, so the `(denom T σ) ^ (-k)` factor is 1.
  have h_denom : denom ModularGroup.T σ = 1 := by
    have h0 : (ModularGroup.T : GL (Fin 2) ℝ) 1 0 = ((0 : ℤ) : ℝ) := by rfl
    have h1 : (ModularGroup.T : GL (Fin 2) ℝ) 1 1 = ((1 : ℤ) : ℝ) := by rfl
    rw [denom, h0, h1]
    push_cast
    ring
  rw [h_denom, one_zpow, mul_one]
  -- Goal: g (↑(1 : ℝ) + ↑σ) = g ↑σ.  Cast ↑(1 : ℝ) → 1, then apply h_T.
  rw [show ((1 : ℝ) : ℂ) + (↑σ : ℂ) = (↑σ : ℂ) + 1 from by push_cast; ring]
  exact h_T _ σ.2

/-- **`S`-slash of a `weight-k`-`S`-form.** If `g : ℂ → ℂ` satisfies
`g(-1/τ) = τ^k · g(τ)` on the upper half-plane, then the restriction
`g_H` satisfies `g_H ∣[k] S = g_H` as a function `ℍ → ℂ`. -/
theorem slash_S_eq_of_S_weight_k {g : ℂ → ℂ} {k : ℤ}
    (h_S : ∀ τ : ℂ, 0 < τ.im → g (-1 / τ) = τ ^ k * g τ) :
    (fun σ : ℍ => g (↑σ : ℂ)) ∣[k] ModularGroup.S
      = (fun σ : ℍ => g (↑σ : ℂ)) := by
  funext σ
  have h_σ_ne : (↑σ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero σ
  have h_σ_pos : 0 < (↑σ : ℂ).im := σ.2
  -- Rewrite slash + S-smul; then handle denom and the substituted argument.
  suffices h_main : g ((-(↑σ : ℂ))⁻¹) * denom ModularGroup.S σ ^ (-k) = g (↑σ : ℂ) by
    rw [ModularForm.SL_slash_apply, UpperHalfPlane.modular_S_smul]
    exact h_main
  have h_denom : denom ModularGroup.S σ = (↑σ : ℂ) := by
    have h0 : (ModularGroup.S : GL (Fin 2) ℝ) 1 0 = ((1 : ℤ) : ℝ) := by rfl
    have h1 : (ModularGroup.S : GL (Fin 2) ℝ) 1 1 = ((0 : ℤ) : ℝ) := by rfl
    rw [denom, h0, h1]
    push_cast
    ring
  have h_arg : (-(↑σ : ℂ))⁻¹ = -1 / (↑σ : ℂ) := by field_simp
  rw [h_arg, h_S _ h_σ_pos, h_denom]
  rw [show (↑σ : ℂ) ^ k * g (↑σ : ℂ) * (↑σ : ℂ) ^ (-k)
      = g (↑σ : ℂ) * ((↑σ : ℂ) ^ k * (↑σ : ℂ) ^ (-k)) from by ring]
  rw [← zpow_add₀ h_σ_ne, add_neg_cancel, zpow_zero, mul_one]

/-- **Manifold differentiability from `DifferentiableOn ℂ` on `ℍ`.**
The restriction of a function holomorphic on `{τ | 0 < τ.im}` is
manifold-differentiable on `ℍ`. -/
theorem mdiff_of_differentiableOn_upperHalfPlane {g : ℂ → ℂ}
    (h_holo : DifferentiableOn ℂ g { τ : ℂ | 0 < τ.im }) :
    MDiff (fun σ : ℍ => g (↑σ : ℂ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine h_holo.congr ?_
  intro z hz
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- **Cusp vanishing from exponential decay.** A function on `ℍ` whose
underlying values decay like `exp(-π · τ.im)` at `+i∞` is zero at
`atImInfty`. -/
theorem isZeroAtImInfty_of_exp_decay {g : ℂ → ℂ}
    (h_cusp : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℂ, 1 ≤ τ.im →
        ‖g τ‖ ≤ C * Real.exp (-Real.pi * τ.im)) :
    IsZeroAtImInfty (fun σ : ℍ => g (↑σ : ℂ)) := by
  obtain ⟨C, hC_pos, h_bound⟩ := h_cusp
  -- `IsZeroAtImInfty f = Filter.Tendsto f atImInfty (𝓝 0)`.
  -- For `σ.im ≥ 1`, `‖g ↑σ‖ ≤ C · exp(-π · σ.im) → 0` as `σ.im → ∞`.
  rw [show IsZeroAtImInfty (fun σ : ℍ => g (↑σ : ℂ))
        ↔ Filter.Tendsto (fun σ : ℍ => g (↑σ : ℂ)) atImInfty (nhds 0) from Iff.rfl]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  -- Show `‖g ↑σ‖ → 0` as `σ.im → ∞`, by squeezing between 0 and `C * exp(-π · σ.im)`.
  have h_bound_ev : ∀ᶠ σ : ℍ in atImInfty,
      ‖g (↑σ : ℂ)‖ ≤ C * Real.exp (-Real.pi * σ.im) := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{σ : ℍ | 1 ≤ σ.im}, ?_, fun σ hσ => h_bound (↑σ : ℂ) hσ⟩
    rw [atImInfty_mem]
    exact ⟨1, fun _ h => h⟩
  have h_rhs_tend : Filter.Tendsto (fun σ : ℍ => C * Real.exp (-Real.pi * σ.im))
      atImInfty (nhds 0) := by
    have h_tend_im : Filter.Tendsto (fun σ : ℍ => σ.im) atImInfty Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro A
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨{σ : ℍ | A ≤ σ.im}, ?_, fun _ hσ => hσ⟩
      rw [atImInfty_mem]
      exact ⟨A, fun _ hσ => hσ⟩
    have h_neg_pi : Filter.Tendsto (fun σ : ℍ => -Real.pi * σ.im)
        atImInfty Filter.atBot := by
      simpa using h_tend_im.const_mul_atTop_of_neg (show -Real.pi < 0 by
        simpa using Real.pi_pos)
    have h_exp : Filter.Tendsto (fun σ : ℍ => Real.exp (-Real.pi * σ.im))
        atImInfty (nhds 0) :=
      Real.tendsto_exp_atBot.comp h_neg_pi
    simpa using h_exp.const_mul C
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    h_bound_ev h_rhs_tend

/-! ### Bundling `Δ` as a Mathlib `CuspForm`

Mathlib provides `discriminant : ℍ → ℂ` along with `discriminant_T_invariant`,
`discriminant_S_invariant`, `discriminant_ne_zero`, and the q-product expansion
`discriminant_eq_q_prod`, but does not bundle the discriminant as a
`CuspForm Γ(1) 12`. We do so here. The three components are:
- Slash invariance for every `γ ∈ SL(2, ℤ)`, via the generator-level
  invariances and `slashInvariant_via_S_T_in_SL2Z`.
- Manifold holomorphy `MDiff discriminant`, via `Δ = η²⁴` and Mathlib's
  `differentiableAt_eta_of_mem_upperHalfPlaneSet`.
- Vanishing at every cusp, reduced to `IsZeroAtImInfty discriminant` via
  the `IsArithmetic` cusp-iff-SL2Z lemma + slash invariance, with
  the `IsZeroAtImInfty discriminant` step following from the leading
  `q¹` factor in the q-expansion `Δ = q · ∏(1 − qⁿ)²⁴`. -/

/-- The slash-action equation for `discriminant` under every `γ ∈ SL(2, ℤ)`,
extending the two-generator invariance via `SL2Z_generators`. -/
theorem delta_slash_action_eq (γ : SL(2, ℤ)) :
    discriminant ∣[(12 : ℤ)] γ = discriminant :=
  slashInvariant_via_S_T_in_SL2Z discriminant_S_invariant discriminant_T_invariant γ

/-- Manifold holomorphy of `discriminant : ℍ → ℂ`. Follows from
`Δ = η²⁴` and the Mathlib `differentiableAt_eta_of_mem_upperHalfPlaneSet`. -/
theorem delta_mdiff : MDiff (discriminant : ℍ → ℂ) := by
  have h_eta : MDiff (fun τ : ℍ => η (↑τ : ℂ)) := fun τ =>
    (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
      (z := (↑τ : ℂ)) τ.2).mdifferentiableAt.comp τ (UpperHalfPlane.mdifferentiable_coe τ)
  exact fun τ => (h_eta τ).pow 24

/-- **Boundedness of the eta-related product `∏(1 − qⁿ)` near `+i∞`.**
For `τ.im ≥ 1`, the infinite product `∏' n, (1 − eta_q n τ)` is
uniformly bounded by `M = exp(1)`. The proof uses
`Finset.norm_prod_one_add_sub_one_le` for the partial product bound
`‖∏(1 + fᵢ) − 1‖ ≤ exp(∑‖fᵢ‖) − 1` (applied with `fᵢ = -eta_q i τ`),
passed to the infinite limit via the `HasProd` topology and
`le_of_tendsto`. The geometric sum bound
`∑' n, exp(−2π(n+1)·τ.im) ≤ exp(−2π)/(1 − exp(−2π)) ≤ 1` keeps the
constant bounded for all `τ.im ≥ 1`. -/
theorem tprod_norm_one_sub_eta_q_le :
    ∃ M : ℝ, 0 < M ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖∏' n : ℕ, (1 - eta_q n τ)‖ ≤ M := by
  refine ⟨Real.exp 1, Real.exp_pos 1, ?_⟩
  intro τ hτ_im
  have hτ_pos : 0 < (↑τ : ℂ).im := lt_of_lt_of_le zero_lt_one hτ_im
  -- Step 1: explicit norm of `eta_q n τ`.
  have h_norm_eta_q : ∀ n : ℕ,
      ‖eta_q n (↑τ : ℂ)‖ = Real.exp (-2 * Real.pi * (n + 1) * (↑τ : ℂ).im) := by
    intro n
    rw [eta_q_eq_pow, norm_pow, Complex.norm_exp]
    have h_re : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (↑τ : ℂ)).re
        = -2 * Real.pi * (↑τ : ℂ).im := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [h_re]
    rw [show -2 * Real.pi * ((n : ℝ) + 1) * (↑τ : ℂ).im
        = ((n + 1 : ℕ) : ℝ) * (-2 * Real.pi * (↑τ : ℂ).im) from by push_cast; ring]
    rw [Real.exp_nat_mul]
  -- Step 2: per-term bound `‖eta_q n τ‖ ≤ exp(-2π(n+1))` for `τ.im ≥ 1`.
  have h_pi_pos := Real.pi_pos
  have h_eta_q_bound : ∀ n : ℕ,
      ‖eta_q n (↑τ : ℂ)‖ ≤ Real.exp (-2 * Real.pi * (n + 1)) := by
    intro n
    rw [h_norm_eta_q]
    apply Real.exp_le_exp.mpr
    have h_coeff_nonpos : -2 * Real.pi * ((n : ℝ) + 1) ≤ 0 := by
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      nlinarith
    -- `-2π(n+1) · τ.im ≤ -2π(n+1) · 1 = -2π(n+1)` since coeff ≤ 0 and τ.im ≥ 1.
    have h_mul : -2 * Real.pi * ((n : ℝ) + 1) * (↑τ : ℂ).im
        ≤ -2 * Real.pi * ((n : ℝ) + 1) * 1 :=
      mul_le_mul_of_nonpos_left hτ_im h_coeff_nonpos
    linarith
  -- Step 3: summable + bound on the sum.
  have h_summ : Summable fun n : ℕ => ‖-eta_q n (↑τ : ℂ)‖ := by
    simpa using summable_eta_q τ
  have h_summ' : Summable fun n : ℕ => ‖eta_q n (↑τ : ℂ)‖ := by
    simpa using h_summ
  -- The reference geometric sum: `r := exp(-2π)`, `Σ_n r^(n+1) = r / (1-r)`.
  set r : ℝ := Real.exp (-2 * Real.pi) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have h_geom_summable : Summable fun n : ℕ => r ^ (n + 1) := by
    exact (summable_geometric_of_lt_one hr_pos.le hr_lt_one).mul_left r |>.congr
      (fun n => by simp [pow_succ, mul_comm])
  have h_per_term_le : ∀ n : ℕ, ‖eta_q n (↑τ : ℂ)‖ ≤ r ^ (n + 1) := by
    intro n
    refine (h_eta_q_bound n).trans ?_
    rw [hr_def, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast; ring_nf; rfl
  -- `∑' n, ‖eta_q n τ‖ ≤ ∑' n, r^(n+1) = r / (1 - r)`.
  have h_tsum_le : ∑' n : ℕ, ‖eta_q n (↑τ : ℂ)‖ ≤ r / (1 - r) := by
    have h_sum_geom : ∑' n : ℕ, r ^ (n + 1) = r / (1 - r) := by
      rw [show (fun n : ℕ => r ^ (n + 1)) = (fun n => r * r ^ n) from by
        funext n; rw [pow_succ, mul_comm]]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr_pos.le hr_lt_one]
      ring
    refine h_sum_geom ▸ ?_
    exact h_summ'.tsum_le_tsum h_per_term_le h_geom_summable
  -- `r / (1 - r) ≤ 1` since `r ≤ exp(-2π) < 1/2`.
  have h_bound_S : r / (1 - r) ≤ 1 := by
    have h_one_sub : 0 < 1 - r := by linarith
    rw [div_le_one h_one_sub]
    -- need r ≤ 1 - r, i.e., 2r ≤ 1, i.e., r ≤ 1/2.
    have h_r_le_half : r ≤ 1 / 2 := by
      rw [hr_def, show (-2 * Real.pi : ℝ) = -(2 * Real.pi) from by ring, Real.exp_neg,
          inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/2),
          show (1/2 : ℝ)⁻¹ = 2 from by norm_num]
      have h1 : (1 : ℝ) + 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h2 : Real.exp 1 < Real.exp (2 * Real.pi) :=
        Real.exp_lt_exp.mpr (by nlinarith [Real.pi_gt_three])
      linarith
    linarith
  -- Step 4: bound the partial product norm. Define f n := -eta_q n τ.
  -- Then `1 + f n = 1 - eta_q n τ` and `‖f n‖ = ‖eta_q n τ‖`.
  -- By `Finset.norm_prod_one_add_sub_one_le`:
  --   `‖∏ in t, (1 + f n) - 1‖ ≤ exp(∑ in t, ‖f n‖) - 1`.
  -- Hence `‖∏ in t, (1 + f n)‖ ≤ exp(∑ in t, ‖f n‖) ≤ exp(∑' ‖f n‖) ≤ exp(1)`.
  have h_partial_bound : ∀ t : Finset ℕ,
      ‖∏ n ∈ t, ((1 : ℂ) - eta_q n (↑τ : ℂ))‖ ≤ Real.exp 1 := by
    intro t
    have h_sum_t_le : ∑ n ∈ t, ‖-eta_q n (↑τ : ℂ)‖ ≤ 1 := by
      have h_simp_term : ∀ n : ℕ, ‖-eta_q n (↑τ : ℂ)‖ = ‖eta_q n (↑τ : ℂ)‖ :=
        fun n => norm_neg _
      have h_sum_le_tsum : ∑ n ∈ t, ‖eta_q n (↑τ : ℂ)‖
          ≤ ∑' n : ℕ, ‖eta_q n (↑τ : ℂ)‖ :=
        h_summ'.sum_le_tsum t (fun _ _ => norm_nonneg _)
      have h_sum_eq : ∑ n ∈ t, ‖-eta_q n (↑τ : ℂ)‖ = ∑ n ∈ t, ‖eta_q n (↑τ : ℂ)‖ :=
        Finset.sum_congr rfl (fun n _ => h_simp_term n)
      rw [h_sum_eq]
      linarith [h_sum_le_tsum, h_tsum_le, h_bound_S]
    have h_prod_eq : ∀ t : Finset ℕ,
        ∏ n ∈ t, ((1 : ℂ) - eta_q n (↑τ : ℂ))
          = ∏ n ∈ t, ((1 : ℂ) + (-eta_q n (↑τ : ℂ))) := by
      intro t; refine Finset.prod_congr rfl ?_; intros; ring
    rw [h_prod_eq]
    have h_finset_bound :
        ‖(∏ n ∈ t, ((1 : ℂ) + (-eta_q n (↑τ : ℂ)))) - 1‖
          ≤ Real.exp (∑ n ∈ t, ‖-eta_q n (↑τ : ℂ)‖) - 1 :=
      Finset.norm_prod_one_add_sub_one_le t (fun n => -eta_q n (↑τ : ℂ))
    have h_exp_sum_le : Real.exp (∑ n ∈ t, ‖-eta_q n (↑τ : ℂ)‖) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr h_sum_t_le
    have h_prod_le_exp :
        ‖∏ n ∈ t, ((1 : ℂ) + (-eta_q n (↑τ : ℂ)))‖
          ≤ Real.exp (∑ n ∈ t, ‖-eta_q n (↑τ : ℂ)‖) := by
      have h_tri := norm_le_norm_sub_add (∏ n ∈ t, ((1 : ℂ) + (-eta_q n (↑τ : ℂ)))) 1
      rw [norm_one] at h_tri
      linarith
    linarith
  -- Step 5: pass to the infinite product limit.
  have h_mul : Multipliable fun n : ℕ => (1 : ℂ) + (-eta_q n (↑τ : ℂ)) :=
    multipliable_one_add_of_summable h_summ
  have h_mul' : Multipliable fun n : ℕ => (1 : ℂ) - eta_q n (↑τ : ℂ) := by
    have h_eq : (fun n : ℕ => (1 : ℂ) - eta_q n (↑τ : ℂ))
        = fun n : ℕ => (1 : ℂ) + (-eta_q n (↑τ : ℂ)) := by funext n; ring
    rw [h_eq]; exact h_mul
  -- `Multipliable.tendsto_prod_tprod_nat` gives convergence of `∏ i ∈ range n` to `∏'`.
  have h_tendsto :
      Filter.Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, ((1 : ℂ) - eta_q i (↑τ : ℂ)))
        Filter.atTop (nhds (∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ)))) :=
    h_mul'.tendsto_prod_tprod_nat
  have h_tendsto_norm :
      Filter.Tendsto (fun n : ℕ => ‖∏ i ∈ Finset.range n, ((1 : ℂ) - eta_q i (↑τ : ℂ))‖)
        Filter.atTop (nhds (‖∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ))‖)) :=
    h_tendsto.norm
  have h_ev : ∀ᶠ n : ℕ in Filter.atTop,
      ‖∏ i ∈ Finset.range n, ((1 : ℂ) - eta_q i (↑τ : ℂ))‖ ≤ Real.exp 1 :=
    Filter.Eventually.of_forall (fun n => h_partial_bound (Finset.range n))
  exact le_of_tendsto h_tendsto_norm h_ev

/-- **Exponential decay bound for `discriminant` near the cusp.** For
`τ.im ≥ 1`, the discriminant `discriminant τ = q · ∏(1 − qⁿ)²⁴` satisfies
`‖discriminant τ‖ ≤ C · exp(−2π · τ.im)` for `C = M²⁴` where `M` is the
product bound from `tprod_norm_one_sub_eta_q_le`. The factor
`exp(−2π · τ.im) = ‖𝕢 1 τ‖` comes from `Function.Periodic.norm_qParam`. -/
theorem delta_norm_le_exp_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖discriminant τ‖ ≤ C * Real.exp (-2 * Real.pi * τ.im) := by
  obtain ⟨M, hM_pos, hM_bound⟩ := tprod_norm_one_sub_eta_q_le
  refine ⟨M ^ 24, by positivity, ?_⟩
  intro τ hτ_im
  have h_summ : Summable fun n : ℕ => ‖-eta_q n (↑τ : ℂ)‖ := by
    simpa using summable_eta_q τ
  have h_mul : Multipliable fun n : ℕ => 1 + (-eta_q n (↑τ : ℂ)) :=
    multipliable_one_add_of_summable h_summ
  have h_mul' : Multipliable fun n : ℕ => 1 - eta_q n (↑τ : ℂ) := by
    have h_eq : (fun n : ℕ => (1 : ℂ) - eta_q n (↑τ : ℂ))
        = fun n : ℕ => 1 + (-eta_q n (↑τ : ℂ)) := by funext n; ring
    rw [h_eq]; exact h_mul
  -- `∏'((1 - eta_q n τ)^24) = (∏'(1 - eta_q n τ))^24`.
  have h_tprod_pow : ∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ)) ^ 24
      = (∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ))) ^ 24 :=
    h_mul'.tprod_pow 24
  rw [discriminant_eq_q_prod, h_tprod_pow, norm_mul, norm_pow]
  -- `‖𝕢 1 τ‖ = exp(-2π τ.im)`.
  rw [Function.Periodic.norm_qParam]
  have h_div_one : Real.exp (-2 * Real.pi * (↑τ : ℂ).im / 1)
      = Real.exp (-2 * Real.pi * τ.im) := by
    rw [div_one]; rfl
  rw [h_div_one]
  have h_prod_nn : 0 ≤ ‖∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ))‖ := norm_nonneg _
  have h_pow_le : ‖∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ))‖ ^ 24 ≤ M ^ 24 :=
    pow_le_pow_left₀ h_prod_nn (hM_bound τ hτ_im) 24
  have h_exp_pos' : 0 < Real.exp (-2 * Real.pi * τ.im) := Real.exp_pos _
  calc Real.exp (-2 * Real.pi * τ.im) * ‖∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ))‖ ^ 24
      ≤ Real.exp (-2 * Real.pi * τ.im) * M ^ 24 :=
        mul_le_mul_of_nonneg_left h_pow_le h_exp_pos'.le
    _ = M ^ 24 * Real.exp (-2 * Real.pi * τ.im) := by ring

/-- `discriminant : ℍ → ℂ` is zero at the cusp `+i∞`: this is the leading
`q¹` behaviour in the q-expansion `Δ = q · ∏(1 − qⁿ)²⁴`. The proof
combines the explicit exponential decay bound `delta_norm_le_exp_decay`
with a squeeze using `Real.tendsto_exp_atBot`. -/
theorem delta_isZeroAtImInfty : IsZeroAtImInfty (discriminant : ℍ → ℂ) := by
  obtain ⟨C, hC_pos, h_bound⟩ := delta_norm_le_exp_decay
  rw [show IsZeroAtImInfty (discriminant : ℍ → ℂ)
        ↔ Filter.Tendsto (discriminant : ℍ → ℂ) atImInfty (nhds 0) from Iff.rfl]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h_bound_ev : ∀ᶠ τ : ℍ in atImInfty,
      ‖discriminant τ‖ ≤ C * Real.exp (-2 * Real.pi * τ.im) := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{τ : ℍ | 1 ≤ τ.im}, ?_, fun τ hτ => h_bound τ hτ⟩
    rw [atImInfty_mem]
    exact ⟨1, fun _ hσ => hσ⟩
  have h_tend_im : Filter.Tendsto (fun τ : ℍ => τ.im) atImInfty Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro A
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{σ : ℍ | A ≤ σ.im}, ?_, fun _ hσ => hσ⟩
    rw [atImInfty_mem]
    exact ⟨A, fun _ hσ => hσ⟩
  have h_neg : Filter.Tendsto (fun τ : ℍ => -2 * Real.pi * τ.im)
      atImInfty Filter.atBot := by
    have h_neg_2pi : (-2 * Real.pi : ℝ) < 0 := by
      have := Real.pi_pos; linarith
    simpa using h_tend_im.const_mul_atTop_of_neg h_neg_2pi
  have h_exp : Filter.Tendsto (fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im))
      atImInfty (nhds 0) :=
    Real.tendsto_exp_atBot.comp h_neg
  have h_rhs_tendsto : Filter.Tendsto
      (fun τ : ℍ => C * Real.exp (-2 * Real.pi * τ.im)) atImInfty (nhds 0) := by
    simpa using h_exp.const_mul C
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    h_bound_ev h_rhs_tendsto

/-- **`Δ` as a Mathlib `CuspForm`.** The modular discriminant
`discriminant : ℍ → ℂ` packaged as a weight-12 cusp form for `Γ(1) = SL(2, ℤ)`. -/
noncomputable def delta_cuspForm : CuspForm Γ(1) 12 where
  toFun := discriminant
  slash_action_eq' := by
    intro γ_GL hγ_GL
    obtain ⟨g_SL, _hg_mem, h_eq⟩ := hγ_GL
    have h := delta_slash_action_eq g_SL
    rw [ModularForm.SL_slash] at h
    rw [← h_eq]; exact h
  holo' := delta_mdiff
  zero_at_cusps' := by
    intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _hγ
    rw [delta_slash_action_eq γ]
    exact delta_isZeroAtImInfty

/-! ### Δ-division route to `dim S₄(SL(2, ℤ)) = 0`

Given a weight-4 cusp form `F`, the quotient `F²/Δ` is a weight `−4`
modular form (since `F²` has weight 8, `Δ` has weight 12, and the
quotient is well-defined by `discriminant_ne_zero`). By Mathlib's
`ModularFormClass.levelOne_neg_weight_eq_zero`, every weight `< 0`
modular form for `SL(2,ℤ)` is zero, so `F²/Δ = 0`. Combined with
`discriminant_ne_zero`, this gives `F² = 0`, hence `F = 0`. -/

/-- **Slash invariance of `F²/Δ`** under `Γ(1)`. Given a weight-4 cusp
form `F`, the function `σ ↦ (F σ)² / discriminant σ` satisfies the weight `−4`
slash invariance for every `γ ∈ Γ(1)`. The proof combines the
weight-4 slash invariance of `F` (squared to get weight 8) with the
weight-12 slash invariance of `Δ` (from `delta_cuspForm`); the
quotient has weight `8 − 12 = −4`, and the slash equation
`(F²/Δ)(γ•τ) · (denom γ τ)^4 = (F²/Δ) τ` collapses to identity. -/
theorem cuspForm_sq_div_delta_slash_invariant (F : CuspForm Γ(1) 4)
    (γ_GL : GL (Fin 2) ℝ) (hγ : γ_GL ∈ (Γ(1) : Subgroup (GL (Fin 2) ℝ))) :
    (fun σ : ℍ => (F σ) ^ 2 / discriminant σ) ∣[(-4 : ℤ)] γ_GL
      = fun σ : ℍ => (F σ) ^ 2 / discriminant σ := by
  funext τ
  -- F (γ_GL • τ) = denom γ_GL τ ^ 4 * F τ (weight-4 slash invariance of F).
  have h_F : F (γ_GL • τ) = denom γ_GL τ ^ 4 * F τ :=
    SlashInvariantForm.slash_action_eqn'' F hγ τ
  -- delta_cuspForm (γ_GL • τ) = denom γ_GL τ ^ 12 * delta_cuspForm τ.
  have h_Δ : delta_cuspForm (γ_GL • τ) = denom γ_GL τ ^ 12 * delta_cuspForm τ :=
    SlashInvariantForm.slash_action_eqn'' delta_cuspForm hγ τ
  -- `delta_cuspForm τ = discriminant τ` by definition.
  have h_Δ' : discriminant (γ_GL • τ) = denom γ_GL τ ^ 12 * discriminant τ := h_Δ
  -- `γ_GL.det = 1` since `γ_GL ∈ Γ(1)-GL` (image of SL).
  have h_det_eq : Matrix.GeneralLinearGroup.det γ_GL = 1 :=
    Subgroup.HasDetOne.det_eq hγ
  have h_det : (γ_GL.det.val : ℝ) = 1 := by
    rw [show γ_GL.det = Matrix.GeneralLinearGroup.det γ_GL from rfl, h_det_eq]
    rfl
  -- `σ γ_GL z = z` (det > 0).
  have h_sigma_id : ∀ z : ℂ, σ γ_GL z = z := by
    intro z
    simp [σ, h_det]
  -- Nonzero denominators.
  have h_delta_ne : discriminant τ ≠ 0 := discriminant_ne_zero τ
  have h_denom_ne : (denom γ_GL τ : ℂ) ≠ 0 := denom_ne_zero γ_GL τ
  -- Compute the slash.
  rw [ModularForm.slash_apply, h_sigma_id]
  change ((F (γ_GL • τ)) ^ 2 / discriminant (γ_GL • τ)) * _ * _ = (F τ) ^ 2 / discriminant τ
  rw [h_F, h_Δ', h_det]
  -- Simplify `|↑1| = 1`, `1 ^ (-5) = 1`, then algebra.
  simp only [abs_one, Complex.ofReal_one, one_zpow, mul_one, neg_neg]
  field_simp

/-- **Manifold differentiability of `F²/Δ`.** The quotient of two
holomorphic functions with the denominator nonvanishing on `ℍ`.
Uses `UpperHalfPlane.mdifferentiable_iff` to reduce to standard
`DifferentiableOn`, then chains `DifferentiableOn.pow`,
`DifferentiableOn.div`, plus `discriminant_ne_zero` on the open set
`{z | 0 < z.im}`. -/
theorem cuspForm_sq_div_delta_mdiff (F : CuspForm Γ(1) 4) :
    MDiff (fun σ : ℍ => (F σ) ^ 2 / discriminant σ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  -- Goal: `DifferentiableOn ℂ ((fun σ => F σ^2 / discriminant σ) ∘ ↑ofComplex) {z | 0 < z.im}`.
  -- `F ∘ ofComplex` and `discriminant ∘ ofComplex` are DifferentiableOn from MDiff.
  have h_F_mdiff : MDiff (F : ℍ → ℂ) := ModularFormClass.holo F
  rw [UpperHalfPlane.mdifferentiable_iff] at h_F_mdiff
  have h_delta_mdiff : MDiff (discriminant : ℍ → ℂ) := delta_mdiff
  rw [UpperHalfPlane.mdifferentiable_iff] at h_delta_mdiff
  -- `discriminant ∘ ofComplex` is nonzero on `{z | 0 < z.im}`.
  have h_delta_ne :
      ∀ z ∈ {z : ℂ | 0 < z.im}, (discriminant ∘ (↑UpperHalfPlane.ofComplex)) z ≠ 0 := by
    intro z hz
    rw [Function.comp_apply]
    exact discriminant_ne_zero _
  -- Compose: (F ∘ ofComplex)^2 / (discriminant ∘ ofComplex).
  have h_pow : DifferentiableOn ℂ
      (fun z => ((F : ℍ → ℂ) ∘ (↑UpperHalfPlane.ofComplex)) z ^ 2)
      {z : ℂ | 0 < z.im} := h_F_mdiff.pow 2
  have h_div : DifferentiableOn ℂ
      (fun z => ((F : ℍ → ℂ) ∘ (↑UpperHalfPlane.ofComplex)) z ^ 2
              / (discriminant ∘ (↑UpperHalfPlane.ofComplex)) z)
      {z : ℂ | 0 < z.im} :=
    h_pow.div h_delta_mdiff h_delta_ne
  -- Massage the form to match the goal.
  exact h_div

/-- **Upper bound: a weight-`k` cusp form is `O(qParam 1)` near `+i∞`.**
For τ.im sufficiently large, `‖F τ‖ ≤ M · ‖qParam 1 τ‖`. Closure uses
Mathlib's `CuspFormClass.exp_decay_atImInfty`, which gives the BigO
bound `F =O[atImInfty] (fun τ => exp(−2π·τ.im/h))`, and the fact that
`‖qParam 1 τ‖ = exp(−2π·τ.im/1)` via `Function.Periodic.norm_qParam`. -/
theorem cuspForm_norm_le_qParam (F : CuspForm Γ(1) 4) :
    ∃ M A : ℝ, 0 < M ∧ ∀ τ : ℍ, A ≤ τ.im →
      ‖F τ‖ ≤ M * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ := by
  -- `1 ∈ Γ(1).strictPeriods` since `Γ(1) = ⊤` contains `T`.
  have h_period : (1 : ℝ) ∈ (Γ(1) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Gamma_one_coe_eq_SL]
    exact one_mem_strictPeriods_SL
  -- Mathlib gives `F =O[atImInfty] exp(-2π·τ.im/1)`.
  have h_decay : (F : ℍ → ℂ) =O[atImInfty]
      (fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im / 1)) :=
    CuspFormClass.exp_decay_atImInfty F zero_lt_one h_period
  -- Extract explicit `M` and eventual bound.
  obtain ⟨M, hM⟩ := h_decay.bound
  rw [Filter.eventually_iff_exists_mem] at hM
  obtain ⟨S, hS_mem, hS⟩ := hM
  rw [atImInfty_mem] at hS_mem
  obtain ⟨A, hA⟩ := hS_mem
  -- Norm of `Real.exp` is just `Real.exp` since it's positive.
  have h_norm_eq : ∀ τ : ℍ,
      ‖Real.exp (-2 * Real.pi * τ.im / 1)‖
        = ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ := by
    intro τ
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Function.Periodic.norm_qParam]
    rfl
  -- Choose `M' = max M 1` to ensure positivity.
  refine ⟨max M 1, A, by positivity, fun τ hτA => ?_⟩
  have h_in : τ ∈ S := hA τ hτA
  have h_F := hS τ h_in
  calc ‖F τ‖
      ≤ M * ‖Real.exp (-2 * Real.pi * τ.im / 1)‖ := h_F
    _ = M * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ := by rw [h_norm_eq]
    _ ≤ max M 1 * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- **Lower bound: `‖Δ τ‖ ≥ c · ‖qParam 1 τ‖` near `+i∞`.** `Δ` has
a simple zero at the cusp: `discriminant τ = qParam 1 τ · ∏'(1 − eta_q n τ)²⁴`,
and the product is bounded away from `0` for `τ.im ≥ 1` (since each
factor `1 − eta_q n τ` is close to `1`). The lower bound on the
product uses the reverse triangle inequality applied to
`Finset.norm_prod_one_add_sub_one_le` (which gives
`‖∏(1 + fᵢ) − 1‖ ≤ exp(∑‖fᵢ‖) − 1`), passed to the infinite-product
limit via `Multipliable.tendsto_prod_tprod_nat` and `ge_of_tendsto'`.

Numeric chain (for `τ.im ≥ 1`):
* `r := exp(−2π) ≤ 1/3` from `exp(2π) ≥ exp(2) ≥ 3 = 1 + 2`
  (using `Real.add_one_le_exp 2`).
* `∑' ≤ r/(1 − r) ≤ (1/3)/(2/3) = 1/2`.
* `exp(1/2) ≤ 7/4` from `(exp(1/2))² = exp(1) < 2.72 < 49/16`
  (using `Real.exp_one_lt_d9`).
* `‖∏ − 1‖ ≤ exp(∑) − 1 ≤ 3/4`, so `‖∏‖ ≥ 1 − 3/4 = 1/4`.
* `‖Δ τ‖ = ‖qParam 1 τ‖ · ‖∏‖²⁴ ≥ (1/4)²⁴ · ‖qParam 1 τ‖`. -/
theorem delta_norm_ge_qParam :
    ∃ c A : ℝ, 0 < c ∧ ∀ τ : ℍ, A ≤ τ.im →
      c * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ ≤ ‖discriminant τ‖ := by
  refine ⟨(1/4 : ℝ)^24, 1, by positivity, ?_⟩
  intro τ hτ_im
  have hτ_pos : 0 < (↑τ : ℂ).im := lt_of_lt_of_le zero_lt_one hτ_im
  -- Step 1: explicit norm of eta_q n τ.
  have h_norm_eta_q : ∀ n : ℕ,
      ‖eta_q n (↑τ : ℂ)‖ = Real.exp (-2 * Real.pi * (n + 1) * (↑τ : ℂ).im) := by
    intro n
    rw [eta_q_eq_pow, norm_pow, Complex.norm_exp]
    have h_re : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (↑τ : ℂ)).re
        = -2 * Real.pi * (↑τ : ℂ).im := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [h_re]
    rw [show -2 * Real.pi * ((n : ℝ) + 1) * (↑τ : ℂ).im
        = ((n + 1 : ℕ) : ℝ) * (-2 * Real.pi * (↑τ : ℂ).im) from by push_cast; ring]
    rw [Real.exp_nat_mul]
  have h_pi_pos := Real.pi_pos
  -- Step 2: per-term bound `‖eta_q n τ‖ ≤ exp(-2π(n+1))` for τ.im ≥ 1.
  have h_eta_q_bound : ∀ n : ℕ,
      ‖eta_q n (↑τ : ℂ)‖ ≤ Real.exp (-2 * Real.pi * (n + 1)) := by
    intro n
    rw [h_norm_eta_q]
    apply Real.exp_le_exp.mpr
    have h_coeff_nonpos : -2 * Real.pi * ((n : ℝ) + 1) ≤ 0 := by
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      nlinarith
    have h_mul : -2 * Real.pi * ((n : ℝ) + 1) * (↑τ : ℂ).im
        ≤ -2 * Real.pi * ((n : ℝ) + 1) * 1 :=
      mul_le_mul_of_nonpos_left hτ_im h_coeff_nonpos
    linarith
  -- Step 3: summability and bound on ∑'.
  have h_summ : Summable fun n : ℕ => ‖-eta_q n (↑τ : ℂ)‖ := by
    simpa using summable_eta_q τ
  have h_summ' : Summable fun n : ℕ => ‖eta_q n (↑τ : ℂ)‖ := by
    simpa using h_summ
  set r : ℝ := Real.exp (-2 * Real.pi) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_le_third : r ≤ 1/3 := by
    rw [hr_def, show (-2 * Real.pi : ℝ) = -(2 * Real.pi) from by ring, Real.exp_neg,
        inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/3),
        show (1/3 : ℝ)⁻¹ = 3 from by norm_num]
    -- Need 3 ≤ exp(2π).
    have h1 : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ); linarith
    have h2 : Real.exp 2 ≤ Real.exp (2 * Real.pi) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
    linarith
  have hr_lt_one : r < 1 := by linarith
  have h_geom_summable : Summable fun n : ℕ => r ^ (n + 1) := by
    exact (summable_geometric_of_lt_one hr_pos.le hr_lt_one).mul_left r |>.congr
      (fun n => by simp [pow_succ, mul_comm])
  have h_per_term_le : ∀ n : ℕ, ‖eta_q n (↑τ : ℂ)‖ ≤ r ^ (n + 1) := by
    intro n
    refine (h_eta_q_bound n).trans ?_
    rw [hr_def, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast; ring_nf; rfl
  have h_tsum_le : ∑' n : ℕ, ‖eta_q n (↑τ : ℂ)‖ ≤ r / (1 - r) := by
    have h_sum_geom : ∑' n : ℕ, r ^ (n + 1) = r / (1 - r) := by
      rw [show (fun n : ℕ => r ^ (n + 1)) = (fun n => r * r ^ n) from by
        funext n; rw [pow_succ, mul_comm]]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr_pos.le hr_lt_one]
      ring
    refine h_sum_geom ▸ ?_
    exact h_summ'.tsum_le_tsum h_per_term_le h_geom_summable
  have h_S_le_half : r / (1 - r) ≤ 1/2 := by
    have h_one_sub : 0 < 1 - r := by linarith
    rw [div_le_iff₀ h_one_sub]
    linarith
  -- Step 4: each partial product has ‖·‖ ≥ 1/4.
  have h_partial_ge : ∀ N : ℕ,
      (1/4 : ℝ) ≤ ‖∏ n ∈ Finset.range N, ((1 : ℂ) - eta_q n (↑τ : ℂ))‖ := by
    intro N
    have h_prod_eq :
        ∏ n ∈ Finset.range N, ((1 : ℂ) - eta_q n (↑τ : ℂ))
          = ∏ n ∈ Finset.range N, ((1 : ℂ) + (-eta_q n (↑τ : ℂ))) := by
      refine Finset.prod_congr rfl ?_; intros; ring
    rw [h_prod_eq]
    have h_finset_bound :
        ‖(∏ n ∈ Finset.range N, ((1 : ℂ) + (-eta_q n (↑τ : ℂ)))) - 1‖
          ≤ Real.exp (∑ n ∈ Finset.range N, ‖-eta_q n (↑τ : ℂ)‖) - 1 :=
      Finset.norm_prod_one_add_sub_one_le _ _
    have h_sum_t_le : ∑ n ∈ Finset.range N, ‖-eta_q n (↑τ : ℂ)‖ ≤ 1/2 := by
      have h_simp : ∀ n : ℕ, ‖-eta_q n (↑τ : ℂ)‖ = ‖eta_q n (↑τ : ℂ)‖ :=
        fun n => norm_neg _
      have h_sum_eq : ∑ n ∈ Finset.range N, ‖-eta_q n (↑τ : ℂ)‖
          = ∑ n ∈ Finset.range N, ‖eta_q n (↑τ : ℂ)‖ :=
        Finset.sum_congr rfl (fun n _ => h_simp n)
      have h_sum_le_tsum : ∑ n ∈ Finset.range N, ‖eta_q n (↑τ : ℂ)‖
          ≤ ∑' n : ℕ, ‖eta_q n (↑τ : ℂ)‖ :=
        h_summ'.sum_le_tsum _ (fun _ _ => norm_nonneg _)
      linarith [h_tsum_le, h_S_le_half]
    -- exp(1/2) ≤ 7/4 from exp(1) < 3 ≤ 49/16.
    have h_exp_one_lt : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h_exp_half_le : Real.exp (1/2) ≤ 7/4 := by
      have h_pos : (0 : ℝ) < Real.exp (1/2) := Real.exp_pos _
      have h_sq : Real.exp (1/2) ^ 2 = Real.exp 1 := by
        rw [show (Real.exp (1/2)) ^ 2 = Real.exp (1/2) * Real.exp (1/2) from sq (Real.exp (1/2)),
            ← Real.exp_add]
        norm_num
      nlinarith [h_pos, h_exp_one_lt, h_sq]
    have h_exp_sum_le : Real.exp (∑ n ∈ Finset.range N, ‖-eta_q n (↑τ : ℂ)‖)
        ≤ Real.exp (1/2) :=
      Real.exp_le_exp.mpr h_sum_t_le
    have h_prod_diff_le :
        ‖(∏ n ∈ Finset.range N, ((1 : ℂ) + (-eta_q n (↑τ : ℂ)))) - 1‖ ≤ 3/4 := by
      linarith
    -- Reverse triangle: ‖∏‖ ≥ 1 - ‖∏ - 1‖.
    have h_rev_tri :
        (1 : ℝ) - ‖(∏ n ∈ Finset.range N, ((1 : ℂ) + (-eta_q n (↑τ : ℂ)))) - 1‖
          ≤ ‖∏ n ∈ Finset.range N, ((1 : ℂ) + (-eta_q n (↑τ : ℂ)))‖ := by
      have h := norm_sub_norm_le ((1 : ℂ))
        (∏ n ∈ Finset.range N, ((1 : ℂ) + (-eta_q n (↑τ : ℂ))))
      rw [norm_one] at h
      have h_neg : ((1 : ℂ) - ∏ n ∈ Finset.range N, ((1 : ℂ) + (-eta_q n (↑τ : ℂ))))
          = -((∏ n ∈ Finset.range N, ((1 : ℂ) + (-eta_q n (↑τ : ℂ)))) - 1) := by ring
      rw [h_neg, norm_neg] at h
      linarith
    linarith
  -- Step 5: pass to ∏'.
  have h_mul : Multipliable fun n : ℕ => (1 : ℂ) + (-eta_q n (↑τ : ℂ)) :=
    multipliable_one_add_of_summable h_summ
  have h_mul' : Multipliable fun n : ℕ => (1 : ℂ) - eta_q n (↑τ : ℂ) := by
    have h_eq : (fun n : ℕ => (1 : ℂ) - eta_q n (↑τ : ℂ))
        = fun n : ℕ => (1 : ℂ) + (-eta_q n (↑τ : ℂ)) := by funext n; ring
    rw [h_eq]; exact h_mul
  have h_tendsto :
      Filter.Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, ((1 : ℂ) - eta_q i (↑τ : ℂ)))
        Filter.atTop (nhds (∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ)))) :=
    h_mul'.tendsto_prod_tprod_nat
  have h_tendsto_norm :
      Filter.Tendsto (fun n : ℕ => ‖∏ i ∈ Finset.range n, ((1 : ℂ) - eta_q i (↑τ : ℂ))‖)
        Filter.atTop (nhds (‖∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ))‖)) :=
    h_tendsto.norm
  have h_tprod_ge : (1/4 : ℝ) ≤ ‖∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ))‖ :=
    ge_of_tendsto' h_tendsto_norm h_partial_ge
  -- Step 6: combine with discriminant_eq_q_prod.
  have h_tprod_pow : ∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ)) ^ 24
      = (∏' n : ℕ, ((1 : ℂ) - eta_q n (↑τ : ℂ))) ^ 24 :=
    h_mul'.tprod_pow 24
  rw [discriminant_eq_q_prod, h_tprod_pow, norm_mul, norm_pow]
  -- Goal: (1/4)^24 * ‖qParam‖ ≤ ‖qParam‖ * ‖∏'‖^24.
  rw [show (1/4 : ℝ)^24 * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖
      = ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ * (1/4 : ℝ)^24 from by ring]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/4) h_tprod_ge 24

/-- **`F²/Δ` is bounded at `+i∞`.** Combines the upper bound
`cuspForm_norm_le_qParam` (gives `‖F‖ ≤ M·‖qParam‖`) with the lower
bound `delta_norm_ge_qParam` (gives `‖Δ‖ ≥ c·‖qParam‖`) to conclude
`‖F²/Δ‖ ≤ (M²/c) · ‖qParam‖`, which is bounded since
`‖qParam 1 τ‖ = exp(−2π·τ.im) ≤ 1` for `τ.im ≥ 0`. -/
theorem cuspForm_sq_div_delta_isBoundedAtImInfty (F : CuspForm Γ(1) 4) :
    IsBoundedAtImInfty (fun σ : ℍ => (F σ) ^ 2 / discriminant σ) := by
  obtain ⟨M_F, A_F, hM_F_pos, hM_F_bound⟩ := cuspForm_norm_le_qParam F
  obtain ⟨c_Δ, A_Δ, hc_Δ_pos, hc_Δ_bound⟩ := delta_norm_ge_qParam
  -- Unfold `IsBoundedAtImInfty` and provide the bound via `IsBigO.of_bound`.
  unfold IsBoundedAtImInfty Filter.BoundedAtFilter
  refine Asymptotics.IsBigO.of_bound (M_F ^ 2 / c_Δ) ?_
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨{τ : ℍ | max A_F A_Δ ≤ τ.im}, ?_, ?_⟩
  · rw [atImInfty_mem]
    exact ⟨max A_F A_Δ, fun _ h => h⟩
  · intro τ hτ
    have h_AF : A_F ≤ τ.im := le_trans (le_max_left _ _) hτ
    have h_AΔ : A_Δ ≤ τ.im := le_trans (le_max_right _ _) hτ
    have h_F := hM_F_bound τ h_AF
    have h_Δ := hc_Δ_bound τ h_AΔ
    have h_qParam_pos : 0 < ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ := by
      rw [Function.Periodic.norm_qParam]
      exact Real.exp_pos _
    have h_qParam_le_one : ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ ≤ 1 := by
      rw [Function.Periodic.norm_qParam, div_one]
      apply Real.exp_le_one_iff.mpr
      have h_pi_pos := Real.pi_pos
      have h_tau_pos : 0 < (↑τ : ℂ).im := τ.2
      nlinarith
    have h_delta_pos : 0 < ‖discriminant τ‖ := by
      have := hc_Δ_bound τ h_AΔ
      have h_pos : 0 < c_Δ * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ :=
        mul_pos hc_Δ_pos h_qParam_pos
      linarith
    -- Goal: ‖F²/Δ‖ ≤ (M_F²/c_Δ) · ‖1 τ‖, where `(1 : ℍ → ℂ) τ = (1 : ℂ)`.
    rw [Pi.one_apply, norm_one, mul_one, norm_div, norm_pow]
    -- Compute: ‖F‖² ≤ (M_F · ‖qParam‖)² = M_F² · ‖qParam‖².
    have h_F_nn : 0 ≤ ‖F τ‖ := norm_nonneg _
    have h_F_sq_bound : ‖F τ‖ ^ 2 ≤ M_F ^ 2 * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ ^ 2 := by
      have := pow_le_pow_left₀ h_F_nn h_F 2
      rw [mul_pow] at this
      exact this
    -- ‖F‖² / ‖Δ‖ ≤ M_F²·‖q‖² / (c_Δ · ‖q‖) = (M_F²/c_Δ) · ‖q‖ ≤ M_F²/c_Δ.
    have h_cq_pos : 0 < c_Δ * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ :=
      mul_pos hc_Δ_pos h_qParam_pos
    have h_step1 : ‖F τ‖ ^ 2 / ‖discriminant τ‖
        ≤ (M_F ^ 2 * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ ^ 2)
          / (c_Δ * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖) := by
      rw [div_le_div_iff₀ h_delta_pos h_cq_pos]
      calc ‖F τ‖ ^ 2 * (c_Δ * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖)
          ≤ (M_F ^ 2 * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ ^ 2)
              * (c_Δ * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖) :=
            mul_le_mul_of_nonneg_right h_F_sq_bound h_cq_pos.le
        _ ≤ (M_F ^ 2 * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ ^ 2) * ‖discriminant τ‖ :=
            mul_le_mul_of_nonneg_left h_Δ (by positivity)
    have h_step2 : (M_F ^ 2 * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ ^ 2)
        / (c_Δ * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖)
          = (M_F ^ 2 / c_Δ) * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ := by
      rw [show ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ ^ 2
            = ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖
              * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖ from by ring]
      field_simp
    rw [h_step2] at h_step1
    -- Final: (M_F²/c_Δ) · ‖q‖ ≤ M_F²/c_Δ · 1 = M_F²/c_Δ.
    have h_coeff_nn : 0 ≤ M_F ^ 2 / c_Δ := by positivity
    have h_final : (M_F ^ 2 / c_Δ) * ‖Function.Periodic.qParam 1 (↑τ : ℂ)‖
        ≤ M_F ^ 2 / c_Δ := by
      have := mul_le_mul_of_nonneg_left h_qParam_le_one h_coeff_nn
      linarith
    linarith

/-- **Boundedness of `F²/Δ` at every cusp.** Reduces to
`IsBoundedAtImInfty (F²/Δ)` via the slash invariance
`cuspForm_sq_div_delta_slash_invariant` and the SL(2, ℤ)-orbit
reduction `OnePoint.isBoundedAt_iff_forall_SL2Z` (using that
`Γ(1)` is arithmetic so all cusps are SL(2,ℤ)-equivalent to `+i∞`). -/
theorem cuspForm_sq_div_delta_bdd_at_cusps (F : CuspForm Γ(1) 4)
    {c : OnePoint ℝ} (hc : IsCusp c Γ(1)) :
    c.IsBoundedAt (fun σ : ℍ => (F σ) ^ 2 / discriminant σ) (-4) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
  intro γ _hγ
  -- By slash invariance, `(F²/Δ) ∣[(-4)] γ = F²/Δ`.
  have hγ_GL : (γ : GL (Fin 2) ℝ) ∈ (Γ(1) : Subgroup (GL (Fin 2) ℝ)) := by
    refine ⟨γ, ?_, rfl⟩
    rw [CongruenceSubgroup.Gamma_one_top]
    exact Subgroup.mem_top γ
  have h_slash : (fun σ : ℍ => (F σ) ^ 2 / discriminant σ) ∣[(-4 : ℤ)] γ
        = fun σ : ℍ => (F σ) ^ 2 / discriminant σ := by
    have h := cuspForm_sq_div_delta_slash_invariant F (γ : GL (Fin 2) ℝ) hγ_GL
    rwa [← ModularForm.SL_slash] at h
  rw [h_slash]
  exact cuspForm_sq_div_delta_isBoundedAtImInfty F

/-- **Weight-4 cusp form vanishing for `SL(2, ℤ)`.** The space
`S_4(SL(2, ℤ))` of weight-4 cusp forms for the full modular group is
zero-dimensional. The proof constructs `G := F²/Δ` as a weight `−4`
modular form (using the three slash/holomorphy/cusp-bound helpers
above), applies Mathlib's `ModularFormClass.levelOne_neg_weight_eq_zero`
to get `G ≡ 0`, then deduces `F = 0` from `discriminant_ne_zero`. -/
theorem weight4_levelOne_cuspForm_vanishes
    (F : CuspForm Γ(1) 4) (τ : ℍ) :
    F τ = 0 := by
  -- Construct G := F²/Δ as a weight-(-4) modular form.
  let G : ModularForm Γ(1) (-4) :=
  { toFun := fun σ : ℍ => (F σ) ^ 2 / discriminant σ
    slash_action_eq' := cuspForm_sq_div_delta_slash_invariant F
    holo' := cuspForm_sq_div_delta_mdiff F
    bdd_at_cusps' := cuspForm_sq_div_delta_bdd_at_cusps F }
  -- Apply `levelOne_neg_weight_eq_zero` to get `G ≡ 0`.
  -- (Mathlib 4.33 states the lemma for `𝒮ℒ`; transport along `Γ(1)-GL = 𝒮ℒ`.)
  have h_all_zero : ∀ G' : ModularForm (Γ(1) : Subgroup (GL (Fin 2) ℝ)) (-4), ⇑G' = 0 := by
    rw [Gamma_one_coe_eq_SL]
    intro G'
    exact ModularFormClass.levelOne_neg_weight_eq_zero (show (-4 : ℤ) < 0 by norm_num) G'
  have hG_zero : ⇑G = 0 := h_all_zero G
  -- Conclude `F τ = 0`.
  have h_val : G τ = 0 := congrFun hG_zero τ
  have h_sq_zero : (F τ) ^ 2 / discriminant τ = 0 := h_val
  have h_delta_ne : discriminant τ ≠ 0 := discriminant_ne_zero τ
  rw [div_eq_zero_iff] at h_sq_zero
  rcases h_sq_zero with h_pow | h_delta_zero
  · exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h_pow
  · exact absurd h_delta_zero h_delta_ne

end NoWanderingDomains
