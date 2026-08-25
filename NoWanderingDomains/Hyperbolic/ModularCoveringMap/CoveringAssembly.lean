/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.ModularCoveringMap.WindingInjectivity

/-! # Pillars 3 and 4 and the covering map

Pillars 3 and 4 and the covering map. `λ′ ≠ 0` on `ℍ` by the sign of `Im λ` (the
multiplicity argument for `Im λ = 0`, transport to `F` for `Im λ > 0`, conjugation for
`Im λ < 0`), and `λ` separates `Γ(2)`-orbits. The covering-map assembly: junk values
off `ℍ`, the faithful quotient `Γ(2)/{±I}` with its free, properly discontinuous
descended action, the corestricted quotient map `λ : ℍ → {w // w ≠ 0 ∧ w ≠ 1}`, and the
main theorems `modularLambdaH_isCoveringMapOn` and `modularLambda_isCoveringMapOn`.
-/

namespace NoWanderingDomains
open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-! ## Pillar 3 sub-lemmas: `λ′ ≠ 0` by the sign of `Im λ` -/

/-- **Pillar-3 boundary `= 0` branch.** For `τ ∈ ℍ` with
`Im(λ τ) = 0`, `deriv λ τ ≠ 0`. Suppose `deriv λ τ = 0` for
contradiction. By `analyticAt_localOpen_with_multiplicity`, for
each `k` there are distinct `z₁ᵏ, z₂ᵏ ∈ B(τ, 1/(k+1)) ⊂ ℍ` with
`λ(z₁ᵏ) = λ(z₂ᵏ)` and `Im λ(z₁ᵏ) > 0` (the witness `λ τ + (r/2)·i`
inside the helper neighbourhood `V`). By Pillar-4 upper branch,
`z₂ᵏ = γₖ • z₁ᵏ` for some `γₖ ∈ Γ(2)`. Proper discontinuity
restricts `γₖ` to a finite set on a compact ball around `τ`;
extract a constant subsequence `γₖ = γ`. Passing to the limit,
`γ • τ = τ`, so by Pillar 1 (`gamma_two_fixed_point_implies_pm_one`)
`γ ∈ {I, -I}`. But `±I` acts trivially on `ℍ`, so along the
subsequence `z₁ᵏ = z₂ᵏ`, contradicting distinctness. -/
theorem modularLambdaH_deriv_ne_zero_when_im_lambda_zero
    {τ : ℂ} (hτ : 0 < τ.im)
    (hlam_im : (modularLambdaH τ).im = 0) :
    deriv modularLambdaH τ ≠ 0 := by
  intro h_dz
  -- Setup: H is the open upper half-plane in ℂ.
  set H : Set ℂ := {z | 0 < z.im} with hH_def
  have hH_open : IsOpen H := by
    have : H = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp [hH_def]
    rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
  have h_lam_an : AnalyticOnNhd ℂ modularLambdaH H :=
    modularLambdaH_differentiableOn.analyticOnNhd hH_open
  have h_lam_at : AnalyticAt ℂ modularLambdaH τ := h_lam_an τ hτ
  have h_H_preconn : IsPreconnected H := by
    apply Convex.isPreconnected
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
  -- λ is not eventually constant at τ (identity theorem + global non-constancy).
  have h_lam_not_const : ¬ ∀ᶠ z in nhds τ, modularLambdaH z = modularLambdaH τ := by
    intro h_eq
    have h_const_an : AnalyticOnNhd ℂ (fun _ : ℂ => modularLambdaH τ) H :=
      fun _ _ => analyticAt_const
    have h_eqOn : Set.EqOn modularLambdaH (fun _ => modularLambdaH τ) H :=
      h_lam_an.eqOn_of_preconnected_of_eventuallyEq h_const_an h_H_preconn hτ h_eq
    have h_1i_in : (1 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
      refine ⟨?_, ?_⟩
      · intro h; have := congrArg Complex.im h; simp at this
      · intro h; have := congrArg Complex.im h; simp at this
    have h_2i_in : (2 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
      refine ⟨?_, ?_⟩
      · intro h; have := congrArg Complex.im h; simp at this
      · intro h; have := congrArg Complex.re h; simp at this
    have h_lam_img : modularLambdaH '' H = { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := modularLambdaH_image
    have h_1i_img : (1 + Complex.I : ℂ) ∈ modularLambdaH '' H := h_lam_img ▸ h_1i_in
    have h_2i_img : (2 + Complex.I : ℂ) ∈ modularLambdaH '' H := h_lam_img ▸ h_2i_in
    obtain ⟨τ_a, hτ_a_H, hτ_a_eq⟩ := h_1i_img
    obtain ⟨τ_b, hτ_b_H, hτ_b_eq⟩ := h_2i_img
    have h_a := h_eqOn hτ_a_H
    have h_b := h_eqOn hτ_b_H
    rw [hτ_a_eq] at h_a
    rw [hτ_b_eq] at h_b
    have h_eq_12 : (1 + Complex.I : ℂ) = (2 + Complex.I : ℂ) := h_a.trans h_b.symm
    have h_re := congrArg Complex.re h_eq_12
    simp at h_re
  -- Setup τ_h and proper-discontinuity instance.
  have := gamma_two_properlyDiscontinuousSMul
  set τ_h : UpperHalfPlane := ⟨τ, hτ⟩ with hτ_h_def
  -- For each k, helper produces distinct preimages with Im λ > 0.
  have h_seq : ∀ k : ℕ, ∃ z₁ z₂ : ℂ, 0 < z₁.im ∧ 0 < z₂.im ∧
      ‖z₁ - τ‖ < 1/(k+1) ∧ ‖z₂ - τ‖ < 1/(k+1) ∧
      z₁ ≠ z₂ ∧ modularLambdaH z₁ = modularLambdaH z₂ ∧
      0 < (modularLambdaH z₁).im := by
    intro k
    set ε : ℝ := 1/(k+1) with hε_def
    have hε_pos : 0 < ε := by positivity
    set U : Set ℂ := Metric.ball τ ε ∩ H with hU_def
    have hU_nhds : U ∈ nhds τ := Filter.inter_mem
      (Metric.ball_mem_nhds _ hε_pos) (hH_open.mem_nhds hτ)
    obtain ⟨V, hV_nhds, hV_prop⟩ :=
      analyticAt_localOpen_with_multiplicity h_lam_at h_lam_not_const h_dz U hU_nhds
    rcases Metric.mem_nhds_iff.mp hV_nhds with ⟨r, hr_pos, hr_sub⟩
    set w : ℂ := modularLambdaH τ + (r/2 : ℝ) * Complex.I with hw_def
    have h_dist_w : dist w (modularLambdaH τ) = r/2 := by
      rw [hw_def, dist_self_add_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr_pos)]
    have hw_in_V : w ∈ V := by
      apply hr_sub
      rw [Metric.mem_ball, h_dist_w]; linarith
    have hw_ne : w ≠ modularLambdaH τ := by
      intro h_eq
      have h_im_eq : w.im = (modularLambdaH τ).im := congrArg Complex.im h_eq
      rw [hw_def, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, add_zero, hlam_im] at h_im_eq
      linarith
    obtain ⟨z₁, hz₁_U, z₂, hz₂_U, hne, h_lam_z₁, h_lam_z₂⟩ := hV_prop w hw_in_V hw_ne
    obtain ⟨hz₁_ball, hz₁_im⟩ := hz₁_U
    obtain ⟨hz₂_ball, hz₂_im⟩ := hz₂_U
    refine ⟨z₁, z₂, hz₁_im, hz₂_im, ?_, ?_, hne, ?_, ?_⟩
    · rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz₁_ball
    · rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz₂_ball
    · rw [h_lam_z₁, h_lam_z₂]
    · rw [h_lam_z₁, hw_def]
      show 0 < (modularLambdaH τ + ↑(r/2) * Complex.I).im
      rw [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, add_zero, hlam_im, zero_add]
      exact half_pos hr_pos
  choose z₁ z₂ hz₁_im hz₂_im hd₁ hd₂ hne h_lam_eq h_im_pos using h_seq
  -- Sequences in ℍ.
  set z₁_h : ℕ → UpperHalfPlane := fun n => ⟨z₁ n, hz₁_im n⟩ with hz₁_h_def
  set z₂_h : ℕ → UpperHalfPlane := fun n => ⟨z₂ n, hz₂_im n⟩ with hz₂_h_def
  -- Pillar-4 upper for each n.
  have h_orbit : ∀ n, ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • z₁_h n = z₂_h n := by
    intro n
    exact gamma2_lambda_eq_implies_orbit_when_im_lambda_pos (h_im_pos n) (h_lam_eq n)
  choose γ hγ_in hγ_eq using h_orbit
  -- Tendsto z₁, z₂ → τ in ℂ via norm bounds.
  have h_z₁_tend_c : Filter.Tendsto z₁ Filter.atTop (nhds τ) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    have h_nb : ‖z₁ n - τ‖ < 1/(n+1) := hd₁ n
    have h_le : (1 : ℝ)/(n+1) ≤ 1/(N+1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast Nat.succ_le_succ hn
    rw [dist_eq_norm]
    exact lt_of_lt_of_le h_nb (le_of_lt (lt_of_le_of_lt h_le hN))
  have h_z₂_tend_c : Filter.Tendsto z₂ Filter.atTop (nhds τ) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    have h_nb : ‖z₂ n - τ‖ < 1/(n+1) := hd₂ n
    have h_le : (1 : ℝ)/(n+1) ≤ 1/(N+1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast Nat.succ_le_succ hn
    rw [dist_eq_norm]
    exact lt_of_lt_of_le h_nb (le_of_lt (lt_of_le_of_lt h_le hN))
  -- Bridge ℂ-Tendsto to ℍ-Tendsto via the open embedding.
  have h_ind : Topology.IsInducing (UpperHalfPlane.coe) :=
    UpperHalfPlane.isOpenEmbedding_coe.isInducing
  have h_z₁_tend_h : Filter.Tendsto z₁_h Filter.atTop (nhds τ_h) := by
    rw [h_ind.tendsto_nhds_iff]
    change Filter.Tendsto (fun n => (z₁_h n : ℂ)) Filter.atTop (nhds (τ_h : ℂ))
    exact h_z₁_tend_c
  have h_z₂_tend_h : Filter.Tendsto z₂_h Filter.atTop (nhds τ_h) := by
    rw [h_ind.tendsto_nhds_iff]
    change Filter.Tendsto (fun n => (z₂_h n : ℂ)) Filter.atTop (nhds (τ_h : ℂ))
    exact h_z₂_tend_c
  -- Compact ball K in ℍ.
  set K : Set UpperHalfPlane := Metric.closedBall τ_h 1 with hK_def
  have hK_compact : IsCompact K := isCompact_closedBall _ _
  -- Finite γ-set via proper discontinuity.
  set S : Set (↥(CongruenceSubgroup.Gamma 2)) :=
    { g | ((fun τ => g • τ) '' K ∩ K).Nonempty } with hS_def
  have hS_finite : S.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK_compact hK_compact
  -- For n large, z_h n ∈ K (using dist < 1/2 < 1).
  rw [Metric.tendsto_atTop] at h_z₁_tend_h h_z₂_tend_h
  obtain ⟨N₁, hN₁⟩ := h_z₁_tend_h (1/2) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := h_z₂_tend_h (1/2) (by norm_num)
  set N : ℕ := max N₁ N₂ with hN_def
  have h_γ_in_S : ∀ n, N ≤ n →
      (⟨γ n, hγ_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) ∈ S := by
    intro n hn
    have h1 := hN₁ n (le_of_max_le_left hn)
    have h2 := hN₂ n (le_of_max_le_right hn)
    refine ⟨z₂_h n, ⟨z₁_h n, ?_, hγ_eq n⟩, ?_⟩
    · exact Metric.mem_closedBall.mpr (le_trans h1.le (by norm_num))
    · exact Metric.mem_closedBall.mpr (le_trans h2.le (by norm_num))
  -- Pigeonhole: some γ in S occurs at infinitely many n ≥ N.
  have h_pigeon : ∃ γ_lim : ↥(CongruenceSubgroup.Gamma 2), γ_lim ∈ S ∧
      {n : ℕ | N ≤ n ∧
        (⟨γ n, hγ_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ_lim}.Infinite := by
    by_contra h_neg
    push Not at h_neg
    have h_ici_infinite : Set.Infinite (Set.Ici N) := Set.Ici_infinite N
    apply h_ici_infinite
    have h_eq : Set.Ici N =
        ⋃ γ_lim ∈ S, {n : ℕ | N ≤ n ∧
          (⟨γ n, hγ_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ_lim} := by
      ext n
      simp only [Set.mem_Ici, Set.mem_iUnion, exists_prop, Set.mem_ofPred_eq]
      constructor
      · intro hn
        refine ⟨⟨γ n, hγ_in n⟩, h_γ_in_S n hn, hn, rfl⟩
      · rintro ⟨_, _, hn, _⟩
        exact hn
    rw [h_eq]
    apply hS_finite.biUnion
    intro γ_lim hγ_lim
    exact h_neg γ_lim hγ_lim
  obtain ⟨γ_lim, _hγ_lim_in_S, hγ_inf⟩ := h_pigeon
  -- Strictly mono subseq in the fiber {γ n = γ_lim}.
  have h_seq_idx : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, φ k ∈
      {n : ℕ | N ≤ n ∧
        (⟨γ n, hγ_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ_lim} := by
    apply Nat.exists_strictMono_subsequence
    intro M
    obtain ⟨b, hb_in, hb_gt⟩ := hγ_inf.exists_gt M
    exact ⟨b, hb_gt, hb_in⟩
  obtain ⟨φ, hφ_mono, hφ_in⟩ := h_seq_idx
  -- Along subseq, γ_lim.val • z₁_h (φ k) = z₂_h (φ k).
  have h_subseq_eq : ∀ k, γ_lim.val • z₁_h (φ k) = z₂_h (φ k) := by
    intro k
    have h_γ_eq_lim : γ (φ k) = γ_lim.val := by
      have := (hφ_in k).2
      exact congrArg Subtype.val this
    rw [← h_γ_eq_lim]
    exact hγ_eq (φ k)
  -- Distinct along subseq.
  have h_subseq_ne : ∀ k, z₁_h (φ k) ≠ z₂_h (φ k) := by
    intro k h_eq
    have h_z_eq : z₁ (φ k) = z₂ (φ k) := by
      have : (z₁_h (φ k) : ℂ) = (z₂_h (φ k) : ℂ) := by rw [h_eq]
      exact this
    exact hne (φ k) h_z_eq
  -- Take limit: γ_lim.val • τ_h = τ_h.
  have h_cont : Continuous (fun σ : UpperHalfPlane => γ_lim.val • σ) := by
    change Continuous (fun σ : UpperHalfPlane => ((γ_lim.val : SL(2, ℝ)) • σ))
    exact continuous_const_smul _
  have h_z₁_tend_h' : Filter.Tendsto z₁_h Filter.atTop (nhds τ_h) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    exact h_z₁_tend_h δ hδ
  have h_z₂_tend_h' : Filter.Tendsto z₂_h Filter.atTop (nhds τ_h) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    exact h_z₂_tend_h δ hδ
  have h_tend_left : Filter.Tendsto (fun k => γ_lim.val • z₁_h (φ k)) Filter.atTop
      (nhds (γ_lim.val • τ_h)) :=
    (h_cont.tendsto _).comp (h_z₁_tend_h'.comp hφ_mono.tendsto_atTop)
  have h_tend_right : Filter.Tendsto (fun k => z₂_h (φ k)) Filter.atTop (nhds τ_h) :=
    h_z₂_tend_h'.comp hφ_mono.tendsto_atTop
  have h_replace : (fun k => γ_lim.val • z₁_h (φ k)) = (fun k => z₂_h (φ k)) :=
    funext h_subseq_eq
  rw [h_replace] at h_tend_left
  have h_γ_fix : γ_lim.val • τ_h = τ_h :=
    tendsto_nhds_unique h_tend_left h_tend_right
  -- Pillar 1: γ_lim ∈ {I, -I}.
  have h_pm := gamma_two_fixed_point_implies_pm_one γ_lim.val γ_lim.property τ_h h_γ_fix
  -- ±I acts trivially: γ_lim • z = z. Contradicts h_subseq_ne for k = 0.
  have h_triv : γ_lim.val • z₁_h (φ 0) = z₁_h (φ 0) := by
    rcases h_pm with h | h
    · rw [h]; simp
    · rw [h]
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp
  have h_contra : z₁_h (φ 0) = z₂_h (φ 0) := by
    rw [← h_subseq_eq 0, h_triv]
  exact h_subseq_ne 0 h_contra


/-- **Non-vanishing of `λ'` on the closed half-fundamental domain
`F`.** Case split on `F^o` vs `∂F`. For interior points, suppose
`deriv λ τ = 0`; by `analyticAt_localOpen_with_multiplicity` the
helper produces two distinct preimages `z₁ ≠ z₂` of some value
`w ≠ λ τ` inside a small ball `B(τ, ε) ⊆ F^o`, contradicting
`modularLambdaH_injOn_F_interior`. For boundary points,
`Im(λ τ) = 0` (from the three boundary real-value lemmas) so
`modularLambdaH_deriv_ne_zero_when_im_lambda_zero` applies
directly. -/
theorem modularLambdaH_deriv_ne_zero_on_F
    {τ : ℂ} (hτ_F : τ ∈ Gamma2FundamentalDomain) :
    deriv modularLambdaH τ ≠ 0 := by
  obtain ⟨hτ_im, hτ_re_nn, hτ_re_le, hτ_semicircle⟩ := hτ_F
  by_cases h_interior : τ ∈ Gamma2FundamentalDomainInterior
  · -- F^o case: use H_inj_F^o + multiplicity helper.
    intro h_dz
    -- λ analytic at τ.
    have hH_open : IsOpen {z : ℂ | 0 < z.im} := by
      have : {z : ℂ | 0 < z.im} = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp
      rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
    have h_lam_at : AnalyticAt ℂ modularLambdaH τ :=
      (modularLambdaH_differentiableOn.analyticOnNhd hH_open) τ hτ_im
    -- ℍ is preconnected (convex).
    have h_H_preconn : IsPreconnected {z : ℂ | 0 < z.im} := by
      apply Convex.isPreconnected
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
    have h_lam_an : AnalyticOnNhd ℂ modularLambdaH {z : ℂ | 0 < z.im} :=
      modularLambdaH_differentiableOn.analyticOnNhd hH_open
    have h_lam_not_const : ¬ ∀ᶠ z in nhds τ, modularLambdaH z = modularLambdaH τ := by
      intro h_eq
      have h_const_an : AnalyticOnNhd ℂ (fun _ : ℂ => modularLambdaH τ) {z : ℂ | 0 < z.im} :=
        fun _ _ => analyticAt_const
      have h_eqOn : Set.EqOn modularLambdaH (fun _ => modularLambdaH τ) {z : ℂ | 0 < z.im} :=
        h_lam_an.eqOn_of_preconnected_of_eventuallyEq h_const_an h_H_preconn hτ_im h_eq
      have h_1i_in : (1 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
        refine ⟨?_, ?_⟩
        · intro h; have := congrArg Complex.im h; simp at this
        · intro h; have := congrArg Complex.im h; simp at this
      have h_2i_in : (2 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
        refine ⟨?_, ?_⟩
        · intro h; have := congrArg Complex.im h; simp at this
        · intro h; have := congrArg Complex.re h; simp at this
      have h_lam_img : modularLambdaH '' {z : ℂ | 0 < z.im} = { w : ℂ | w ≠ 0 ∧ w ≠ 1 } :=
        modularLambdaH_image
      have h_1i_img : (1 + Complex.I : ℂ) ∈ modularLambdaH '' {z : ℂ | 0 < z.im} :=
        h_lam_img ▸ h_1i_in
      have h_2i_img : (2 + Complex.I : ℂ) ∈ modularLambdaH '' {z : ℂ | 0 < z.im} :=
        h_lam_img ▸ h_2i_in
      obtain ⟨τ_a, hτ_a_H, hτ_a_eq⟩ := h_1i_img
      obtain ⟨τ_b, hτ_b_H, hτ_b_eq⟩ := h_2i_img
      have h_a := h_eqOn hτ_a_H
      have h_b := h_eqOn hτ_b_H
      rw [hτ_a_eq] at h_a
      rw [hτ_b_eq] at h_b
      have h_eq_12 : (1 + Complex.I : ℂ) = (2 + Complex.I : ℂ) := h_a.trans h_b.symm
      have h_re := congrArg Complex.re h_eq_12
      simp at h_re
    -- F^o is nhd of τ.
    have hF_open : IsOpen Gamma2FundamentalDomainInterior :=
      Gamma2FundamentalDomainInterior_isOpen
    have hF_nhds : Gamma2FundamentalDomainInterior ∈ nhds τ :=
      hF_open.mem_nhds h_interior
    -- Apply multiplicity helper.
    obtain ⟨V, hV_nhds, hV_prop⟩ :=
      analyticAt_localOpen_with_multiplicity h_lam_at h_lam_not_const h_dz
        Gamma2FundamentalDomainInterior hF_nhds
    -- Pick w ∈ V with w ≠ λ τ.
    rcases Metric.mem_nhds_iff.mp hV_nhds with ⟨r, hr_pos, hr_sub⟩
    set w : ℂ := modularLambdaH τ + (r/2 : ℝ) with hw_def
    have h_dist_w : dist w (modularLambdaH τ) = r/2 := by
      rw [hw_def, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr_pos)]
    have hw_in_V : w ∈ V := by
      apply hr_sub
      rw [Metric.mem_ball, h_dist_w]; linarith
    have hw_ne : w ≠ modularLambdaH τ := by
      intro h_eq
      have h_re_eq : w.re = (modularLambdaH τ).re := congrArg Complex.re h_eq
      rw [hw_def, Complex.add_re, Complex.ofReal_re] at h_re_eq
      linarith
    obtain ⟨z_1, hz_1_in, z_2, hz_2_in, h_ne, h_lam_z_1, h_lam_z_2⟩ :=
      hV_prop w hw_in_V hw_ne
    -- z_1, z_2 ∈ F^o, λ(z_1) = λ(z_2). By H_inj_F^o, z_1 = z_2.
    have h_lam_eq : modularLambdaH z_1 = modularLambdaH z_2 := h_lam_z_1.trans h_lam_z_2.symm
    have h_z_eq : z_1 = z_2 :=
      modularLambdaH_injOn_F_interior hz_1_in hz_2_in h_lam_eq
    exact h_ne h_z_eq
  · -- ∂F case: τ ∈ F but not in F^o. Hence Im(λ τ) = 0 (boundary real-value).
    have h_im_lam_zero : (modularLambdaH τ).im = 0 := by
      by_cases h_re_zero : τ.re = 0
      · have h_τ_eq : τ = Complex.I * τ.im := by
          apply Complex.ext
          · simp [Complex.mul_re, Complex.I_re, Complex.I_im, h_re_zero]
          · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
        rw [h_τ_eq]
        exact modularLambdaH_pure_imag_real hτ_im
      · by_cases h_re_one : τ.re = 1
        · have h_τ_eq : τ = 1 + Complex.I * τ.im := by
            apply Complex.ext
            · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, h_re_one]
            · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
          rw [h_τ_eq]
          exact modularLambdaH_one_add_imag_real hτ_im
        · by_cases h_semicircle : ‖2 * τ - 1‖ = 1
          · exact modularLambdaH_semicircle_real hτ_im h_semicircle
          · -- All three boundary conditions strict: τ ∈ F^o, contradicting h_interior.
            exfalso
            apply h_interior
            refine ⟨hτ_im, ?_, ?_, ?_⟩
            · rcases lt_or_eq_of_le hτ_re_nn with h | h
              · exact h
              · exact absurd h.symm h_re_zero
            · rcases lt_or_eq_of_le hτ_re_le with h | h
              · exact h
              · exact absurd h h_re_one
            · rcases lt_or_eq_of_le hτ_semicircle with h | h
              · exact h
              · exact absurd h.symm h_semicircle
    exact modularLambdaH_deriv_ne_zero_when_im_lambda_zero hτ_im h_im_lam_zero

/-- **Möbius-derivative + upper branch for Pillar 3.** For
`τ ∈ ℍ` with `Im(λ τ) > 0`, `deriv λ τ ≠ 0`. Reduce `τ` to
`γ • τ ∈ F` via the half-FD property; apply
`modularLambdaH_deriv_ne_zero_on_F`; transport back along the
`Γ(2)`-orbit via the Möbius chain rule. -/
theorem modularLambdaH_deriv_ne_zero_when_im_lambda_pos
    {τ : ℂ} (hτ : 0 < τ.im)
    (h_im_pos : 0 < (modularLambdaH τ).im) :
    deriv modularLambdaH τ ≠ 0 := by
  set τ_h : UpperHalfPlane := ⟨τ, hτ⟩ with hτ_h_def
  have hlam_τ_h : 0 < (modularLambdaH (τ_h : ℂ)).im := h_im_pos
  obtain ⟨γ, hγ_in, hγτ_F⟩ :=
    gamma2_orbit_meets_F_when_im_lambda_pos τ_h hlam_τ_h
  have h_deriv_γτ : deriv modularLambdaH ((γ • τ_h : UpperHalfPlane) : ℂ) ≠ 0 :=
    modularLambdaH_deriv_ne_zero_on_F hγτ_F
  set a : ℂ := (γ.val 0 0 : ℂ) with ha_def
  set b : ℂ := (γ.val 0 1 : ℂ) with hb_def
  set c : ℂ := (γ.val 1 0 : ℂ) with hc_def
  set d : ℂ := (γ.val 1 1 : ℂ) with hd_def
  have h_det : a * d - b * c = 1 := by
    have hγ_det := γ.2
    have : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by
      have := Matrix.det_fin_two γ.val
      rw [hγ_det] at this
      linarith
    push_cast [ha_def, hb_def, hc_def, hd_def]
    exact_mod_cast this
  set Mob : ℂ → ℂ := fun z => (a * z + b) / (c * z + d) with hMob_def
  have h_smul_coe : ((γ • τ_h : UpperHalfPlane) : ℂ) = Mob τ := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    change ((((algebraMap ℤ ℝ) (γ.val 0 0)) : ℂ) * (τ_h : ℂ) +
        ((algebraMap ℤ ℝ) (γ.val 0 1) : ℂ)) /
        (((algebraMap ℤ ℝ) (γ.val 1 0) : ℂ) * (τ_h : ℂ) +
          ((algebraMap ℤ ℝ) (γ.val 1 1) : ℂ)) = Mob τ
    simp [hMob_def, ha_def, hb_def, hc_def, hd_def, hτ_h_def]
  have h_denom_ne : c * τ + d ≠ 0 := by
    intro h_eq
    have h_im_pos : 0 < ((γ • τ_h : UpperHalfPlane) : ℂ).im :=
      (γ • τ_h : UpperHalfPlane).2
    rw [h_smul_coe] at h_im_pos
    have h_Mob_undef : Mob τ = (a * τ + b) / 0 := by
      change (a * τ + b) / (c * τ + d) = (a * τ + b) / 0
      rw [h_eq]
    rw [h_Mob_undef] at h_im_pos
    simp at h_im_pos
  have h_Mob_deriv : HasDerivAt Mob (1 / (c * τ + d) ^ 2) τ := by
    have h_num : HasDerivAt (fun z : ℂ => a * z + b) a τ := by
      have := (hasDerivAt_id τ).const_mul a
      simpa using this.add_const b
    have h_den : HasDerivAt (fun z : ℂ => c * z + d) c τ := by
      have := (hasDerivAt_id τ).const_mul c
      simpa using this.add_const d
    have h_div : HasDerivAt Mob
        ((a * (c * τ + d) - (a * τ + b) * c) / (c * τ + d) ^ 2) τ := h_num.div h_den h_denom_ne
    have h_simpl : (a * (c * τ + d) - (a * τ + b) * c) / (c * τ + d) ^ 2
        = 1 / (c * τ + d) ^ 2 := by
      rw [div_eq_div_iff (pow_ne_zero 2 h_denom_ne) (pow_ne_zero 2 h_denom_ne)]
      linear_combination ((c * τ + d) ^ 2) * h_det
    rw [← h_simpl]
    exact h_div
  have hγτ_im_pos : 0 < ((γ • τ_h : UpperHalfPlane) : ℂ).im := (γ • τ_h).2
  have h_inv_local :
      ∀ᶠ z in nhds τ, modularLambdaH (Mob z) = modularLambdaH z := by
    have h_open : IsOpen {z : ℂ | 0 < z.im} := by
      have : {z : ℂ | 0 < z.im} = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp
      rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
    have hτ_mem : τ ∈ {z : ℂ | 0 < z.im} := hτ
    refine Filter.eventually_of_mem (h_open.mem_nhds hτ_mem) ?_
    intro z hz
    have hz_im : 0 < z.im := hz
    set z_h : UpperHalfPlane := ⟨z, hz_im⟩ with hz_h_def
    have h_inv_z := modularLambdaH_gamma2_invariant γ hγ_in z_h
    have h_smul_z_coe : ((γ • z_h : UpperHalfPlane) : ℂ) = Mob z := by
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      change ((((algebraMap ℤ ℝ) (γ.val 0 0)) : ℂ) * (z_h : ℂ) +
          ((algebraMap ℤ ℝ) (γ.val 0 1) : ℂ)) /
          (((algebraMap ℤ ℝ) (γ.val 1 0) : ℂ) * (z_h : ℂ) +
            ((algebraMap ℤ ℝ) (γ.val 1 1) : ℂ)) = Mob z
      simp [hMob_def, ha_def, hb_def, hc_def, hd_def, hz_h_def]
    rw [h_smul_z_coe] at h_inv_z
    exact h_inv_z
  have h_compose_deriv :
      deriv (fun z : ℂ => modularLambdaH (Mob z)) τ
        = deriv modularLambdaH (Mob τ) * (1 / (c * τ + d) ^ 2) := by
    have h_Mob_im_pos : 0 < (Mob τ).im := by
      have hh := (γ • τ_h : UpperHalfPlane).2
      rw [h_smul_coe] at hh
      exact hh
    have h_lam_diff_at_Mobτ : DifferentiableAt ℂ modularLambdaH (Mob τ) :=
      modularLambdaH_differentiableAt_of_im_pos h_Mob_im_pos
    have h_chain : HasDerivAt (fun z : ℂ => modularLambdaH (Mob z))
        (deriv modularLambdaH (Mob τ) * (1 / (c * τ + d) ^ 2)) τ :=
      (h_lam_diff_at_Mobτ.hasDerivAt).comp τ h_Mob_deriv
    exact h_chain.deriv
  have h_deriv_eq :
      deriv (fun z : ℂ => modularLambdaH (Mob z)) τ = deriv modularLambdaH τ :=
    Filter.EventuallyEq.deriv_eq h_inv_local
  rw [h_compose_deriv] at h_deriv_eq
  rw [h_smul_coe] at h_deriv_γτ
  intro h_zero
  rw [h_zero] at h_deriv_eq
  have h_factor_ne : (1 : ℂ) / (c * τ + d) ^ 2 ≠ 0 :=
    one_div_ne_zero (pow_ne_zero 2 h_denom_ne)
  have := h_deriv_eq.symm
  rw [eq_comm, mul_eq_zero] at this
  rcases this with h | h
  · exact h_deriv_γτ h
  · exact h_factor_ne h

/-- **Pillar-3 LHP `< 0` branch.** For `τ ∈ ℍ` with `Im(λ τ) < 0`,
`deriv λ τ ≠ 0`. Proof: pass to `τ' := -conj τ ∈ ℍ`; by
`modularLambdaH_conj_symmetry`, `λ τ' = conj(λ τ)` so
`Im(λ τ') > 0` and the upper branch gives `deriv λ τ' ≠ 0`. Define
`G(z) := conj(λ(-conj z))`; by the conjugation identity `G = λ`
locally on `ℍ`. Compute `deriv G τ = -conj(deriv λ τ')` via the
Wirtinger / FDeriv composition `conj ∘ λ ∘ negConj` over `ℝ`; the
two anti-holomorphic `conj` factors cancel algebraically so the
composition is the `ℝ`-linear map `h ↦ -conj(d) · h`, identified as
`(-conj d) • id_ℝ`. Convert this `ℝ`-FDeriv to a `ℂ`-derivative via
the `isLittleO` characterisation. Combined with
`deriv G τ = deriv λ τ` (EventuallyEq), conclude
`deriv λ τ = -conj(deriv λ τ') ≠ 0`. -/
theorem modularLambdaH_deriv_ne_zero_when_im_lambda_neg
    {τ : ℂ} (hτ : 0 < τ.im)
    (hlam_im : (modularLambdaH τ).im < 0) :
    deriv modularLambdaH τ ≠ 0 := by
  -- τ' := -conj τ ∈ ℍ.
  have hτ' : 0 < (-(starRingEnd ℂ τ)).im := by
    simp only [Complex.neg_im, Complex.conj_im, neg_neg]; exact hτ
  have h_lam_τ' :
      modularLambdaH (-(starRingEnd ℂ τ)) = starRingEnd ℂ (modularLambdaH τ) :=
    modularLambdaH_conj_symmetry hτ
  have h_im_pos' : 0 < (modularLambdaH (-(starRingEnd ℂ τ))).im := by
    rw [h_lam_τ', Complex.conj_im]; linarith
  -- Upper branch: deriv λ at τ' is non-zero.
  have hd_ne : deriv modularLambdaH (-(starRingEnd ℂ τ)) ≠ 0 :=
    modularLambdaH_deriv_ne_zero_when_im_lambda_pos hτ' h_im_pos'
  -- G(z) := conj(λ(-conj z)); G = λ locally at τ.
  have hG_eq_lam :
      (fun z => starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z)))) =ᶠ[nhds τ] modularLambdaH := by
    have h_open : IsOpen {z : ℂ | 0 < z.im} := by
      have : {z : ℂ | 0 < z.im} = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp
      rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
    filter_upwards [h_open.mem_nhds (show τ ∈ {z : ℂ | 0 < z.im} from hτ)] with z hz_im
    show starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z))) = modularLambdaH z
    rw [show modularLambdaH (-(starRingEnd ℂ z)) = starRingEnd ℂ (modularLambdaH z) from
        modularLambdaH_conj_symmetry hz_im, Complex.conj_conj]
  -- Abbreviate d := deriv λ τ'.
  set d : ℂ := deriv modularLambdaH (-(starRingEnd ℂ τ)) with hd_def
  -- HasFDerivAt for the three pieces (all `ℝ`-linear, avoiding `restrictScalars`).
  have h_negconj_fderiv : HasFDerivAt (fun z : ℂ => -(starRingEnd ℂ z))
      (-(Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)) τ :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.neg
  have h_conj_fderiv : HasFDerivAt (fun w : ℂ => starRingEnd ℂ w)
      (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)
      (modularLambdaH (-(starRingEnd ℂ τ))) :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
  -- `λ` has `ℝ`-FDeriv `d • (id ℝ ℂ)` at `-conj τ`. Bypass the `restrictScalars`
  -- type-class issue by constructing the `ℝ`-linear FDeriv directly via
  -- `hasFDerivAt_iff_isLittleO` from the underlying `HasDerivAt`.
  have h_lam_diff_at : DifferentiableAt ℂ modularLambdaH (-(starRingEnd ℂ τ)) :=
    modularLambdaH_differentiableAt_of_im_pos hτ'
  have h_lam_hasDeriv : HasDerivAt modularLambdaH d (-(starRingEnd ℂ τ)) :=
    h_lam_diff_at.hasDerivAt
  have h_lam_fderiv : HasFDerivAt modularLambdaH
      (d • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ))
      (-(starRingEnd ℂ τ)) := by
    rw [hasFDerivAt_iff_isLittleO]
    have h_o := h_lam_hasDeriv.isLittleO
    refine h_o.congr_left ?_
    intro y
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  -- Inner composition: λ ∘ negConj.
  have h_inner := h_lam_fderiv.comp τ h_negconj_fderiv
  -- Outer composition: conj ∘ (λ ∘ negConj).
  have h_outer := h_conj_fderiv.comp τ h_inner
  -- The `ℝ`-linear composition equals `(-conj d) • id_ℝ` by ring after
  -- pushing `conj` through products and using `conj_conj`.
  have h_comp_eq :
      (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).comp
        ((d • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ)).comp
          (-(Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ))) =
        (-(starRingEnd ℂ d)) • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ) := by
    ext h
    have h_cle : ∀ z : ℂ, (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ) z = starRingEnd ℂ z :=
      fun _ => rfl
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, neg_apply, h_cle, smul_eq_mul]
    rw [map_mul, map_neg, Complex.conj_conj]
    ring
  rw [h_comp_eq] at h_outer
  -- Convert the `ℝ`-FDeriv with `(-conj d) • id_ℝ` to a `ℂ`-derivative.
  have hG_hasDeriv : HasDerivAt
      (fun z : ℂ => starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z))))
      (-(starRingEnd ℂ d)) τ := by
    rw [hasDerivAt_iff_isLittleO]
    have h_outer_o := h_outer.isLittleO
    refine h_outer_o.congr_left ?_
    intro y
    simp only [Function.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  -- deriv G τ = -conj d via chain rule.
  have h_deriv_G_chain :
      deriv (fun z : ℂ => starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z)))) τ
        = -(starRingEnd ℂ (deriv modularLambdaH (-(starRingEnd ℂ τ)))) :=
    hG_hasDeriv.deriv
  -- deriv G τ = deriv λ τ via EventuallyEq.
  have h_deriv_G_local :
      deriv (fun z : ℂ => starRingEnd ℂ (modularLambdaH (-(starRingEnd ℂ z)))) τ
        = deriv modularLambdaH τ :=
    hG_eq_lam.deriv_eq
  -- Conclude.
  intro h_zero
  rw [h_zero] at h_deriv_G_local
  rw [h_deriv_G_chain] at h_deriv_G_local
  -- h_deriv_G_local : -(starRingEnd ℂ (deriv λ (-conj τ))) = 0.
  have h_conjd_zero : starRingEnd ℂ (deriv modularLambdaH (-(starRingEnd ℂ τ))) = 0 :=
    neg_eq_zero.mp h_deriv_G_local
  have h_d_zero : deriv modularLambdaH (-(starRingEnd ℂ τ)) = 0 := by
    have h_conj_conj :
        starRingEnd ℂ (starRingEnd ℂ (deriv modularLambdaH (-(starRingEnd ℂ τ)))) =
          starRingEnd ℂ 0 := congr_arg _ h_conjd_zero
    rwa [Complex.conj_conj, map_zero] at h_conj_conj
  exact hd_ne h_d_zero
/-- **Pillar-3 LHP-and-boundary branch (dispatcher).** -/
theorem modularLambdaH_deriv_ne_zero_when_im_lambda_non_pos
    {τ : ℂ} (hτ : 0 < τ.im)
    (hlam_im : (modularLambdaH τ).im ≤ 0) :
    deriv modularLambdaH τ ≠ 0 := by
  rcases lt_or_eq_of_le hlam_im with h | h
  · exact modularLambdaH_deriv_ne_zero_when_im_lambda_neg hτ h
  · exact modularLambdaH_deriv_ne_zero_when_im_lambda_zero hτ h

/-! ## Pillar 4, lower and boundary branches: `Im λ ≤ 0` -/

/-- **Pillar-4 LHP branch (Im λ < 0).** For `τ₁, τ₂ ∈ ℍ` with
`Im(λ τ₁) < 0` and `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`.

Proof: pass to `τ_i' := -conj τ_i ∈ ℍ`; by
`modularLambdaH_conj_symmetry` we have `Im(λ τ_i') > 0` and
`λ(τ₁') = λ(τ₂')`. Apply the upper branch to obtain
`γ = ⟨⟨a, b⟩, ⟨c, d⟩⟩ ∈ Γ(2)` with `γ • τ₁' = τ₂'`. Conjugating
both sides translates to `γ' • τ₁ = τ₂` for
`γ' := ⟨⟨a, -b⟩, ⟨-c, d⟩⟩`, also in `Γ(2)`. -/
theorem gamma2_lambda_eq_implies_orbit_when_im_lambda_neg
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_neg : (modularLambdaH (τ₁ : ℂ)).im < 0)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  have hτ₁_im : 0 < (τ₁ : ℂ).im := τ₁.2
  have hτ₂_im : 0 < (τ₂ : ℂ).im := τ₂.2
  -- Build τ_i' := -conj τ_i ∈ ℍ.
  have hτ₁'_im : 0 < (-(starRingEnd ℂ (τ₁ : ℂ))).im := by
    simp only [Complex.neg_im, Complex.conj_im, neg_neg]; exact hτ₁_im
  have hτ₂'_im : 0 < (-(starRingEnd ℂ (τ₂ : ℂ))).im := by
    simp only [Complex.neg_im, Complex.conj_im, neg_neg]; exact hτ₂_im
  set τ₁' : UpperHalfPlane := ⟨-(starRingEnd ℂ (τ₁ : ℂ)), hτ₁'_im⟩ with hτ₁'_def
  set τ₂' : UpperHalfPlane := ⟨-(starRingEnd ℂ (τ₂ : ℂ)), hτ₂'_im⟩ with hτ₂'_def
  have h_lam_τ₁' : modularLambdaH (τ₁' : ℂ) = starRingEnd ℂ (modularLambdaH (τ₁ : ℂ)) :=
    modularLambdaH_conj_symmetry hτ₁_im
  have h_lam_τ₂' : modularLambdaH (τ₂' : ℂ) = starRingEnd ℂ (modularLambdaH (τ₂ : ℂ)) :=
    modularLambdaH_conj_symmetry hτ₂_im
  have h_im_pos' : 0 < (modularLambdaH (τ₁' : ℂ)).im := by
    rw [h_lam_τ₁', Complex.conj_im]
    linarith
  have h_eq' : modularLambdaH (τ₁' : ℂ) = modularLambdaH (τ₂' : ℂ) := by
    rw [h_lam_τ₁', h_lam_τ₂', h_eq]
  obtain ⟨γ, hγ_in, hγ_eq⟩ :=
    gamma2_lambda_eq_implies_orbit_when_im_lambda_pos h_im_pos' h_eq'
  -- Build γ' = [[a, -b], [-c, d]] ∈ SL(2, ℤ).
  set γ'_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![γ.val 0 0, -γ.val 0 1; -γ.val 1 0, γ.val 1 1] with hγ'_mat_def
  have hγ'_det : γ'_mat.det = 1 := by
    simp only [hγ'_mat_def, Matrix.det_fin_two_of]
    have hd := γ.2
    rw [Matrix.det_fin_two] at hd
    linarith
  set γ' : SL(2, ℤ) := ⟨γ'_mat, hγ'_det⟩ with hγ'_def
  have hγ'_in : γ' ∈ CongruenceSubgroup.Gamma 2 := by
    rw [CongruenceSubgroup.Gamma_mem]
    have hγ_mem : _ ∧ _ ∧ _ ∧ _ := CongruenceSubgroup.Gamma_mem.mp hγ_in
    obtain ⟨ha, hb, hc, hd⟩ := hγ_mem
    have h00' : γ'.val 0 0 = γ.val 0 0 := by
      simp only [hγ'_def, hγ'_mat_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    have h01' : γ'.val 0 1 = -γ.val 0 1 := by
      simp only [hγ'_def, hγ'_mat_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
    have h10' : γ'.val 1 0 = -γ.val 1 0 := by
      simp only [hγ'_def, hγ'_mat_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
    have h11' : γ'.val 1 1 = γ.val 1 1 := by
      simp only [hγ'_def, hγ'_mat_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h00']; exact ha
    · rw [h01']; push_cast; rw [hb]; ring
    · rw [h10']; push_cast; rw [hc]; ring
    · rw [h11']; exact hd
  refine ⟨γ', hγ'_in, ?_⟩
  apply UpperHalfPlane.ext
  -- The upper-branch identity in ℂ.
  have h_γ_eq_c : ((γ • τ₁' : UpperHalfPlane) : ℂ) = (τ₂' : ℂ) := by rw [hγ_eq]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at h_γ_eq_c
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  -- γ' entries match γ with sign flips on b, c.
  have h00 : γ'.val 0 0 = γ.val 0 0 := by simp [hγ'_def, hγ'_mat_def]
  have h01 : γ'.val 0 1 = -γ.val 0 1 := by simp [hγ'_def, hγ'_mat_def]
  have h10 : γ'.val 1 0 = -γ.val 1 0 := by simp [hγ'_def, hγ'_mat_def]
  have h11 : γ'.val 1 1 = γ.val 1 1 := by simp [hγ'_def, hγ'_mat_def]
  rw [h00, h01, h10, h11]
  -- Abbreviate the real-cast entries.
  set a : ℂ := ((algebraMap ℤ ℝ) (γ.val 0 0) : ℂ) with ha_def
  set b : ℂ := ((algebraMap ℤ ℝ) (γ.val 0 1) : ℂ) with hb_def
  set c : ℂ := ((algebraMap ℤ ℝ) (γ.val 1 0) : ℂ) with hc_def
  set d : ℂ := ((algebraMap ℤ ℝ) (γ.val 1 1) : ℂ) with hd_def
  -- Negation through algebraMap.
  have hb_neg : ((algebraMap ℤ ℝ) (-γ.val 0 1) : ℂ) = -b := by push_cast; ring
  have hc_neg : ((algebraMap ℤ ℝ) (-γ.val 1 0) : ℂ) = -c := by push_cast; ring
  rw [hb_neg, hc_neg]
  -- Substitute τ_i' = -conj τ_i in h_γ_eq_c.
  have h_τ₁'_c_eq : (τ₁' : ℂ) = -(starRingEnd ℂ (τ₁ : ℂ)) := rfl
  have h_τ₂'_c_eq : (τ₂' : ℂ) = -(starRingEnd ℂ (τ₂ : ℂ)) := rfl
  rw [h_τ₁'_c_eq, h_τ₂'_c_eq] at h_γ_eq_c
  -- Take conjugate of the equation.
  have h_conj := congr_arg (starRingEnd ℂ) h_γ_eq_c
  simp only [map_div₀, map_add, map_mul, map_neg, Complex.conj_conj] at h_conj
  -- Conj of real-coerced values is itself.
  have hca : starRingEnd ℂ a = a := Complex.conj_ofReal _
  have hcb : starRingEnd ℂ b = b := Complex.conj_ofReal _
  have hcc : starRingEnd ℂ c = c := Complex.conj_ofReal _
  have hcd : starRingEnd ℂ d = d := Complex.conj_ofReal _
  rw [hca, hcb, hcc, hcd] at h_conj
  -- h_conj : (a * -(τ₁) + b) / (c * -(τ₁) + d) = -(τ₂).
  -- Goal: (a * τ₁ + -b) / (-c * τ₁ + d) = τ₂.
  -- Reduce to h_conj via numerator/denominator sign manipulation.
  have h_num_eq : a * (τ₁ : ℂ) + -b = -(a * -(τ₁ : ℂ) + b) := by ring
  have h_den_eq : -c * (τ₁ : ℂ) + d = c * -(τ₁ : ℂ) + d := by ring
  rw [h_num_eq, h_den_eq, neg_div, h_conj, neg_neg]

/-- **Orbit relation is closed.** The `Γ(2)`-orbit relation
`{(τ₁, τ₂) : ∃ γ ∈ Γ(2), γ • τ₁ = τ₂}` is closed in
`ℍ × ℍ`. Proof: take a convergent sequence
`(τ₁^n, τ₂^n) → (τ₁, τ₂)` with `γₙ • τ₁^n = τ₂^n`. Locally compact
neighbourhoods of `τ₁, τ₂` and `gamma_two_properlyDiscontinuousSMul`
restrict `γₙ` to a finite set; extract a subsequence with constant
`γₙ = γ`, take the limit using continuity of `γ•`, and conclude
`γ • τ₁ = τ₂`. -/
theorem gamma2_orbitRel_isClosed :
    IsClosed { p : UpperHalfPlane × UpperHalfPlane |
      ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • p.1 = p.2 } := by
  rw [← isSeqClosed_iff_isClosed]
  intro xn x h_in_n h_tendsto
  have := gamma_two_properlyDiscontinuousSMul
  -- Extract γₙ for each xₙ.
  choose γn hγn_in hγn_eq using h_in_n
  -- Compact closed balls around x.1, x.2.
  set K₁ : Set UpperHalfPlane := Metric.closedBall x.1 1 with hK₁_def
  set K₂ : Set UpperHalfPlane := Metric.closedBall x.2 1 with hK₂_def
  have hK₁_compact : IsCompact K₁ := isCompact_closedBall _ _
  have hK₂_compact : IsCompact K₂ := isCompact_closedBall _ _
  -- Convergence in each coordinate.
  have h_tendsto_1 : Filter.Tendsto (fun n => (xn n).1) Filter.atTop (nhds x.1) :=
    (continuous_fst.tendsto x).comp h_tendsto
  have h_tendsto_2 : Filter.Tendsto (fun n => (xn n).2) Filter.atTop (nhds x.2) :=
    (continuous_snd.tendsto x).comp h_tendsto
  rw [Metric.tendsto_atTop] at h_tendsto_1 h_tendsto_2
  obtain ⟨N₁, hN₁⟩ := h_tendsto_1 (1/2) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := h_tendsto_2 (1/2) (by norm_num)
  set N : ℕ := max N₁ N₂ with hN_def
  -- Finite γ-set from proper discontinuity.
  set S : Set (↥(CongruenceSubgroup.Gamma 2)) :=
    { g | ((fun τ => g • τ) '' K₁ ∩ K₂).Nonempty } with hS_def
  have hS_finite : S.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK₁_compact hK₂_compact
  -- For n ≥ N, the lifted γn n lives in S.
  have h_γn_in_S : ∀ n, N ≤ n →
      (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) ∈ S := by
    intro n hn
    have h1 := hN₁ n (le_of_max_le_left hn)
    have h2 := hN₂ n (le_of_max_le_right hn)
    refine ⟨(xn n).2, ⟨(xn n).1, ?_, hγn_eq n⟩, ?_⟩
    · exact Metric.mem_closedBall.mpr (le_trans h1.le (by norm_num))
    · exact Metric.mem_closedBall.mpr (le_trans h2.le (by norm_num))
  -- Pigeonhole: some γ ∈ S is hit infinitely often in (γn n)_{n ≥ N}.
  have h_pigeon : ∃ γ : ↥(CongruenceSubgroup.Gamma 2), γ ∈ S ∧
      {n : ℕ | N ≤ n ∧ (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ}.Infinite := by
    by_contra h_neg
    push Not at h_neg
    have h_ici_infinite : Set.Infinite (Set.Ici N) := Set.Ici_infinite N
    apply h_ici_infinite
    have h_eq : Set.Ici N =
        ⋃ γ ∈ S, {n : ℕ | N ≤ n ∧ (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ} := by
      ext n
      simp only [Set.mem_Ici, Set.mem_iUnion, exists_prop, Set.mem_ofPred_eq]
      constructor
      · intro hn
        refine ⟨⟨γn n, hγn_in n⟩, h_γn_in_S n hn, hn, rfl⟩
      · rintro ⟨_, _, hn, _⟩
        exact hn
    rw [h_eq]
    apply hS_finite.biUnion
    intro γ hγ
    exact h_neg γ hγ
  -- Extract γ and infinite subsequence.
  obtain ⟨γ, _hγ_in_S, hγ_inf⟩ := h_pigeon
  -- Build a strictly increasing index sequence in the fiber.
  have h_seq : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k, φ k ∈ {n : ℕ | N ≤ n ∧ (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ} := by
    apply Nat.exists_strictMono_subsequence
    intro M
    obtain ⟨b, hb_in, hb_gt⟩ := hγ_inf.exists_gt M
    exact ⟨b, hb_gt, hb_in⟩
  obtain ⟨φ, hφ_mono, hφ_in⟩ := h_seq
  -- For each k: γn (φ k) = γ.val, so γ.val • (xn (φ k)).1 = (xn (φ k)).2.
  -- Take limit using continuity of γ.val•.
  refine ⟨γ.val, γ.property, ?_⟩
  -- γ.val • x.1 = x.2: use continuity.
  have h_cont : Continuous (fun τ : UpperHalfPlane => γ.val • τ) := by
    change Continuous (fun τ : UpperHalfPlane => ((γ.val : SL(2, ℝ)) • τ))
    exact continuous_const_smul _
  have h_tend1 : Filter.Tendsto (fun n => (xn n).1) Filter.atTop (nhds x.1) :=
    (continuous_fst.tendsto x).comp h_tendsto
  have h_tend2 : Filter.Tendsto (fun n => (xn n).2) Filter.atTop (nhds x.2) :=
    (continuous_snd.tendsto x).comp h_tendsto
  have h_tendsto_left : Filter.Tendsto (fun k => γ.val • (xn (φ k)).1) Filter.atTop
      (nhds (γ.val • x.1)) :=
    (h_cont.tendsto _).comp (h_tend1.comp hφ_mono.tendsto_atTop)
  have h_tendsto_right : Filter.Tendsto (fun k => (xn (φ k)).2) Filter.atTop (nhds x.2) :=
    h_tend2.comp hφ_mono.tendsto_atTop
  -- For each k: γ.val • (xn (φ k)).1 = (xn (φ k)).2.
  have h_eq_seq : ∀ k, γ.val • (xn (φ k)).1 = (xn (φ k)).2 := by
    intro k
    have hk_in : φ k ∈ {n | N ≤ n ∧ (⟨γn n, hγn_in n⟩ : ↥(CongruenceSubgroup.Gamma 2)) = γ} :=
      hφ_in k
    have h_γ_eq : γn (φ k) = γ.val := by
      have := hk_in.2
      exact congrArg Subtype.val this
    rw [← h_γ_eq]
    exact hγn_eq (φ k)
  have h_replace : (fun k => γ.val • (xn (φ k)).1) = (fun k => (xn (φ k)).2) :=
    funext h_eq_seq
  rw [h_replace] at h_tendsto_left
  exact tendsto_nhds_unique h_tendsto_left h_tendsto_right

/-- **Density of upper `λ`-fibre at the boundary.** For
`(τ₁, τ₂) ∈ ℍ × ℍ` with `λ(τ₁) = λ(τ₂)` and `Im(λ τ₁) = 0` (the
boundary case), every neighbourhood of `(τ₁, τ₂)` in `ℍ × ℍ`
contains some `(τ₁', τ₂')` with `λ(τ₁') = λ(τ₂')` and
`Im(λ τ₁') > 0`. Proof: the open mapping theorem
(`AnalyticAt.eventually_constant_or_nhds_le_map_nhds` applied to `λ`
at `τ₁, τ₂`) gives `λ(D₁) ∩ λ(D₂)` as a neighbourhood of
`λ(τ₁) = λ(τ₂)` for any small balls `D₁, D₂`. With `Im λ τ₁ = 0`,
the open neighbourhood intersects `{Im > 0}`; pick `v` there and
pull back to `τ₁' ∈ D₁`, `τ₂' ∈ D₂`. -/
theorem modularLambdaH_eq_fibre_dense_in_im_lambda_pos
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_zero : (modularLambdaH (τ₁ : ℂ)).im = 0)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ))
    (U : Set (UpperHalfPlane × UpperHalfPlane))
    (hU : U ∈ nhds (τ₁, τ₂)) :
    ∃ p ∈ U, modularLambdaH (p.1 : ℂ) = modularLambdaH (p.2 : ℂ) ∧
      0 < (modularLambdaH (p.1 : ℂ)).im := by
  -- Get product nhd V₁ ×ˢ V₂ ⊆ U.
  obtain ⟨V₁, hV₁, V₂, hV₂, hV_sub⟩ := mem_nhds_prod_iff.mp hU
  -- Set H := {z : ℂ | 0 < z.im}, open.
  set H : Set ℂ := {z : ℂ | 0 < z.im} with hH_def
  have hH_open : IsOpen H := by
    have : H = Complex.im ⁻¹' Set.Ioi 0 := by ext; simp [hH_def]
    rw [this]; exact isOpen_Ioi.preimage Complex.continuous_im
  have hH_preconn : IsPreconnected H := by
    apply Convex.isPreconnected
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
  -- λ is analytic on H.
  have h_lam_analytic : AnalyticOnNhd ℂ modularLambdaH H :=
    modularLambdaH_differentiableOn.analyticOnNhd hH_open
  -- λ has different values: 1+i and 2+i are both in image (in ℂ ∖ {0, 1}).
  have h_lam_not_const : ¬ Set.EqOn modularLambdaH (fun _ => modularLambdaH (τ₁ : ℂ)) H := by
    intro h_eqOn
    -- Use modularLambdaH_image to find τ_a, τ_b with different λ-values.
    have h_1i_in : (1 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
      refine ⟨?_, ?_⟩
      · intro h; have := congrArg Complex.im h; simp at this
      · intro h; have := congrArg Complex.im h; simp at this
    have h_2i_in : (2 + Complex.I : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
      refine ⟨?_, ?_⟩
      · intro h; have := congrArg Complex.im h; simp at this
      · intro h; have := congrArg Complex.re h; simp at this
    have h_1i_img : (1 + Complex.I : ℂ) ∈ modularLambdaH '' H := by
      rw [modularLambdaH_image]; exact h_1i_in
    have h_2i_img : (2 + Complex.I : ℂ) ∈ modularLambdaH '' H := by
      rw [modularLambdaH_image]; exact h_2i_in
    obtain ⟨τ_a, hτ_a_H, hτ_a_eq⟩ := h_1i_img
    obtain ⟨τ_b, hτ_b_H, hτ_b_eq⟩ := h_2i_img
    have h_eq_a : modularLambdaH τ_a = modularLambdaH (τ₁ : ℂ) := h_eqOn hτ_a_H
    have h_eq_b : modularLambdaH τ_b = modularLambdaH (τ₁ : ℂ) := h_eqOn hτ_b_H
    have : (1 + Complex.I : ℂ) = (2 + Complex.I : ℂ) := by
      rw [← hτ_a_eq, ← hτ_b_eq, h_eq_a, h_eq_b]
    have h_re := congrArg Complex.re this
    simp at h_re
  -- λ is not eventually constant at (τ₁ : ℂ).
  have hτ₁_in_H : (τ₁ : ℂ) ∈ H := τ₁.2
  have hτ₂_in_H : (τ₂ : ℂ) ∈ H := τ₂.2
  have h_not_evt_const_at_τ₁ : ¬ (∀ᶠ z in nhds (τ₁ : ℂ),
      modularLambdaH z = modularLambdaH (τ₁ : ℂ)) := by
    intro h_evt
    apply h_lam_not_const
    exact h_lam_analytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hH_preconn
      hτ₁_in_H h_evt
  have h_not_evt_const_at_τ₂ : ¬ (∀ᶠ z in nhds (τ₂ : ℂ),
      modularLambdaH z = modularLambdaH (τ₂ : ℂ)) := by
    intro h_evt
    apply h_lam_not_const
    have h_lam_analytic_const : AnalyticOnNhd ℂ (fun _ => modularLambdaH (τ₁ : ℂ)) H :=
      analyticOnNhd_const
    -- λ =ᶠ const-at-τ₂ at τ₂, but const-at-τ₂ = const-at-τ₁ (h_eq).
    have h_evt' : ∀ᶠ z in nhds (τ₂ : ℂ), modularLambdaH z = modularLambdaH (τ₁ : ℂ) := by
      filter_upwards [h_evt] with z hz
      rw [hz]; exact h_eq.symm
    exact h_lam_analytic.eqOn_of_preconnected_of_eventuallyEq h_lam_analytic_const hH_preconn
      hτ₂_in_H h_evt'
  -- Apply open mapping at τ₁ and τ₂.
  have h_lam_at_τ₁ : AnalyticAt ℂ modularLambdaH (τ₁ : ℂ) :=
    h_lam_analytic _ hτ₁_in_H
  have h_lam_at_τ₂ : AnalyticAt ℂ modularLambdaH (τ₂ : ℂ) :=
    h_lam_analytic _ hτ₂_in_H
  have h_open_τ₁ : nhds (modularLambdaH (τ₁ : ℂ)) ≤ Filter.map modularLambdaH (nhds (τ₁ : ℂ)) :=
    (h_lam_at_τ₁.eventually_constant_or_nhds_le_map_nhds).resolve_left h_not_evt_const_at_τ₁
  have h_open_τ₂ : nhds (modularLambdaH (τ₂ : ℂ)) ≤ Filter.map modularLambdaH (nhds (τ₂ : ℂ)) :=
    (h_lam_at_τ₂.eventually_constant_or_nhds_le_map_nhds).resolve_left h_not_evt_const_at_τ₂
  -- Bridge V_i to nhd in ℂ via open embedding.
  have hW₁_nhd : ((↑) : UpperHalfPlane → ℂ) '' V₁ ∈ nhds (τ₁ : ℂ) :=
    (UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq τ₁).symm ▸ Filter.image_mem_map hV₁
  have hW₂_nhd : ((↑) : UpperHalfPlane → ℂ) '' V₂ ∈ nhds (τ₂ : ℂ) :=
    (UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq τ₂).symm ▸ Filter.image_mem_map hV₂
  -- λ(W_i) is a nhd of λ τ_i.
  have h_lamW₁_nhd : modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₁) ∈
      nhds (modularLambdaH (τ₁ : ℂ)) :=
    h_open_τ₁ (Filter.image_mem_map hW₁_nhd)
  have h_lamW₂_nhd : modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₂) ∈
      nhds (modularLambdaH (τ₂ : ℂ)) :=
    h_open_τ₂ (Filter.image_mem_map hW₂_nhd)
  -- λ(W₁) ∩ λ(W₂) is a nhd of λ τ_1 (= λ τ_2).
  have h_inter_nhd :
      modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₁) ∩
        modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₂) ∈
      nhds (modularLambdaH (τ₁ : ℂ)) := by
    have h_lamW₂_nhd' : modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₂) ∈
        nhds (modularLambdaH (τ₁ : ℂ)) := h_eq ▸ h_lamW₂_nhd
    exact Filter.inter_mem h_lamW₁_nhd h_lamW₂_nhd'
  -- {Im > 0} ∩ (nhd of λ τ_1) is non-empty since Im(λ τ_1) = 0.
  have h_im_pos_nhd : ∃ v ∈ modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₁) ∩
        modularLambdaH '' (((↑) : UpperHalfPlane → ℂ) '' V₂), 0 < v.im := by
    -- Take open ball around λ τ_1 small enough inside the inter nhd; pick a point with Im > 0.
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.mem_nhds_iff.mp h_inter_nhd
    refine ⟨modularLambdaH (τ₁ : ℂ) + (ε/2 : ℝ) * Complex.I, ?_, ?_⟩
    · apply hε_ball
      rw [Metric.mem_ball, dist_self_add_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε/2)]
      linarith
    · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, h_im_zero]
      linarith
  obtain ⟨v, hv_inter, hv_im⟩ := h_im_pos_nhd
  -- Pull back v to τ_1' ∈ V_1 and τ_2' ∈ V_2.
  obtain ⟨hv₁_in, hv₂_in⟩ := hv_inter
  obtain ⟨z₁, ⟨τ₁', hτ₁'_V, rfl⟩, h_lam_z₁⟩ := hv₁_in
  obtain ⟨z₂, ⟨τ₂', hτ₂'_V, rfl⟩, h_lam_z₂⟩ := hv₂_in
  -- The witness pair.
  refine ⟨(τ₁', τ₂'), hV_sub ⟨hτ₁'_V, hτ₂'_V⟩, ?_, ?_⟩
  · change modularLambdaH (τ₁' : ℂ) = modularLambdaH (τ₂' : ℂ)
    rw [h_lam_z₁, h_lam_z₂]
  · change 0 < (modularLambdaH (τ₁' : ℂ)).im
    rw [h_lam_z₁]; exact hv_im

/-- **Pillar-4 boundary branch (Im λ = 0).** For `τ₁, τ₂ ∈ ℍ` with
`Im(λ τ₁) = 0` and `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`. Closes via density (`modularLambdaH_eq_fibre_dense_in_im_lambda_pos`)
of the upper `λ`-fibre + closedness of the orbit relation
(`gamma2_orbitRel_isClosed`) + the upper branch
`gamma2_lambda_eq_implies_orbit_when_im_lambda_pos`. -/
theorem gamma2_lambda_eq_implies_orbit_when_im_lambda_zero
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_zero : (modularLambdaH (τ₁ : ℂ)).im = 0)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  -- The orbit relation R, the target set of (τ₁, τ₂).
  set R : Set (UpperHalfPlane × UpperHalfPlane) :=
    { p | ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • p.1 = p.2 } with hR_def
  change (τ₁, τ₂) ∈ R
  have hR_closed : IsClosed R := gamma2_orbitRel_isClosed
  rw [← hR_closed.closure_eq, mem_closure_iff_nhds]
  intro U hU
  obtain ⟨p, hp_U, hp_eq, hp_im⟩ :=
    modularLambdaH_eq_fibre_dense_in_im_lambda_pos h_im_zero h_eq U hU
  exact ⟨p, hp_U, gamma2_lambda_eq_implies_orbit_when_im_lambda_pos hp_im hp_eq⟩

/-- **Pillar-4 LHP-and-boundary branch.** Combination of the
`Im(λ) < 0` and `Im(λ) = 0` cases. -/
theorem gamma2_lambda_eq_implies_orbit_when_im_lambda_non_pos
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_le : (modularLambdaH (τ₁ : ℂ)).im ≤ 0)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  rcases lt_or_eq_of_le h_im_le with h_lt | h_eq_zero
  · exact gamma2_lambda_eq_implies_orbit_when_im_lambda_neg h_lt h_eq
  · exact gamma2_lambda_eq_implies_orbit_when_im_lambda_zero h_eq_zero h_eq

/-! ## Pillar 3, main statement: `λ′ ≠ 0` on `ℍ` -/

/-- **Pillar 3: `λ'(τ) ≠ 0` for every `τ ∈ ℍ`.** Case split on the
sign of `Im(λ τ)`. -/
theorem modularLambdaH_deriv_ne_zero_on_upperHalf
    {τ : ℂ} (hτ : 0 < τ.im) :
    deriv modularLambdaH τ ≠ 0 := by
  rcases le_or_gt (modularLambdaH τ).im 0 with h_im_le | h_im_pos
  · exact modularLambdaH_deriv_ne_zero_when_im_lambda_non_pos hτ h_im_le
  · exact modularLambdaH_deriv_ne_zero_when_im_lambda_pos hτ h_im_pos

/-! ## Pillar 4, main statement: `λ` separates `Γ(2)`-orbits -/

/-- **Pillar 4: `λ` separates `Γ(2)`-orbits.** Case split on the
sign of `Im(λ τ₁)` (which equals `Im(λ τ₂)` by hypothesis). -/
theorem modularLambdaH_eq_iff_gamma2_orbit
    {τ₁ τ₂ : UpperHalfPlane} :
    modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ) ↔
      ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  constructor
  · intro h_eq
    rcases le_or_gt (modularLambdaH (τ₁ : ℂ)).im 0 with h_im_le | h_im_pos
    · exact gamma2_lambda_eq_implies_orbit_when_im_lambda_non_pos h_im_le h_eq
    · exact gamma2_lambda_eq_implies_orbit_when_im_lambda_pos h_im_pos h_eq
  · rintro ⟨γ, hγ_in, h_eq⟩
    rw [← h_eq]
    exact (modularLambdaH_gamma2_invariant γ hγ_in τ₁).symm

/-! ## The covering-map assembly

The route to `IsCoveringMapOn modularLambdaH {w | w ≠ 0 ∧ w ≠ 1}`:

1. **Junk values** (`theta3_eq_zero_of_im_nonpos`,
   `modularLambdaH_eq_zero_of_im_nonpos`): off `ℍ`, the theta series
   is non-summable, `tsum` returns `0`, and `λ` collapses to the junk
   value `0`, which the base set excludes. Hence preimages of base
   neighborhoods stay inside `ℍ`.
2. **The faithful quotient** `Γ(2)/{±1}` (`Gamma2PMOne`,
   `gamma2QuotMulAction`): `−I ∈ Γ(2)` acts trivially on `ℍ`, so the
   matrix group itself never acts freely; the action descends to the
   quotient by `zpowers (−I)`, where Pillar 1 makes every stabilizer
   trivial. Pillar 2 (proper discontinuity) and continuity transfer
   along the projection.
3. **The `ℍ`-level covering** (`modularLambdaHRestrict_*`): the
   corestriction `λ : ℍ → {w // w ≠ 0 ∧ w ≠ 1}` is a quotient map
   (continuous + open by the nonvanishing derivative, Pillar 3 +
   surjective by `modularLambdaH_image`), identifies fibres with
   quotient orbits (Pillar 4), and Mathlib's
   `IsQuotientMap.isCoveringMapOn_of_properlyDiscontinuousSMul`
   yields the covering on the full base.
4. **Transport** (`modularLambdaH_isEvenlyCovered`): each subtype
   trivialization is conjugated by the open embeddings
   `ℍ ↪ ℂ` and `{w // w ≠ 0 ∧ w ≠ 1} ↪ ℂ` into a trivialization of
   the bare `modularLambdaH : ℂ → ℂ`, using step 1 to identify the
   `ℂ`-level preimage of the base set with the `ℍ`-level one. -/

/-- **Junk value of `θ₃` off `ℍ`.** For `Im τ ≤ 0` the series
`∑' n : ℤ, cexp (π i n² τ)` has terms of norm `exp (−π n² Im τ) ≥ 1`,
hence is not summable, and `tsum` returns `0`. -/
theorem theta3_eq_zero_of_im_nonpos {τ : ℂ} (hτ : τ.im ≤ 0) :
    theta3 τ = 0 := by
  unfold theta3 jacobiTheta
  apply tsum_eq_zero_of_not_summable
  intro hs
  have htend := hs.tendsto_cofinite_zero
  have hev : ∀ᶠ n : ℤ in Filter.cofinite,
      ‖Complex.exp (↑Real.pi * Complex.I * (n : ℂ) ^ 2 * τ)‖ < 1 := by
    filter_upwards [htend.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with n hn
    simpa [Metric.mem_ball, dist_zero_right] using hn
  obtain ⟨n, hn⟩ := hev.exists
  have hge : (1 : ℝ) ≤ ‖Complex.exp (↑Real.pi * Complex.I * (n : ℂ) ^ 2 * τ)‖ := by
    rw [Complex.norm_exp]
    apply Real.one_le_exp
    have h1 : (↑Real.pi * Complex.I * (n : ℂ) ^ 2 * τ)
        = ((Real.pi * (n : ℝ) ^ 2 : ℝ) : ℂ) * (Complex.I * τ) := by
      push_cast; ring
    rw [h1, Complex.re_ofReal_mul]
    have h2 : (Complex.I * τ).re = -τ.im := by
      simp [Complex.mul_re]
    rw [h2]
    have h3 : (0 : ℝ) ≤ Real.pi * (n : ℝ) ^ 2 := by positivity
    nlinarith
  linarith

/-- **Junk value of `λ` off `ℍ`.** With `θ₃ τ = 0`, the quotient
`θ₂⁴/θ₃⁴` is a division by zero, hence `0`. -/
theorem modularLambdaH_eq_zero_of_im_nonpos {τ : ℂ} (hτ : τ.im ≤ 0) :
    modularLambdaH τ = 0 := by
  unfold modularLambdaH
  rw [theta3_eq_zero_of_im_nonpos hτ]
  simp

/-- `−I ∈ Γ(2)`: all four entries are congruent to those of `I`
modulo `2`. -/
theorem gamma2_neg_one_mem :
    (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- **`−I` acts trivially on `ℍ`.** The Möbius action of `−I` is
`τ ↦ (−τ + 0)/(0 − 1) = τ`. -/
theorem sl2z_neg_one_smul (τ : UpperHalfPlane) :
    (-1 : SL(2, ℤ)) • τ = τ := by
  apply UpperHalfPlane.ext
  rw [sl2z_smul_coe]
  have h00 : ((-1 : SL(2, ℤ)) 0 0 : ℤ) = -1 := by simp
  have h01 : ((-1 : SL(2, ℤ)) 0 1 : ℤ) = 0 := by simp
  have h10 : ((-1 : SL(2, ℤ)) 1 0 : ℤ) = 0 := by simp
  have h11 : ((-1 : SL(2, ℤ)) 1 1 : ℤ) = -1 := by simp
  rw [h00, h01, h10, h11]
  push_cast
  ring

/-- **Elements of `zpowers (−I)` act trivially on `ℍ`.** `(−I)^k` is
`I` or `−I` by parity, and both act trivially. -/
theorem gamma2PMOne_smul_eq
    (z : ↥(CongruenceSubgroup.Gamma 2))
    (hz : z ∈ Subgroup.zpowers
      (⟨-1, gamma2_neg_one_mem⟩ : ↥(CongruenceSubgroup.Gamma 2)))
    (τ : UpperHalfPlane) : z • τ = τ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← hk]
  change ((((⟨-1, gamma2_neg_one_mem⟩ : ↥(CongruenceSubgroup.Gamma 2)) ^ k :
      ↥(CongruenceSubgroup.Gamma 2)) : SL(2, ℤ))) • τ = τ
  rw [SubgroupClass.coe_zpow]
  change ((-1 : SL(2, ℤ)) ^ k) • τ = τ
  rcases Int.even_or_odd k with hk' | hk'
  · rw [hk'.neg_one_zpow, one_smul]
  · obtain ⟨m, rfl⟩ := hk'
    rw [zpow_add_one, (even_two_mul m).neg_one_zpow, one_mul]
    exact sl2z_neg_one_smul τ

/-- The central subgroup `{±I}` of `Γ(2)`, as the integer powers of
`−I`. The quotient `Γ(2)/{±I}` is the group that acts freely on `ℍ`. -/
def Gamma2PMOne : Subgroup ↥(CongruenceSubgroup.Gamma 2) :=
  Subgroup.zpowers ⟨-1, gamma2_neg_one_mem⟩

/-- `{±I}` is normal in `Γ(2)`: `−I` is central in `SL(2, ℤ)`. -/
instance gamma2PMOne_normal : (Gamma2PMOne).Normal := by
  constructor
  intro n hn g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
  rw [← hk]
  -- −I is central in Γ(2)
  have hcomm : Commute (g : ↥(CongruenceSubgroup.Gamma 2))
      (⟨-1, gamma2_neg_one_mem⟩ : ↥(CongruenceSubgroup.Gamma 2)) := by
    apply Subtype.ext
    change ((g : SL(2, ℤ)) * (-1)) = ((-1) * (g : SL(2, ℤ)))
    rw [mul_neg_one, neg_one_mul]
  -- g commutes with (−I)^k, so conjugation is the identity
  have : g * ⟨-1, gamma2_neg_one_mem⟩ ^ k * g⁻¹
      = ⟨-1, gamma2_neg_one_mem⟩ ^ k := by
    rw [(hcomm.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [this]
  exact Subgroup.zpow_mem_zpowers _ k

/-- **The descended action of `Γ(2)/{±I}` on `ℍ`.** Well-defined
because `{±I}` acts trivially (`gamma2PMOne_smul_eq`). -/
noncomputable instance gamma2QuotMulAction :
    MulAction (↥(CongruenceSubgroup.Gamma 2) ⧸ Gamma2PMOne)
      UpperHalfPlane where
  smul q τ := Quotient.liftOn' q (fun γ => γ • τ) (fun γ₁ γ₂ h => by
    rw [QuotientGroup.leftRel_apply] at h
    have hz : (γ₁⁻¹ * γ₂) • τ = τ := gamma2PMOne_smul_eq _ h τ
    calc γ₁ • τ = γ₁ • ((γ₁⁻¹ * γ₂) • τ) := by rw [hz]
      _ = (γ₁ * (γ₁⁻¹ * γ₂)) • τ := (mul_smul _ _ _).symm
      _ = γ₂ • τ := by rw [mul_inv_cancel_left])
  one_smul τ := by
    change Quotient.liftOn' (Quotient.mk'' 1) _ _ = τ
    rw [Quotient.liftOn'_mk'']
    exact one_smul _ τ
  mul_smul q₁ q₂ τ := by
    induction q₁ using Quotient.inductionOn' with
    | h γ₁ =>
      induction q₂ using Quotient.inductionOn' with
      | h γ₂ =>
        change Quotient.liftOn' (Quotient.mk'' (γ₁ * γ₂)) _ _ =
          Quotient.liftOn' (Quotient.mk'' γ₁) _ _
        rw [Quotient.liftOn'_mk'', Quotient.liftOn'_mk'']
        change _ = γ₁ • (Quotient.liftOn' (Quotient.mk'' γ₂) _ _)
        rw [Quotient.liftOn'_mk'']
        exact mul_smul γ₁ γ₂ τ

/-- The descended action computes via any representative. -/
theorem gamma2Quot_mk_smul (γ : ↥(CongruenceSubgroup.Gamma 2))
    (τ : UpperHalfPlane) :
    (QuotientGroup.mk γ :
      ↥(CongruenceSubgroup.Gamma 2) ⧸ Gamma2PMOne) • τ = γ • τ :=
  rfl

/-- **Continuity of the descended action.** Each class acts as some
`γ ∈ Γ(2) ⊆ SL(2, ℝ)`, which acts continuously. -/
instance gamma2Quot_continuousConstSMul :
    ContinuousConstSMul (↥(CongruenceSubgroup.Gamma 2) ⧸ Gamma2PMOne)
      UpperHalfPlane := by
  constructor
  intro q
  induction q using Quotient.inductionOn' with
  | h γ =>
    change Continuous (fun σ : UpperHalfPlane => ((γ.val : SL(2, ℝ)) • σ))
    exact continuous_const_smul _

/-- **Proper discontinuity of the descended action.** The set of
classes moving a compact `K` into a compact `L` is the image under
the projection of the corresponding finite set in `Γ(2)`
(Pillar 2, `gamma_two_properlyDiscontinuousSMul`). -/
instance gamma2Quot_properlyDiscontinuousSMul :
    ProperlyDiscontinuousSMul
      (↥(CongruenceSubgroup.Gamma 2) ⧸ Gamma2PMOne) UpperHalfPlane := by
  constructor
  intro K L hK hL
  have hG2 := gamma_two_properlyDiscontinuousSMul.finite_disjoint_inter_image hK hL
  refine Set.Finite.subset (hG2.image (QuotientGroup.mk :
    ↥(CongruenceSubgroup.Gamma 2) →
      ↥(CongruenceSubgroup.Gamma 2) ⧸ Gamma2PMOne)) ?_
  rintro q hq
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨γ, hq, rfl⟩

/-- **The descended action is free.** A class fixing `τ` lifts to
`γ ∈ Γ(2)` fixing `τ`, hence `γ = ±I` (Pillar 1,
`gamma_two_fixed_point_implies_pm_one`), hence the class is trivial. -/
theorem gamma2Quot_stabilizer_eq_bot (τ : UpperHalfPlane) :
    MulAction.stabilizer
      (↥(CongruenceSubgroup.Gamma 2) ⧸ Gamma2PMOne) τ = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  rw [MulAction.mem_stabilizer_iff] at hq
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
  rw [Subgroup.mem_bot]
  refine (QuotientGroup.eq_one_iff γ).mpr ?_
  have hfix : (γ.val : SL(2, ℤ)) • τ = τ := hq
  rcases gamma_two_fixed_point_implies_pm_one γ.val γ.2 τ hfix with h1 | hneg
  · have hγ : γ = 1 := Subtype.ext h1
    rw [hγ]
    exact Subgroup.one_mem _
  · have hγ : γ = ⟨-1, gamma2_neg_one_mem⟩ := Subtype.ext hneg
    rw [hγ]
    exact Subgroup.mem_zpowers _

/-- **Fibres of `λ` are the orbits of the descended action**
(Pillar 4, `modularLambdaH_eq_iff_gamma2_orbit`, with the existential
inverted to match `MulAction.orbit`). -/
theorem gamma2Quot_orbit_iff {τ₁ τ₂ : UpperHalfPlane} :
    modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ) ↔
      τ₁ ∈ MulAction.orbit
        (↥(CongruenceSubgroup.Gamma 2) ⧸ Gamma2PMOne) τ₂ := by
  rw [modularLambdaH_eq_iff_gamma2_orbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨γ, hmem, heq⟩
    refine ⟨QuotientGroup.mk
      ((⟨γ, hmem⟩ : ↥(CongruenceSubgroup.Gamma 2))⁻¹), ?_⟩
    have h1 : (⟨γ, hmem⟩ : ↥(CongruenceSubgroup.Gamma 2)) • τ₁ = τ₂ := heq
    have h2 : (⟨γ, hmem⟩ : ↥(CongruenceSubgroup.Gamma 2))⁻¹ • τ₂ = τ₁ := by
      rw [inv_smul_eq_iff]
      exact h1.symm
    exact h2
  · rintro ⟨q, heq⟩
    obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : δ • τ₂ = τ₁ := heq
    refine ⟨(δ⁻¹ : ↥(CongruenceSubgroup.Gamma 2)).val, (δ⁻¹).2, ?_⟩
    have h2 : δ⁻¹ • τ₁ = τ₂ := by
      rw [inv_smul_eq_iff]
      exact h1.symm
    exact h2

/-- The corestriction of `λ` to `ℍ → ℂ ∖ {0, 1}`, the map whose
covering property is established at the subtype level before being
transported to the bare `modularLambdaH : ℂ → ℂ`. -/
noncomputable def modularLambdaHRestrict
    (τ : UpperHalfPlane) : { w : ℂ // w ≠ 0 ∧ w ≠ 1 } :=
  ⟨modularLambdaH (τ : ℂ),
    modularLambdaH_ne_zero τ.2, modularLambdaH_ne_one τ.2⟩

/-- **Continuity of the corestriction:** `λ` is differentiable on the
open set `ℍ` (`modularLambdaH_differentiableAt_of_im_pos`). -/
theorem modularLambdaHRestrict_continuous :
    Continuous modularLambdaHRestrict := by
  have h : Continuous fun τ : UpperHalfPlane => modularLambdaH (τ : ℂ) := by
    rw [continuous_iff_continuousAt]
    intro τ
    exact (modularLambdaH_differentiableAt_of_im_pos τ.2).continuousAt.comp
      UpperHalfPlane.continuous_coe.continuousAt
  exact h.subtype_mk _

/-- **Openness of the corestriction.** At every `τ ∈ ℍ`, `λ` is
analytic with `λ'(τ) ≠ 0` (Pillar 3), so it maps neighborhoods onto
neighborhoods (`HasStrictDerivAt.map_nhds_eq`). -/
theorem modularLambdaHRestrict_isOpenMap :
    IsOpenMap modularLambdaHRestrict := by
  intro U hU
  have hopen_coe : IsOpen (UpperHalfPlane.coe '' U) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU
  have hsub : UpperHalfPlane.coe '' U ⊆ { z : ℂ | 0 < z.im } := by
    rintro z ⟨τ, hτ, rfl⟩
    exact τ.2
  have hopen_img : IsOpen (modularLambdaH '' (UpperHalfPlane.coe '' U)) := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨z, hzU, rfl⟩
    have him : 0 < z.im := hsub hzU
    have hA : AnalyticAt ℂ modularLambdaH z := by
      refine DifferentiableOn.analyticAt (s := { z : ℂ | 0 < z.im })
        (fun z' hz' =>
          (modularLambdaH_differentiableAt_of_im_pos hz').differentiableWithinAt) ?_
      exact (isOpen_lt continuous_const Complex.continuous_im).mem_nhds him
    have hmap : Filter.map modularLambdaH (nhds z) = nhds (modularLambdaH z) :=
      hA.hasStrictDerivAt.map_nhds_eq (modularLambdaH_deriv_ne_zero_on_upperHalf him)
    rw [← hmap]
    exact Filter.image_mem_map (hopen_coe.mem_nhds hzU)
  have hset : modularLambdaHRestrict '' U =
      Subtype.val ⁻¹' (modularLambdaH '' (UpperHalfPlane.coe '' U)) := by
    ext s
    constructor
    · rintro ⟨τ, hτU, rfl⟩
      exact ⟨(τ : ℂ), ⟨τ, hτU, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨τ, hτU, rfl⟩, hval⟩
      exact ⟨τ, hτU, Subtype.ext hval⟩
  rw [hset]
  exact hopen_img.preimage continuous_subtype_val

/-- **Surjectivity of the corestriction**, from the image computation
`modularLambdaH_image`. -/
theorem modularLambdaHRestrict_surjective :
    Function.Surjective modularLambdaHRestrict := by
  intro w
  have hmem : (w : ℂ) ∈ { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := ⟨w.2.1, w.2.2⟩
  rw [← modularLambdaH_image] at hmem
  obtain ⟨τc, hτ_im, heq⟩ := hmem
  exact ⟨⟨τc, hτ_im⟩, Subtype.ext heq⟩

/-- The corestriction is a quotient map: continuous, open,
surjective. -/
theorem modularLambdaHRestrict_isQuotientMap :
    Topology.IsQuotientMap modularLambdaHRestrict :=
  modularLambdaHRestrict_isOpenMap.isQuotientMap
    modularLambdaHRestrict_continuous modularLambdaHRestrict_surjective

/-- **The `ℍ`-level covering.** Mathlib's
`IsQuotientMap.isCoveringMapOn_of_properlyDiscontinuousSMul` applied
to the free, properly discontinuous action of `Γ(2)/{±I}`; the
trivial-stabilizer set is all of `ℍ` and its image is the whole base
by surjectivity. -/
theorem modularLambdaHRestrict_isCoveringMapOn :
    IsCoveringMapOn modularLambdaHRestrict Set.univ := by
  have hfG : ∀ {e₁ e₂ : UpperHalfPlane},
      modularLambdaHRestrict e₁ = modularLambdaHRestrict e₂ ↔
        e₁ ∈ MulAction.orbit
          (↥(CongruenceSubgroup.Gamma 2) ⧸ Gamma2PMOne) e₂ :=
    fun {e₁ e₂} => Subtype.ext_iff.trans gamma2Quot_orbit_iff
  have h :=
    modularLambdaHRestrict_isQuotientMap.isCoveringMapOn_of_properlyDiscontinuousSMul hfG
  have hstab : { e : UpperHalfPlane |
      MulAction.stabilizer
        (↥(CongruenceSubgroup.Gamma 2) ⧸ Gamma2PMOne) e = ⊥ } = Set.univ :=
    Set.eq_univ_iff_forall.mpr gamma2Quot_stabilizer_eq_bot
  rw [hstab, Set.image_univ, modularLambdaHRestrict_surjective.range_eq] at h
  exact h

/-- **Transport of the evenly-covered property to `ℂ`.** The subtype
trivialization through `w` is conjugated by the open embeddings
`ℍ ↪ ℂ` (domain) and `{w // w ≠ 0 ∧ w ≠ 1} ↪ ℂ` (base) into a
trivialization of `modularLambdaH : ℂ → ℂ`; the junk-value lemma
keeps the `ℂ`-level preimage of the base set inside `ℍ`. -/
theorem modularLambdaH_isEvenlyCovered {w : ℂ}
    (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    IsEvenlyCovered modularLambdaH w (modularLambdaH ⁻¹' {w}) := by
  -- The base set is open.
  have hS_open : IsOpen {w : ℂ | w ≠ 0 ∧ w ≠ 1} := by
    rw [Set.ofPred_and]
    exact isOpen_ne.inter isOpen_ne
  -- By the junk-value lemma, the ℂ-level preimage of the base set is exactly ℍ.
  have hpre : modularLambdaH ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} = {z : ℂ | 0 < z.im} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h0, -⟩
      by_contra hz
      exact h0 (modularLambdaH_eq_zero_of_im_nonpos (not_lt.mp hz))
    · intro hz
      exact ⟨modularLambdaH_ne_zero hz, modularLambdaH_ne_one hz⟩
  have hpre_open : IsOpen (modularLambdaH ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1}) := by
    rw [hpre]
    exact isOpen_lt continuous_const Complex.continuous_im
  -- The preimage subtype is canonically homeomorphic to `UpperHalfPlane`.
  have him : ∀ e : (modularLambdaH ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} : Set ℂ),
      0 < (e : ℂ).im := by
    intro e
    exact (Set.ext_iff.mp hpre _).mp e.2
  have hmem : ∀ τ : UpperHalfPlane,
      (τ : ℂ) ∈ modularLambdaH ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} := by
    intro τ
    rw [hpre]
    exact τ.2
  let g : (modularLambdaH ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} : Set ℂ) ≃ₜ UpperHalfPlane :=
    { toFun := fun e => ⟨(e : ℂ), him e⟩
      invFun := fun τ => ⟨(τ : ℂ), hmem τ⟩
      left_inv := fun e => rfl
      right_inv := fun τ => rfl
      continuous_toFun := by
        rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
        exact continuous_subtype_val
      continuous_invFun := UpperHalfPlane.continuous_coe.subtype_mk hmem }
  -- Transport the ℍ-level covering through `g` to the restriction of the bare map.
  have hrestrict : IsCoveringMap
      (Set.restrictPreimage {w : ℂ | w ≠ 0 ∧ w ≠ 1} modularLambdaH) := by
    rw [isCoveringMap_iff_isCoveringMapOn_univ]
    exact modularLambdaHRestrict_isCoveringMapOn.comp_homeomorph g
  -- Undo the restriction on both sides using openness of base set and preimage.
  have hcov : IsCoveringMapOn modularLambdaH {w : ℂ | w ≠ 0 ∧ w ≠ 1} :=
    IsCoveringMapOn.of_isCoveringMap_restrictPreimage _ hS_open hpre_open hrestrict
  exact hcov w ⟨hw0, hw1⟩

/-! ## Main theorems: `λ` is a covering map of the triply-punctured plane -/

/-- **Covering map property of `λ : ℍ → ℂ ∖ {0, 1}`.**

The source space here is `ℂ` (since `modularLambdaH : ℂ → ℂ`), not `ℍ`,
yet the statement is mathematically correct. Off `ℍ` the defining series
`theta3 τ = ∑' n, cexp (π·i·n²·τ)` is non-summable, so Mathlib's `tsum`
returns `0` and the division `theta2 τ ^ 4 / theta3 τ ^ 4` yields the
junk value `0`. Since the base set explicitly excludes `0`, the preimage
of any small `U` around a point `w ∈ {w | w ≠ 0 ∧ w ≠ 1}` cannot contain
any `τ ∉ ℍ`, so `f⁻¹ U ⊆ ℍ`. Because `ℍ` is open in `ℂ`, the subspace
topology on `f⁻¹ U` from `ℂ` agrees with that from `ℍ`, and the standard
covering-map property of `λ : ℍ → ℂ ∖ {0, 1}` transports verbatim. -/
theorem modularLambdaH_isCoveringMapOn :
    IsCoveringMapOn modularLambdaH { w : ℂ | w ≠ 0 ∧ w ≠ 1 } :=
  fun _ hw => modularLambdaH_isEvenlyCovered hw.1 hw.2

/-- **The Cayley image of the disk exterior has nonpositive imaginary
part.** By `cayleyToHalfPlane_im`, the imaginary part is
`(1 − ‖z‖²)/‖1 − z‖²`, whose numerator is nonpositive for `‖z‖ ≥ 1`
(the `z = 1` division-by-zero case yields `0`). -/
theorem cayleyToHalfPlane_im_nonpos_of_not_mem_ball {z : ℂ}
    (hz : z ∉ Metric.ball (0 : ℂ) 1) :
    (cayleyToHalfPlane z).im ≤ 0 := by
  rw [cayleyToHalfPlane_im]
  have hz1 : 1 ≤ ‖z‖ := by
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hz
    exact hz
  have hnum : 1 - ‖z‖ ^ 2 ≤ 0 := by nlinarith
  exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg _)

/-- **Junk value of the disk-level `λ` off `𝔻`.** The Cayley image has
nonpositive imaginary part, where `modularLambdaH` takes the junk
value `0`. -/
theorem modularLambda_eq_zero_of_not_mem_ball {z : ℂ}
    (hz : z ∉ Metric.ball (0 : ℂ) 1) :
    modularLambda z = 0 := by
  exact modularLambdaH_eq_zero_of_im_nonpos
    (cayleyToHalfPlane_im_nonpos_of_not_mem_ball hz)

/-- **Covering property of `λ` on the unit disk.**

Same source-topology subtlety as `modularLambdaH_isCoveringMapOn`: the
Cayley transform composition `modularLambda := modularLambdaH ∘
cayleyToHalfPlane` is typed as `ℂ → ℂ`, but the junk value off `𝔻` lands
on the excluded point `0` (`modularLambda_eq_zero_of_not_mem_ball`), so
the `ℂ`-level preimage of the base set is exactly `𝔻`. The restriction
of `modularLambda` over the base set is the restriction of
`modularLambdaH` conjugated by the Cayley homeomorphism
`𝔻 ≃ₜ {Im > 0}` (`cayleyToHalfPlane`/`halfPlaneToCayley`), so the
covering property transports through
`IsCoveringMapOn.of_isCoveringMap_restrictPreimage`. -/
theorem modularLambda_isCoveringMapOn :
    IsCoveringMapOn modularLambda { w : ℂ | w ≠ 0 ∧ w ≠ 1 } := by
  -- The base set is open.
  have hS_open : IsOpen {w : ℂ | w ≠ 0 ∧ w ≠ 1} := by
    rw [Set.ofPred_and]
    exact isOpen_ne.inter isOpen_ne
  -- By the junk-value lemma, the ℂ-level preimage of the base set is exactly 𝔻.
  have hpre : modularLambda ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} = Metric.ball (0 : ℂ) 1 := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h0, -⟩
      by_contra hz
      exact h0 (modularLambda_eq_zero_of_not_mem_ball hz)
    · intro hz
      have him := cayleyToHalfPlane_im_pos hz
      exact ⟨modularLambdaH_ne_zero him, modularLambdaH_ne_one him⟩
  have hpre_open : IsOpen (modularLambda ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1}) := by
    rw [hpre]
    exact Metric.isOpen_ball
  -- The analogous ℍ-level preimage identity.
  have hpreH : modularLambdaH ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} = {τ : ℂ | 0 < τ.im} := by
    ext τ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h0, -⟩
      by_contra hτ
      exact h0 (modularLambdaH_eq_zero_of_im_nonpos (not_lt.mp hτ))
    · intro hτ
      exact ⟨modularLambdaH_ne_zero hτ, modularLambdaH_ne_one hτ⟩
  -- Membership helpers between the literal preimage subtypes.
  have hball : ∀ e : (modularLambda ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} : Set ℂ),
      (e : ℂ) ∈ Metric.ball (0 : ℂ) 1 :=
    fun e => (Set.ext_iff.mp hpre _).mp e.2
  have himpos : ∀ t : (modularLambdaH ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} : Set ℂ),
      0 < (t : ℂ).im :=
    fun t => (Set.ext_iff.mp hpreH _).mp t.2
  have hmemH : ∀ e : (modularLambda ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} : Set ℂ),
      cayleyToHalfPlane (e : ℂ) ∈ modularLambdaH ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} := by
    intro e
    rw [hpreH]
    exact cayleyToHalfPlane_im_pos (hball e)
  have hmemD : ∀ t : (modularLambdaH ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} : Set ℂ),
      halfPlaneToCayley (t : ℂ) ∈ modularLambda ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} := by
    intro t
    rw [hpre]
    exact halfPlaneToCayley_mem_ball (himpos t)
  -- The Cayley transform as a homeomorphism between the two preimage subtypes.
  let g : (modularLambda ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} : Set ℂ) ≃ₜ
      (modularLambdaH ⁻¹' {w : ℂ | w ≠ 0 ∧ w ≠ 1} : Set ℂ) :=
    { toFun := fun e => ⟨cayleyToHalfPlane (e : ℂ), hmemH e⟩
      invFun := fun t => ⟨halfPlaneToCayley (t : ℂ), hmemD t⟩
      left_inv := fun e =>
        Subtype.ext (halfPlaneToCayley_cayleyToHalfPlane (hball e))
      right_inv := fun t =>
        Subtype.ext (cayleyToHalfPlane_halfPlaneToCayley (himpos t))
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        rw [continuous_iff_continuousAt]
        intro e
        have h_ne : (1 : ℂ) - (e : ℂ) ≠ 0 := one_sub_ne_zero_of_mem_ball (hball e)
        have hC : ContinuousAt cayleyToHalfPlane (e : ℂ) := by
          unfold cayleyToHalfPlane
          exact (continuousAt_const.mul (continuousAt_const.add continuousAt_id)).div
            (continuousAt_const.sub continuousAt_id) h_ne
        exact hC.comp continuous_subtype_val.continuousAt
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        rw [continuous_iff_continuousAt]
        intro t
        have h_ne : (t : ℂ) + Complex.I ≠ 0 := add_I_ne_zero_of_im_pos (himpos t)
        have hC : ContinuousAt halfPlaneToCayley (t : ℂ) := by
          unfold halfPlaneToCayley
          exact (continuousAt_id.sub continuousAt_const).div
            (continuousAt_id.add continuousAt_const) h_ne
        exact hC.comp continuous_subtype_val.continuousAt }
  -- The restriction of the ℍ-level map over the base set is a covering map.
  have hrestrictH : IsCoveringMap
      (Set.restrictPreimage {w : ℂ | w ≠ 0 ∧ w ≠ 1} modularLambdaH) :=
    IsCoveringMapOn.isCoveringMap_restrictPreimage _ modularLambdaH_isCoveringMapOn
  -- The restriction of the disk-level map factors through `g`.
  have hcomp : Set.restrictPreimage {w : ℂ | w ≠ 0 ∧ w ≠ 1} modularLambda =
      (Set.restrictPreimage {w : ℂ | w ≠ 0 ∧ w ≠ 1} modularLambdaH) ∘ g := by
    funext e
    exact Subtype.ext rfl
  have hrestrict : IsCoveringMap
      (Set.restrictPreimage {w : ℂ | w ≠ 0 ∧ w ≠ 1} modularLambda) := by
    rw [hcomp]
    exact hrestrictH.comp_homeomorph g
  exact IsCoveringMapOn.of_isCoveringMap_restrictPreimage _ hS_open hpre_open hrestrict

end NoWanderingDomains
