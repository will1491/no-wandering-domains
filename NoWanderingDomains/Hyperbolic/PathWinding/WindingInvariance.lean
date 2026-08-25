/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.LinearAlgebra.Complex.Module
import NoWanderingDomains.Hyperbolic.WindingNumber.CircleRectangleWinding
import NoWanderingDomains.Hyperbolic.ModularFunction.JacobiIdentity

/-! # Integrality and homotopy invariance of winding indices

Winding indices of closed paths in `ℂ`: integrality of `Complex.pathWindingNumber` for
closed C¹ paths avoiding `w`, parametric continuity of the winding number under a
jointly C¹ homotopy, homotopy invariance in `ℂ \\ {w}`, and the reference computation
that a counterclockwise circle around `w` has winding index `1`. Also contains the
closed contour parameterization `F_Y_boundary_parameterization : ℝ → ℂ` of the `F_Y`
boundary over `[0, 6]` and the FTC bridges identifying the contour integral of
`(z − w)⁻¹` along a C¹ (resp. `ContDiffOn`) path with the boundary difference of a
continuous log lift of `γ − w`.
-/

namespace NoWanderingDomains
open Complex MeasureTheory intervalIntegral

/-- **Closed-path winding index is an integer.** For a `C¹` closed path
`γ : ℝ → ℂ` (with `γ a = γ b`) whose image avoids `w`, the winding
index `Complex.pathWindingNumber γ a b w` is an integer (positive,
negative, or zero).

Hypothesis: `ContDiff ℝ 1 γ` (γ is `C¹` globally on `ℝ`) is the
standard regularity for path-winding theorems. The previous loose
`DifferentiableAt`-only hypothesis was insufficient for the FTC
argument used below.

Proof: define `G(t) := ∫_a^t (γ τ − w)⁻¹ · γ'(τ) dτ` and
`F(t) := (γ(t) − w) · exp(−G(t))`. Use FTC to show
`F(b) − F(a) = ∫_a^b F'(t) dt = 0` (where `F'` is the right-derivative
0 on `Ico a b`). So `F(a) = F(b)`. With `γ(a) = γ(b) ≠ w`, this gives
`exp(−G(b)) = 1`. By `Complex.exp_eq_one_iff`, `G(b) = -m · 2πi` for
some `m : ℤ`. The winding index `(2πi)⁻¹ · G(b) = −m`. -/
theorem pathWindingNumber_isInt_of_closed
    (γ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) (w : ℂ)
    (h_closed : γ a = γ b)
    (h_avoid : ∀ t ∈ Set.Icc a b, γ t ≠ w)
    (hγ_C1 : ContDiff ℝ 1 γ) :
    ∃ n : ℤ, Complex.pathWindingNumber γ a b w = (n : ℂ) := by
  -- Continuity, differentiability, and continuous-derivative consequences of ContDiff 1.
  have hγ_cont : Continuous γ := hγ_C1.continuous
  have hγ_diff : Differentiable ℝ γ := hγ_C1.differentiable (by norm_num)
  have hγ'_cont : Continuous (deriv γ) := hγ_C1.continuous_deriv (by norm_num)
  -- Integrand f, primitive G, target F.
  set f : ℝ → ℂ := fun τ => (γ τ - w)⁻¹ * deriv γ τ with hf_def
  set G : ℝ → ℂ := fun t => ∫ τ in a..t, f τ with hG_def
  set F : ℝ → ℂ := fun t => (γ t - w) * Complex.exp (-G t) with hF_def
  -- f continuous on Icc a b.
  have hf_cont_Icc : ContinuousOn f (Set.Icc a b) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.inv₀
      · exact (hγ_cont.continuousOn).sub continuousOn_const
      · intro t ht
        exact sub_ne_zero.mpr (h_avoid t ht)
    · exact hγ'_cont.continuousOn
  -- f IntervalIntegrable on a..b.
  have hf_intInt : IntervalIntegrable f MeasureTheory.volume a b :=
    hf_cont_Icc.intervalIntegrable_of_Icc hab
  -- G(a) = 0.
  have hG_a : G a = 0 := intervalIntegral.integral_same
  -- G is continuous on Icc a b (primitive of integrable f).
  have hG_cont : ContinuousOn G (Set.Icc a b) := by
    have hf_intOn : MeasureTheory.IntegrableOn f (Set.Icc a b) MeasureTheory.volume :=
      hf_cont_Icc.integrableOn_Icc
    have h := intervalIntegral.continuousOn_primitive hf_intOn
    refine h.congr ?_
    intro x hx
    change (∫ τ in a..x, f τ) = ∫ t in Set.Ioc a x, f t
    exact intervalIntegral.integral_of_le hx.1
  -- F is continuous on Icc a b.
  have hF_cont_Icc : ContinuousOn F (Set.Icc a b) := by
    apply ContinuousOn.mul
    · exact (hγ_cont.continuousOn).sub continuousOn_const
    · -- exp(-G) continuous from G continuous.
      exact (hG_cont.neg).cexp
  -- At each interior t ∈ Ioo a b, G has derivative f t (FTC).
  have hG_hasDeriv : ∀ t ∈ Set.Ioo a b, HasDerivAt G (f t) t := by
    intro t ht
    -- f is continuous at t (since t ∈ Ioo a b ⊆ Icc a b and f continuous on Icc).
    have hf_contAt : ContinuousAt f t := by
      apply hf_cont_Icc.continuousAt
      rw [mem_nhds_iff]
      exact ⟨Set.Ioo a b, Set.Ioo_subset_Icc_self, isOpen_Ioo, ht⟩
    -- f StronglyMeasurableAtFilter (nhds t).
    have hf_meas : StronglyMeasurableAtFilter f (nhds t) MeasureTheory.volume := by
      refine ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo a b) isOpen_Ioo ?_ t ht
      intro x hx
      apply hf_cont_Icc.continuousAt
      rw [mem_nhds_iff]
      exact ⟨Set.Ioo a b, Set.Ioo_subset_Icc_self, isOpen_Ioo, hx⟩
    -- Restrict integrability to a..t.
    have hf_intInt_at : IntervalIntegrable f MeasureTheory.volume a t := by
      apply hf_intInt.mono_set
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le ht.1.le]
      exact Set.Icc_subset_Icc_right ht.2.le
    -- FTC.
    exact intervalIntegral.integral_hasDerivAt_right hf_intInt_at hf_meas hf_contAt
  -- At each interior t, F has derivative 0.
  have hF_hasDeriv : ∀ t ∈ Set.Ioo a b, HasDerivAt F 0 t := by
    intro t ht
    -- γ has derivative deriv γ t at t.
    have hγ_at : HasDerivAt γ (deriv γ t) t := (hγ_diff t).hasDerivAt
    -- γ - w has derivative deriv γ t at t.
    have hγw_at : HasDerivAt (fun s => γ s - w) (deriv γ t) t :=
      hγ_at.sub_const w
    -- -G has derivative -f t at t.
    have hnegG_at : HasDerivAt (fun s => -G s) (-f t) t :=
      (hG_hasDeriv t ht).neg
    -- exp(-G) has derivative exp(-G t) * (-f t) at t.
    have hexp_at : HasDerivAt (fun s => Complex.exp (-G s)) (Complex.exp (-G t) * (-f t)) t :=
      hnegG_at.cexp
    -- F = (γ - w) * exp(-G). Product rule.
    have hF_at : HasDerivAt F
        (deriv γ t * Complex.exp (-G t) + (γ t - w) * (Complex.exp (-G t) * (-f t))) t := by
      simpa only [hF_def] using! hγw_at.fun_mul hexp_at
    -- Simplify the derivative to 0.
    have h_simplify : deriv γ t * Complex.exp (-G t) +
        (γ t - w) * (Complex.exp (-G t) * (-f t)) = 0 := by
      have hf_t : f t = (γ t - w)⁻¹ * deriv γ t := hf_def ▸ rfl
      have hγ_ne : γ t - w ≠ 0 :=
        sub_ne_zero.mpr (h_avoid t (Set.Ioo_subset_Icc_self ht))
      rw [hf_t]
      field_simp
      ring
    rw [← h_simplify]
    exact hF_at
  -- Apply integral_eq_sub_of_hasDeriv_right_of_le with the constant function 0.
  have h_zero_intInt : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) MeasureTheory.volume a b :=
    intervalIntegrable_const
  have hF_deriv_right : ∀ t ∈ Set.Ioo a b, HasDerivWithinAt F 0 (Set.Ioi t) t :=
    fun t ht => (hF_hasDeriv t ht).hasDerivWithinAt
  have h_int_eq : (∫ _ in a..b, (0 : ℂ)) = F b - F a :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hF_cont_Icc hF_deriv_right
      h_zero_intInt
  -- The integral of 0 is 0, so F b = F a.
  rw [intervalIntegral.integral_zero] at h_int_eq
  have hF_a_eq_b : F a = F b := by linear_combination h_int_eq
  -- F a = γ a - w (since G a = 0).
  have hF_a_eq : F a = γ a - w := by
    change (γ a - w) * Complex.exp (-G a) = γ a - w
    rw [hG_a, neg_zero, Complex.exp_zero, mul_one]
  -- F b = (γ a - w) * exp(-G b) (using h_closed).
  have hF_b_eq : F b = (γ a - w) * Complex.exp (-G b) := by
    change (γ b - w) * Complex.exp (-G b) = (γ a - w) * Complex.exp (-G b)
    rw [h_closed]
  -- Combining: (γ a - w) * exp(-G b) = γ a - w.
  have h_eq : (γ a - w) * Complex.exp (-G b) = γ a - w := by
    rw [← hF_b_eq, ← hF_a_eq_b, hF_a_eq]
  -- γ a - w ≠ 0.
  have hγa_ne : γ a - w ≠ 0 :=
    sub_ne_zero.mpr (h_avoid a (Set.left_mem_Icc.mpr hab))
  -- Deduce exp(-G b) = 1.
  have h_exp_eq_one : Complex.exp (-G b) = 1 := by
    have := mul_left_cancel₀ hγa_ne (h_eq.trans (mul_one (γ a - w)).symm)
    exact this
  -- Apply exp_eq_one_iff to get integer m with -G b = m * 2πi.
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h_exp_eq_one
  -- Conclude: pathWindingNumber = -m.
  refine ⟨-m, ?_⟩
  -- Compute pathWindingNumber γ a b w = (2πi)⁻¹ * G b.
  have h_pwn : Complex.pathWindingNumber γ a b w = (2 * Real.pi * Complex.I)⁻¹ * G b := by
    unfold Complex.pathWindingNumber Complex.pathContourIntegral
    rfl
  rw [h_pwn]
  -- -G b = m * 2πi means G b = -m * 2πi.
  have hG_b : G b = -(↑m * (2 * Real.pi * Complex.I)) := by
    have : -G b = ↑m * (2 * Real.pi * Complex.I) := hm
    linear_combination -this
  rw [hG_b]
  -- (2πi)⁻¹ * (-(m * 2πi)) = -m.
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- **Helper: agreement on `Icc a b` for `C¹` paths gives equal winding
numbers.** For `γ₀, γ₁ : ℝ → ℂ` both `C¹` with `γ₀ = γ₁` on `Icc a b`,
the path-winding numbers around any `w` are equal.

Proof uses `intervalIntegral.integral_congr_ae`: the integrands agree
on `Ioo a b` (open subset where neighborhood-derivative agreement gives
equal `deriv` values), which has full measure within `Ioc a b`. -/
theorem pathWindingNumber_congr_of_eqOn_C1
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (w : ℂ)
    (_hγ₀_C1 : ContDiff ℝ 1 γ₀) (_hγ₁_C1 : ContDiff ℝ 1 γ₁)
    (h_eq : ∀ t ∈ Set.Icc a b, γ₀ t = γ₁ t) :
    Complex.pathWindingNumber γ₀ a b w = Complex.pathWindingNumber γ₁ a b w := by
  unfold Complex.pathWindingNumber Complex.pathContourIntegral
  congr 1
  -- The integrands agree on the open set Ioo a b (where the deriv-eq argument applies).
  have h_eqOn : Set.EqOn (fun t => (γ₀ t - w)⁻¹ * deriv γ₀ t)
      (fun t => (γ₁ t - w)⁻¹ * deriv γ₁ t) (Set.Ioo a b) := by
    intro t ht
    have h_eq_nbd : γ₀ =ᶠ[nhds t] γ₁ := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact h_eq s (Set.Ioo_subset_Icc_self hs)
    change (γ₀ t - w)⁻¹ * deriv γ₀ t = (γ₁ t - w)⁻¹ * deriv γ₁ t
    rw [h_eq_nbd.eq_of_nhds, h_eq_nbd.deriv_eq]
  -- Convert to integral equality via integral_congr_ae.
  apply intervalIntegral.integral_congr_ae
  rw [Set.uIoc_of_le hab]
  -- Goal: ∀ᵐ x ∂volume, x ∈ Ioc a b → integrands equal at x.
  -- Strategy: {b}ᶜ is a.e., and on {b}ᶜ ∩ Ioc a b ⊆ Ioo a b the integrands agree.
  have h_compl : ({b} : Set ℝ)ᶜ ∈ MeasureTheory.ae MeasureTheory.volume :=
    MeasureTheory.compl_mem_ae_iff.mpr Real.volume_singleton
  filter_upwards [h_compl] with t ht_ne_b ht_Ioc
  have ht_lt_b : t < b := lt_of_le_of_ne ht_Ioc.2 ht_ne_b
  exact h_eqOn ⟨ht_Ioc.1, ht_lt_b⟩

/-- **Parametric continuity of the winding number.** For a jointly `C¹`
homotopy `H` avoiding `w` on `Icc 0 1 × Icc a b`, the function
`s ↦ pathWindingNumber (H s) a b w` is continuous on `Icc 0 1`.

This is the load-bearing analytic step in the homotopy invariance
proof. The proof globally extends the integrand by replacing the
factor `(H s t - w)⁻¹` with a continuous regularization `ψ(H s t - w)`
that equals the true inverse on a neighborhood of the compact set
`Icc 0 1 × Icc a b` (using a strict positive lower bound `ε` on
`‖H - w‖` over the compact set), and identifies
`deriv (fun u => H s u) t` with the partial Fréchet derivative
`fderiv ℝ (uncurry H) (s, t) (0, 1)`. The extended integrand is
globally jointly continuous in `(s, t) ∈ ℝ × ℝ`, so its parametric
integral is continuous in `s` on `ℝ` by Mathlib's
`continuous_parametric_intervalIntegral_of_continuous`; on `Icc 0 1`
the extended and original integrals coincide. -/
theorem pathWindingNumber_continuous_in_param
    {a b : ℝ} (hab : a ≤ b) (w : ℂ) (H : ℝ → ℝ → ℂ)
    (hH_C1 : ContDiff ℝ 1 (Function.uncurry H))
    (hH_avoid : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc a b, H s t ≠ w) :
    ContinuousOn (fun s => Complex.pathWindingNumber (fun t => H s t) a b w)
      (Set.Icc (0 : ℝ) 1) := by
  -- Properties of uncurry H from ContDiff ℝ 1.
  have h_one_ne_zero : (1 : WithTop ℕ∞) ≠ 0 := by decide
  have h_diff : Differentiable ℝ (Function.uncurry H) := hH_C1.differentiable h_one_ne_zero
  have h_fderiv_cont : Continuous (fderiv ℝ (Function.uncurry H)) :=
    hH_C1.continuous_fderiv h_one_ne_zero
  have h_uncurry_cont : Continuous (Function.uncurry H) := hH_C1.continuous
  -- Step 1: Identify deriv of section with partial fderiv via chain rule.
  have h_deriv_eq : ∀ s t : ℝ,
      deriv (fun u => H s u) t = fderiv ℝ (Function.uncurry H) (s, t) (0, 1) := by
    intro s t
    have h_uncurry_at : HasFDerivAt (Function.uncurry H)
        (fderiv ℝ (Function.uncurry H) (s, t)) (s, t) :=
      (h_diff (s, t)).hasFDerivAt
    have h_const : HasFDerivAt (fun _ : ℝ => s) (0 : ℝ →L[ℝ] ℝ) t := hasFDerivAt_const s t
    have h_id : HasFDerivAt (fun u : ℝ => u) (ContinuousLinearMap.id ℝ ℝ) t := hasFDerivAt_id t
    have h_pair : HasFDerivAt (fun u : ℝ => ((s, u) : ℝ × ℝ))
        ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)) t := h_const.prodMk h_id
    have h_comp : HasFDerivAt (Function.uncurry H ∘ fun u => ((s, u) : ℝ × ℝ))
        ((fderiv ℝ (Function.uncurry H) (s, t)).comp
          ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ))) t :=
      h_uncurry_at.comp t h_pair
    have h_section_eq : (Function.uncurry H ∘ fun u => ((s, u) : ℝ × ℝ)) = fun u => H s u := by
      funext u; rfl
    rw [h_section_eq] at h_comp
    have h_at := h_comp.hasDerivAt
    rw [h_at.deriv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply]
  -- Step 2: Jointly continuous derivative-factor g.
  set g : ℝ → ℝ → ℂ := fun s t => fderiv ℝ (Function.uncurry H) (s, t) (0, 1) with hg_def
  have hg_uncurry_cont : Continuous (Function.uncurry g) := by
    change Continuous (fun st : ℝ × ℝ => fderiv ℝ (Function.uncurry H) st (0, 1))
    exact Continuous.clm_apply h_fderiv_cont continuous_const
  -- Step 3: Positive lower bound ε on ‖H - w‖ over the compact set.
  have h_compact : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc a b) :=
    isCompact_Icc.prod isCompact_Icc
  have h_nonempty : (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc a b).Nonempty :=
    ⟨(0, a), Set.mk_mem_prod (Set.left_mem_Icc.mpr zero_le_one) (Set.left_mem_Icc.mpr hab)⟩
  have h_norm_cont : Continuous (fun st : ℝ × ℝ => ‖Function.uncurry H st - w‖) :=
    (h_uncurry_cont.sub continuous_const).norm
  obtain ⟨st₀, hst₀_mem, hst₀_min⟩ :=
    h_compact.exists_isMinOn h_nonempty h_norm_cont.continuousOn
  set ε : ℝ := ‖Function.uncurry H st₀ - w‖ with hε_def
  have hε_pos : 0 < ε := by
    rw [hε_def, norm_pos_iff]
    exact sub_ne_zero.mpr (hH_avoid st₀.1 hst₀_mem.1 st₀.2 hst₀_mem.2)
  have h_norm_lb : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc a b, ε ≤ ‖H s t - w‖ := by
    intro s hs t ht
    exact hst₀_min (Set.mk_mem_prod hs ht)
  -- Step 4: Globally continuous regularization ψ : ℂ → ℂ.
  -- ψ(z) := ((max ‖z‖² ε²)⁻¹ : ℝ) cast to ℂ, times conjugate of z.
  -- Equals z⁻¹ when ‖z‖ ≥ ε; continuous everywhere because denominator ≥ ε² > 0.
  set ψ : ℂ → ℂ := fun z =>
    (((max (‖z‖^2) (ε^2) : ℝ)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ z) with hψ_def
  have h_max_pos : ∀ z : ℂ, 0 < max (‖z‖^2) (ε^2) := by
    intro z
    have h1 : ε^2 ≤ max (‖z‖^2) (ε^2) := le_max_right _ _
    have h2 : (0:ℝ) < ε^2 := by positivity
    linarith
  have hψ_cont : Continuous ψ := by
    change Continuous (fun z : ℂ => (((max (‖z‖^2) (ε^2) : ℝ)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ z))
    refine Continuous.mul ?_ Complex.continuous_conj
    refine Complex.continuous_ofReal.comp ?_
    refine Continuous.inv₀ ((continuous_norm.pow 2).max continuous_const) ?_
    intro z; exact ne_of_gt (h_max_pos z)
  have hψ_eq_inv : ∀ z : ℂ, ε ≤ ‖z‖ → ψ z = z⁻¹ := by
    intro z hz
    have h_sq : ε^2 ≤ ‖z‖^2 := sq_le_sq' (by linarith [hε_pos]) hz
    have h_max : max (‖z‖^2) (ε^2) = ‖z‖^2 := max_eq_left h_sq
    change (((max (‖z‖^2) (ε^2) : ℝ)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ z) = z⁻¹
    rw [h_max, Complex.inv_def, ← Complex.normSq_eq_norm_sq]
    push_cast; ring
  -- Step 5: Globally continuous integrand ĝ : ℝ → ℝ → ℂ.
  set ĝ : ℝ → ℝ → ℂ := fun s t => ψ (H s t - w) * g s t with hĝ_def
  have hĝ_uncurry_cont : Continuous (Function.uncurry ĝ) := by
    change Continuous (fun st : ℝ × ℝ => ψ (H st.1 st.2 - w) * g st.1 st.2)
    refine Continuous.mul ?_ hg_uncurry_cont
    refine hψ_cont.comp ?_
    exact h_uncurry_cont.sub continuous_const
  -- Step 6: On Icc 0 1 × Icc a b, ĝ = original integrand.
  have h_ĝ_eq : ∀ s ∈ Set.Icc (0:ℝ) 1, Set.EqOn
      (fun t => ĝ s t)
      (fun t => (H s t - w)⁻¹ * deriv (fun u => H s u) t)
      (Set.Icc a b) := by
    intro s hs t ht
    change ψ (H s t - w) * g s t = (H s t - w)⁻¹ * deriv (fun u => H s u) t
    rw [hψ_eq_inv (H s t - w) (h_norm_lb s hs t ht), h_deriv_eq s t]
  -- Step 7: Global continuity of the parametric integral of ĝ.
  have hĝ_int_cont : Continuous (fun s : ℝ => ∫ t in a..b, ĝ s t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := a) hĝ_uncurry_cont continuous_const
  -- Step 8: Equate the extended integral to the path contour integral on Icc 0 1.
  have h_pathContour_eq : ∀ s ∈ Set.Icc (0:ℝ) 1,
      ∫ t in a..b, ĝ s t =
      Complex.pathContourIntegral (fun t => H s t) a b (fun z => (z - w)⁻¹) := by
    intro s hs
    unfold Complex.pathContourIntegral
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact h_ĝ_eq s hs ht
  -- Step 9: Combine for the final ContinuousOn.
  apply ContinuousOn.congr
    (f := fun s => (2 * Real.pi * Complex.I)⁻¹ * (∫ t in a..b, ĝ s t))
  · exact ContinuousOn.mul continuousOn_const hĝ_int_cont.continuousOn
  · intro s hs
    change Complex.pathWindingNumber (fun t => H s t) a b w =
      (2 * Real.pi * Complex.I)⁻¹ * (∫ t in a..b, ĝ s t)
    unfold Complex.pathWindingNumber
    rw [h_pathContour_eq s hs]

/-- **Homotopy invariance of the winding index.** If two closed `C¹`
paths `γ₀, γ₁ : ℝ → ℂ` are `C¹`-homotopic in `ℂ \ {w}` via a homotopy
`H : ℝ → ℝ → ℂ` with constant endpoints (`H(s, a) = γ₀ a` and
`H(s, b) = γ₀ b` for all `s ∈ [0, 1]`), their winding indices
`Complex.pathWindingNumber` around `w` are equal.

Hypothesis strengthening (from the original loose continuous-only form):
the `C¹` smoothness of `γ₀`, `γ₁`, and `H` (jointly) is required for
the integrals defining the winding number to be well-defined and for
the `_isInt_of_closed` machinery to apply at each `s`. The constant-
endpoint condition (`H s a = γ₀ a`, `H s b = γ₀ b`) ensures each
intermediate path `H(s, ·)` is closed (so `_isInt_of_closed` applies).

Proof: define `n(s) := pathWindingNumber (H s ·) a b w`. By
`_isInt_of_closed` applied to each closed `C¹` path `H(s, ·)`, `n(s)`
is integer-valued. The integrand of `n(s)` is jointly continuous in
`(s, τ)`, so `n` is continuous. By connectivity of `[0, 1]` and
discreteness of `ℤ` in `ℂ`, `n` is constant. So `n(0) = n(1)`. Combined
with `n(0) = pathWindingNumber γ₀ a b w` and `n(1) = pathWindingNumber
γ₁ a b w`, the result follows.

The key topological tool for reducing complicated image-curve windings
(like `λ ∘ ∂F_Y`) to a standard reference curve (small circle around
`w`). -/
theorem pathWindingNumber_homotopy_invariant
    (γ₀ γ₁ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) (w : ℂ)
    (h_closed_0 : γ₀ a = γ₀ b)
    (hγ₀_C1 : ContDiff ℝ 1 γ₀)
    (hγ₁_C1 : ContDiff ℝ 1 γ₁)
    (h_homotopic : ∃ H : ℝ → ℝ → ℂ,
      ContDiff ℝ 1 (Function.uncurry H) ∧
      (∀ t ∈ Set.Icc a b, H 0 t = γ₀ t) ∧
      (∀ t ∈ Set.Icc a b, H 1 t = γ₁ t) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, H s a = γ₀ a) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, H s b = γ₀ b) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc a b, H s t ≠ w)) :
    Complex.pathWindingNumber γ₀ a b w = Complex.pathWindingNumber γ₁ a b w := by
  obtain ⟨H, hH_C1, hH_0, hH_1, hH_a, hH_b, hH_avoid⟩ := h_homotopic
  -- For each s, fun t => H s t is C¹.
  have hH_s_C1 : ∀ s : ℝ, ContDiff ℝ 1 (fun t => H s t) := fun s => by
    have h_emb : ContDiff ℝ 1 (fun t : ℝ => (s, t)) :=
      contDiff_const.prodMk contDiff_id
    exact hH_C1.comp h_emb
  -- Define n : ℝ → ℂ.
  set n : ℝ → ℂ := fun s => Complex.pathWindingNumber (fun t => H s t) a b w with hn_def
  -- n is continuous on Icc 0 1.
  have hn_cont : ContinuousOn n (Set.Icc (0 : ℝ) 1) :=
    pathWindingNumber_continuous_in_param hab w H hH_C1 hH_avoid
  -- For each s ∈ Icc 0 1, n s is integer-valued.
  have hn_int : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ k : ℤ, n s = (k : ℂ) := by
    intro s hs
    apply pathWindingNumber_isInt_of_closed (fun t => H s t) hab w
    · -- closed: H s a = γ₀ a = γ₀ b = H s b
      rw [hH_a s hs, h_closed_0, ← hH_b s hs]
    · -- avoid w
      intro t ht
      exact hH_avoid s hs t ht
    · -- C¹
      exact hH_s_C1 s
  -- Extract integer-valued function f : ℝ → ℤ on Icc 0 1.
  classical
  let f : ℝ → ℤ := fun s =>
    if h : ∃ k : ℤ, n s = (k : ℂ) then Classical.choose h else 0
  have hf_eq : ∀ s ∈ Set.Icc (0 : ℝ) 1, n s = (f s : ℂ) := by
    intro s hs
    simp only [f, dif_pos (hn_int s hs)]
    exact Classical.choose_spec (hn_int s hs)
  -- f is continuous on Icc 0 1 (locally constant from n continuous + integer isolation).
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    intro s₀ hs₀
    -- For codomain ℤ (discrete), show f tends to f s₀ in nhdsWithin s₀ (Icc 0 1).
    change Filter.Tendsto f (nhdsWithin s₀ (Set.Icc (0 : ℝ) 1)) (nhds (f s₀))
    rw [nhds_discrete ℤ, Filter.tendsto_pure]
    -- Goal: ∀ᶠ s in nhdsWithin s₀ (Icc 0 1), f s = f s₀.
    have hns₀ : n s₀ = (f s₀ : ℂ) := hf_eq s₀ hs₀
    have h_cont_n : ContinuousWithinAt n (Set.Icc (0 : ℝ) 1) s₀ := hn_cont s₀ hs₀
    rw [Metric.continuousWithinAt_iff] at h_cont_n
    obtain ⟨δ, hδ_pos, hδ_lt⟩ := h_cont_n (1/2) (by norm_num)
    -- ∀ᶠ s in nhdsWithin, dist s s₀ < δ AND s ∈ Icc.
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds s₀ hδ_pos),
      self_mem_nhdsWithin] with s h_ball h_icc
    -- s ∈ Ball(s₀, δ) ∩ Icc.
    have h_dist_s : dist s s₀ < δ := Metric.mem_ball.mp h_ball
    have h_dist_n : dist (n s) (n s₀) < 1/2 := hδ_lt h_icc h_dist_s
    -- |((f s : ℂ) - (f s₀ : ℂ))| < 1/2, integers → equal.
    have hns : n s = (f s : ℂ) := hf_eq s h_icc
    rw [hns, hns₀, Complex.dist_eq] at h_dist_n
    have h_diff_int : ((f s - f s₀ : ℤ) : ℂ) = (f s : ℂ) - (f s₀ : ℂ) := by push_cast; ring
    rw [← h_diff_int, Complex.norm_intCast] at h_dist_n
    -- (|f s - f s₀| : ℝ) < 1/2 → f s - f s₀ = 0.
    have h_abs_lt_1 : |(f s - f s₀ : ℤ)| < 1 := by
      have h_cast : ((|f s - f s₀| : ℤ) : ℝ) < 1 := by
        have : ((|f s - f s₀| : ℤ) : ℝ) < 1/2 := by exact_mod_cast h_dist_n
        linarith
      exact_mod_cast h_cast
    have h_eq : f s - f s₀ = 0 := Int.abs_lt_one_iff.mp h_abs_lt_1
    linarith
  -- Icc 0 1 is preconnected.
  have h_Icc_preconn : IsPreconnected (Set.Icc (0 : ℝ) 1) := isPreconnected_Icc
  -- f is constant on Icc 0 1.
  have hf_const : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, f s = f t :=
    fun s hs t ht => h_Icc_preconn.constant hf_cont hs ht
  -- n is constant on Icc 0 1.
  have hn_const : ∀ s ∈ Set.Icc (0 : ℝ) 1, n s = n 0 := fun s hs => by
    rw [hf_eq s hs, hf_eq 0 ⟨le_refl _, zero_le_one⟩,
      hf_const s hs 0 ⟨le_refl _, zero_le_one⟩]
  -- n 0 = pathWindingNumber γ₀ a b w.
  have hn_0_eq : n 0 = Complex.pathWindingNumber γ₀ a b w := by
    apply pathWindingNumber_congr_of_eqOn_C1 hab w
    · exact hH_s_C1 0
    · exact hγ₀_C1
    · exact fun t ht => hH_0 t ht
  -- n 1 = pathWindingNumber γ₁ a b w.
  have hn_1_eq : n 1 = Complex.pathWindingNumber γ₁ a b w := by
    apply pathWindingNumber_congr_of_eqOn_C1 hab w
    · exact hH_s_C1 1
    · exact hγ₁_C1
    · exact fun t ht => hH_1 t ht
  -- Conclude.
  rw [← hn_0_eq, ← hn_1_eq, hn_const 1 ⟨zero_le_one, le_refl _⟩]

/-- **Winding index of a CCW circle around its center.** For `R > 0`
and `w ∈ Metric.ball c R`, the CCW circle `circleMap c R` traversed
over `[0, 2π]` has `Complex.pathWindingNumber` equal to `1` around `w`.

This is the "reference curve" theorem used to compute winding indices
of complicated curves via homotopy reduction. It wraps Mathlib's
`circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` in
the `Complex.pathWindingNumber` formalism. -/
theorem pathWindingNumber_circleMap_inside_eq_one
    (c : ℂ) (R : ℝ) (_hR : 0 < R) (w : ℂ) (hw : w ∈ Metric.ball c R) :
    Complex.pathWindingNumber (_root_.circleMap c R) 0 (2 * Real.pi) w = 1 := by
  unfold Complex.pathWindingNumber Complex.pathContourIntegral
  -- Apply Mathlib's Cauchy integral formula at w, with f = 1.
  have h_circ := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := ∅) (R := R) (c := c) (w := w) (f := fun _ : ℂ => (1 : ℂ))
    Set.countable_empty hw continuousOn_const
    (fun x _ => differentiableAt_const _)
  -- Unfold the circle integral to an interval integral on Icc 0 (2π).
  rw [circleIntegral_def_Icc] at h_circ
  -- Simplify: smul = mul in ℂ, and (...)⁻¹ • 1 = (...)⁻¹.
  simp only [smul_eq_mul, mul_one] at h_circ
  -- Convert Set.Icc form to intervalIntegral form.
  have h_two_pi_nn : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [intervalIntegral.integral_of_le h_two_pi_nn,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- Reorder integrand multiplication to match Mathlib's form.
  have h_rewrite : (∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
      (_root_.circleMap c R t - w)⁻¹ * deriv (_root_.circleMap c R) t) =
      ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (_root_.circleMap c R) θ * (_root_.circleMap c R θ - w)⁻¹ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t
    ring
  rw [h_rewrite, h_circ]
  -- Goal: (2 * π * I)⁻¹ * (2 * π * I) = 1.
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  exact inv_mul_cancel₀ hpi

/-- **F_Y boundary parameterization.** The closed contour `∂F_Y`
parameterized as a function `ℝ → ℂ`, with parameter `t ∈ [0, 6]`
(one unit per piece). Traversed CCW with the F_Y region interior on
the left, starting from the bottom-left corner `(0, δ)`.

Six segments:
- `t ∈ [0, 1]`: bot_left edge from `(0, δ)` to `(1/2 − R₀, δ)`.
- `t ∈ [1, 2]`: upper semicircle from `(1/2 − R₀, δ)` over to
  `(1/2 + R₀, δ)` (parameterized by `θ = π · (2 − t)`, going from
  `π` down to `0` so the arc curves over the cut-out disk).
- `t ∈ [2, 3]`: bot_right edge from `(1/2 + R₀, δ)` to `(1, δ)`.
- `t ∈ [3, 4]`: right edge from `(1, δ)` to `(1, Y)`.
- `t ∈ [4, 5]`: top edge from `(1, Y)` to `(0, Y)`.
- `t ∈ [5, 6]`: left edge from `(0, Y)` to `(0, δ)`.

At `t = 0` and `t = 6` the value is `(0, δ)`, so the curve is closed.
For `t ∉ [0, 6]` the function returns `0` (irrelevant for the
parameter range used by the homotopy / winding-index integrals). -/
noncomputable def F_Y_boundary_parameterization
    (δ Y R₀ : ℝ) (t : ℝ) : ℂ :=
  if t ≤ 1 then
    (t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I
  else if t ≤ 2 then
    _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - t))
  else if t ≤ 3 then
    (((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I
  else if t ≤ 4 then
    (1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I
  else if t ≤ 5 then
    ((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I
  else if t ≤ 6 then
    ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I
  else
    0

/-- **F_Y boundary parameterization has positive imaginary part.**
For valid F_Y parameters and `t ∈ Icc 0 6`, the boundary point
`F_Y_boundary_parameterization δ Y R₀ t` has strictly positive
imaginary part, so it lies in the open upper half-plane `ℍ`.

The six pieces all have imaginary part bounded below by `δ > 0`
(the bottom edges and arc) or by some value in `[δ, Y]` (the
side edges and top edge). -/
theorem F_Y_boundary_parameterization_im_pos
    {δ Y R₀ : ℝ} (hδ : 0 < δ) (hδY : δ < Y) (_hR₀_pos : 0 < R₀)
    (_hR₀_lt : R₀ < 1 / 2) :
    ∀ t ∈ Set.Icc (0 : ℝ) 6,
      0 < (F_Y_boundary_parameterization δ Y R₀ t).im := by
  intro t ht
  obtain ⟨ht0, ht6⟩ := ht
  -- Local helper: imaginary part of circleMap formula.
  have h_cm_im : ∀ (c : ℂ) (R θ : ℝ), (_root_.circleMap c R θ).im = c.im + R * Real.sin θ := by
    intro c R θ
    unfold _root_.circleMap
    rw [Complex.exp_mul_I]
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im]
  unfold F_Y_boundary_parameterization
  split_ifs with h1 h2 h3 h4 h5
  · -- t ≤ 1: bot_left edge, Im = δ.
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    linarith
  · -- 1 < t ≤ 2: upper semicircle, Im = δ + R₀ · sin(π · (2 - t)) ≥ δ.
    have h1' : 1 < t := not_le.mp h1
    rw [h_cm_im]
    have h_c_im : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im = δ := by
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]
    rw [h_c_im]
    have h_sin_nn : 0 ≤ Real.sin (Real.pi * (2 - t)) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · apply mul_nonneg Real.pi_pos.le; linarith
      · have h2t : (2 - t) ≤ 1 := by linarith
        have : Real.pi * (2 - t) ≤ Real.pi * 1 :=
          mul_le_mul_of_nonneg_left h2t Real.pi_pos.le
        linarith
    nlinarith [_hR₀_pos]
  · -- 2 < t ≤ 3: bot_right edge, Im = δ.
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    linarith
  · -- 3 < t ≤ 4: right edge, Im = δ + (t - 3) · (Y - δ) ≥ δ.
    have h3' : 3 < t := not_le.mp h3
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    have hYδ : 0 < Y - δ := by linarith
    have h_t3 : 0 ≤ t - 3 := by linarith
    nlinarith
  · -- 4 < t ≤ 5: top edge, Im = Y.
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    linarith
  · -- 5 < t ≤ 6: left edge, Im = Y - (t - 5) · (Y - δ) ∈ [δ, Y).
    have h5' : 5 < t := not_le.mp h5
    simp [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    have hYδ : 0 < Y - δ := by linarith
    have h_t5 : t - 5 ≤ 1 := by linarith
    nlinarith

/-- **F_Y boundary parameterization is continuous on `Icc 0 6`.**
The piecewise definition is continuous on each piece, and the
values match at the seams `t = 1, 2, 3, 4, 5` so the overall
function is continuous on `Icc 0 6`.

Proof construction: build a globally continuous auxiliary `gg : ℝ → ℂ`
that drops the final `if t ≤ 6 then ... else 0` clause (collapsing it
to the unconditional piece 6 formula), via repeated
`Continuous.if_le`. Since on `Icc 0 6` the condition `t ≤ 6` always
holds, `gg = F_Y_boundary_parameterization δ Y R₀` on `Icc 0 6`, and
the result follows from `Continuous.continuousOn` + `ContinuousOn.congr`. -/
theorem F_Y_boundary_parameterization_continuousOn
    (δ Y R₀ : ℝ) :
    ContinuousOn (F_Y_boundary_parameterization δ Y R₀)
      (Set.Icc (0 : ℝ) 6) := by
  -- Piece-wise functions p1, ..., p6 (matching F_Y_boundary's six branches).
  set p1 : ℝ → ℂ := fun t => (t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I
  set p2 : ℝ → ℂ := fun t =>
    _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - t))
  set p3 : ℝ → ℂ := fun t =>
    (((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I
  set p4 : ℝ → ℂ := fun t =>
    (1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I
  set p5 : ℝ → ℂ := fun t =>
    ((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I
  set p6 : ℝ → ℂ := fun t =>
    ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I
  -- Each piece is globally continuous in t.
  have hp1_cont : Continuous p1 := by fun_prop
  have hp2_cont : Continuous p2 :=
    (continuous_circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀).comp (by fun_prop)
  have hp3_cont : Continuous p3 := by fun_prop
  have hp4_cont : Continuous p4 := by fun_prop
  have hp5_cont : Continuous p5 := by fun_prop
  have hp6_cont : Continuous p6 := by fun_prop
  -- Matching values at the five interior seams.
  have match5 : p5 5 = p6 5 := by
    change ((5 - 5 : ℝ) : ℂ) + (Y : ℂ) * Complex.I =
        ((Y - (5 - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I
    push_cast; ring
  have match4 : p4 4 = p5 4 := by
    change (1 : ℂ) + ((δ + (4 - 3) * (Y - δ)) : ℂ) * Complex.I =
        ((5 - 4 : ℝ) : ℂ) + (Y : ℂ) * Complex.I
    push_cast; ring
  have match3 : p3 3 = p4 3 := by
    change (((1 / 2 + R₀) + (3 - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I =
        (1 : ℂ) + ((δ + (3 - 3) * (Y - δ)) : ℂ) * Complex.I
    ring
  have match2 : p2 2 = p3 2 := by
    change _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - 2)) =
        (((1 / 2 + R₀) + (2 - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I
    unfold _root_.circleMap
    rw [show (Real.pi * (2 - 2) : ℝ) = 0 from by ring]
    push_cast
    simp; ring
  have match1 : p1 1 = p2 1 := by
    change (1 * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I =
        _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - 1))
    unfold _root_.circleMap
    rw [show (Real.pi * (2 - 1) : ℝ) = Real.pi from by ring,
      show ((Real.pi : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I from rfl,
      Complex.exp_pi_mul_I]
    ring
  -- Build up gg = nested if's from inside out.
  -- gg5 = if t ≤ 5 then p5 else p6
  have hg5 : Continuous (fun t : ℝ => if t ≤ 5 then p5 t else p6 t) :=
    Continuous.if_le hp5_cont hp6_cont continuous_id continuous_const
      (fun x hx => by subst hx; exact match5)
  -- gg4 = if t ≤ 4 then p4 else gg5; at the seam t = 4, gg5(4) = p5(4) since 4 ≤ 5.
  have hg4 : Continuous (fun t : ℝ => if t ≤ 4 then p4 t else
      (if t ≤ 5 then p5 t else p6 t)) :=
    Continuous.if_le hp4_cont hg5 continuous_id continuous_const
      (fun x hx => by
        subst hx
        have h : (4 : ℝ) ≤ 5 := by norm_num
        simp only [if_pos h]
        exact match4)
  have hg3 : Continuous (fun t : ℝ => if t ≤ 3 then p3 t else
      (if t ≤ 4 then p4 t else (if t ≤ 5 then p5 t else p6 t))) :=
    Continuous.if_le hp3_cont hg4 continuous_id continuous_const
      (fun x hx => by
        subst hx
        have h : (3 : ℝ) ≤ 4 := by norm_num
        simp only [if_pos h]
        exact match3)
  have hg2 : Continuous (fun t : ℝ => if t ≤ 2 then p2 t else
      (if t ≤ 3 then p3 t else (if t ≤ 4 then p4 t else
        (if t ≤ 5 then p5 t else p6 t)))) :=
    Continuous.if_le hp2_cont hg3 continuous_id continuous_const
      (fun x hx => by
        subst hx
        have h : (2 : ℝ) ≤ 3 := by norm_num
        simp only [if_pos h]
        exact match2)
  have hg1 : Continuous (fun t : ℝ => if t ≤ 1 then p1 t else
      (if t ≤ 2 then p2 t else (if t ≤ 3 then p3 t else
        (if t ≤ 4 then p4 t else (if t ≤ 5 then p5 t else p6 t))))) :=
    Continuous.if_le hp1_cont hg2 continuous_id continuous_const
      (fun x hx => by
        subst hx
        have h : (1 : ℝ) ≤ 2 := by norm_num
        simp only [if_pos h]
        exact match1)
  -- F_Y_boundary equals gg on Icc 0 6: gg drops the final `if t ≤ 6 then p6 else 0`
  -- and uses p6 directly, which matches F_Y_boundary's value for t ≤ 6.
  refine ContinuousOn.congr hg1.continuousOn ?_
  intro t ⟨_, _ht6⟩
  change F_Y_boundary_parameterization δ Y R₀ t = (if t ≤ 1 then p1 t else _)
  unfold F_Y_boundary_parameterization
  split_ifs <;> rfl

/-- **F_Y image curve is continuous on `Icc 0 6`.**
The composition `t ↦ modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w`
is continuous on `Icc 0 6`, since the boundary parameterization is
continuous (`F_Y_boundary_parameterization_continuousOn`) and lands in
the open upper half-plane `ℍ` (`F_Y_boundary_parameterization_im_pos`)
where `modularLambdaH` is holomorphic. -/
theorem F_Y_image_curve_continuousOn
    (w : ℂ) {δ Y R₀ : ℝ} (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀)
    (hR₀_lt : R₀ < 1 / 2) :
    ContinuousOn (fun t : ℝ =>
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w)
      (Set.Icc (0 : ℝ) 6) := by
  refine ContinuousOn.sub ?_ continuousOn_const
  intro t ht
  have h_im_pos := F_Y_boundary_parameterization_im_pos hδ hδY hR₀_pos hR₀_lt t ht
  have h_F_Y_cont := F_Y_boundary_parameterization_continuousOn δ Y R₀ t ht
  have h_lambda_at : ContinuousAt modularLambdaH
      (F_Y_boundary_parameterization δ Y R₀ t) :=
    (modularLambdaH_differentiableAt_of_im_pos h_im_pos).continuousAt
  exact h_lambda_at.comp_continuousWithinAt h_F_Y_cont

/-- **F_Y image curve avoids zero on `Icc 0 6`.**
The composition `t ↦ modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w`
is nonzero on `Icc 0 6`. By case analysis on which boundary piece `t`
belongs to, the value reduces to one of the six non-vanishing
hypotheses. -/
theorem F_Y_image_curve_ne_zero
    {w : ℂ} {δ Y R₀ : ℝ}
    (_hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2) (hδY : δ ≤ Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w ≠ 0 := by
  intro t ht
  obtain ⟨ht0, ht6⟩ := ht
  have h_R₀_lt_half : 0 ≤ 1 / 2 - R₀ := by linarith
  have hYδ : 0 ≤ Y - δ := by linarith
  unfold F_Y_boundary_parameterization
  split_ifs with h1 h2 h3 h4 h5
  · -- t ≤ 1: bot_left edge.
    have hx : t * (1 / 2 - R₀) ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀) :=
      ⟨by positivity, by nlinarith⟩
    have key := hg_bot_left _ hx
    push_cast at key
    exact key
  · -- 1 < t ≤ 2: upper semicircle.
    have h1' : 1 < t := not_le.mp h1
    have hθ : Real.pi * (2 - t) ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    exact hg_arc _ hθ
  · -- 2 < t ≤ 3: bot_right edge.
    have h2' : 2 < t := not_le.mp h2
    have hx : (1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀) ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1 :=
      ⟨by nlinarith, by nlinarith⟩
    have key := hg_bot_right _ hx
    push_cast at key
    convert key using 2
  · -- 3 < t ≤ 4: right edge.
    have h3' : 3 < t := not_le.mp h3
    have hy : δ + (t - 3) * (Y - δ) ∈ Set.Icc δ Y :=
      ⟨by nlinarith, by nlinarith⟩
    have key := hg_right _ hy
    push_cast at key
    convert key using 2
  · -- 4 < t ≤ 5: top edge.
    have h4' : 4 < t := not_le.mp h4
    have hx : (5 - t) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith, by linarith⟩
    exact_mod_cast hg_top _ hx
  · -- 5 < t ≤ 6: left edge.
    have h5' : 5 < t := not_le.mp h5
    have hy : (Y - (t - 5) * (Y - δ)) ∈ Set.Icc δ Y :=
      ⟨by nlinarith, by nlinarith⟩
    have key := hg_left _ hy
    simp only [zero_add] at key
    exact_mod_cast key

/-- **FTC bridge: pathContourIntegral of `(z − w)⁻¹` equals log-lift
boundary difference for `C¹` paths.** For a globally `C¹` path
`γ : ℝ → ℂ` whose image avoids `w` on `Icc a b`, with a continuous log
lift `L` of `γ − w` on `Icc a b` (so `Complex.exp (L t) = γ t − w` for
`t ∈ Icc a b`), the path contour integral equals the boundary difference
of `L`:
`Complex.pathContourIntegral γ a b ((z − w)⁻¹) = L b − L a`.

Proof outline: on `Icc a b`, the C¹ structure makes
`u(t) := γ t − w` differentiable with `u'(t) = γ'(t)`. By
`HasDerivAt.cexp` applied in reverse (combined with the log-lift
condition), `L` is differentiable with `L'(t) = u'(t) / u(t) =
(γ - w)⁻¹ · γ'(t)`. Apply `intervalIntegral.integral_eq_sub_of_hasDerivAt`. -/
theorem pathContourIntegral_inv_eq_log_lift_diff_of_contDiff
    {a b : ℝ} (hab : a ≤ b) (γ : ℝ → ℂ) {w : ℂ}
    (hγ_C1 : ContDiff ℝ 1 γ)
    (hγ_ne : ∀ t ∈ Set.Icc a b, γ t ≠ w)
    (L : ℝ → ℂ) (hL_cont : Continuous L)
    (hL_exp : ∀ t ∈ Set.Icc a b, Complex.exp (L t) = γ t - w) :
    Complex.pathContourIntegral γ a b (fun z => (z - w)⁻¹) = L b - L a := by
  -- Phase A: setup.
  have hγ_cont : Continuous γ := hγ_C1.continuous
  have hγ'_cont : Continuous (deriv γ) := hγ_C1.continuous_deriv (le_refl 1)
  have hγ_diff_all : ∀ t : ℝ, HasDerivAt γ (deriv γ t) t := fun t =>
    (hγ_C1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt.hasDerivAt
  have hγw_ne : ∀ t ∈ Set.Icc a b, γ t - w ≠ 0 := fun t ht =>
    sub_ne_zero.mpr (hγ_ne t ht)
  -- Integrand `u(t) := (γ t - w)⁻¹ · γ'(t)`.
  let u : ℝ → ℂ := fun t => (γ t - w)⁻¹ * deriv γ t
  -- `u` is continuous at each `t ∈ Icc a b` (global ContinuousAt — not just within).
  have hu_cont_at : ∀ t ∈ Set.Icc a b, ContinuousAt u t := by
    intro t ht
    refine ContinuousAt.mul ?_ hγ'_cont.continuousAt
    refine ContinuousAt.inv₀ ?_ (hγw_ne t ht)
    exact (hγ_cont.sub continuous_const).continuousAt
  have hu_cont_on : ContinuousOn u (Set.Icc a b) := fun t ht =>
    (hu_cont_at t ht).continuousWithinAt
  -- `u` is strongly measurable globally (using junk-value inv).
  have hu_meas : MeasureTheory.StronglyMeasurable u := by
    refine MeasureTheory.StronglyMeasurable.mul ?_ hγ'_cont.stronglyMeasurable
    exact (Measurable.inv (hγ_cont.measurable.sub measurable_const)).stronglyMeasurable
  have hu_smaf : ∀ t : ℝ,
      StronglyMeasurableAtFilter u (nhds t) MeasureTheory.volume := fun _ =>
    hu_meas.stronglyMeasurableAtFilter
  -- `u` is interval-integrable on `[a, b]`.
  have hu_integrable_ab : IntervalIntegrable u MeasureTheory.volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact hu_cont_on
  -- Phase B: define `L̃(t) := L a + ∫_a^t u` and show it has the right derivative.
  let Ltil : ℝ → ℂ := fun t => L a + ∫ s in a..t, u s
  have hLtil_a : Ltil a = L a := by
    change L a + (∫ s in a..a, u s) = L a
    rw [intervalIntegral.integral_same, add_zero]
  have hLtil_deriv : ∀ t ∈ Set.Icc a b, HasDerivAt Ltil (u t) t := by
    intro t ht
    have h_integrable_at : IntervalIntegrable u MeasureTheory.volume a t := by
      refine hu_integrable_ab.mono_set ?_
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le ht.1]
      exact Set.Icc_subset_Icc_right ht.2
    have h_int_deriv : HasDerivAt (fun v : ℝ => ∫ s in a..v, u s) (u t) t :=
      intervalIntegral.integral_hasDerivAt_right h_integrable_at (hu_smaf t)
        (hu_cont_at t ht)
    exact h_int_deriv.const_add (L a)
  -- Phase C: show `exp(L̃) = γ − w` on `Icc a b`.
  -- Define `F(t) := exp(L̃ t) / (γ t − w)`; show `F` constant on `[a, b]`.
  let F : ℝ → ℂ := fun t => Complex.exp (Ltil t) / (γ t - w)
  have hF_deriv : ∀ t ∈ Set.Icc a b, HasDerivAt F 0 t := by
    intro t ht
    have hw_ne : γ t - w ≠ 0 := hγw_ne t ht
    have h_exp_d : HasDerivAt (fun s => Complex.exp (Ltil s))
        (Complex.exp (Ltil t) * u t) t := (hLtil_deriv t ht).cexp
    have h_subw_d : HasDerivAt (fun s : ℝ => γ s - w) (deriv γ t) t :=
      (hγ_diff_all t).sub_const w
    have h_div := h_exp_d.div h_subw_d hw_ne
    -- Show the derivative value (the quotient-rule expression) equals 0.
    have h_num_eq : Complex.exp (Ltil t) * u t * (γ t - w) -
        Complex.exp (Ltil t) * deriv γ t = 0 := by
      change Complex.exp (Ltil t) * ((γ t - w)⁻¹ * deriv γ t) * (γ t - w) -
          Complex.exp (Ltil t) * deriv γ t = 0
      have h_rewrite : Complex.exp (Ltil t) * ((γ t - w)⁻¹ * deriv γ t) * (γ t - w) =
          Complex.exp (Ltil t) * deriv γ t * ((γ t - w)⁻¹ * (γ t - w)) := by ring
      rw [h_rewrite, inv_mul_cancel₀ hw_ne, mul_one, sub_self]
    have h_val_zero : (Complex.exp (Ltil t) * u t * (γ t - w) -
        Complex.exp (Ltil t) * deriv γ t) / (γ t - w) ^ 2 = 0 := by
      rw [h_num_eq, zero_div]
    rw [← h_val_zero]
    exact h_div
  -- Show F is constant on Icc a b by integrating F' = 0.
  have hF_const : ∀ t ∈ Set.Icc a b, F t = F a := by
    intro t ht
    have hat : a ≤ t := ht.1
    have hF_at_uIcc : ∀ s ∈ Set.uIcc a t, HasDerivAt F 0 s := by
      intro s hs
      rw [Set.uIcc_of_le hat] at hs
      exact hF_deriv s ⟨hs.1, le_trans hs.2 ht.2⟩
    have h_integral := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F)
      hF_at_uIcc (intervalIntegrable_const)
    rw [intervalIntegral.integral_zero] at h_integral
    linear_combination -h_integral
  have hF_a : F a = 1 := by
    have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
    change Complex.exp (Ltil a) / (γ a - w) = 1
    rw [hLtil_a, hL_exp a ha_mem, div_self (hγw_ne a ha_mem)]
  have h_exp_Ltil : ∀ t ∈ Set.Icc a b, Complex.exp (Ltil t) = γ t - w := by
    intro t ht
    have hFt : F t = 1 := (hF_const t ht).trans hF_a
    have hFt' : Complex.exp (Ltil t) / (γ t - w) = 1 := hFt
    rw [div_eq_one_iff_eq (hγw_ne t ht)] at hFt'
    exact hFt'
  -- Phase D: show `L = L̃` on `Icc a b` via integer-continuity.
  let g : ℝ → ℂ := fun t => L t - Ltil t
  have hLtil_cont_on : ContinuousOn Ltil (Set.Icc a b) := fun t ht =>
    (hLtil_deriv t ht).continuousAt.continuousWithinAt
  have hg_cont_on : ContinuousOn g (Set.Icc a b) :=
    (hL_cont.continuousOn).sub hLtil_cont_on
  -- `exp(g) = 1` on `Icc a b`.
  have h_exp_g : ∀ t ∈ Set.Icc a b, Complex.exp (g t) = 1 := by
    intro t ht
    change Complex.exp (L t - Ltil t) = 1
    rw [Complex.exp_sub, hL_exp t ht, h_exp_Ltil t ht, div_self (hγw_ne t ht)]
  have hg_int : ∀ t ∈ Set.Icc a b,
      ∃ n : ℤ, g t = (n : ℂ) * (2 * Real.pi * Complex.I) := fun t ht =>
    Complex.exp_eq_one_iff.mp (h_exp_g t ht)
  have hg_a : g a = 0 := by
    change L a - Ltil a = 0
    rw [hLtil_a, sub_self]
  -- Define `ψ(t) := (g t).im / (2π)`; integer-valued on `Icc a b`, continuous.
  let ψ : ℝ → ℝ := fun t => (g t).im / (2 * Real.pi)
  have hψ_cont_on : ContinuousOn ψ (Set.Icc a b) := by
    refine ContinuousOn.div_const ?_ (2 * Real.pi)
    exact Complex.continuous_im.comp_continuousOn hg_cont_on
  have hψ_int : ∀ t ∈ Set.Icc a b, ∃ n : ℤ, ψ t = (n : ℝ) := by
    intro t ht
    obtain ⟨n, hn⟩ := hg_int t ht
    refine ⟨n, ?_⟩
    have h_im : (g t).im = (n : ℝ) * (2 * Real.pi) := by
      rw [hn]
      simp [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    change (g t).im / (2 * Real.pi) = (n : ℝ)
    rw [h_im]
    have h_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp
  have hψ_a : ψ a = 0 := by
    change (g a).im / (2 * Real.pi) = 0
    rw [hg_a, Complex.zero_im, zero_div]
  -- Use IVT to show ψ ≡ 0 on Icc a b.
  have hψ_zero : ∀ t ∈ Set.Icc a b, ψ t = 0 := by
    intro t ht
    by_contra hψt_ne
    obtain ⟨n, hn⟩ := hψ_int t ht
    have hn_ne : (n : ℝ) ≠ 0 := hn ▸ hψt_ne
    have hn_int_ne : n ≠ 0 := by exact_mod_cast hn_ne
    have hψ_cont_at : ContinuousOn ψ (Set.Icc a t) :=
      hψ_cont_on.mono (Set.Icc_subset_Icc_right ht.2)
    -- n is a nonzero integer, so |n| ≥ 1.
    rcases lt_or_gt_of_ne hn_ne with hn_neg | hn_pos
    · -- n < 0 as ℝ ⟹ n ≤ -1 as ℤ.
      have hn_int_neg : n < 0 := by exact_mod_cast hn_neg
      have hn_int_le : n ≤ -1 := by omega
      have h_n_le : (n : ℝ) ≤ -1 := by exact_mod_cast hn_int_le
      have h_half_in : (-(1/2 : ℝ)) ∈ Set.Icc (ψ t) (ψ a) := by
        rw [hψ_a, hn]; exact ⟨by linarith, by norm_num⟩
      have h_ivt :=
        intermediate_value_Icc' (a := a) (b := t) ht.1 hψ_cont_at h_half_in
      obtain ⟨s, hs_mem, hs_val⟩ := h_ivt
      have hs_in_ab : s ∈ Set.Icc a b :=
        ⟨hs_mem.1, le_trans hs_mem.2 ht.2⟩
      obtain ⟨m, hm⟩ := hψ_int s hs_in_ab
      have hm_eq : (m : ℝ) = -(1/2) := by rw [← hm]; exact hs_val
      have : ((2 * m : ℤ) : ℝ) = -1 := by push_cast; linarith
      have h2m : (2 * m : ℤ) = -1 := by exact_mod_cast this
      omega
    · -- n > 0 as ℝ ⟹ n ≥ 1 as ℤ.
      have hn_int_pos : 0 < n := by exact_mod_cast hn_pos
      have hn_int_ge : 1 ≤ n := by omega
      have h_n_ge : (1 : ℝ) ≤ n := by exact_mod_cast hn_int_ge
      have h_half_in : ((1/2 : ℝ)) ∈ Set.Icc (ψ a) (ψ t) := by
        rw [hψ_a, hn]; exact ⟨by norm_num, by linarith⟩
      have h_ivt :=
        intermediate_value_Icc (a := a) (b := t) ht.1 hψ_cont_at h_half_in
      obtain ⟨s, hs_mem, hs_val⟩ := h_ivt
      have hs_in_ab : s ∈ Set.Icc a b :=
        ⟨hs_mem.1, le_trans hs_mem.2 ht.2⟩
      obtain ⟨m, hm⟩ := hψ_int s hs_in_ab
      have hm_eq : (m : ℝ) = 1/2 := by rw [← hm]; exact hs_val
      have : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
      have h2m : (2 * m : ℤ) = 1 := by exact_mod_cast this
      omega
  -- From ψ(t) = 0 and the structure of g: g(t) = 0.
  have hg_im_zero : ∀ t ∈ Set.Icc a b, (g t).im = 0 := by
    intro t ht
    have hψt : ψ t = 0 := hψ_zero t ht
    have h1 : (g t).im / (2 * Real.pi) = 0 := hψt
    have h_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp at h1
    linarith
  have hg_re_zero : ∀ t ∈ Set.Icc a b, (g t).re = 0 := by
    intro t ht
    obtain ⟨n, hn⟩ := hg_int t ht
    rw [hn]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  have hg_zero : ∀ t ∈ Set.Icc a b, g t = 0 := fun t ht =>
    Complex.ext (hg_re_zero t ht) (hg_im_zero t ht)
  -- Phase E: conclude.
  have hL_b : L b = Ltil b := by
    have h_g_b : g b = 0 := hg_zero b ⟨hab, le_refl b⟩
    have h_g_b' : L b - Ltil b = 0 := h_g_b
    linear_combination h_g_b'
  -- pathContourIntegral = ∫_a^b u = L̃ b - L̃ a = L b - L a.
  unfold Complex.pathContourIntegral
  have h_integrand_eq : (fun t : ℝ => (fun z => (z - w)⁻¹) (γ t) * deriv γ t) = u := by
    funext _; rfl
  rw [h_integrand_eq]
  have h_integral : ∫ t in a..b, u t = Ltil b - Ltil a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Ltil) ?_ hu_integrable_ab
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact hLtil_deriv t ht
  rw [h_integral, hLtil_a, ← hL_b]

/-- **ContDiffOn variant of the FTC bridge.** Generalization of
`pathContourIntegral_inv_eq_log_lift_diff_of_contDiff`: only requires
`ContDiffOn ℝ 1 γ U` for some open `U ⊇ Icc a b`, not global C¹. -/
theorem pathContourIntegral_inv_eq_log_lift_diff_of_contDiffOn
    {a b : ℝ} (hab : a ≤ b) (γ : ℝ → ℂ) {w : ℂ} {U : Set ℝ}
    (hU : IsOpen U) (hUab : Set.Icc a b ⊆ U)
    (hγ : ContDiffOn ℝ 1 γ U)
    (hγ_ne : ∀ t ∈ Set.Icc a b, γ t ≠ w)
    (L : ℝ → ℂ) (hL_cont : Continuous L)
    (hL_exp : ∀ t ∈ Set.Icc a b, Complex.exp (L t) = γ t - w) :
    Complex.pathContourIntegral γ a b (fun z => (z - w)⁻¹) = L b - L a := by
  -- Phase A: setup.
  have hγ_contOn : ContinuousOn γ U := hγ.continuousOn
  have hγ'_contOn : ContinuousOn (deriv γ) U :=
    hγ.continuousOn_deriv_of_isOpen hU (le_refl 1)
  have hγ_diff_U : ∀ t ∈ U, HasDerivAt γ (deriv γ t) t := by
    intro t ht
    have h_diff_at : DifferentiableAt ℝ γ t :=
      ((hγ.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) t ht).differentiableAt
        (hU.mem_nhds ht)
    exact h_diff_at.hasDerivAt
  have hγw_ne : ∀ t ∈ Set.Icc a b, γ t - w ≠ 0 := fun t ht =>
    sub_ne_zero.mpr (hγ_ne t ht)
  -- Integrand `u(t) := (γ t - w)⁻¹ · γ'(t)`.
  let u : ℝ → ℂ := fun t => (γ t - w)⁻¹ * deriv γ t
  -- For each `t ∈ Icc a b`, there is an open neighborhood `W_t ⊆ U` of `t`
  -- on which `γ - w ≠ 0` everywhere, hence `u` is `ContinuousOn`.
  have hu_local : ∀ t ∈ Set.Icc a b, ∃ W : Set ℝ, IsOpen W ∧ t ∈ W ∧
      ContinuousOn u W := by
    intro t ht
    have htU : t ∈ U := hUab ht
    have hγw_at : ContinuousAt (fun s => γ s - w) t :=
      (hγ_contOn.continuousAt (hU.mem_nhds htU)).sub continuousAt_const
    have h_ne_event : ∀ᶠ s in nhds t, γ s - w ≠ 0 :=
      hγw_at.eventually_ne (sub_ne_zero.mpr (hγ_ne t ht))
    rw [Filter.eventually_iff_exists_mem] at h_ne_event
    obtain ⟨N, hN_nhds, hN_prop⟩ := h_ne_event
    rcases mem_nhds_iff.mp hN_nhds with ⟨W₀, hW₀_sub, hW₀_open, hW₀_mem⟩
    refine ⟨W₀ ∩ U, hW₀_open.inter hU, ⟨hW₀_mem, htU⟩, ?_⟩
    intro s ⟨hsW₀, hsU⟩
    refine ContinuousAt.continuousWithinAt ?_
    have hγs_at : ContinuousAt γ s := hγ_contOn.continuousAt (hU.mem_nhds hsU)
    have hγ's_at : ContinuousAt (deriv γ) s := hγ'_contOn.continuousAt (hU.mem_nhds hsU)
    have hs_ne : γ s - w ≠ 0 := hN_prop _ (hW₀_sub hsW₀)
    refine ContinuousAt.mul ?_ hγ's_at
    exact ContinuousAt.inv₀ (hγs_at.sub continuousAt_const) hs_ne
  have hu_cont_at : ∀ t ∈ Set.Icc a b, ContinuousAt u t := by
    intro t ht
    obtain ⟨W, hW_open, hW_mem, hu_W⟩ := hu_local t ht
    exact (hu_W.continuousAt (hW_open.mem_nhds hW_mem))
  have hu_cont_on : ContinuousOn u (Set.Icc a b) := fun t ht =>
    (hu_cont_at t ht).continuousWithinAt
  -- Strong-measurability-at-filter via the local open neighborhood.
  have hu_smaf : ∀ t ∈ Set.Icc a b,
      StronglyMeasurableAtFilter u (nhds t) MeasureTheory.volume := by
    intro t ht
    obtain ⟨W, hW_open, hW_mem, hu_W⟩ := hu_local t ht
    exact hu_W.stronglyMeasurableAtFilter hW_open t hW_mem
  -- `u` is interval-integrable on `[a, b]`.
  have hu_integrable_ab : IntervalIntegrable u MeasureTheory.volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact hu_cont_on
  -- Phase B: define `L̃(t) := L a + ∫_a^t u` and show it has the right derivative.
  let Ltil : ℝ → ℂ := fun t => L a + ∫ s in a..t, u s
  have hLtil_a : Ltil a = L a := by
    change L a + (∫ s in a..a, u s) = L a
    rw [intervalIntegral.integral_same, add_zero]
  have hLtil_deriv : ∀ t ∈ Set.Icc a b, HasDerivAt Ltil (u t) t := by
    intro t ht
    have h_integrable_at : IntervalIntegrable u MeasureTheory.volume a t := by
      refine hu_integrable_ab.mono_set ?_
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le ht.1]
      exact Set.Icc_subset_Icc_right ht.2
    have h_int_deriv : HasDerivAt (fun v : ℝ => ∫ s in a..v, u s) (u t) t :=
      intervalIntegral.integral_hasDerivAt_right h_integrable_at (hu_smaf t ht)
        (hu_cont_at t ht)
    exact h_int_deriv.const_add (L a)
  -- Phase C: show `exp(L̃) = γ − w` on `Icc a b`.
  let F : ℝ → ℂ := fun t => Complex.exp (Ltil t) / (γ t - w)
  have hF_deriv : ∀ t ∈ Set.Icc a b, HasDerivAt F 0 t := by
    intro t ht
    have htU : t ∈ U := hUab ht
    have hw_ne : γ t - w ≠ 0 := hγw_ne t ht
    have h_exp_d : HasDerivAt (fun s => Complex.exp (Ltil s))
        (Complex.exp (Ltil t) * u t) t := (hLtil_deriv t ht).cexp
    have h_subw_d : HasDerivAt (fun s : ℝ => γ s - w) (deriv γ t) t :=
      (hγ_diff_U t htU).sub_const w
    have h_div := h_exp_d.div h_subw_d hw_ne
    have h_num_eq : Complex.exp (Ltil t) * u t * (γ t - w) -
        Complex.exp (Ltil t) * deriv γ t = 0 := by
      change Complex.exp (Ltil t) * ((γ t - w)⁻¹ * deriv γ t) * (γ t - w) -
          Complex.exp (Ltil t) * deriv γ t = 0
      have h_rewrite : Complex.exp (Ltil t) * ((γ t - w)⁻¹ * deriv γ t) * (γ t - w) =
          Complex.exp (Ltil t) * deriv γ t * ((γ t - w)⁻¹ * (γ t - w)) := by ring
      rw [h_rewrite, inv_mul_cancel₀ hw_ne, mul_one, sub_self]
    have h_val_zero : (Complex.exp (Ltil t) * u t * (γ t - w) -
        Complex.exp (Ltil t) * deriv γ t) / (γ t - w) ^ 2 = 0 := by
      rw [h_num_eq, zero_div]
    rw [← h_val_zero]
    exact h_div
  have hF_const : ∀ t ∈ Set.Icc a b, F t = F a := by
    intro t ht
    have hat : a ≤ t := ht.1
    have hF_at_uIcc : ∀ s ∈ Set.uIcc a t, HasDerivAt F 0 s := by
      intro s hs
      rw [Set.uIcc_of_le hat] at hs
      exact hF_deriv s ⟨hs.1, le_trans hs.2 ht.2⟩
    have h_integral := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F)
      hF_at_uIcc (intervalIntegrable_const)
    rw [intervalIntegral.integral_zero] at h_integral
    linear_combination -h_integral
  have hF_a : F a = 1 := by
    have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
    change Complex.exp (Ltil a) / (γ a - w) = 1
    rw [hLtil_a, hL_exp a ha_mem, div_self (hγw_ne a ha_mem)]
  have h_exp_Ltil : ∀ t ∈ Set.Icc a b, Complex.exp (Ltil t) = γ t - w := by
    intro t ht
    have hFt : F t = 1 := (hF_const t ht).trans hF_a
    have hFt' : Complex.exp (Ltil t) / (γ t - w) = 1 := hFt
    rw [div_eq_one_iff_eq (hγw_ne t ht)] at hFt'
    exact hFt'
  -- Phase D: show `L = L̃` on `Icc a b` via integer-continuity (same as C¹ FTC).
  let g : ℝ → ℂ := fun t => L t - Ltil t
  have hLtil_cont_on : ContinuousOn Ltil (Set.Icc a b) := fun t ht =>
    (hLtil_deriv t ht).continuousAt.continuousWithinAt
  have hg_cont_on : ContinuousOn g (Set.Icc a b) :=
    (hL_cont.continuousOn).sub hLtil_cont_on
  have h_exp_g : ∀ t ∈ Set.Icc a b, Complex.exp (g t) = 1 := by
    intro t ht
    change Complex.exp (L t - Ltil t) = 1
    rw [Complex.exp_sub, hL_exp t ht, h_exp_Ltil t ht, div_self (hγw_ne t ht)]
  have hg_int : ∀ t ∈ Set.Icc a b,
      ∃ n : ℤ, g t = (n : ℂ) * (2 * Real.pi * Complex.I) := fun t ht =>
    Complex.exp_eq_one_iff.mp (h_exp_g t ht)
  have hg_a : g a = 0 := by
    change L a - Ltil a = 0
    rw [hLtil_a, sub_self]
  let ψ : ℝ → ℝ := fun t => (g t).im / (2 * Real.pi)
  have hψ_cont_on : ContinuousOn ψ (Set.Icc a b) := by
    refine ContinuousOn.div_const ?_ (2 * Real.pi)
    exact Complex.continuous_im.comp_continuousOn hg_cont_on
  have hψ_int : ∀ t ∈ Set.Icc a b, ∃ n : ℤ, ψ t = (n : ℝ) := by
    intro t ht
    obtain ⟨n, hn⟩ := hg_int t ht
    refine ⟨n, ?_⟩
    have h_im : (g t).im = (n : ℝ) * (2 * Real.pi) := by
      rw [hn]
      simp [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    change (g t).im / (2 * Real.pi) = (n : ℝ)
    rw [h_im]
    have h_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp
  have hψ_a : ψ a = 0 := by
    change (g a).im / (2 * Real.pi) = 0
    rw [hg_a, Complex.zero_im, zero_div]
  have hψ_zero : ∀ t ∈ Set.Icc a b, ψ t = 0 := by
    intro t ht
    by_contra hψt_ne
    obtain ⟨n, hn⟩ := hψ_int t ht
    have hn_ne : (n : ℝ) ≠ 0 := hn ▸ hψt_ne
    have hn_int_ne : n ≠ 0 := by exact_mod_cast hn_ne
    have hψ_cont_at : ContinuousOn ψ (Set.Icc a t) :=
      hψ_cont_on.mono (Set.Icc_subset_Icc_right ht.2)
    rcases lt_or_gt_of_ne hn_ne with hn_neg | hn_pos
    · have hn_int_neg : n < 0 := by exact_mod_cast hn_neg
      have hn_int_le : n ≤ -1 := by omega
      have h_n_le : (n : ℝ) ≤ -1 := by exact_mod_cast hn_int_le
      have h_half_in : (-(1/2 : ℝ)) ∈ Set.Icc (ψ t) (ψ a) := by
        rw [hψ_a, hn]; exact ⟨by linarith, by norm_num⟩
      have h_ivt :=
        intermediate_value_Icc' (a := a) (b := t) ht.1 hψ_cont_at h_half_in
      obtain ⟨s, hs_mem, hs_val⟩ := h_ivt
      have hs_in_ab : s ∈ Set.Icc a b :=
        ⟨hs_mem.1, le_trans hs_mem.2 ht.2⟩
      obtain ⟨m, hm⟩ := hψ_int s hs_in_ab
      have hm_eq : (m : ℝ) = -(1/2) := by rw [← hm]; exact hs_val
      have : ((2 * m : ℤ) : ℝ) = -1 := by push_cast; linarith
      have h2m : (2 * m : ℤ) = -1 := by exact_mod_cast this
      omega
    · have hn_int_pos : 0 < n := by exact_mod_cast hn_pos
      have hn_int_ge : 1 ≤ n := by omega
      have h_n_ge : (1 : ℝ) ≤ n := by exact_mod_cast hn_int_ge
      have h_half_in : ((1/2 : ℝ)) ∈ Set.Icc (ψ a) (ψ t) := by
        rw [hψ_a, hn]; exact ⟨by norm_num, by linarith⟩
      have h_ivt :=
        intermediate_value_Icc (a := a) (b := t) ht.1 hψ_cont_at h_half_in
      obtain ⟨s, hs_mem, hs_val⟩ := h_ivt
      have hs_in_ab : s ∈ Set.Icc a b :=
        ⟨hs_mem.1, le_trans hs_mem.2 ht.2⟩
      obtain ⟨m, hm⟩ := hψ_int s hs_in_ab
      have hm_eq : (m : ℝ) = 1/2 := by rw [← hm]; exact hs_val
      have : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
      have h2m : (2 * m : ℤ) = 1 := by exact_mod_cast this
      omega
  have hg_im_zero : ∀ t ∈ Set.Icc a b, (g t).im = 0 := by
    intro t ht
    have hψt : ψ t = 0 := hψ_zero t ht
    have h1 : (g t).im / (2 * Real.pi) = 0 := hψt
    have h_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp at h1
    linarith
  have hg_re_zero : ∀ t ∈ Set.Icc a b, (g t).re = 0 := by
    intro t ht
    obtain ⟨n, hn⟩ := hg_int t ht
    rw [hn]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  have hg_zero : ∀ t ∈ Set.Icc a b, g t = 0 := fun t ht =>
    Complex.ext (hg_re_zero t ht) (hg_im_zero t ht)
  -- Phase E: conclude.
  have hL_b : L b = Ltil b := by
    have h_g_b : g b = 0 := hg_zero b ⟨hab, le_refl b⟩
    have h_g_b' : L b - Ltil b = 0 := h_g_b
    linear_combination h_g_b'
  unfold Complex.pathContourIntegral
  have h_integrand_eq : (fun t : ℝ => (fun z => (z - w)⁻¹) (γ t) * deriv γ t) = u := by
    funext _; rfl
  rw [h_integrand_eq]
  have h_integral : ∫ t in a..b, u t = Ltil b - Ltil a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Ltil) ?_ hu_integrable_ab
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact hLtil_deriv t ht
  rw [h_integral, hLtil_a, ← hL_b]

end NoWanderingDomains
