/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.OpenMapping
import NoWanderingDomains.Sphere.MobiusAction
import NoWanderingDomains.Sphere.RationalMap
import NoWanderingDomains.Sphere.SphereHolomorphic

/-!
# Nonconstant rational maps are open and surjective

A nonconstant rational map `f : ℂ̂ → ℂ̂` is an open map, hence (the sphere
being compact and connected) surjective. This is the analytic layer that
turns the abstract invariance theory of `Dynamics/JuliaFatou/` into
statements about rational dynamics.

The proof of openness is chart-local. Near a finite point the map reads as
the quotient `numReduced / denReduced` of coprime polynomials; near a pole
or near `∞` the reading is conjugated by the inversion `inversionGL`
(swapping `0 ↔ ∞`), with the point at infinity handled by the reflected
polynomials `Polynomial.reflect r.degree`. In every chart the reading is
analytic, so Mathlib's local dichotomy
`AnalyticAt.eventually_constant_or_nhds_le_map_nhds` applies: either the
reading is eventually constant — which propagates, by the polynomial
identity theorem, to global constancy of the rational map — or the map
sends neighborhoods to neighborhoods at that point.

Surjectivity follows from openness alone: the image of a continuous open
self-map of `ℂ̂` is open, compact (hence closed), and nonempty, so it is
all of the connected sphere.

## Main results

* `IsRational.isOpenMap` — a nonconstant rational map is an open map.
* `IsRational.surjective` — a nonconstant rational map is surjective.
* `IsRational.ne_const` — a nonconstant rational map is not a constant map.
* `IsRational.sphereHolomorphicOn_comp_coe`,
  `IsRational.sphereHolomorphicOn_comp_inversionGL` — the chart readings of a
  rational map are sphere-holomorphic.
* `exists_branch_of_deriv_ne_zero` — a local holomorphic branch exists where the
  derivative reading is nonzero.
-/

open OnePoint Polynomial Filter Topology Matrix

namespace NoWanderingDomains

/-- Rational maps are continuous. -/
theorem IsRational.continuous {f : ℂ̂ → ℂ̂} (hf : IsRational f) :
    Continuous f := by
  obtain ⟨r, rfl⟩ := hf
  exact r.continuous_toSphereMap

/-- Sending a quotient to the sphere with poles at the zeros of the
denominator is, after inversion, the reciprocal quotient: the value-level
form of "the inversion interchanges the two charts". -/
theorem ite_div_eq_inversionGL_smul {p q : ℂ} (hp : p ≠ 0) :
    (if q = 0 then (∞ : ℂ̂) else ((p / q : ℂ) : ℂ̂))
      = inversionGL • ((q / p : ℂ) : ℂ̂) := by
  by_cases hq : q = 0
  · rw [if_pos hq, hq, zero_div, inversionGL_smul_coe, if_pos rfl]
  · rw [if_neg hq, inversionGL_smul_coe, if_neg (div_ne_zero hq hp), inv_div]

/-- The reduced numerator and denominator of a `RationalData` have no
common zero. -/
theorem RationalData.eval_ne_zero_or (r : RationalData) (w : ℂ) :
    r.numReduced.eval w ≠ 0 ∨ r.denReduced.eval w ≠ 0 := by
  by_contra hcon
  obtain ⟨hn, hd⟩ := not_or.mp hcon
  have hn' : r.numReduced.eval w = 0 := not_not.mp hn
  have hd' : r.denReduced.eval w = 0 := not_not.mp hd
  have hcop : IsCoprime r.numReduced r.denReduced :=
    isCoprime_div_gcd_div_gcd r.den_ne_zero
  obtain ⟨a, b, hab⟩ := hcop
  have heval := congrArg (Polynomial.eval w) hab
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_one, hn', hd', mul_zero, mul_zero, add_zero] at heval
  exact zero_ne_one heval

/-- The reflections of the reduced numerator and denominator to the common
degree `r.degree` have no common zero: away from `0` a common zero would
reciprocate to a common zero of the reduced pair, and at `0` it would force
both polynomials to have degree strictly less than `r.degree = max`. -/
theorem RationalData.reflect_eval_ne_zero_or (r : RationalData) (w : ℂ) :
    (Polynomial.reflect r.degree r.numReduced).eval w ≠ 0 ∨
      (Polynomial.reflect r.degree r.denReduced).eval w ≠ 0 := by
  have hdeg : r.degree = max r.numReduced.natDegree r.denReduced.natDegree := rfl
  by_cases hw : w = 0
  · -- At `0` the reflected evaluations are the degree-`r.degree` coefficients,
    -- and the one realizing the max is a nonzero leading coefficient.
    subst hw
    have hn0 : (Polynomial.reflect r.degree r.numReduced).eval 0
        = r.numReduced.coeff r.degree := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
        Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero]
    have hd0 : (Polynomial.reflect r.degree r.denReduced).eval 0
        = r.denReduced.coeff r.degree := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
        Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero]
    rw [hn0, hd0]
    rcases lt_or_ge r.denReduced.natDegree r.numReduced.natDegree with hlt | hle
    · left
      have hd_eq : r.degree = r.numReduced.natDegree := by
        rw [hdeg]; exact max_eq_left hlt.le
      have hnum_ne : r.numReduced ≠ 0 := by
        intro hz
        rw [hz, Polynomial.natDegree_zero] at hlt
        exact Nat.not_lt_zero _ hlt
      rw [hd_eq, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hnum_ne
    · right
      have hdenR_ne_zero : r.denReduced ≠ 0 := r.denReduced_ne_zero
      have hd_eq : r.degree = r.denReduced.natDegree := by
        rw [hdeg]; exact max_eq_right hle
      rw [hd_eq, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hdenR_ne_zero
  · -- Away from `0` reflect-evaluation is `w ^ degree` times evaluation of the
    -- original polynomial at `w⁻¹`, so a common zero reciprocates.
    have hnum_le : r.numReduced.natDegree ≤ r.degree := le_max_left _ _
    have hden_le : r.denReduced.natDegree ≤ r.degree := le_max_right _ _
    have reflect_eval : ∀ (N : ℕ) (p : ℂ[X]), p.natDegree ≤ N → ∀ x : ℂ, x ≠ 0 →
        (Polynomial.reflect N p).eval x = x ^ N * p.eval x⁻¹ := by
      intro N p hp x hx
      have : Invertible (x⁻¹ : ℂ) := invertibleOfNonzero (inv_ne_zero hx)
      have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) x⁻¹ N p hp
      rw [Polynomial.eval₂_id, Polynomial.eval₂_id, invOf_eq_inv, inv_inv, inv_pow,
        ← div_eq_mul_inv, div_eq_iff (pow_ne_zero N hx)] at h
      exact h.trans (mul_comm _ _)
    rw [reflect_eval r.degree r.numReduced hnum_le w hw,
      reflect_eval r.degree r.denReduced hden_le w hw]
    have hwd : (w : ℂ) ^ r.degree ≠ 0 := pow_ne_zero _ hw
    rcases r.eval_ne_zero_or w⁻¹ with h | h
    · exact Or.inl (mul_ne_zero hwd h)
    · exact Or.inr (mul_ne_zero hwd h)

/-- **The infinity-chart reading of a rational map.** Composing with the
inversion parameterization `w ↦ inversionGL • ↑w` of a neighborhood of `∞`,
a rational map reads as the quotient of the reflected polynomials
`Polynomial.reflect r.degree` — including at `w = 0`, where the formula
recovers the defining value of `toSphereMap` at `∞`. -/
theorem RationalData.toSphereMap_inversionGL_smul_coe (r : RationalData)
    (w : ℂ) :
    r.toSphereMap (inversionGL • (w : ℂ̂))
      = if (Polynomial.reflect r.degree r.denReduced).eval w = 0 then ∞
        else (((Polynomial.reflect r.degree r.numReduced).eval w
              / (Polynomial.reflect r.degree r.denReduced).eval w : ℂ) : ℂ̂) := by
  have hdeg : r.degree = max r.numReduced.natDegree r.denReduced.natDegree := rfl
  by_cases hw : w = 0
  · -- At `w = 0` the left side is the defining value of `toSphereMap` at `∞`
    -- and the right side reads off the degree-`r.degree` coefficients.
    subst hw
    rw [inversionGL_smul_coe, if_pos rfl]
    have hn0 : (Polynomial.reflect r.degree r.numReduced).eval 0
        = r.numReduced.coeff r.degree := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
        Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero]
    have hd0 : (Polynomial.reflect r.degree r.denReduced).eval 0
        = r.denReduced.coeff r.degree := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
        Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero]
    rw [hn0, hd0]
    have htop : r.toSphereMap ∞
        = if r.numReduced.natDegree < r.denReduced.natDegree then ((0 : ℂ) : ℂ̂)
          else if r.numReduced.natDegree = r.denReduced.natDegree then
            ((r.numReduced.leadingCoeff / r.denReduced.leadingCoeff : ℂ) : ℂ̂)
          else ∞ := rfl
    have hdenR_ne_zero : r.denReduced ≠ 0 := r.denReduced_ne_zero
    rcases lt_trichotomy r.numReduced.natDegree r.denReduced.natDegree with hlt | heq | hgt
    · -- `deg num < deg den`: the value at `∞` is `0`, and the reflected
      -- numerator coefficient vanishes while the denominator one does not.
      have hd_eq : r.degree = r.denReduced.natDegree := by
        rw [hdeg]; exact max_eq_right hlt.le
      have hden_ne : r.denReduced.coeff r.degree ≠ 0 := by
        rw [hd_eq, Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hdenR_ne_zero
      have hnum_zero : r.numReduced.coeff r.degree = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd_eq]; exact hlt)
      rw [if_neg hden_ne, hnum_zero, zero_div, htop, if_pos hlt]
    · -- `deg num = deg den`: both coefficients are the leading coefficients.
      have hn_eq : r.degree = r.numReduced.natDegree := by
        rw [hdeg, heq, max_self]
      have hd_eq : r.degree = r.denReduced.natDegree := by
        rw [hdeg, heq, max_self]
      have hden_ne : r.denReduced.coeff r.degree ≠ 0 := by
        rw [hd_eq, Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hdenR_ne_zero
      rw [if_neg hden_ne, htop, if_neg (not_lt.mpr heq.ge), if_pos heq,
        hn_eq, Polynomial.coeff_natDegree, heq, Polynomial.coeff_natDegree]
    · -- `deg num > deg den`: the value at `∞` is `∞`, and the reflected
      -- denominator coefficient vanishes.
      have hd_eq : r.degree = r.numReduced.natDegree := by
        rw [hdeg]; exact max_eq_left hgt.le
      have hden_zero : r.denReduced.coeff r.degree = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd_eq]; exact hgt)
      rw [if_pos hden_zero, htop, if_neg (not_lt.mpr hgt.le), if_neg (ne_of_gt hgt)]
  · -- At `w ≠ 0` the inversion lands at the finite point `w⁻¹`, and the
    -- reflected evaluations are `w ^ degree` times the evaluations at `w⁻¹`.
    have hnum_le : r.numReduced.natDegree ≤ r.degree := le_max_left _ _
    have hden_le : r.denReduced.natDegree ≤ r.degree := le_max_right _ _
    have reflect_eval : ∀ (N : ℕ) (p : ℂ[X]), p.natDegree ≤ N → ∀ x : ℂ, x ≠ 0 →
        (Polynomial.reflect N p).eval x = x ^ N * p.eval x⁻¹ := by
      intro N p hp x hx
      have : Invertible (x⁻¹ : ℂ) := invertibleOfNonzero (inv_ne_zero hx)
      have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) x⁻¹ N p hp
      rw [Polynomial.eval₂_id, Polynomial.eval₂_id, invOf_eq_inv, inv_inv, inv_pow,
        ← div_eq_mul_inv, div_eq_iff (pow_ne_zero N hx)] at h
      exact h.trans (mul_comm _ _)
    rw [inversionGL_smul_coe, if_neg hw]
    have hcoe : r.toSphereMap ((w⁻¹ : ℂ) : ℂ̂)
        = if r.denReduced.eval w⁻¹ = 0 then ∞
          else ((r.numReduced.eval w⁻¹ / r.denReduced.eval w⁻¹ : ℂ) : ℂ̂) := rfl
    rw [hcoe, reflect_eval r.degree r.numReduced hnum_le w hw,
      reflect_eval r.degree r.denReduced hden_le w hw]
    have hwd : (w : ℂ) ^ r.degree ≠ 0 := pow_ne_zero _ hw
    by_cases hden : r.denReduced.eval w⁻¹ = 0
    · rw [if_pos hden, if_pos (by rw [hden, mul_zero])]
    · rw [if_neg hden, if_neg (mul_ne_zero hwd hden), mul_div_mul_left _ _ hwd]

/-- **Identity-theorem propagation.** A rational map that is eventually
constant near any point of the sphere is globally constant: every sphere
neighborhood contains infinitely many finite points, so the polynomial
`numReduced - c * denReduced` has infinitely many roots and vanishes, and
coprimality then forces the denominator to be a nonvanishing constant. -/
theorem RationalData.toSphereMap_eq_const_of_eventuallyEq {r : RationalData}
    {z₀ : ℂ̂} {c : ℂ̂} (h : ∀ᶠ z in nhds z₀, r.toSphereMap z = c) :
    r.toSphereMap = Function.const ℂ̂ c := by
  have hdenR_ne_zero : r.denReduced ≠ 0 := r.denReduced_ne_zero
  have hcop : IsCoprime r.numReduced r.denReduced :=
    isCoprime_div_gcd_div_gcd r.den_ne_zero
  -- Step 1: infinitely many finite points carry the value `c`.
  obtain ⟨V, hV, hVall⟩ := h.exists_mem
  have hS : {w : ℂ | r.toSphereMap ↑w = c}.Infinite := by
    have hV_inf : V.Infinite := infinite_of_mem_nhds z₀ hV
    have hdiff : (V \ {∞}).Infinite := hV_inf.sdiff (Set.finite_singleton ∞)
    have himg : (((↑) : ℂ → ℂ̂) '' (((↑) : ℂ → ℂ̂) ⁻¹' V)).Infinite := by
      refine Set.Infinite.mono ?_ hdiff
      intro z hz
      cases z with
      | infty => exact absurd rfl hz.2
      | coe w => exact ⟨w, hz.1, rfl⟩
    exact (Set.Infinite.of_image _ himg).mono fun w hw => hVall _ hw
  clear hVall hV
  -- Step 2: case on the constant value.
  cases c with
  | infty =>
    -- A rational map is `∞` only at the (finitely many) roots of `denReduced`.
    exfalso
    apply hdenR_ne_zero
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ hS
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    change r.denReduced.eval w = 0
    by_contra hne
    simp only [RationalData.toSphereMap, hne, if_false] at hw
    exact OnePoint.coe_ne_infty _ hw
  | coe c' =>
    -- The polynomial `numReduced - C c' * denReduced` has infinitely many roots.
    have hpoly : r.numReduced - Polynomial.C c' * r.denReduced = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono ?_ hS
      intro w hw
      simp only [Set.mem_ofPred_eq] at hw ⊢
      change (r.numReduced - Polynomial.C c' * r.denReduced).eval w = 0
      by_cases hdw : r.denReduced.eval w = 0
      · simp only [RationalData.toSphereMap, hdw, if_true] at hw
        exact absurd hw (OnePoint.infty_ne_coe _)
      · simp only [RationalData.toSphereMap, hdw, if_false] at hw
        have hw' : r.numReduced.eval w / r.denReduced.eval w = c' :=
          OnePoint.coe_eq_coe.mp hw
        rw [div_eq_iff hdw] at hw'
        rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hw']
        exact sub_self _
    have hnum_eq : r.numReduced = Polynomial.C c' * r.denReduced := sub_eq_zero.mp hpoly
    -- Coprimality forces the denominator to be a nonzero constant.
    have hdvd : r.denReduced ∣ r.numReduced := by
      rw [hnum_eq]; exact dvd_mul_left _ _
    have hunit : IsUnit r.denReduced := hcop.isUnit_of_dvd' hdvd dvd_rfl
    obtain ⟨u, hu_unit, hu⟩ := Polynomial.isUnit_iff.mp hunit
    have hu_ne : u ≠ 0 := hu_unit.ne_zero
    have hn_deg : r.numReduced.natDegree = 0 := by
      rw [hnum_eq, ← hu, ← Polynomial.C_mul]
      exact Polynomial.natDegree_C _
    have hd_deg : r.denReduced.natDegree = 0 := by
      rw [← hu]
      exact Polynomial.natDegree_C _
    funext z
    cases z with
    | infty =>
      simp only [RationalData.toSphereMap, Function.const_apply]
      rw [hn_deg, hd_deg, if_neg (lt_irrefl 0), if_pos rfl, OnePoint.coe_eq_coe,
          hnum_eq, ← hu, ← Polynomial.C_mul, Polynomial.leadingCoeff_C,
          Polynomial.leadingCoeff_C]
      exact mul_div_cancel_right₀ c' hu_ne
    | coe w =>
      have hd_ne : r.denReduced.eval w ≠ 0 := by
        rw [← hu, Polynomial.eval_C]
        exact hu_ne
      simp only [RationalData.toSphereMap, Function.const_apply, hd_ne, if_false]
      rw [OnePoint.coe_eq_coe, hnum_eq, ← hu, ← Polynomial.C_mul, Polynomial.eval_C,
          Polynomial.eval_C]
      exact mul_div_cancel_right₀ c' hu_ne

/-- **Nonconstant rational maps are open.** Chart-local proof via the
analytic open-mapping dichotomy in each of the four chart configurations. -/
theorem IsRational.isOpenMap {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hnc : ∀ c : ℂ̂, f ≠ Function.const ℂ̂ c) : IsOpenMap f := by
  rw [isOpenMap_iff_nhds_le]
  obtain ⟨r, rfl⟩ := hf
  -- Eventual constancy near any point contradicts nonconstancy.
  have hkill : ∀ (z₁ c : ℂ̂), (∀ᶠ z in 𝓝 z₁, r.toSphereMap z = c) → False :=
    fun _ c hc => hnc c (RationalData.toSphereMap_eq_const_of_eventuallyEq hc)
  -- The inversion is an involutive homeomorphism of the sphere.
  have hJJ : inversionGL * inversionGL = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [inversionGL, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hinvol : ∀ z : ℂ̂, inversionGL • inversionGL • z = z := by
    intro z
    rw [← SemigroupAction.mul_smul, hJJ, one_smul]
  have hT : ∀ x : ℂ̂,
      map (fun z : ℂ̂ => inversionGL • z) (𝓝 x) = 𝓝 (inversionGL • x) := by
    intro x
    exact Homeomorph.map_nhds_eq
      ⟨⟨fun z => inversionGL • z, fun z => inversionGL • z, hinvol, hinvol⟩,
        continuous_gl_smul _, continuous_gl_smul _⟩ x
  -- Neighborhood transport along the two chart parameterizations.
  have hcoe : ∀ w : ℂ, map ((↑) : ℂ → ℂ̂) (𝓝 w) = 𝓝 (w : ℂ̂) :=
    fun w => OnePoint.isOpenEmbedding_coe.map_nhds_eq w
  have hpsi : ∀ x : ℂ,
      map (fun w : ℂ => inversionGL • (w : ℂ̂)) (𝓝 x) = 𝓝 (inversionGL • (x : ℂ̂)) := by
    intro x
    calc map (fun w : ℂ => inversionGL • (w : ℂ̂)) (𝓝 x)
        = map (fun z : ℂ̂ => inversionGL • z) (map ((↑) : ℂ → ℂ̂) (𝓝 x)) :=
          (Filter.map_map (m := ((↑) : ℂ → ℂ̂)) (m' := fun z : ℂ̂ => inversionGL • z)).symm
      _ = map (fun z : ℂ̂ => inversionGL • z) (𝓝 (x : ℂ̂)) := by rw [hcoe]
      _ = 𝓝 (inversionGL • (x : ℂ̂)) := hT _
  have hzero : inversionGL • ((0 : ℂ) : ℂ̂) = ∞ := by
    rw [inversionGL_smul_coe]
    exact if_pos rfl
  -- Analyticity of polynomial quotients at points where the denominator is nonzero.
  have hdivA : ∀ (p q : ℂ[X]) (x : ℂ), q.eval x ≠ 0 →
      AnalyticAt ℂ (fun w => p.eval w / q.eval w) x := fun p q x hx =>
    (p.differentiable.analyticAt x).div (q.differentiable.analyticAt x) hx
  -- Polynomials that do not vanish at a point do not vanish nearby.
  have hevne : ∀ (q : ℂ[X]) (x : ℂ), q.eval x ≠ 0 → ∀ᶠ w in 𝓝 x, q.eval w ≠ 0 :=
    fun q x hx => (q.continuous.continuousAt).eventually_ne hx
  -- The defining reading of `toSphereMap` at finite points.
  have hread_coe : ∀ w : ℂ, r.toSphereMap ↑w
      = if r.denReduced.eval w = 0 then (∞ : ℂ̂)
        else ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂) := fun _ => rfl
  -- The generic chart-local open-mapping step: a source parameterization `φ`,
  -- a target parameterization `ψ`, and an analytic local reading `g` together
  -- transport the analytic dichotomy to the sphere map.
  have hmain : ∀ (φ ψ : ℂ → ℂ̂) (g : ℂ → ℂ) (w₀ : ℂ),
      AnalyticAt ℂ g w₀ →
      map φ (𝓝 w₀) = 𝓝 (φ w₀) →
      map ψ (𝓝 (g w₀)) = 𝓝 (ψ (g w₀)) →
      (∀ᶠ w in 𝓝 w₀, r.toSphereMap (φ w) = ψ (g w)) →
      r.toSphereMap (φ w₀) = ψ (g w₀) →
      𝓝 (r.toSphereMap (φ w₀)) ≤ map r.toSphereMap (𝓝 (φ w₀)) := by
    intro φ ψ g w₀ hg hφ hψ hev hval
    rcases hg.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
    · exfalso
      apply hkill (φ w₀) (ψ (g w₀))
      rw [← hφ, eventually_map]
      filter_upwards [hev, hconst] with w hw hwc
      rw [hw, hwc]
    · calc 𝓝 (r.toSphereMap (φ w₀))
          = 𝓝 (ψ (g w₀)) := by rw [hval]
        _ = map ψ (𝓝 (g w₀)) := hψ.symm
        _ ≤ map ψ (map g (𝓝 w₀)) := Filter.map_mono hopen
        _ = map (fun w => ψ (g w)) (𝓝 w₀) := Filter.map_map
        _ = map (fun w => r.toSphereMap (φ w)) (𝓝 w₀) :=
            Filter.map_congr (hev.mono fun w hw => hw.symm)
        _ = map r.toSphereMap (map φ (𝓝 w₀)) :=
            (Filter.map_map (m := φ) (m' := r.toSphereMap)).symm
        _ = map r.toSphereMap (𝓝 (φ w₀)) := by rw [hφ]
  intro z₀
  cases z₀ with
  | coe w₀ =>
    by_cases hden : r.denReduced.eval w₀ = 0
    · -- Pole: the map reads, through the inversion, as `denReduced / numReduced`.
      have hnum : r.numReduced.eval w₀ ≠ 0 :=
        (r.eval_ne_zero_or w₀).resolve_right fun h => h hden
      have hev : ∀ᶠ (w : ℂ) in 𝓝 w₀, r.toSphereMap ↑w
          = inversionGL • ((r.denReduced.eval w / r.numReduced.eval w : ℂ) : ℂ̂) := by
        filter_upwards [hevne r.numReduced w₀ hnum] with w hw
        rw [hread_coe w]
        exact ite_div_eq_inversionGL_smul hw
      have hval : r.toSphereMap ↑w₀
          = inversionGL • ((r.denReduced.eval w₀ / r.numReduced.eval w₀ : ℂ) : ℂ̂) := by
        rw [hread_coe w₀]
        exact ite_div_eq_inversionGL_smul hnum
      exact hmain ((↑) : ℂ → ℂ̂) (fun x : ℂ => inversionGL • (x : ℂ̂))
        (fun w => r.denReduced.eval w / r.numReduced.eval w) w₀
        (hdivA r.denReduced r.numReduced w₀ hnum) (hcoe w₀)
        (hpsi (r.denReduced.eval w₀ / r.numReduced.eval w₀)) hev hval
    · -- Regular point: the map reads directly as `numReduced / denReduced`.
      have hev : ∀ᶠ (w : ℂ) in 𝓝 w₀, r.toSphereMap ↑w
          = ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂) := by
        filter_upwards [hevne r.denReduced w₀ hden] with w hw
        rw [hread_coe w, if_neg hw]
      have hval : r.toSphereMap ↑w₀
          = ((r.numReduced.eval w₀ / r.denReduced.eval w₀ : ℂ) : ℂ̂) := by
        rw [hread_coe w₀, if_neg hden]
      exact hmain ((↑) : ℂ → ℂ̂) ((↑) : ℂ → ℂ̂)
        (fun w => r.numReduced.eval w / r.denReduced.eval w) w₀
        (hdivA r.numReduced r.denReduced w₀ hden) (hcoe w₀)
        (hcoe (r.numReduced.eval w₀ / r.denReduced.eval w₀)) hev hval
  | infty =>
    rw [← hzero]
    by_cases hQ : (Polynomial.reflect r.degree r.denReduced).eval 0 = 0
    · -- `f ∞ = ∞`: read through the inversion on both source and target sides.
      have hP : (Polynomial.reflect r.degree r.numReduced).eval 0 ≠ 0 :=
        (r.reflect_eval_ne_zero_or 0).resolve_right fun h => h hQ
      have hev : ∀ᶠ (w : ℂ) in 𝓝 (0 : ℂ), r.toSphereMap (inversionGL • (w : ℂ̂))
          = inversionGL • (((Polynomial.reflect r.degree r.denReduced).eval w
              / (Polynomial.reflect r.degree r.numReduced).eval w : ℂ) : ℂ̂) := by
        filter_upwards [hevne (Polynomial.reflect r.degree r.numReduced) 0 hP] with w hw
        rw [r.toSphereMap_inversionGL_smul_coe w]
        exact ite_div_eq_inversionGL_smul hw
      have hval : r.toSphereMap (inversionGL • ((0 : ℂ) : ℂ̂))
          = inversionGL • (((Polynomial.reflect r.degree r.denReduced).eval 0
              / (Polynomial.reflect r.degree r.numReduced).eval 0 : ℂ) : ℂ̂) := by
        rw [r.toSphereMap_inversionGL_smul_coe 0]
        exact ite_div_eq_inversionGL_smul hP
      exact hmain (fun w : ℂ => inversionGL • (w : ℂ̂))
        (fun x : ℂ => inversionGL • (x : ℂ̂))
        (fun w => (Polynomial.reflect r.degree r.denReduced).eval w
          / (Polynomial.reflect r.degree r.numReduced).eval w) 0
        (hdivA (Polynomial.reflect r.degree r.denReduced)
          (Polynomial.reflect r.degree r.numReduced) 0 hP) (hpsi 0)
        (hpsi ((Polynomial.reflect r.degree r.denReduced).eval 0
          / (Polynomial.reflect r.degree r.numReduced).eval 0)) hev hval
    · -- `f ∞` finite: read through the inversion on the source side only.
      have hev : ∀ᶠ (w : ℂ) in 𝓝 (0 : ℂ), r.toSphereMap (inversionGL • (w : ℂ̂))
          = (((Polynomial.reflect r.degree r.numReduced).eval w
              / (Polynomial.reflect r.degree r.denReduced).eval w : ℂ) : ℂ̂) := by
        filter_upwards [hevne (Polynomial.reflect r.degree r.denReduced) 0 hQ] with w hw
        rw [r.toSphereMap_inversionGL_smul_coe w, if_neg hw]
      have hval : r.toSphereMap (inversionGL • ((0 : ℂ) : ℂ̂))
          = (((Polynomial.reflect r.degree r.numReduced).eval 0
              / (Polynomial.reflect r.degree r.denReduced).eval 0 : ℂ) : ℂ̂) := by
        rw [r.toSphereMap_inversionGL_smul_coe 0, if_neg hQ]
      exact hmain (fun w : ℂ => inversionGL • (w : ℂ̂)) ((↑) : ℂ → ℂ̂)
        (fun w => (Polynomial.reflect r.degree r.numReduced).eval w
          / (Polynomial.reflect r.degree r.denReduced).eval w) 0
        (hdivA (Polynomial.reflect r.degree r.numReduced)
          (Polynomial.reflect r.degree r.denReduced) 0 hQ) (hpsi 0)
        (hcoe ((Polynomial.reflect r.degree r.numReduced).eval 0
          / (Polynomial.reflect r.degree r.denReduced).eval 0)) hev hval

/-- A continuous open self-map of the sphere is surjective: its image is
open, closed (compact in a Hausdorff space), and nonempty, hence the whole
connected sphere. -/
theorem surjective_of_continuous_isOpenMap {f : ℂ̂ → ℂ̂}
    (hf : Continuous f) (hfo : IsOpenMap f) : Function.Surjective f := by
  have hclopen : IsClopen (Set.range f) :=
    ⟨(isCompact_range hf).isClosed, hfo.isOpen_range⟩
  exact Set.range_eq_univ.mp (hclopen.eq_univ (Set.range_nonempty f))

/-- **Nonconstant rational maps are surjective.** -/
theorem IsRational.surjective {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hnc : ∀ c : ℂ̂, f ≠ Function.const ℂ̂ c) : Function.Surjective f :=
  surjective_of_continuous_isOpenMap hf.continuous (hf.isOpenMap hnc)

/-- A rational map of degree at least one is nonconstant: the constant map
`∞` is not rational (its denominator would vanish identically), and a
finite constant is rational of degree zero by
`degreeOfRational_eq_of_witness`. -/
theorem IsRational.ne_const {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hd : 1 ≤ degreeOfRational f) (c : ℂ̂) : f ≠ Function.const ℂ̂ c := by
  intro hc
  obtain ⟨r, hr⟩ := hf
  have hdenR_ne_zero : r.denReduced ≠ 0 := r.denReduced_ne_zero
  have hcop : IsCoprime r.numReduced r.denReduced :=
    isCoprime_div_gcd_div_gcd r.den_ne_zero
  have hval : ∀ w : ℂ, r.toSphereMap ↑w = c := by
    intro w
    rw [← hr, hc, Function.const_apply]
  cases c with
  | infty =>
    -- The denominator would vanish at every finite point.
    apply hdenR_ne_zero
    apply Polynomial.funext
    intro w
    rw [Polynomial.eval_zero]
    have hw := hval w
    by_contra hne
    simp only [RationalData.toSphereMap, hne, if_false] at hw
    exact OnePoint.coe_ne_infty _ hw
  | coe c' =>
    -- The identity `numReduced = C c' * denReduced` holds at every point.
    have hnum_eq : r.numReduced = Polynomial.C c' * r.denReduced := by
      apply Polynomial.funext
      intro w
      have hw := hval w
      rw [Polynomial.eval_mul, Polynomial.eval_C]
      by_cases hdw : r.denReduced.eval w = 0
      · simp only [RationalData.toSphereMap, hdw, if_true] at hw
        exact absurd hw (OnePoint.infty_ne_coe _)
      · simp only [RationalData.toSphereMap, hdw, if_false] at hw
        have hw' : r.numReduced.eval w / r.denReduced.eval w = c' :=
          OnePoint.coe_eq_coe.mp hw
        rw [div_eq_iff hdw] at hw'
        exact hw'
    have hdvd : r.denReduced ∣ r.numReduced := by
      rw [hnum_eq]; exact dvd_mul_left _ _
    have hunit : IsUnit r.denReduced := hcop.isUnit_of_dvd' hdvd dvd_rfl
    obtain ⟨u, hu_unit, hu⟩ := Polynomial.isUnit_iff.mp hunit
    have hn_deg : r.numReduced.natDegree = 0 := by
      rw [hnum_eq, ← hu, ← Polynomial.C_mul]
      exact Polynomial.natDegree_C _
    have hd_deg : r.denReduced.natDegree = 0 := by
      rw [← hu]
      exact Polynomial.natDegree_C _
    have hdeg0 : degreeOfRational f = 0 := by
      rw [degreeOfRational_eq_of_witness f r hr]
      unfold RationalData.degree
      rw [hn_deg, hd_deg]
      exact Nat.max_self 0
    omega

/-- The finite-chart reading of a rational map is sphere-holomorphic: near a
regular point it reads holomorphically in the finite chart, and near a pole
the infinity-chart reading is the reciprocal quotient, which extends
holomorphically across the pole. -/
theorem IsRational.sphereHolomorphicOn_comp_coe {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) {U : Set ℂ} (hU : IsOpen U) :
    SphereHolomorphicOn (fun w => f ((w : ℂ̂))) U := by
  obtain ⟨r, rfl⟩ := hf
  have cf : ∀ x : ℂ, chartFiniteMap (x : ℂ̂) = x := fun _ => rfl
  have ci : ∀ x : ℂ, chartInftyMap (x : ℂ̂) = x⁻¹ := fun _ => rfl
  have ci0 : chartInftyMap (∞ : ℂ̂) = 0 := rfl
  have hread : ∀ w : ℂ, r.toSphereMap ↑w
      = if r.denReduced.eval w = 0 then (∞ : ℂ̂)
        else ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂) := fun _ => rfl
  intro z hz
  by_cases hden : r.denReduced.eval z = 0
  · -- Pole: read in the infinity chart as the reciprocal quotient.
    have hnum : r.numReduced.eval z ≠ 0 :=
      (r.eval_ne_zero_or z).resolve_right fun h => h hden
    have hcont : ContinuousAt (fun w => r.numReduced.eval w) z :=
      r.numReduced.continuous.continuousAt
    obtain ⟨t, ht_ne, ht_open, hzt⟩ := eventually_nhds_iff.mp (hcont.eventually_ne hnum)
    refine ⟨U ∩ t, hU.inter ht_open, ⟨hz, hzt⟩, Set.inter_subset_left, Or.inr ⟨?_, ?_⟩⟩
    · intro w hw
      simp only [hread]
      split_ifs with hdw
      · exact OnePoint.infty_ne_coe 0
      · intro hc
        exact div_ne_zero (ht_ne w hw.2) hdw (OnePoint.coe_eq_coe.mp hc)
    · have hinv : DifferentiableOn ℂ (fun w => (r.numReduced.eval w)⁻¹) (U ∩ t) :=
        r.numReduced.differentiable.differentiableOn.inv fun w hw => ht_ne w hw.2
      have hdiv : DifferentiableOn ℂ
          (fun w => r.denReduced.eval w * (r.numReduced.eval w)⁻¹) (U ∩ t) :=
        r.denReduced.differentiable.differentiableOn.mul hinv
      refine hdiv.congr fun w _ => ?_
      simp only [hread]
      split_ifs with hdw
      · rw [ci0, hdw, zero_mul]
      · rw [ci, inv_div, div_eq_mul_inv]
  · -- Regular point: read in the finite chart as the quotient itself.
    have hcont : ContinuousAt (fun w => r.denReduced.eval w) z :=
      r.denReduced.continuous.continuousAt
    obtain ⟨t, ht_ne, ht_open, hzt⟩ := eventually_nhds_iff.mp (hcont.eventually_ne hden)
    refine ⟨U ∩ t, hU.inter ht_open, ⟨hz, hzt⟩, Set.inter_subset_left, Or.inl ⟨?_, ?_⟩⟩
    · intro w hw
      simp only [hread]
      rw [if_neg (ht_ne w hw.2)]
      exact OnePoint.coe_ne_infty _
    · have hinv : DifferentiableOn ℂ (fun w => (r.denReduced.eval w)⁻¹) (U ∩ t) :=
        r.denReduced.differentiable.differentiableOn.inv fun w hw => ht_ne w hw.2
      have hdiv : DifferentiableOn ℂ
          (fun w => r.numReduced.eval w * (r.denReduced.eval w)⁻¹) (U ∩ t) :=
        r.numReduced.differentiable.differentiableOn.mul hinv
      refine hdiv.congr fun w hw => ?_
      simp only [hread]
      rw [if_neg (ht_ne w hw.2), cf, div_eq_mul_inv]

/-- The infinity-chart reading of a rational map is sphere-holomorphic: the
reading through the inversion parameterization of a neighborhood of `∞` is
the quotient of the reflected polynomials. -/
theorem IsRational.sphereHolomorphicOn_comp_inversionGL {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) {U : Set ℂ} (hU : IsOpen U) :
    SphereHolomorphicOn (fun w => f (inversionGL • (w : ℂ̂))) U := by
  obtain ⟨r, rfl⟩ := hf
  have cf : ∀ x : ℂ, chartFiniteMap (x : ℂ̂) = x := fun _ => rfl
  have ci : ∀ x : ℂ, chartInftyMap (x : ℂ̂) = x⁻¹ := fun _ => rfl
  have ci0 : chartInftyMap (∞ : ℂ̂) = 0 := rfl
  have hread := r.toSphereMap_inversionGL_smul_coe
  intro z hz
  by_cases hden : (Polynomial.reflect r.degree r.denReduced).eval z = 0
  · -- Pole: read in the infinity chart as the reciprocal reflected quotient.
    have hnum : (Polynomial.reflect r.degree r.numReduced).eval z ≠ 0 :=
      (r.reflect_eval_ne_zero_or z).resolve_right fun h => h hden
    have hcont : ContinuousAt (fun w => (Polynomial.reflect r.degree r.numReduced).eval w) z :=
      (Polynomial.reflect r.degree r.numReduced).continuous.continuousAt
    obtain ⟨t, ht_ne, ht_open, hzt⟩ := eventually_nhds_iff.mp (hcont.eventually_ne hnum)
    refine ⟨U ∩ t, hU.inter ht_open, ⟨hz, hzt⟩, Set.inter_subset_left, Or.inr ⟨?_, ?_⟩⟩
    · intro w hw
      simp only [hread]
      split_ifs with hdw
      · exact OnePoint.infty_ne_coe 0
      · intro hc
        exact div_ne_zero (ht_ne w hw.2) hdw (OnePoint.coe_eq_coe.mp hc)
    · have hinv : DifferentiableOn ℂ
          (fun w => ((Polynomial.reflect r.degree r.numReduced).eval w)⁻¹) (U ∩ t) :=
        (Polynomial.reflect r.degree r.numReduced).differentiable.differentiableOn.inv
          fun w hw => ht_ne w hw.2
      have hdiv : DifferentiableOn ℂ
          (fun w => (Polynomial.reflect r.degree r.denReduced).eval w
            * ((Polynomial.reflect r.degree r.numReduced).eval w)⁻¹) (U ∩ t) :=
        (Polynomial.reflect r.degree r.denReduced).differentiable.differentiableOn.mul hinv
      refine hdiv.congr fun w _ => ?_
      simp only [hread]
      split_ifs with hdw
      · rw [ci0, hdw, zero_mul]
      · rw [ci, inv_div, div_eq_mul_inv]
  · -- Regular point: read in the finite chart as the reflected quotient.
    have hcont : ContinuousAt (fun w => (Polynomial.reflect r.degree r.denReduced).eval w) z :=
      (Polynomial.reflect r.degree r.denReduced).continuous.continuousAt
    obtain ⟨t, ht_ne, ht_open, hzt⟩ := eventually_nhds_iff.mp (hcont.eventually_ne hden)
    refine ⟨U ∩ t, hU.inter ht_open, ⟨hz, hzt⟩, Set.inter_subset_left, Or.inl ⟨?_, ?_⟩⟩
    · intro w hw
      simp only [hread]
      rw [if_neg (ht_ne w hw.2)]
      exact OnePoint.coe_ne_infty _
    · have hinv : DifferentiableOn ℂ
          (fun w => ((Polynomial.reflect r.degree r.denReduced).eval w)⁻¹) (U ∩ t) :=
        (Polynomial.reflect r.degree r.denReduced).differentiable.differentiableOn.inv
          fun w hw => ht_ne w hw.2
      have hdiv : DifferentiableOn ℂ
          (fun w => (Polynomial.reflect r.degree r.numReduced).eval w
            * ((Polynomial.reflect r.degree r.denReduced).eval w)⁻¹) (U ∩ t) :=
        (Polynomial.reflect r.degree r.numReduced).differentiable.differentiableOn.mul hinv
      refine hdiv.congr fun w hw => ?_
      simp only [hread]
      rw [if_neg (ht_ne w hw.2), cf, div_eq_mul_inv]

/-- The Wronskian `num′·den − num·den′` of the reduced representation. Its
zeros among non-poles are exactly the critical points of the finite-chart
reading. -/
noncomputable def RationalData.wronskian (r : RationalData) : ℂ[X] :=
  Polynomial.derivative r.numReduced * r.denReduced
    - r.numReduced * Polynomial.derivative r.denReduced

/-- The Wronskian of a rational map of degree at least two is a nonzero
polynomial: its vanishing would force both reduced polynomials to be
constant. -/
theorem RationalData.wronskian_ne_zero (r : RationalData) (hdeg : 2 ≤ r.degree) :
    r.wronskian ≠ 0 := by
  intro h0
  have hcop : IsCoprime r.numReduced r.denReduced :=
    isCoprime_div_gcd_div_gcd r.den_ne_zero
  have hdenR_ne_zero : r.denReduced ≠ 0 := r.denReduced_ne_zero
  have hid : Polynomial.derivative r.numReduced * r.denReduced
      = r.numReduced * Polynomial.derivative r.denReduced := by
    have h0' : Polynomial.derivative r.numReduced * r.denReduced
        - r.numReduced * Polynomial.derivative r.denReduced = 0 := h0
    exact sub_eq_zero.mp h0'
  have hdvd : r.denReduced ∣ r.numReduced * Polynomial.derivative r.denReduced := by
    rw [← hid]
    exact dvd_mul_left _ _
  have hdvd' : r.denReduced ∣ Polynomial.derivative r.denReduced :=
    hcop.symm.dvd_of_dvd_mul_left hdvd
  have hderD : Polynomial.derivative r.denReduced = 0 := by
    by_cases hd0 : r.denReduced.natDegree = 0
    · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hd0
      rw [← hc, Polynomial.derivative_C]
    · exact Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd'
        (Polynomial.natDegree_derivative_lt hd0)
  have hdD : r.denReduced.natDegree = 0 :=
    Polynomial.derivative_eq_zero.mp hderD
  have hderN : Polynomial.derivative r.numReduced = 0 := by
    have h2 : Polynomial.derivative r.numReduced * r.denReduced = 0 := by
      rw [hid, hderD, mul_zero]
    exact (mul_eq_zero.mp h2).resolve_right hdenR_ne_zero
  have hdN : r.numReduced.natDegree = 0 :=
    Polynomial.derivative_eq_zero.mp hderN
  have hmax : r.degree = max r.numReduced.natDegree r.denReduced.natDegree := rfl
  omega

/-- At a non-pole, the derivative of the finite-chart reading is the
Wronskian divided by the squared denominator. -/
theorem RationalData.deriv_reading (r : RationalData) {w : ℂ}
    (hden : r.denReduced.eval w ≠ 0) :
    deriv (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂)))) w
      = r.wronskian.eval w / (r.denReduced.eval w) ^ 2 := by
  have hev : (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
      =ᶠ[𝓝 w] fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x := by
    filter_upwards [r.denReduced.continuous.continuousAt.eventually_ne hden] with x hx
    have hread : r.toSphereMap ↑x
        = if r.denReduced.eval x = 0 then (∞ : ℂ̂)
          else ((r.numReduced.eval x / r.denReduced.eval x : ℂ) : ℂ̂) := rfl
    rw [hread, if_neg hx]
    rfl
  have hdiv : HasDerivAt (fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x)
      (((Polynomial.derivative r.numReduced).eval w * r.denReduced.eval w
          - r.numReduced.eval w * (Polynomial.derivative r.denReduced).eval w)
        / r.denReduced.eval w ^ 2) w :=
    (r.numReduced.hasDerivAt w).div (r.denReduced.hasDerivAt w) hden
  have hwr : r.wronskian.eval w
      = (Polynomial.derivative r.numReduced).eval w * r.denReduced.eval w
        - r.numReduced.eval w * (Polynomial.derivative r.denReduced).eval w := by
    simp only [RationalData.wronskian, Polynomial.eval_sub, Polynomial.eval_mul]
  rw [hev.deriv_eq, hdiv.deriv, hwr]

/-- **Local inverse branches at non-critical points.** If `f ↑b = ↑a` and
the finite-chart reading of `f` has nonvanishing derivative at `b`, there
is a holomorphic local section of `f` through `b` defined near `a`. -/
theorem exists_branch_of_deriv_ne_zero {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    {a b : ℂ} (hab : f ((b : ℂ̂)) = ((a : ℂ̂)))
    (hcrit : deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) b ≠ 0) :
    ∃ (V : Set ℂ) (g : ℂ → ℂ), IsOpen V ∧ a ∈ V ∧ g a = b ∧
      DifferentiableOn ℂ g V ∧ ∀ y ∈ V, f ((g y : ℂ̂)) = ((y : ℂ̂)) := by
  classical
  have cf : ∀ x : ℂ, chartFiniteMap ((x : ℂ̂)) = x := fun _ => rfl
  set φ : ℂ → ℂ := fun x : ℂ => chartFiniteMap (f ((x : ℂ̂))) with hφ_def
  have hcrit' : deriv φ b ≠ 0 := by rw [hφ_def]; exact hcrit
  -- The open set where `f` takes finite values.
  set U₀ : Set ℂ := {x : ℂ | f ((x : ℂ̂)) ≠ ∞} with hU₀_def
  have hU₀_open : IsOpen U₀ := by
    have hcont : Continuous fun x : ℂ => f ((x : ℂ̂)) :=
      hf.continuous.comp OnePoint.continuous_coe
    rw [hU₀_def]
    exact (OnePoint.isClosed_infty.isOpen_compl).preimage hcont
  have hb₀ : b ∈ U₀ := by
    have hb' : f ((b : ℂ̂)) ≠ ∞ := by
      rw [hab]; exact OnePoint.coe_ne_infty a
    exact hb'
  -- On `U₀` the map is the coercion of its finite reading `φ`.
  have hread : ∀ x ∈ U₀, f ((x : ℂ̂)) = ((φ x : ℂ̂)) := by
    intro x hx
    have hx' : f ((x : ℂ̂)) ≠ ∞ := hx
    cases hfx : f ((x : ℂ̂)) with
    | infty => exact absurd hfx hx'
    | coe t =>
      have hphi : φ x = t := by simp only [hφ_def, hfx, cf]
      rw [hphi]
  have hφb : φ b = a := by simp only [hφ_def, hab, cf]
  -- The finite reading is analytic on `U₀`, with continuous derivative.
  have hφ_diff : DifferentiableOn ℂ φ U₀ := by
    rw [hφ_def]
    exact (hf.sphereHolomorphicOn_comp_coe hU₀_open).differentiableOn_chartFiniteMap
      fun z hz => hz
  have hφ_an : AnalyticOnNhd ℂ φ U₀ := hφ_diff.analyticOnNhd hU₀_open
  have hderiv_cont : ContinuousOn (deriv φ) U₀ := hφ_an.deriv.continuousOn
  -- Shrink to the open locus of nonvanishing derivative.
  set U₁ : Set ℂ := U₀ ∩ deriv φ ⁻¹' {(0 : ℂ)}ᶜ with hU₁_def
  have hU₁_open : IsOpen U₁ :=
    hderiv_cont.isOpen_inter_preimage hU₀_open isOpen_compl_singleton
  have hU₁_sub : U₁ ⊆ U₀ := Set.inter_subset_left
  have hb₁ : b ∈ U₁ := by
    rw [hU₁_def]
    exact ⟨hb₀, hcrit'⟩
  -- The inverse-function-theorem partial homeomorphism at `b`.
  have hb_strict : HasStrictDerivAt φ (deriv φ b) b := (hφ_an b hb₀).hasStrictDerivAt
  have hb_strictF := hb_strict.hasStrictFDerivAt_equiv hcrit'
  set e := hb_strictF.toOpenPartialHomeomorph φ with he_def
  have hcoe : ⇑e = φ := hb_strictF.toOpenPartialHomeomorph_coe
  have hb_source : b ∈ e.source := hb_strictF.mem_toOpenPartialHomeomorph_source
  have heb : e b = a := by rw [hcoe]; exact hφb
  have ha_target : a ∈ e.target := by
    rw [← heb]
    exact e.map_source hb_source
  have hsymm_a : e.symm a = b := by
    rw [← heb]
    exact e.left_inv hb_source
  -- The branch domain: target points whose inverse lies in the good locus.
  set V : Set ℂ := e.target ∩ ⇑e.symm ⁻¹' (U₁ ∩ e.source) with hV_def
  have hV_open : IsOpen V :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target (hU₁_open.inter e.open_source)
  have ha_V : a ∈ V := by
    rw [hV_def]
    refine ⟨ha_target, ?_⟩
    rw [Set.mem_preimage, hsymm_a]
    exact ⟨hb₁, hb_source⟩
  -- `e.symm` is a right inverse for the reading on `V`.
  have hright : ∀ y, y ∈ V → φ (e.symm y) = y := by
    intro y hy
    rw [hV_def] at hy
    have h := e.right_inv hy.1
    rw [hcoe] at h
    exact h
  refine ⟨V, ⇑e.symm, hV_open, ha_V, hsymm_a, ?_, ?_⟩
  · -- Differentiability, pointwise from the local inverse at each branch point.
    intro y hy
    have hφx : φ (e.symm y) = y := hright y hy
    rw [hV_def] at hy
    obtain ⟨hy_t, hy_pre⟩ := hy
    have hx_mem : e.symm y ∈ U₁ ∩ e.source := hy_pre
    obtain ⟨hx₁, hx_src⟩ := hx_mem
    have hx₁' := hx₁
    rw [hU₁_def] at hx₁'
    have hx₀ : e.symm y ∈ U₀ := hx₁'.1
    have hx_ne : deriv φ (e.symm y) ≠ 0 := hx₁'.2
    have hx_strict : HasStrictDerivAt φ (deriv φ (e.symm y)) (e.symm y) :=
      (hφ_an _ hx₀).hasStrictDerivAt
    obtain ⟨gx, hgx_left, hgx_right, hgx_strict⟩ :
        ∃ gx : ℂ → ℂ, (∀ᶠ x' in 𝓝 (e.symm y), gx (φ x') = x') ∧
          (∀ᶠ z in 𝓝 (φ (e.symm y)), φ (gx z) = z) ∧
          HasStrictDerivAt gx (deriv φ (e.symm y))⁻¹ (φ (e.symm y)) :=
      ⟨hx_strict.localInverse φ (deriv φ (e.symm y)) (e.symm y) hx_ne,
        hx_strict.eventually_left_inverse hx_ne,
        hx_strict.eventually_right_inverse hx_ne,
        hx_strict.to_localInverse hx_ne⟩
    rw [hφx] at hgx_right hgx_strict
    have hgx_diff : DifferentiableAt ℂ gx y := hgx_strict.hasDerivAt.differentiableAt
    have hgx_yx : gx y = e.symm y := by
      have h := hgx_left.self_of_nhds
      rwa [hφx] at h
    have hev_t : ∀ᶠ y' in 𝓝 y, y' ∈ e.target := e.open_target.mem_nhds hy_t
    have hev_s : ∀ᶠ y' in 𝓝 y, gx y' ∈ e.source := by
      have hmem : e.source ∈ 𝓝 (gx y) := by
        rw [hgx_yx]
        exact e.open_source.mem_nhds hx_src
      exact hgx_diff.continuousAt.eventually_mem hmem
    -- Near `y` the branch agrees with the differentiable local inverse `gx`.
    have heq : ⇑e.symm =ᶠ[𝓝 y] gx := by
      filter_upwards [hev_t, hgx_right, hev_s] with y' h1 h2 h3
      refine e.injOn (e.map_target h1) h3 ?_
      rw [e.right_inv h1, hcoe]
      exact h2.symm
    exact (hgx_diff.congr_of_eventuallyEq heq).differentiableWithinAt
  · -- The branch property.
    intro y hy
    have hx₀ : e.symm y ∈ U₀ := by
      have hy' := hy
      rw [hV_def] at hy'
      exact hU₁_sub hy'.2.1
    rw [hread _ hx₀, hright y hy]

end NoWanderingDomains
