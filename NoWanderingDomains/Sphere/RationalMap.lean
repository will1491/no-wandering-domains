/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Algebra.Polynomial
import NoWanderingDomains.Sphere.Basic

/-!
# Rational maps `ℂ̂ → ℂ̂`

A rational map is a ratio `P/Q` of two complex polynomials. After cancelling
the common factor `gcd(P, Q)`, the resulting coprime pair `(P', Q')` defines
a unique map `ℂ̂ → ℂ̂`:

* on a finite point `w ∈ ℂ` with `Q'(w) ≠ 0`, send `w ↦ P'(w)/Q'(w)`;
* on a finite point `w ∈ ℂ` with `Q'(w) = 0` (necessarily `P'(w) ≠ 0` since
  `P'` and `Q'` are coprime), send `w ↦ ∞`;
* at `∞`, send to the limit of `P'/Q'` as the argument grows: `0` if
  `deg P' < deg Q'`, `lc P' / lc Q'` if degrees agree, and `∞` if
  `deg P' > deg Q'`.

The degree of the resulting rational map is `max(deg P', deg Q')`.

## Main definitions

* `RationalData` — the raw data of a rational map: a numerator, a denominator,
  and a proof that the denominator is nonzero.
* `RationalData.numReduced`, `RationalData.denReduced` — the coprime pair
  obtained by dividing `num`, `den` by `gcd num den`.
* `RationalData.toSphereMap` — the extension of `num / den` to `ℂ̂ → ℂ̂`.
* `RationalData.degree` — `max numReduced.natDegree denReduced.natDegree`.
* `RationalData.composeNum`, `RationalData.composeDen` — the numerator and
  denominator polynomials of the composition `r₁ ∘ r₂`.
* `RationalData.composeRational` — the composition packaged as `RationalData`.
* `IsRational` — the predicate that a map `f : ℂ̂ → ℂ̂` arises from some
  `RationalData`.
* `degreeOfRational` — the degree of a rational map (`0` on non-rational maps).

## Main results

* `RationalData.degree_eq_of_toSphereMap_eq` — equal maps have equal `degree`.
* `RationalData.continuous_toSphereMap` — the extension is continuous.
* `RationalData.composeRational_toSphereMap_eq` — the composed data realizes the
  composition of the underlying maps, when the inner map is nonconstant.
* `RationalData.composeRational_degree_eq` — the degree is multiplicative under
  composition of nonconstant maps.
* `isRational_comp` — rational maps are closed under composition, provided the
  inner map is nonconstant.
* `degreeOfRational_comp` — degree multiplicativity for nonconstant maps:
  `degreeOfRational (f ∘ g) = degreeOfRational f * degreeOfRational g`.
* `degreeOfRational_eq_of_witness` — `degreeOfRational` agrees with
  `RationalData.degree` for any witness producing the map.

## Implementation notes

* `RationalData` is not quotiented by the scaling relation `(P, Q) ~ (λP, λQ)`;
  every downstream statement is phrased to be invariant under it (see
  `RationalData.degree_eq_of_toSphereMap_eq`).
* `RationalData.composeRational` is total: when the composed denominator
  vanishes (which happens only when the inner map is constant) it falls back to
  `r₁`. Its semantics are meaningful only for `1 ≤ r₂.degree`, the hypothesis of
  every composition lemma.
* `degreeOfRational` returns `0` on non-rational maps by convention and is never
  applied to such maps downstream.
-/

open OnePoint Polynomial Filter Topology

namespace NoWanderingDomains

/-- The zero set of a nonzero complex polynomial is finite. -/
theorem finite_setOf_eval_eq_zero {p : ℂ[X]} (hp : p ≠ 0) :
    {z : ℂ | p.eval z = 0}.Finite := by
  have hsub : {z : ℂ | p.eval z = 0} ⊆ (p.roots.toFinset : Set ℂ) := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    simp [Multiset.mem_toFinset, Polynomial.mem_roots hp, hz, Polynomial.IsRoot]
  exact ((p.roots.toFinset : Set ℂ).toFinite).subset hsub

/-- The raw data of a rational map: two complex polynomials with nonzero
denominator. We do not quotient by `(P, Q) ~ (λP, λQ)` here; downstream
results are stated invariantly. -/
structure RationalData where
  /-- Numerator polynomial. -/
  num : ℂ[X]
  /-- Denominator polynomial. -/
  den : ℂ[X]
  /-- The denominator is nonzero. -/
  den_ne_zero : den ≠ 0

namespace RationalData

variable (r : RationalData)

/-- The reduced numerator: `num` divided by `gcd(num, den)`. -/
noncomputable def numReduced : ℂ[X] := r.num / gcd r.num r.den

/-- The reduced denominator: `den` divided by `gcd(num, den)`. -/
noncomputable def denReduced : ℂ[X] := r.den / gcd r.num r.den

/-- The extension of the rational map `num/den` to `ℂ̂ → ℂ̂`. -/
noncomputable def toSphereMap : ℂ̂ → ℂ̂ := fun z =>
  match z with
  | OnePoint.some w =>
      if r.denReduced.eval w = 0 then ∞
      else ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂)
  | ∞ =>
      if r.numReduced.natDegree < r.denReduced.natDegree then
        ((0 : ℂ) : ℂ̂)
      else if r.numReduced.natDegree = r.denReduced.natDegree then
        ((r.numReduced.leadingCoeff / r.denReduced.leadingCoeff : ℂ) : ℂ̂)
      else ∞

/-- The degree of the rational map associated with `r`, defined as the maximum
of the reduced numerator's and denominator's degrees. -/
noncomputable def degree : ℕ :=
  max r.numReduced.natDegree r.denReduced.natDegree

/-- Numerator polynomial of the composition `r₁ ∘ r₂`: the homogenization of
`r₁.numReduced` to degree `r₁.degree` substituted with `(N₂, D₂) = (r₂.numReduced,
r₂.denReduced)`. -/
noncomputable def composeNum (r₁ r₂ : RationalData) : ℂ[X] :=
  ∑ i ∈ Finset.range (r₁.degree + 1),
    Polynomial.C (r₁.numReduced.coeff i) *
      r₂.numReduced ^ i * r₂.denReduced ^ (r₁.degree - i)

/-- Denominator polynomial of the composition `r₁ ∘ r₂`: the homogenization of
`r₁.denReduced` to degree `r₁.degree` substituted with
`(r₂.numReduced, r₂.denReduced)`. -/
noncomputable def composeDen (r₁ r₂ : RationalData) : ℂ[X] :=
  ∑ i ∈ Finset.range (r₁.degree + 1),
    Polynomial.C (r₁.denReduced.coeff i) *
      r₂.numReduced ^ i * r₂.denReduced ^ (r₁.degree - i)

/-- The composition of two rational data as a rational map. When the composed
denominator is nonzero (which holds whenever `1 ≤ r₂.degree`), it is taken
directly; otherwise we fall back to `r₁` to keep the type total. The
`1 ≤ r₂.degree` case is the only one with meaningful semantics; see
`composeRational_toSphereMap_eq` and `composeRational_degree_eq`. -/
noncomputable def composeRational (r₁ r₂ : RationalData) : RationalData :=
  if h : composeDen r₁ r₂ ≠ 0 then
    ⟨composeNum r₁ r₂, composeDen r₁ r₂, h⟩
  else r₁

variable (r₁ r₂ : RationalData)

/-- The reduced denominator of a `RationalData` is nonzero. -/
theorem denReduced_ne_zero : r.denReduced ≠ 0 := by
  rw [RationalData.denReduced]
  intro hz
  have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
    (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
      (gcd_dvd_right _ _)).symm
  rw [hz, mul_zero] at h1
  exact r.den_ne_zero h1

/-- If the inner map `r₂` is nonconstant then `numReduced - C c * denReduced` is
nonzero for every scalar `c`: otherwise `numReduced = c • denReduced` would force
`denReduced` to be a unit, making `r₂.degree = 0`. -/
theorem numReduced_sub_C_mul_denReduced_ne_zero (h : 1 ≤ r₂.degree) (c : ℂ) :
    r₂.numReduced - Polynomial.C c * r₂.denReduced ≠ 0 := by
  intro hzero
  have hN₂_eq : r₂.numReduced = Polynomial.C c * r₂.denReduced := by
    linear_combination hzero
  have hcop_g : IsCoprime r₂.numReduced r₂.denReduced :=
    isCoprime_div_gcd_div_gcd r₂.den_ne_zero
  have hD₂_unit : IsUnit r₂.denReduced := by
    obtain ⟨a, b, hab⟩ := hcop_g
    have h1 : a * (Polynomial.C c * r₂.denReduced) + b * r₂.denReduced = 1 := by
      rw [← hN₂_eq]; exact hab
    have h2 : r₂.denReduced * (a * Polynomial.C c + b) = 1 := by linear_combination h1
    exact IsUnit.of_mul_eq_one _ h2
  have hD₂_natDeg : r₂.denReduced.natDegree = 0 := by
    rcases Polynomial.isUnit_iff.mp hD₂_unit with ⟨c', _, hc'⟩
    rw [← hc']; exact Polynomial.natDegree_C c'
  have hN₂_natDeg : r₂.numReduced.natDegree = 0 := by
    rcases Polynomial.isUnit_iff.mp hD₂_unit with ⟨d, _, hd⟩
    rw [hN₂_eq, ← hd, ← Polynomial.C_mul]
    exact Polynomial.natDegree_C _
  have hr₂_deg : r₂.degree = 0 := by
    rw [RationalData.degree, hN₂_natDeg, hD₂_natDeg]; rfl
  rw [hr₂_deg] at h
  exact Nat.lt_irrefl 0 h

/-- Evaluation of a polynomial homogenized in `(numReduced, denReduced)` of `r₂`:
at a point `z` where `denReduced` does not vanish it factors through `P`
evaluated at `numReduced z / denReduced z`. -/
theorem homogenize_eval (P : ℂ[X]) (n : ℕ) (hP : P.natDegree ≤ n) {z : ℂ}
    (hz : r₂.denReduced.eval z ≠ 0) :
    (∑ i ∈ Finset.range (n + 1),
        Polynomial.C (P.coeff i) * r₂.numReduced ^ i * r₂.denReduced ^ (n - i)).eval z
      = r₂.denReduced.eval z ^ n *
          P.eval (r₂.numReduced.eval z / r₂.denReduced.eval z) := by
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
             Polynomial.eval_pow]
  rw [Polynomial.eval_eq_sum_range' (n := n + 1) (by omega)
      (p := P) (x := r₂.numReduced.eval z / r₂.denReduced.eval z)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hpow_i_ne : r₂.denReduced.eval z ^ i ≠ 0 := pow_ne_zero _ hz
  have hpow_eq : r₂.denReduced.eval z ^ i * r₂.denReduced.eval z ^ (n - i)
      = r₂.denReduced.eval z ^ n := by
    rw [← pow_add]; congr 1; omega
  have hsub : r₂.denReduced.eval z ^ (n - i)
      = r₂.denReduced.eval z ^ n / r₂.denReduced.eval z ^ i := by
    rw [eq_div_iff hpow_i_ne]; linear_combination hpow_eq
  rw [hsub, div_pow]; ring

/-- The homogenization of `P` in `(numReduced, denReduced)` of `r₂` to degree
`n` has natural degree at most `n * r₂.degree`. -/
theorem homogenize_natDegree_le (P : ℂ[X]) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
        Polynomial.C (P.coeff i) * r₂.numReduced ^ i * r₂.denReduced ^ (n - i)).natDegree
      ≤ n * r₂.degree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [Finset.mem_range] at hi
  refine (Polynomial.natDegree_mul_le).trans ?_
  refine (add_le_add (Polynomial.natDegree_mul_le) le_rfl).trans ?_
  rw [Polynomial.natDegree_C, zero_add, Polynomial.natDegree_pow, Polynomial.natDegree_pow]
  have hN₂_le : r₂.numReduced.natDegree ≤ r₂.degree := by
    rw [RationalData.degree]; exact le_max_left _ _
  have hD₂_le : r₂.denReduced.natDegree ≤ r₂.degree := by
    rw [RationalData.degree]; exact le_max_right _ _
  have step1 : i * r₂.numReduced.natDegree + (n - i) * r₂.denReduced.natDegree
      ≤ i * r₂.degree + (n - i) * r₂.degree :=
    Nat.add_le_add (Nat.mul_le_mul_left i hN₂_le) (Nat.mul_le_mul_left (n - i) hD₂_le)
  have step2 : i * r₂.degree + (n - i) * r₂.degree = n * r₂.degree := by
    rw [← Nat.add_mul]; congr 1; omega
  omega

/-- The composed denominator `composeDen r₁ r₂` is nonzero when the inner map
`r₂` is nonconstant. -/
theorem composeDen_ne_zero (h : 1 ≤ r₂.degree) : r₁.composeDen r₂ ≠ 0 := by
  intro hzero
  have hD₁_ne_zero : r₁.denReduced ≠ 0 := r₁.denReduced_ne_zero
  have hD₂_ne_zero : r₂.denReduced ≠ 0 := r₂.denReduced_ne_zero
  have hD₁_natDeg_le : r₁.denReduced.natDegree ≤ r₁.degree := by
    rw [RationalData.degree]; exact le_max_right _ _
  have hden_eval : ∀ z : ℂ, r₂.denReduced.eval z ≠ 0 →
      (r₁.composeDen r₂).eval z =
        r₂.denReduced.eval z ^ r₁.degree *
          r₁.denReduced.eval (r₂.numReduced.eval z / r₂.denReduced.eval z) := by
    intro z hz
    rw [RationalData.composeDen]
    exact r₂.homogenize_eval r₁.denReduced r₁.degree hD₁_natDeg_le hz
  set S : Set ℂ := {z | r₂.denReduced.eval z = 0} ∪
      ⋃ α ∈ {α : ℂ | r₁.denReduced.eval α = 0},
        {z : ℂ | r₂.numReduced.eval z = α * r₂.denReduced.eval z} with hS_def
  have hS_fin : S.Finite := by
    apply Set.Finite.union (finite_setOf_eval_eq_zero hD₂_ne_zero)
    apply Set.Finite.biUnion (finite_setOf_eval_eq_zero hD₁_ne_zero)
    intro α _
    have hpoly_ne : r₂.numReduced - Polynomial.C α * r₂.denReduced ≠ 0 :=
      r₂.numReduced_sub_C_mul_denReduced_ne_zero h α
    have hsub : {z : ℂ | r₂.numReduced.eval z = α * r₂.denReduced.eval z} ⊆
        {z : ℂ | (r₂.numReduced - Polynomial.C α * r₂.denReduced).eval z = 0} := by
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz ⊢
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hz, sub_self]
    exact (finite_setOf_eval_eq_zero hpoly_ne).subset hsub
  have hexists : ∃ z : ℂ, z ∉ S := by
    by_contra hno
    push Not at hno
    exact Set.infinite_univ (hS_fin.subset (fun z _ => hno z))
  obtain ⟨z, hz_notin⟩ := hexists
  have hz_D₂ : r₂.denReduced.eval z ≠ 0 := fun hh => hz_notin (Or.inl hh)
  have hz_D₁ : r₁.denReduced.eval (r₂.numReduced.eval z / r₂.denReduced.eval z) ≠ 0 := by
    intro heval
    apply hz_notin
    right
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨r₂.numReduced.eval z / r₂.denReduced.eval z, heval, ?_⟩
    field_simp
  have hden_eval_z := hden_eval z hz_D₂
  rw [hzero, Polynomial.eval_zero] at hden_eval_z
  have hpow_ne : r₂.denReduced.eval z ^ r₁.degree ≠ 0 := pow_ne_zero _ hz_D₂
  exact hz_D₁ ((mul_eq_zero.mp hden_eval_z.symm).resolve_left hpow_ne)

end RationalData

/-- A map `f : ℂ̂ → ℂ̂` is *rational* if it arises from some `RationalData`. -/
def IsRational (f : ℂ̂ → ℂ̂) : Prop :=
  ∃ r : RationalData, f = r.toSphereMap

/-- The degree of a rational map `f : ℂ̂ → ℂ̂`. If `f` is not rational, returns
`0` by convention (we never invoke `degreeOfRational` on non-rational maps in
downstream code). -/
noncomputable def degreeOfRational (f : ℂ̂ → ℂ̂) : ℕ :=
  open Classical in if h : IsRational f then h.choose.degree else 0

/-! ## Basic theorems -/

/-- The degree of a rational map is well defined: any two `RationalData` values
producing the same map `ℂ̂ → ℂ̂` have equal `degree`. -/
theorem RationalData.degree_eq_of_toSphereMap_eq
    (r₁ r₂ : RationalData) (h : r₁.toSphereMap = r₂.toSphereMap) :
    r₁.degree = r₂.degree := by
  -- Step 1: derive cross-product polynomial identity from functional equality.
  have cross : r₁.numReduced * r₂.denReduced = r₂.numReduced * r₁.denReduced := by
    apply Polynomial.funext
    intro w
    simp only [Polynomial.eval_mul]
    have hw := congrFun h ((w : ℂ̂))
    simp only [RationalData.toSphereMap] at hw
    by_cases hd₁ : r₁.denReduced.eval w = 0
    · by_cases hd₂ : r₂.denReduced.eval w = 0
      · rw [hd₁, hd₂]; ring
      · -- r₁ side is ∞, r₂ side is finite — contradiction
        rw [if_pos hd₁, if_neg hd₂] at hw
        exact absurd hw.symm (OnePoint.coe_ne_infty _)
    · by_cases hd₂ : r₂.denReduced.eval w = 0
      · -- r₂ side is ∞, r₁ side is finite — contradiction
        rw [if_neg hd₁, if_pos hd₂] at hw
        exact absurd hw (OnePoint.coe_ne_infty _)
      · -- both denominators nonzero: extract the equality of ℂ-values
        rw [if_neg hd₁, if_neg hd₂] at hw
        have hw' : r₁.numReduced.eval w / r₁.denReduced.eval w
                 = r₂.numReduced.eval w / r₂.denReduced.eval w :=
          OnePoint.coe_eq_coe.mp hw
        field_simp at hw'
        linear_combination hw'
  -- Step 2: derive natDegree equality from cross-product + coprimality.
  -- The reduced numerator and denominator are coprime by construction (gcd divided out).
  have denR₁_ne_zero : r₁.denReduced ≠ 0 := r₁.denReduced_ne_zero
  have denR₂_ne_zero : r₂.denReduced ≠ 0 := r₂.denReduced_ne_zero
  have cop₁ : IsCoprime r₁.numReduced r₁.denReduced :=
    isCoprime_div_gcd_div_gcd r₁.den_ne_zero
  have cop₂ : IsCoprime r₂.numReduced r₂.denReduced :=
    isCoprime_div_gcd_div_gcd r₂.den_ne_zero
  -- From cross product `n₁ * d₂ = n₂ * d₁` and coprimality, derive Associated for d's
  have d_assoc : Associated r₁.denReduced r₂.denReduced := by
    have hd₁ : r₁.denReduced ∣ r₂.denReduced := by
      have : r₁.denReduced ∣ r₂.numReduced * r₁.denReduced := dvd_mul_left _ _
      rw [← cross] at this
      exact cop₁.symm.dvd_of_dvd_mul_left this
    have hd₂ : r₂.denReduced ∣ r₁.denReduced := by
      have : r₂.denReduced ∣ r₁.numReduced * r₂.denReduced := dvd_mul_left _ _
      rw [cross] at this
      exact cop₂.symm.dvd_of_dvd_mul_left this
    exact associated_of_dvd_dvd hd₁ hd₂
  -- For n's, two cases: both zero or both nonzero
  have n_natDeg_eq : r₁.numReduced.natDegree = r₂.numReduced.natDegree := by
    by_cases hn₁ : r₁.numReduced = 0
    · -- if n₁ = 0, then n₁ * d₂ = 0 = n₂ * d₁, and d₁ ≠ 0 so n₂ = 0
      have hn₂ : r₂.numReduced = 0 := by
        have hzero : r₂.numReduced * r₁.denReduced = 0 := by
          rw [← cross, hn₁, zero_mul]
        exact (mul_eq_zero.mp hzero).resolve_right denR₁_ne_zero
      rw [hn₁, hn₂]
    · -- if n₁ ≠ 0, derive Associated n₁ n₂
      have hn₂ : r₂.numReduced ≠ 0 := by
        intro hz
        apply hn₁
        have hzero : r₁.numReduced * r₂.denReduced = 0 := by
          rw [cross, hz, zero_mul]
        exact (mul_eq_zero.mp hzero).resolve_right denR₂_ne_zero
      have n_assoc : Associated r₁.numReduced r₂.numReduced := by
        have hn₁_dvd : r₁.numReduced ∣ r₂.numReduced := by
          have : r₁.numReduced ∣ r₂.numReduced * r₁.denReduced := by
            rw [← cross]; exact dvd_mul_right _ _
          exact cop₁.dvd_of_dvd_mul_right this
        have hn₂_dvd : r₂.numReduced ∣ r₁.numReduced := by
          have : r₂.numReduced ∣ r₁.numReduced * r₂.denReduced := by
            rw [cross]; exact dvd_mul_right _ _
          exact cop₂.dvd_of_dvd_mul_right this
        exact associated_of_dvd_dvd hn₁_dvd hn₂_dvd
      -- Associated polys over ℂ differ by a nonzero scalar, so equal natDegree
      obtain ⟨u, hu⟩ := n_assoc
      have hunatdeg : ((↑u : Polynomial ℂ)).natDegree = 0 := by
        have hu_ne_zero : (↑u : Polynomial ℂ) ≠ 0 := Units.ne_zero _
        have hu_isUnit : IsUnit (↑u : Polynomial ℂ) := Units.isUnit u
        rw [Polynomial.natDegree_eq_zero]
        rcases Polynomial.isUnit_iff.mp hu_isUnit with ⟨c, _, hc⟩
        exact ⟨c, hc⟩
      have : r₂.numReduced.natDegree = (r₁.numReduced * ↑u).natDegree := by rw [hu]
      rw [this, Polynomial.natDegree_mul hn₁ (Units.ne_zero _), hunatdeg, Nat.add_zero]
  have d_natDeg_eq : r₁.denReduced.natDegree = r₂.denReduced.natDegree := by
    obtain ⟨u, hu⟩ := d_assoc
    have hunatdeg : ((↑u : Polynomial ℂ)).natDegree = 0 := by
      have hu_isUnit : IsUnit (↑u : Polynomial ℂ) := Units.isUnit u
      rw [Polynomial.natDegree_eq_zero]
      rcases Polynomial.isUnit_iff.mp hu_isUnit with ⟨c, _, hc⟩
      exact ⟨c, hc⟩
    have : r₂.denReduced.natDegree = (r₁.denReduced * ↑u).natDegree := by rw [hu]
    rw [this, Polynomial.natDegree_mul denR₁_ne_zero (Units.ne_zero _), hunatdeg,
        Nat.add_zero]
  unfold RationalData.degree
  rw [n_natDeg_eq, d_natDeg_eq]

/-- `degreeOfRational` is consistent with `RationalData.degree` for any
witness producing the map. -/
theorem degreeOfRational_eq_of_witness
    (f : ℂ̂ → ℂ̂) (r : RationalData) (h : f = r.toSphereMap) :
    degreeOfRational f = r.degree := by
  have hf : IsRational f := ⟨r, h⟩
  unfold degreeOfRational
  rw [dif_pos hf]
  apply RationalData.degree_eq_of_toSphereMap_eq
  rw [← hf.choose_spec, ← h]

/-- The extension of a rational map to `ℂ̂` is continuous for the topology of the
one-point compactification. -/
theorem RationalData.continuous_toSphereMap (r : RationalData) :
    Continuous r.toSphereMap := by
  -- Helpers used in multiple cases.
  have hcont_num : Continuous (fun w : ℂ => r.numReduced.eval w) :=
    Polynomial.continuous r.numReduced
  have hcont_den : Continuous (fun w : ℂ => r.denReduced.eval w) :=
    Polynomial.continuous r.denReduced
  have hdenR_ne_zero : r.denReduced ≠ 0 := r.denReduced_ne_zero
  have hcop : IsCoprime r.numReduced r.denReduced :=
    isCoprime_div_gcd_div_gcd r.den_ne_zero
  -- No common roots at finite points: if denReduced(w) = 0 then numReduced(w) ≠ 0.
  have hno_common : ∀ w : ℂ, r.denReduced.eval w = 0 → r.numReduced.eval w ≠ 0 := by
    intro w hdw hnw
    obtain ⟨a, b, hab⟩ := hcop
    have heval : a.eval w * r.numReduced.eval w + b.eval w * r.denReduced.eval w = 1 := by
      have := congrArg (Polynomial.eval w) hab
      simpa [Polynomial.eval_add, Polynomial.eval_mul] using this
    rw [hnw, hdw, mul_zero, mul_zero, add_zero] at heval
    exact zero_ne_one heval
  -- Eventually-nonzero of denReduced on cocompact ℂ (finitely many roots).
  have hden_cocompact : ∀ᶠ z in Filter.cocompact ℂ, r.denReduced.eval z ≠ 0 := by
    have hroots_fin : {z : ℂ | r.denReduced.eval z = 0}.Finite :=
      finite_setOf_eval_eq_zero hdenR_ne_zero
    have hroots_compact : IsCompact {z : ℂ | r.denReduced.eval z = 0} :=
      hroots_fin.isCompact
    exact hroots_compact.compl_mem_cocompact
  rw [OnePoint.continuous_iff]
  refine ⟨?_, ?_⟩
  · -- Tendsto at ∞: use the reflection identity to substitute s = 1/z.
    -- Convert from coclosedCompact to cocompact (equal for R1 spaces, hence ℂ).
    rw [Filter.coclosedCompact_eq_cocompact]
    -- Set up m = max(n, d), where n, d are the natDegrees of the reduced polys.
    set n := r.numReduced.natDegree with hn_def
    set d := r.denReduced.natDegree with hd_def
    set m := max n d with hm_def
    set numRev := Polynomial.reflect m r.numReduced with hnumRev_def
    set denRev := Polynomial.reflect m r.denReduced with hdenRev_def
    -- Numerator may be zero. Use `or_split` later.
    have hn_le_m : n ≤ m := le_max_left _ _
    have hd_le_m : d ≤ m := le_max_right _ _
    -- Identity: for z ≠ 0, num(z)/den(z) = numRev(1/z)/denRev(1/z).
    have hident_num : ∀ z : ℂ, z ≠ 0 →
        r.numReduced.eval z = z ^ m * numRev.eval z⁻¹ := by
      intro z hz
      have hinv : Invertible z := invertibleOfNonzero hz
      have heq : z⁻¹ = ⅟z := (invOf_eq_inv z).symm
      rw [heq, mul_comm]
      have htmp := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) z m r.numReduced hn_le_m
      simp only [Polynomial.eval₂_eq_eval_map, Polynomial.map_id] at htmp
      exact htmp.symm
    have hident_den : ∀ z : ℂ, z ≠ 0 →
        r.denReduced.eval z = z ^ m * denRev.eval z⁻¹ := by
      intro z hz
      have hinv : Invertible z := invertibleOfNonzero hz
      have heq : z⁻¹ = ⅟z := (invOf_eq_inv z).symm
      rw [heq, mul_comm]
      have htmp := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) z m r.denReduced hd_le_m
      simp only [Polynomial.eval₂_eq_eval_map, Polynomial.map_id] at htmp
      exact htmp.symm
    -- denRev ≠ 0 since denReduced ≠ 0 and reflection preserves nonzeroness.
    have hdenRev_ne_zero : denRev ≠ 0 := by
      intro heq
      apply hdenR_ne_zero
      -- denReduced.coeff d ≠ 0 implies reflected coeff is also nonzero
      have hcoeff_d : r.denReduced.coeff d ≠ 0 := by
        rw [hd_def]
        exact Polynomial.leadingCoeff_ne_zero.mpr hdenR_ne_zero
      have hrev_coeff : denRev.coeff ((Polynomial.revAt m) d) = r.denReduced.coeff d := by
        rw [hdenRev_def, Polynomial.coeff_reflect m r.denReduced (Polynomial.revAt m d),
            Polynomial.revAt_invol]
      rw [heq, Polynomial.coeff_zero] at hrev_coeff
      exact (hcoeff_d hrev_coeff.symm).elim
    -- Limits of numRev, denRev at 0.
    have hnumRev_eval_zero : numRev.eval 0 =
        if n = m then r.numReduced.leadingCoeff else 0 := by
      rw [hnumRev_def]
      rw [show (Polynomial.reflect m r.numReduced).eval 0
              = (Polynomial.reflect m r.numReduced).coeff 0 from
            Polynomial.coeff_zero_eq_eval_zero _ |>.symm,
          Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.zero_le m), Nat.sub_zero]
      by_cases hnm : n = m
      · rw [if_pos hnm]
        show r.numReduced.coeff m = r.numReduced.leadingCoeff
        rw [← hnm, hn_def]
        exact Polynomial.coeff_natDegree
      · rw [if_neg hnm]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
    have hdenRev_eval_zero : denRev.eval 0 =
        if d = m then r.denReduced.leadingCoeff else 0 := by
      rw [hdenRev_def]
      rw [show (Polynomial.reflect m r.denReduced).eval 0
              = (Polynomial.reflect m r.denReduced).coeff 0 from
            Polynomial.coeff_zero_eq_eval_zero _ |>.symm,
          Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.zero_le m), Nat.sub_zero]
      by_cases hdm : d = m
      · rw [if_pos hdm]
        show r.denReduced.coeff m = r.denReduced.leadingCoeff
        rw [← hdm, hd_def]
        exact Polynomial.coeff_natDegree
      · rw [if_neg hdm]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
    -- 1/z tends to 0 on cocompact ℂ.
    have hinv_tendsto : Filter.Tendsto (fun z : ℂ => z⁻¹) (Filter.cocompact ℂ) (𝓝 0) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    -- Eventually z ≠ 0 on cocompact ℂ.
    have hz_ne_cocompact : ∀ᶠ z in Filter.cocompact ℂ, z ≠ 0 := by
      have h0 : IsCompact ({(0 : ℂ)} : Set ℂ) := isCompact_singleton
      filter_upwards [h0.compl_mem_cocompact] with z hz
      intro hzz
      exact hz (by simp [hzz])
    -- Eventually denRev(1/z) ≠ 0 on cocompact: since denRev(0) might be nonzero
    -- in cases n ≤ d, or zero in case n > d; handle case-by-case below.
    -- Continuity of numRev, denRev evaluated at 1/z.
    have hnumRev_tendsto :
        Filter.Tendsto (fun z : ℂ => numRev.eval z⁻¹) (Filter.cocompact ℂ)
          (𝓝 (numRev.eval 0)) :=
      ((Polynomial.continuous numRev).continuousAt (x := 0)).tendsto.comp hinv_tendsto
    have hdenRev_tendsto :
        Filter.Tendsto (fun z : ℂ => denRev.eval z⁻¹) (Filter.cocompact ℂ)
          (𝓝 (denRev.eval 0)) :=
      ((Polynomial.continuous denRev).continuousAt (x := 0)).tendsto.comp hinv_tendsto
    -- Three cases based on n vs d.
    rcases lt_trichotomy n d with hnd | hnd | hnd
    · -- Case 1: n < d, m = d. numRev(0) = 0, denRev(0) = lc den ≠ 0. Limit = 0.
      have hm_eq_d : m = d := by simp [hm_def, hnd.le]
      have hn_ne_m : n ≠ m := by omega
      have hd_eq_m : d = m := hm_eq_d.symm
      have hnumRev0 : numRev.eval 0 = 0 := by rw [hnumRev_eval_zero, if_neg hn_ne_m]
      have hdenRev0 : denRev.eval 0 = r.denReduced.leadingCoeff := by
        rw [hdenRev_eval_zero, if_pos hd_eq_m]
      have hdenRev0_ne : denRev.eval 0 ≠ 0 := by
        rw [hdenRev0]; exact Polynomial.leadingCoeff_ne_zero.mpr hdenR_ne_zero
      -- r.toSphereMap ∞ = ↑0
      have hval_inf : r.toSphereMap ∞ = ((0 : ℂ) : ℂ̂) := by
        simp only [RationalData.toSphereMap]
        have hnd' : r.numReduced.natDegree < r.denReduced.natDegree := hnd
        rw [if_pos hnd']
      rw [hval_inf]
      -- Goal: Tendsto (fun z => r.toSphereMap ↑z) (cocompact ℂ) (𝓝 ↑0)
      -- Strategy: eventually den(z) ≠ 0 so r.toSphereMap ↑z = ↑(num/den),
      -- and num/den → 0 in ℂ.
      have hnumOdenRev_tendsto :
          Filter.Tendsto (fun z : ℂ => numRev.eval z⁻¹ / denRev.eval z⁻¹)
            (Filter.cocompact ℂ) (𝓝 0) := by
        have := hnumRev_tendsto.div hdenRev_tendsto hdenRev0_ne
        rw [hnumRev0, zero_div] at this
        exact this
      -- Combine: r.toSphereMap ↑z = ↑(num/den) eventually, and num/den = numRev(1/z)/denRev(1/z).
      have hcong : ∀ᶠ (z : ℂ) in Filter.cocompact ℂ,
          r.toSphereMap (↑z : ℂ̂) =
            ((numRev.eval z⁻¹ / denRev.eval z⁻¹ : ℂ) : ℂ̂) := by
        filter_upwards [hden_cocompact, hz_ne_cocompact] with z hdz hzne
        have hnum := hident_num z hzne
        have hden := hident_den z hzne
        have hzm_ne : z ^ m ≠ 0 := pow_ne_zero _ hzne
        have : r.toSphereMap (↑z : ℂ̂) =
            ((r.numReduced.eval z / r.denReduced.eval z : ℂ) : ℂ̂) := by
          simp only [RationalData.toSphereMap, hdz, if_false]
        rw [this]
        congr 1
        rw [hnum, hden, mul_div_mul_left _ _ hzm_ne]
      have hcont_coe := (OnePoint.continuous_coe (X := ℂ)).continuousAt (x := (0 : ℂ))
      have : Filter.Tendsto (fun z : ℂ => ((numRev.eval z⁻¹ / denRev.eval z⁻¹ : ℂ) : ℂ̂))
          (Filter.cocompact ℂ) (𝓝 ((0 : ℂ) : ℂ̂)) :=
        hcont_coe.tendsto.comp hnumOdenRev_tendsto
      exact this.congr' (hcong.mono fun _ h => h.symm)
    · -- Case 2: n = d, m = n = d. numRev(0) = lc num, denRev(0) = lc den.
      -- Limit = lc num / lc den.
      have hm_eq_n : m = n := by simp [hm_def, hnd.symm.le]
      have hn_eq_m : n = m := hm_eq_n.symm
      have hd_eq_m : d = m := by omega
      have hnumRev0 : numRev.eval 0 = r.numReduced.leadingCoeff := by
        rw [hnumRev_eval_zero, if_pos hn_eq_m]
      have hdenRev0 : denRev.eval 0 = r.denReduced.leadingCoeff := by
        rw [hdenRev_eval_zero, if_pos hd_eq_m]
      have hdenRev0_ne : denRev.eval 0 ≠ 0 := by
        rw [hdenRev0]; exact Polynomial.leadingCoeff_ne_zero.mpr hdenR_ne_zero
      have hval_inf : r.toSphereMap ∞ =
          ((r.numReduced.leadingCoeff / r.denReduced.leadingCoeff : ℂ) : ℂ̂) := by
        simp only [RationalData.toSphereMap]
        have hnlt : ¬ r.numReduced.natDegree < r.denReduced.natDegree := by omega
        have hneq : r.numReduced.natDegree = r.denReduced.natDegree := hnd
        rw [if_neg hnlt, if_pos hneq]
      rw [hval_inf]
      have hnumOdenRev_tendsto :
          Filter.Tendsto (fun z : ℂ => numRev.eval z⁻¹ / denRev.eval z⁻¹)
            (Filter.cocompact ℂ) (𝓝 (r.numReduced.leadingCoeff / r.denReduced.leadingCoeff)) := by
        have := hnumRev_tendsto.div hdenRev_tendsto hdenRev0_ne
        rw [hnumRev0, hdenRev0] at this
        exact this
      have hcong : ∀ᶠ (z : ℂ) in Filter.cocompact ℂ,
          r.toSphereMap (↑z : ℂ̂) =
            ((numRev.eval z⁻¹ / denRev.eval z⁻¹ : ℂ) : ℂ̂) := by
        filter_upwards [hden_cocompact, hz_ne_cocompact] with z hdz hzne
        have hnum := hident_num z hzne
        have hden := hident_den z hzne
        have hzm_ne : z ^ m ≠ 0 := pow_ne_zero _ hzne
        have hval : r.toSphereMap (↑z : ℂ̂) =
            ((r.numReduced.eval z / r.denReduced.eval z : ℂ) : ℂ̂) := by
          simp only [RationalData.toSphereMap, hdz, if_false]
        rw [hval]
        congr 1
        rw [hnum, hden, mul_div_mul_left _ _ hzm_ne]
      have hcont_coe :=
        (OnePoint.continuous_coe (X := ℂ)).continuousAt
          (x := (r.numReduced.leadingCoeff / r.denReduced.leadingCoeff : ℂ))
      have : Filter.Tendsto (fun z : ℂ => ((numRev.eval z⁻¹ / denRev.eval z⁻¹ : ℂ) : ℂ̂))
          (Filter.cocompact ℂ)
          (𝓝 (((r.numReduced.leadingCoeff / r.denReduced.leadingCoeff : ℂ) : ℂ̂))) :=
        hcont_coe.tendsto.comp hnumOdenRev_tendsto
      exact this.congr' (hcong.mono fun _ h => h.symm)
    · -- Case 3: n > d, m = n. numRev(0) = lc num ≠ 0, denRev(0) = 0.
      -- ‖num/den‖ → ∞.
      have hm_eq_n : m = n := by simp [hm_def, hnd.le]
      have hn_eq_m : n = m := hm_eq_n.symm
      have hd_ne_m : d ≠ m := by omega
      have hnumRev0 : numRev.eval 0 = r.numReduced.leadingCoeff := by
        rw [hnumRev_eval_zero, if_pos hn_eq_m]
      have hdenRev0 : denRev.eval 0 = 0 := by
        rw [hdenRev_eval_zero, if_neg hd_ne_m]
      -- num is nonzero (n > 0 since n > d ≥ 0)
      have hnum_ne_zero : r.numReduced ≠ 0 := by
        intro heq
        have : n = 0 := by rw [hn_def, heq, Polynomial.natDegree_zero]
        omega
      have hnumRev0_ne : numRev.eval 0 ≠ 0 := by
        rw [hnumRev0]; exact Polynomial.leadingCoeff_ne_zero.mpr hnum_ne_zero
      have hval_inf : r.toSphereMap ∞ = ∞ := by
        simp only [RationalData.toSphereMap]
        have hnlt : ¬ r.numReduced.natDegree < r.denReduced.natDegree := by omega
        have hneq : ¬ r.numReduced.natDegree = r.denReduced.natDegree := by omega
        rw [if_neg hnlt, if_neg hneq]
      rw [hval_inf]
      -- Tendsto to ∞ via OnePoint basis at infinity.
      rw [(OnePoint.hasBasis_nhds_infty (X := ℂ)).tendsto_right_iff]
      rintro K ⟨_, hK_compact⟩
      -- K is compact, get an upper bound on ‖·‖
      have hMbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, ‖z‖ ≤ M := by
        have himg : IsCompact ((fun z : ℂ => ‖z‖) '' K) := hK_compact.image continuous_norm
        obtain ⟨M, hM⟩ := himg.bddAbove
        refine ⟨max 0 M, le_max_left _ _, fun z hz => ?_⟩
        exact le_trans (hM ⟨z, hz, rfl⟩) (le_max_right _ _)
      obtain ⟨M, hM_nn, hM⟩ := hMbd
      -- We want eventually ‖num(z)/den(z)‖ > M (or den(z) = 0, both go into the target set)
      -- Equivalent: ‖numRev(1/z)/denRev(1/z)‖ > M eventually, by hkey.
      -- Use: ‖numRev(1/z)‖ > ‖lc num‖/2 and ‖denRev(1/z)‖ < ‖lc num‖/(2(M+1)) eventually.
      have hlc_norm_pos : 0 < ‖r.numReduced.leadingCoeff‖ :=
        norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hnum_ne_zero)
      have hbound_num : ∀ᶠ z in Filter.cocompact ℂ,
          ‖r.numReduced.leadingCoeff‖ / 2 < ‖numRev.eval z⁻¹‖ := by
        have hnumRev_norm_tendsto :
            Filter.Tendsto (fun z : ℂ => ‖numRev.eval z⁻¹‖) (Filter.cocompact ℂ)
              (𝓝 (‖r.numReduced.leadingCoeff‖)) := by
          rw [← hnumRev0]
          exact hnumRev_tendsto.norm
        have hpos : ‖r.numReduced.leadingCoeff‖ / 2 < ‖r.numReduced.leadingCoeff‖ := by linarith
        exact hnumRev_norm_tendsto.eventually (eventually_gt_nhds hpos)
      have hbound_den : ∀ᶠ z in Filter.cocompact ℂ,
          ‖denRev.eval z⁻¹‖ < ‖r.numReduced.leadingCoeff‖ / (2 * (M + 1)) := by
        have hdenRev_norm_tendsto :
            Filter.Tendsto (fun z : ℂ => ‖denRev.eval z⁻¹‖) (Filter.cocompact ℂ)
              (𝓝 0) := by
          have h0 : ‖denRev.eval (0 : ℂ)‖ = 0 := by rw [hdenRev0, norm_zero]
          rw [← h0]
          exact hdenRev_tendsto.norm
        have hpos : (0 : ℝ) < ‖r.numReduced.leadingCoeff‖ / (2 * (M + 1)) := by positivity
        exact hdenRev_norm_tendsto.eventually (eventually_lt_nhds hpos)
      filter_upwards [hden_cocompact, hz_ne_cocompact, hbound_num, hbound_den]
        with z hdz hzne hwn hwd
      -- Reduce the membership goal.
      by_cases hdenZ : r.denReduced.eval z = 0
      · -- denominator zero: r.toSphereMap ↑z = ∞ ∈ {∞}
        right
        show r.toSphereMap (↑z : ℂ̂) ∈ ({∞} : Set ℂ̂)
        simp only [RationalData.toSphereMap, hdenZ, if_true, Set.mem_singleton_iff]
      · -- denominator nonzero: r.toSphereMap ↑z = ↑(num/den), ‖num/den‖ > M.
        left
        show r.toSphereMap (↑z : ℂ̂) ∈ ((↑) : ℂ → ℂ̂) '' Kᶜ
        have hval : r.toSphereMap (↑z : ℂ̂) =
            ((r.numReduced.eval z / r.denReduced.eval z : ℂ) : ℂ̂) := by
          simp only [RationalData.toSphereMap, hdenZ, if_false]
        rw [hval]
        refine ⟨r.numReduced.eval z / r.denReduced.eval z, ?_, rfl⟩
        intro hin
        have hnorm_le : ‖r.numReduced.eval z / r.denReduced.eval z‖ ≤ M := hM _ hin
        -- Use the identity to rewrite num/den as numRev(1/z)/denRev(1/z).
        have hnum := hident_num z hzne
        have hden := hident_den z hzne
        have hzm_ne : z ^ m ≠ 0 := pow_ne_zero _ hzne
        have hrewrite : r.numReduced.eval z / r.denReduced.eval z =
            numRev.eval z⁻¹ / denRev.eval z⁻¹ := by
          rw [hnum, hden, mul_div_mul_left _ _ hzm_ne]
        rw [hrewrite, norm_div] at hnorm_le
        -- denRev(1/z) ≠ 0 since denReduced(z) ≠ 0 and the identity.
        have hdenRevInv_ne : denRev.eval z⁻¹ ≠ 0 := by
          intro hz0
          apply hdenZ
          rw [hden, hz0, mul_zero]
        have hdenRevInv_pos : 0 < ‖denRev.eval z⁻¹‖ := norm_pos_iff.mpr hdenRevInv_ne
        rw [div_le_iff₀ hdenRevInv_pos] at hnorm_le
        -- chain: ‖lc num‖/2 < ‖numRev(1/z)‖ ≤ M·‖denRev(1/z)‖ ≤ M·‖lc num‖/(2(M+1)) < ‖lc num‖/2.
        have hMp1_pos : (0 : ℝ) < M + 1 := by linarith
        have hkey₁ : M * ‖denRev.eval z⁻¹‖ ≤ M * (‖r.numReduced.leadingCoeff‖ / (2 * (M + 1))) :=
          mul_le_mul_of_nonneg_left hwd.le hM_nn
        have hkey₂ : M * (‖r.numReduced.leadingCoeff‖ / (2 * (M + 1))) <
            ‖r.numReduced.leadingCoeff‖ / 2 := by
          have hrew : ‖r.numReduced.leadingCoeff‖ / (2 * (M + 1))
              = ‖r.numReduced.leadingCoeff‖ / 2 / (M + 1) := by field_simp
          rw [hrew, ← mul_div_assoc, div_lt_iff₀ hMp1_pos]
          have : M * (‖r.numReduced.leadingCoeff‖ / 2) <
              (M + 1) * (‖r.numReduced.leadingCoeff‖ / 2) :=
            mul_lt_mul_of_pos_right (by linarith) (by linarith)
          linarith
        linarith
  · -- Continuity on finite ℂ.
    rw [continuous_iff_continuousAt]
    intro w₀
    by_cases hpole : r.denReduced.eval w₀ = 0
    · -- Pole case: r.toSphereMap (↑w₀) = ∞.
      have hval₀ : r.toSphereMap (↑w₀ : ℂ̂) = ∞ := by
        simp only [RationalData.toSphereMap, hpole, if_true]
      rw [ContinuousAt, hval₀]
      rw [(OnePoint.hasBasis_nhds_infty (X := ℂ)).tendsto_right_iff]
      rintro K ⟨hK_closed, hK_compact⟩
      -- K is compact, hence bounded; pick `M ≥ 0` bounding ‖·‖ on K.
      have hMbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, ‖z‖ ≤ M := by
        have himg : IsCompact ((fun z : ℂ => ‖z‖) '' K) := hK_compact.image continuous_norm
        obtain ⟨M, hM⟩ := himg.bddAbove
        refine ⟨max 0 M, le_max_left _ _, fun z hz => ?_⟩
        exact le_trans (hM ⟨z, hz, rfl⟩) (le_max_right _ _)
      obtain ⟨M, hM_nn, hM⟩ := hMbd
      have hnum_w₀ : r.numReduced.eval w₀ ≠ 0 := hno_common w₀ hpole
      have hnum_norm_pos : 0 < ‖r.numReduced.eval w₀‖ := norm_pos_iff.mpr hnum_w₀
      -- Choose target: |num(w)/den(w)| > M
      -- In a nbhd of w₀, |num(w)| > |num(w₀)|/2 and |den(w)| < |num(w₀)|/(2(M+1)).
      -- Then |num/den| > (|num(w₀)|/2) / (|num(w₀)|/(2(M+1))) = M+1 > M.
      have hbound_num : ∀ᶠ w in nhds w₀,
          ‖r.numReduced.eval w₀‖ / 2 < ‖r.numReduced.eval w‖ := by
        have hpos : (‖r.numReduced.eval w₀‖ / 2 : ℝ) < ‖r.numReduced.eval w₀‖ := by linarith
        exact ContinuousAt.eventually_lt continuousAt_const
          hcont_num.norm.continuousAt hpos
      have hbound_den : ∀ᶠ w in nhds w₀,
          ‖r.denReduced.eval w‖ < ‖r.numReduced.eval w₀‖ / (2 * (M + 1)) := by
        have hMp1_pos : (0 : ℝ) < 2 * (M + 1) := by linarith
        have hpos : (0 : ℝ) < ‖r.numReduced.eval w₀‖ / (2 * (M + 1)) := by positivity
        have hden_z : ‖r.denReduced.eval w₀‖ = 0 := by rw [hpole, norm_zero]
        exact ContinuousAt.eventually_lt hcont_den.norm.continuousAt continuousAt_const
          (by rw [hden_z]; exact hpos)
      filter_upwards [hbound_num, hbound_den] with w hwn hwd
      by_cases h : r.denReduced.eval w = 0
      · -- denominator is zero: value is ∞ ∈ {∞}
        right
        show r.toSphereMap (↑w : ℂ̂) ∈ ({∞} : Set ℂ̂)
        simp only [RationalData.toSphereMap, h, if_true, Set.mem_singleton_iff]
      · -- denominator nonzero: value is ↑(num/den), |num/den| > M ≥ ‖z‖ for z ∈ K, so ∉ K
        left
        show r.toSphereMap (↑w : ℂ̂) ∈ ((↑) : ℂ → ℂ̂) '' Kᶜ
        have hval : r.toSphereMap (↑w : ℂ̂) =
            ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂) := by
          simp only [RationalData.toSphereMap, h, if_false]
        rw [hval]
        refine ⟨r.numReduced.eval w / r.denReduced.eval w, ?_, rfl⟩
        intro hin
        have hnorm_le : ‖r.numReduced.eval w / r.denReduced.eval w‖ ≤ M := hM _ hin
        have hden_pos : 0 < ‖r.denReduced.eval w‖ := norm_pos_iff.mpr h
        rw [norm_div] at hnorm_le
        have hcontra : ‖r.numReduced.eval w‖ ≤ M * ‖r.denReduced.eval w‖ := by
          rw [div_le_iff₀ hden_pos] at hnorm_le; exact hnorm_le
        -- Derive the contradiction by chaining the three inequalities:
        --   ‖num(w₀)‖/2 < ‖num(w)‖ ≤ M·‖den(w)‖ ≤ M·‖num(w₀)‖/(2(M+1)) < ‖num(w₀)‖/2.
        have hMp1_pos : (0 : ℝ) < M + 1 := by linarith
        have hkey₁ : M * ‖r.denReduced.eval w‖ ≤ M * (‖r.numReduced.eval w₀‖ / (2 * (M + 1))) :=
          mul_le_mul_of_nonneg_left hwd.le hM_nn
        have hkey₂ : M * (‖r.numReduced.eval w₀‖ / (2 * (M + 1))) <
            ‖r.numReduced.eval w₀‖ / 2 := by
          have hrewrite : ‖r.numReduced.eval w₀‖ / (2 * (M + 1))
              = ‖r.numReduced.eval w₀‖ / 2 / (M + 1) := by field_simp
          rw [hrewrite, ← mul_div_assoc, div_lt_iff₀ hMp1_pos]
          have : M * (‖r.numReduced.eval w₀‖ / 2) <
              (M + 1) * (‖r.numReduced.eval w₀‖ / 2) :=
            mul_lt_mul_of_pos_right (by linarith) (by linarith)
          linarith
        linarith
    · -- Non-pole case
      have h_nbhd : ∀ᶠ w in nhds w₀, r.denReduced.eval w ≠ 0 :=
        hcont_den.continuousAt.eventually_ne hpole
      have hval_eq : (fun w : ℂ => r.toSphereMap (↑w : ℂ̂)) =ᶠ[nhds w₀]
                     (fun w => ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂)) := by
        filter_upwards [h_nbhd] with w hw
        simp only [RationalData.toSphereMap, hw, if_false]
      have hcont_local : ContinuousAt
          (fun w => ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂)) w₀ :=
        OnePoint.continuous_coe.continuousAt.comp
          (ContinuousAt.div hcont_num.continuousAt hcont_den.continuousAt hpole)
      have hval₀ : r.toSphereMap (↑w₀ : ℂ̂) =
          ((r.numReduced.eval w₀ / r.denReduced.eval w₀ : ℂ) : ℂ̂) := by
        simp only [RationalData.toSphereMap, hpole, if_false]
      rw [ContinuousAt, hval₀]
      have hca : ContinuousAt (fun w : ℂ => r.toSphereMap (↑w : ℂ̂)) w₀ :=
        hcont_local.congr hval_eq.symm
      rw [ContinuousAt] at hca
      rw [hval₀] at hca
      exact hca

/-- The composed rational data realizes the composition of the underlying
rational maps, provided the inner map is nonconstant. -/
theorem RationalData.composeRational_toSphereMap_eq (r₁ r₂ : RationalData)
    (h : 1 ≤ r₂.degree) :
    (r₁.composeRational r₂).toSphereMap = r₁.toSphereMap ∘ r₂.toSphereMap := by
  -- Setup the constituent polynomials.
  set N₁ := r₁.numReduced with hN₁_def
  set D₁ := r₁.denReduced with hD₁_def
  set N₂ := r₂.numReduced with hN₂_def
  set D₂ := r₂.denReduced with hD₂_def
  set n := r₁.degree with hn_def
  set num_comp : ℂ[X] :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.C (N₁.coeff i) * N₂ ^ i * D₂ ^ (n - i)
    with hnum_comp_def
  set den_comp : ℂ[X] :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.C (D₁.coeff i) * N₂ ^ i * D₂ ^ (n - i)
    with hden_comp_def
  have hD₁_ne_zero : D₁ ≠ 0 := by rw [hD₁_def]; exact r₁.denReduced_ne_zero
  have hD₂_ne_zero : D₂ ≠ 0 := by rw [hD₂_def]; exact r₂.denReduced_ne_zero
  have hcop_g : IsCoprime N₂ D₂ := isCoprime_div_gcd_div_gcd r₂.den_ne_zero
  have hN₁_natDeg_le_n : N₁.natDegree ≤ n := by
    rw [hn_def, RationalData.degree]; exact le_max_left _ _
  have hD₁_natDeg_le_n : D₁.natDegree ≤ n := by
    rw [hn_def, RationalData.degree]; exact le_max_right _ _
  have hnum_comp_eval : ∀ z : ℂ, D₂.eval z ≠ 0 →
      num_comp.eval z = D₂.eval z ^ n * N₁.eval (N₂.eval z / D₂.eval z) := by
    intro z hz
    rw [hnum_comp_def]
    exact r₂.homogenize_eval N₁ n hN₁_natDeg_le_n hz
  have hden_comp_eval : ∀ z : ℂ, D₂.eval z ≠ 0 →
      den_comp.eval z = D₂.eval z ^ n * D₁.eval (N₂.eval z / D₂.eval z) := by
    intro z hz
    rw [hden_comp_def]
    exact r₂.homogenize_eval D₁ n hD₁_natDeg_le_n hz
  have hden_comp_ne_zero : den_comp ≠ 0 := by
    have hbridge : r₁.composeDen r₂ = den_comp := by
      rw [hden_comp_def, RationalData.composeDen]
    rw [← hbridge]; exact r₁.composeDen_ne_zero r₂ h
  -- Unfold composeRational to the explicit construction.
  have hcomposeNum_eq : r₁.composeNum r₂ = num_comp := by
    rw [hnum_comp_def, RationalData.composeNum]
  have hcomposeDen_eq : r₁.composeDen r₂ = den_comp := by
    rw [hden_comp_def, RationalData.composeDen]
  have hcomp_unfold :
      r₁.composeRational r₂ = ⟨num_comp, den_comp, hden_comp_ne_zero⟩ := by
    unfold RationalData.composeRational
    rw [hcomposeDen_eq]
    rw [dif_pos hden_comp_ne_zero]
    congr 1
  rw [hcomp_unfold]
  -- Show ⟨num_comp, den_comp, _⟩.toSphereMap = r₁.toSphereMap ∘ r₂.toSphereMap
  -- via continuity on ℂ̂ and density of ℂ.
  have hcomp_cont : Continuous
      (⟨num_comp, den_comp, hden_comp_ne_zero⟩ : RationalData).toSphereMap :=
    RationalData.continuous_toSphereMap _
  have hfg_cont : Continuous (r₁.toSphereMap ∘ r₂.toSphereMap) :=
    r₁.continuous_toSphereMap.comp r₂.continuous_toSphereMap
  symm
  apply Continuous.ext_on (s := Set.range (OnePoint.some : ℂ → ℂ̂)) ?_ hfg_cont hcomp_cont ?_
  · exact OnePoint.denseRange_coe
  · rintro _ ⟨w, rfl⟩
    have hbad_fin : {w : ℂ | D₂.eval w = 0 ∨ den_comp.eval w = 0}.Finite := by
      apply Set.Finite.union
      · exact finite_setOf_eval_eq_zero hD₂_ne_zero
      · exact finite_setOf_eval_eq_zero hden_comp_ne_zero
    have hbad_countable : Set.Countable {w : ℂ | D₂.eval w = 0 ∨ den_comp.eval w = 0} :=
      hbad_fin.countable
    have hgood_dense : Dense ({w : ℂ | D₂.eval w = 0 ∨ den_comp.eval w = 0}ᶜ) :=
      Set.Countable.dense_compl ℝ hbad_countable
    have hfg_finite_cont :
        Continuous (fun w : ℂ => (r₁.toSphereMap ∘ r₂.toSphereMap) (OnePoint.some w)) :=
      hfg_cont.comp OnePoint.continuous_coe
    have hcomp_finite_cont : Continuous (fun w : ℂ =>
        (⟨num_comp, den_comp, hden_comp_ne_zero⟩ : RationalData).toSphereMap (OnePoint.some w)) :=
      hcomp_cont.comp OnePoint.continuous_coe
    have heq_fn :
        (fun w : ℂ => (r₁.toSphereMap ∘ r₂.toSphereMap) (OnePoint.some w)) =
        (fun w : ℂ =>
          (⟨num_comp, den_comp, hden_comp_ne_zero⟩ :
            RationalData).toSphereMap (OnePoint.some w)) := by
      apply Continuous.ext_on hgood_dense hfg_finite_cont hcomp_finite_cont
      intro w hw
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_or] at hw
      obtain ⟨hD₂_w, hden_w⟩ := hw
      have hD₁_quot_ne : D₁.eval (N₂.eval w / D₂.eval w) ≠ 0 := by
        intro hzero
        apply hden_w
        rw [hden_comp_eval w hD₂_w, hzero, mul_zero]
      have hg_val : r₂.toSphereMap (OnePoint.some w) = ((N₂.eval w / D₂.eval w : ℂ) : ℂ̂) := by
        simp only [RationalData.toSphereMap, ← hN₂_def, ← hD₂_def, hD₂_w, if_false]
      have hf_val : r₁.toSphereMap ((N₂.eval w / D₂.eval w : ℂ) : ℂ̂) =
          ((N₁.eval (N₂.eval w / D₂.eval w) / D₁.eval (N₂.eval w / D₂.eval w) : ℂ) : ℂ̂) := by
        simp only [RationalData.toSphereMap, ← hN₁_def, ← hD₁_def, hD₁_quot_ne, if_false]
      let r_comp : RationalData := ⟨num_comp, den_comp, hden_comp_ne_zero⟩
      have hg_dvd_num : gcd num_comp den_comp ∣ num_comp := gcd_dvd_left _ _
      have hg_dvd_den : gcd num_comp den_comp ∣ den_comp := gcd_dvd_right _ _
      have hg_ne_zero : gcd num_comp den_comp ≠ 0 := gcd_ne_zero_of_right hden_comp_ne_zero
      have hnum_factor : num_comp = gcd num_comp den_comp * r_comp.numReduced := by
        change num_comp = gcd num_comp den_comp * (num_comp / gcd num_comp den_comp)
        rw [EuclideanDomain.mul_div_cancel' hg_ne_zero hg_dvd_num]
      have hden_factor : den_comp = gcd num_comp den_comp * r_comp.denReduced := by
        change den_comp = gcd num_comp den_comp * (den_comp / gcd num_comp den_comp)
        rw [EuclideanDomain.mul_div_cancel' hg_ne_zero hg_dvd_den]
      have hg_eval_ne : (gcd num_comp den_comp).eval w ≠ 0 := by
        intro hg0
        apply hden_w
        rw [hden_factor, Polynomial.eval_mul, hg0, zero_mul]
      have hden_red_ne : r_comp.denReduced.eval w ≠ 0 := by
        intro hred0
        apply hden_w
        rw [hden_factor, Polynomial.eval_mul, hred0, mul_zero]
      have hcross : r_comp.numReduced.eval w * den_comp.eval w =
          num_comp.eval w * r_comp.denReduced.eval w := by
        have h1 := congrArg (Polynomial.eval w) hnum_factor
        have h2 := congrArg (Polynomial.eval w) hden_factor
        simp only [Polynomial.eval_mul] at h1 h2
        rw [h1, h2]; ring
      have hcomp_val :
          r_comp.toSphereMap (OnePoint.some w) =
            ((num_comp.eval w / den_comp.eval w : ℂ) : ℂ̂) := by
        change (if r_comp.denReduced.eval w = 0 then ∞
                else ((r_comp.numReduced.eval w / r_comp.denReduced.eval w : ℂ) : ℂ̂)) = _
        rw [if_neg hden_red_ne]
        congr 1
        rw [div_eq_div_iff hden_red_ne hden_w]
        linear_combination hcross
      change r₁.toSphereMap (r₂.toSphereMap (OnePoint.some w)) =
          r_comp.toSphereMap (OnePoint.some w)
      rw [hg_val, hf_val, hcomp_val]
      congr 1
      rw [hnum_comp_eval w hD₂_w, hden_comp_eval w hD₂_w]
      have hD₂_pow : D₂.eval w ^ n ≠ 0 := pow_ne_zero _ hD₂_w
      field_simp
    exact congrFun heq_fn w

/-- Lower bound on the natural degree of the composed polynomials: at least one
of `composeNum r₁ r₂` or `composeDen r₁ r₂` has natural degree at least the
product `r₁.degree * r₂.degree`. -/
theorem RationalData.mul_degree_le_max_natDegree_composeNum_composeDen
    (r₁ r₂ : RationalData) (h : 1 ≤ r₂.degree) :
    r₁.degree * r₂.degree ≤
      max (r₁.composeNum r₂).natDegree (r₁.composeDen r₂).natDegree := by
  set N₁ := r₁.numReduced with hN₁_def
  set D₁ := r₁.denReduced with hD₁_def
  set N₂ := r₂.numReduced with hN₂_def
  set D₂ := r₂.denReduced with hD₂_def
  set n := r₁.degree with hn_def
  set m := r₂.degree with hm_def
  -- Unfold composeNum/composeDen to explicit sums.
  set num_comp : ℂ[X] :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.C (N₁.coeff i) * N₂ ^ i * D₂ ^ (n - i)
    with hnum_comp_def
  set den_comp : ℂ[X] :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.C (D₁.coeff i) * N₂ ^ i * D₂ ^ (n - i)
    with hden_comp_def
  have hcomposeNum_eq : r₁.composeNum r₂ = num_comp := by
    rw [hnum_comp_def, RationalData.composeNum]
  have hcomposeDen_eq : r₁.composeDen r₂ = den_comp := by
    rw [hden_comp_def, RationalData.composeDen]
  rw [hcomposeNum_eq, hcomposeDen_eq]
  -- D₁, D₂ nonzero (denReduced ≠ 0).
  have hD₁_ne_zero : D₁ ≠ 0 := by rw [hD₁_def]; exact r₁.denReduced_ne_zero
  have hD₂_ne_zero : D₂ ≠ 0 := by rw [hD₂_def]; exact r₂.denReduced_ne_zero
  have hcop_f : IsCoprime N₁ D₁ := isCoprime_div_gcd_div_gcd r₁.den_ne_zero
  have hcop_g : IsCoprime N₂ D₂ := isCoprime_div_gcd_div_gcd r₂.den_ne_zero
  have hN₁_natDeg_le_n : N₁.natDegree ≤ n := by
    rw [hn_def, RationalData.degree]; exact le_max_left _ _
  have hD₁_natDeg_le_n : D₁.natDegree ≤ n := by
    rw [hn_def, RationalData.degree]; exact le_max_right _ _
  have hN₂_natDeg_le_m : N₂.natDegree ≤ m := by
    rw [hm_def, RationalData.degree]; exact le_max_left _ _
  have hD₂_natDeg_le_m : D₂.natDegree ≤ m := by
    rw [hm_def, RationalData.degree]; exact le_max_right _ _
  -- m = max(N₂.natDegree, D₂.natDegree).
  have hm_eq_max : m = max N₂.natDegree D₂.natDegree := by
    rw [hm_def, RationalData.degree]
  -- N₂ ≠ 0.
  have hN₂_ne_zero : N₂ ≠ 0 := by
    intro hzero
    have hD₂_unit : IsUnit D₂ := by
      have := hcop_g; rw [hzero] at this
      rwa [isCoprime_zero_left] at this
    have hD₂_natDeg : D₂.natDegree = 0 := by
      rcases Polynomial.isUnit_iff.mp hD₂_unit with ⟨c, _, hc⟩
      rw [← hc]; exact Polynomial.natDegree_C _
    have hr₂_deg : r₂.degree = 0 := by
      rw [RationalData.degree, ← hN₂_def, ← hD₂_def, hzero, Polynomial.natDegree_zero,
          hD₂_natDeg]; rfl
    rw [hm_def, hr₂_deg] at h
    exact Nat.lt_irrefl 0 h
  have hlc_N₂_ne : N₂.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hN₂_ne_zero
  have hlc_D₂_ne : D₂.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD₂_ne_zero
  -- Coefficient formula for each summand at index (n * m).
  have hterm_coeff : ∀ (c : ℂ) (i : ℕ), i ≤ n →
      (Polynomial.C c * N₂ ^ i * D₂ ^ (n - i)).coeff (n * m) =
        if i * N₂.natDegree + (n - i) * D₂.natDegree = n * m then
          c * N₂.leadingCoeff ^ i * D₂.leadingCoeff ^ (n - i)
        else 0 := by
    intro c i hi
    rw [mul_assoc, Polynomial.coeff_C_mul]
    have hND_natDeg : (N₂ ^ i * D₂ ^ (n - i)).natDegree =
        i * N₂.natDegree + (n - i) * D₂.natDegree := by
      rw [Polynomial.natDegree_mul (pow_ne_zero i hN₂_ne_zero) (pow_ne_zero (n - i) hD₂_ne_zero),
          Polynomial.natDegree_pow, Polynomial.natDegree_pow]
    have hND_lc : (N₂ ^ i * D₂ ^ (n - i)).leadingCoeff =
        N₂.leadingCoeff ^ i * D₂.leadingCoeff ^ (n - i) := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_pow]
    have hbd : i * N₂.natDegree + (n - i) * D₂.natDegree ≤ n * m := by
      have step1 : i * N₂.natDegree + (n - i) * D₂.natDegree ≤ i * m + (n - i) * m :=
        Nat.add_le_add (Nat.mul_le_mul_left i hN₂_natDeg_le_m)
          (Nat.mul_le_mul_left (n - i) hD₂_natDeg_le_m)
      have step2 : i * m + (n - i) * m = n * m := by rw [← Nat.add_mul]; congr 1; omega
      omega
    by_cases heq : i * N₂.natDegree + (n - i) * D₂.natDegree = n * m
    · rw [if_pos heq]
      have hnatDeg : (N₂ ^ i * D₂ ^ (n - i)).natDegree = n * m := by rw [hND_natDeg, heq]
      rw [show (N₂ ^ i * D₂ ^ (n - i)).coeff (n * m) = (N₂ ^ i * D₂ ^ (n - i)).leadingCoeff from by
          rw [← hnatDeg]; exact Polynomial.coeff_natDegree]
      rw [hND_lc]; ring
    · rw [if_neg heq]
      have hlt : (N₂ ^ i * D₂ ^ (n - i)).natDegree < n * m := by rw [hND_natDeg]; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
  -- Case analysis on N₂.natDegree vs D₂.natDegree.
  rcases Nat.lt_trichotomy N₂.natDegree D₂.natDegree with hcmp | hcmp | hcmp
  · -- Case 1: N₂.natDeg < D₂.natDeg, so m = D₂.natDeg.
    have hm_eq_D₂ : m = D₂.natDegree := by rw [hm_eq_max]; exact max_eq_right hcmp.le
    -- num_comp.coeff (n * m) = N₁.coeff 0 * (lc D₂) ^ n.
    have hnum_coeff : num_comp.coeff (n * m) =
        N₁.coeff 0 * D₂.leadingCoeff ^ n := by
      rw [hnum_comp_def, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single 0]
      · rw [hterm_coeff (N₁.coeff 0) 0 (Nat.zero_le _)]
        have h0 : 0 * N₂.natDegree + (n - 0) * D₂.natDegree = n * m := by
          rw [Nat.sub_zero, hm_eq_D₂]; ring
        rw [if_pos h0, Nat.sub_zero, pow_zero, mul_one]
      · intro i hi hi_ne
        rw [Finset.mem_range] at hi
        rw [hterm_coeff (N₁.coeff i) i (by omega)]
        have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_ne
        have hne : i * N₂.natDegree + (n - i) * D₂.natDegree ≠ n * m := by
          rw [hm_eq_D₂]
          have hsum : i * N₂.natDegree + (n - i) * D₂.natDegree
              < i * D₂.natDegree + (n - i) * D₂.natDegree := by
            have : i * N₂.natDegree < i * D₂.natDegree :=
              Nat.mul_lt_mul_of_pos_left hcmp hi_pos
            omega
          have hrw : i * D₂.natDegree + (n - i) * D₂.natDegree = n * D₂.natDegree := by
            rw [← Nat.add_mul]; congr 1; omega
          omega
        rw [if_neg hne]
      · intro h0_ne; exfalso; apply h0_ne; rw [Finset.mem_range]; omega
    have hden_coeff : den_comp.coeff (n * m) =
        D₁.coeff 0 * D₂.leadingCoeff ^ n := by
      rw [hden_comp_def, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single 0]
      · rw [hterm_coeff (D₁.coeff 0) 0 (Nat.zero_le _)]
        have h0 : 0 * N₂.natDegree + (n - 0) * D₂.natDegree = n * m := by
          rw [Nat.sub_zero, hm_eq_D₂]; ring
        rw [if_pos h0, Nat.sub_zero, pow_zero, mul_one]
      · intro i hi hi_ne
        rw [Finset.mem_range] at hi
        rw [hterm_coeff (D₁.coeff i) i (by omega)]
        have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_ne
        have hne : i * N₂.natDegree + (n - i) * D₂.natDegree ≠ n * m := by
          rw [hm_eq_D₂]
          have hsum : i * N₂.natDegree + (n - i) * D₂.natDegree
              < i * D₂.natDegree + (n - i) * D₂.natDegree := by
            have : i * N₂.natDegree < i * D₂.natDegree :=
              Nat.mul_lt_mul_of_pos_left hcmp hi_pos
            omega
          have hrw : i * D₂.natDegree + (n - i) * D₂.natDegree = n * D₂.natDegree := by
            rw [← Nat.add_mul]; congr 1; omega
          omega
        rw [if_neg hne]
      · intro h0_ne; exfalso; apply h0_ne; rw [Finset.mem_range]; omega
    have hlcD₂n_ne : D₂.leadingCoeff ^ n ≠ 0 := pow_ne_zero _ hlc_D₂_ne
    -- At least one of N₁.coeff 0 or D₁.coeff 0 is nonzero.
    have hne_or : num_comp.coeff (n * m) ≠ 0 ∨ den_comp.coeff (n * m) ≠ 0 := by
      by_contra hboth
      push Not at hboth
      obtain ⟨hnum_zero, hden_zero⟩ := hboth
      rw [hnum_coeff, mul_eq_zero] at hnum_zero
      rw [hden_coeff, mul_eq_zero] at hden_zero
      have hN₁0 : N₁.coeff 0 = 0 := hnum_zero.resolve_right hlcD₂n_ne
      have hD₁0 : D₁.coeff 0 = 0 := hden_zero.resolve_right hlcD₂n_ne
      have hX_dvd_N₁ : Polynomial.X ∣ N₁ := by rw [Polynomial.X_dvd_iff]; exact hN₁0
      have hX_dvd_D₁ : Polynomial.X ∣ D₁ := by rw [Polynomial.X_dvd_iff]; exact hD₁0
      exact Polynomial.not_isUnit_X (hcop_f.isUnit_of_dvd' hX_dvd_N₁ hX_dvd_D₁)
    rcases hne_or with hne | hne
    · exact le_max_of_le_left (Polynomial.le_natDegree_of_ne_zero hne)
    · exact le_max_of_le_right (Polynomial.le_natDegree_of_ne_zero hne)
  · -- Case 2: N₂.natDeg = D₂.natDeg = m.
    have hN₂_eq_m : N₂.natDegree = m := by rw [hm_eq_max, hcmp, max_self]
    have hD₂_eq_m : D₂.natDegree = m := by rw [hm_eq_max, hcmp, max_self]
    have hall_eq : ∀ i ≤ n, i * N₂.natDegree + (n - i) * D₂.natDegree = n * m := by
      intro i _
      rw [hN₂_eq_m, hD₂_eq_m, ← Nat.add_mul]; congr 1; omega
    set α := N₂.leadingCoeff / D₂.leadingCoeff with hα_def
    have hnum_coeff : num_comp.coeff (n * m) =
        D₂.leadingCoeff ^ n * N₁.eval α := by
      rw [hnum_comp_def, Polynomial.finsetSum_coeff]
      have hsum : ∑ i ∈ Finset.range (n + 1),
          (Polynomial.C (N₁.coeff i) * N₂ ^ i * D₂ ^ (n - i)).coeff (n * m) =
          ∑ i ∈ Finset.range (n + 1),
            N₁.coeff i * N₂.leadingCoeff ^ i * D₂.leadingCoeff ^ (n - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        rw [hterm_coeff (N₁.coeff i) i (by omega), if_pos (hall_eq i (by omega))]
      rw [hsum]
      rw [Polynomial.eval_eq_sum_range' (n := n + 1) (by omega) (p := N₁) (x := α)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hi_le : i ≤ n := by omega
      have hlcD₂_i_ne : D₂.leadingCoeff ^ i ≠ 0 := pow_ne_zero _ hlc_D₂_ne
      have hpow_split : D₂.leadingCoeff ^ n =
          D₂.leadingCoeff ^ i * D₂.leadingCoeff ^ (n - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hi_le]
      have hsub : D₂.leadingCoeff ^ (n - i) =
          D₂.leadingCoeff ^ n / D₂.leadingCoeff ^ i := by
        rw [eq_div_iff hlcD₂_i_ne, mul_comm]; exact hpow_split.symm
      rw [hsub, hα_def, div_pow]; ring
    have hden_coeff : den_comp.coeff (n * m) =
        D₂.leadingCoeff ^ n * D₁.eval α := by
      rw [hden_comp_def, Polynomial.finsetSum_coeff]
      have hsum : ∑ i ∈ Finset.range (n + 1),
          (Polynomial.C (D₁.coeff i) * N₂ ^ i * D₂ ^ (n - i)).coeff (n * m) =
          ∑ i ∈ Finset.range (n + 1),
            D₁.coeff i * N₂.leadingCoeff ^ i * D₂.leadingCoeff ^ (n - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        rw [hterm_coeff (D₁.coeff i) i (by omega), if_pos (hall_eq i (by omega))]
      rw [hsum]
      rw [Polynomial.eval_eq_sum_range' (n := n + 1) (by omega) (p := D₁) (x := α)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hi_le : i ≤ n := by omega
      have hlcD₂_i_ne : D₂.leadingCoeff ^ i ≠ 0 := pow_ne_zero _ hlc_D₂_ne
      have hpow_split : D₂.leadingCoeff ^ n =
          D₂.leadingCoeff ^ i * D₂.leadingCoeff ^ (n - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hi_le]
      have hsub : D₂.leadingCoeff ^ (n - i) =
          D₂.leadingCoeff ^ n / D₂.leadingCoeff ^ i := by
        rw [eq_div_iff hlcD₂_i_ne, mul_comm]; exact hpow_split.symm
      rw [hsub, hα_def, div_pow]; ring
    have hlcD₂n_ne : D₂.leadingCoeff ^ n ≠ 0 := pow_ne_zero _ hlc_D₂_ne
    have hne_or : num_comp.coeff (n * m) ≠ 0 ∨ den_comp.coeff (n * m) ≠ 0 := by
      by_contra hboth
      push Not at hboth
      obtain ⟨hnum_zero, hden_zero⟩ := hboth
      rw [hnum_coeff, mul_eq_zero] at hnum_zero
      rw [hden_coeff, mul_eq_zero] at hden_zero
      have hN₁α : N₁.eval α = 0 := hnum_zero.resolve_left hlcD₂n_ne
      have hD₁α : D₁.eval α = 0 := hden_zero.resolve_left hlcD₂n_ne
      obtain ⟨a, b, hab⟩ := hcop_f
      have := congrArg (Polynomial.eval α) hab
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] at this
      rw [hN₁α, hD₁α, mul_zero, mul_zero, add_zero] at this
      exact zero_ne_one this
    rcases hne_or with hne | hne
    · exact le_max_of_le_left (Polynomial.le_natDegree_of_ne_zero hne)
    · exact le_max_of_le_right (Polynomial.le_natDegree_of_ne_zero hne)
  · -- Case 3: N₂.natDeg > D₂.natDeg, so m = N₂.natDeg.
    have hm_eq_N₂ : m = N₂.natDegree := by rw [hm_eq_max]; exact max_eq_left hcmp.le
    have hnum_coeff : num_comp.coeff (n * m) =
        N₁.coeff n * N₂.leadingCoeff ^ n := by
      rw [hnum_comp_def, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single n]
      · rw [hterm_coeff (N₁.coeff n) n le_rfl]
        have h_eq : n * N₂.natDegree + (n - n) * D₂.natDegree = n * m := by
          rw [Nat.sub_self, hm_eq_N₂]; ring
        rw [if_pos h_eq, Nat.sub_self, pow_zero, mul_one]
      · intro i hi hi_ne
        rw [Finset.mem_range] at hi
        rw [hterm_coeff (N₁.coeff i) i (by omega)]
        have hi_lt : i < n := lt_of_le_of_ne (by omega) hi_ne
        have hne : i * N₂.natDegree + (n - i) * D₂.natDegree ≠ n * m := by
          rw [hm_eq_N₂]
          have hsum : i * N₂.natDegree + (n - i) * D₂.natDegree
              < i * N₂.natDegree + (n - i) * N₂.natDegree := by
            have : (n - i) * D₂.natDegree < (n - i) * N₂.natDegree :=
              Nat.mul_lt_mul_of_pos_left hcmp (by omega)
            omega
          have hrw : i * N₂.natDegree + (n - i) * N₂.natDegree = n * N₂.natDegree := by
            rw [← Nat.add_mul]; congr 1; omega
          omega
        rw [if_neg hne]
      · intro hn_ne; exfalso; apply hn_ne; rw [Finset.mem_range]; omega
    have hden_coeff : den_comp.coeff (n * m) =
        D₁.coeff n * N₂.leadingCoeff ^ n := by
      rw [hden_comp_def, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single n]
      · rw [hterm_coeff (D₁.coeff n) n le_rfl]
        have h_eq : n * N₂.natDegree + (n - n) * D₂.natDegree = n * m := by
          rw [Nat.sub_self, hm_eq_N₂]; ring
        rw [if_pos h_eq, Nat.sub_self, pow_zero, mul_one]
      · intro i hi hi_ne
        rw [Finset.mem_range] at hi
        rw [hterm_coeff (D₁.coeff i) i (by omega)]
        have hi_lt : i < n := lt_of_le_of_ne (by omega) hi_ne
        have hne : i * N₂.natDegree + (n - i) * D₂.natDegree ≠ n * m := by
          rw [hm_eq_N₂]
          have hsum : i * N₂.natDegree + (n - i) * D₂.natDegree
              < i * N₂.natDegree + (n - i) * N₂.natDegree := by
            have : (n - i) * D₂.natDegree < (n - i) * N₂.natDegree :=
              Nat.mul_lt_mul_of_pos_left hcmp (by omega)
            omega
          have hrw : i * N₂.natDegree + (n - i) * N₂.natDegree = n * N₂.natDegree := by
            rw [← Nat.add_mul]; congr 1; omega
          omega
        rw [if_neg hne]
      · intro hn_ne; exfalso; apply hn_ne; rw [Finset.mem_range]; omega
    have hlcN₂n_ne : N₂.leadingCoeff ^ n ≠ 0 := pow_ne_zero _ hlc_N₂_ne
    have hne_or : num_comp.coeff (n * m) ≠ 0 ∨ den_comp.coeff (n * m) ≠ 0 := by
      by_contra hboth
      push Not at hboth
      obtain ⟨hnum_zero, hden_zero⟩ := hboth
      rw [hnum_coeff, mul_eq_zero] at hnum_zero
      rw [hden_coeff, mul_eq_zero] at hden_zero
      have hN₁n : N₁.coeff n = 0 := hnum_zero.resolve_right hlcN₂n_ne
      have hD₁n : D₁.coeff n = 0 := hden_zero.resolve_right hlcN₂n_ne
      have hn_eq_max : n = max N₁.natDegree D₁.natDegree := by
        rw [hn_def, RationalData.degree]
      rcases Nat.lt_or_ge N₁.natDegree D₁.natDegree with hND | hND
      · have hn_D₁ : n = D₁.natDegree := by rw [hn_eq_max]; exact max_eq_right hND.le
        rw [hn_D₁] at hD₁n
        exact (Polynomial.leadingCoeff_ne_zero.mpr hD₁_ne_zero) hD₁n
      · have hn_N₁ : n = N₁.natDegree := by rw [hn_eq_max]; exact max_eq_left hND
        rw [hn_N₁] at hN₁n
        by_cases hN₁_ne : N₁ = 0
        · -- N₁ = 0. Then N₁.coeff n = 0 trivially. Use D₁ coprimality.
          -- IsCoprime 0 D₁ ⟹ D₁ unit ⟹ D₁.natDegree = 0 ⟹ n = 0
          have hD₁_unit : IsUnit D₁ := by
            have := hcop_f; rw [hN₁_ne] at this
            rwa [isCoprime_zero_left] at this
          have hD₁_natDeg : D₁.natDegree = 0 := by
            rcases Polynomial.isUnit_iff.mp hD₁_unit with ⟨c, _, hc⟩
            rw [← hc]; exact Polynomial.natDegree_C _
          have hn_zero : n = 0 := by
            rw [hn_N₁, hN₁_ne, Polynomial.natDegree_zero]
          -- Then D₁.coeff 0 = D₁.coeff (D₁.natDegree) = lc D₁ ≠ 0
          rw [hn_zero] at hD₁n
          have : D₁.coeff 0 = D₁.leadingCoeff := by
            rw [Polynomial.leadingCoeff, hD₁_natDeg]
          rw [this] at hD₁n
          exact (Polynomial.leadingCoeff_ne_zero.mpr hD₁_ne_zero) hD₁n
        · exact (Polynomial.leadingCoeff_ne_zero.mpr hN₁_ne) hN₁n
    rcases hne_or with hne | hne
    · exact le_max_of_le_left (Polynomial.le_natDegree_of_ne_zero hne)
    · exact le_max_of_le_right (Polynomial.le_natDegree_of_ne_zero hne)

/-- The degree of the composed rational data is the product of degrees, when the
inner is nonconstant. -/
theorem RationalData.composeRational_degree_eq (r₁ r₂ : RationalData)
    (h : 1 ≤ r₂.degree) :
    (r₁.composeRational r₂).degree = r₁.degree * r₂.degree := by
  -- Setup, identical to composeRational_toSphereMap_eq.
  set N₁ := r₁.numReduced with hN₁_def
  set D₁ := r₁.denReduced with hD₁_def
  set N₂ := r₂.numReduced with hN₂_def
  set D₂ := r₂.denReduced with hD₂_def
  set n := r₁.degree with hn_def
  set m := r₂.degree with hm_def
  set num_comp : ℂ[X] :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.C (N₁.coeff i) * N₂ ^ i * D₂ ^ (n - i)
    with hnum_comp_def
  set den_comp : ℂ[X] :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.C (D₁.coeff i) * N₂ ^ i * D₂ ^ (n - i)
    with hden_comp_def
  have hD₁_ne_zero : D₁ ≠ 0 := by rw [hD₁_def]; exact r₁.denReduced_ne_zero
  have hD₂_ne_zero : D₂ ≠ 0 := by rw [hD₂_def]; exact r₂.denReduced_ne_zero
  have hcop_g : IsCoprime N₂ D₂ := isCoprime_div_gcd_div_gcd r₂.den_ne_zero
  have hcop_f : IsCoprime N₁ D₁ := isCoprime_div_gcd_div_gcd r₁.den_ne_zero
  have hN₁_natDeg_le_n : N₁.natDegree ≤ n := by
    rw [hn_def, RationalData.degree]; exact le_max_left _ _
  have hD₁_natDeg_le_n : D₁.natDegree ≤ n := by
    rw [hn_def, RationalData.degree]; exact le_max_right _ _
  have hN₂_natDeg_le_m : N₂.natDegree ≤ m := by
    rw [hm_def, RationalData.degree]; exact le_max_left _ _
  have hD₂_natDeg_le_m : D₂.natDegree ≤ m := by
    rw [hm_def, RationalData.degree]; exact le_max_right _ _
  -- Algebraic identities at points with D₂(z) ≠ 0.
  have hnum_comp_eval : ∀ z : ℂ, D₂.eval z ≠ 0 →
      num_comp.eval z = D₂.eval z ^ n * N₁.eval (N₂.eval z / D₂.eval z) := by
    intro z hz
    rw [hnum_comp_def]
    exact r₂.homogenize_eval N₁ n hN₁_natDeg_le_n hz
  have hden_comp_eval : ∀ z : ℂ, D₂.eval z ≠ 0 →
      den_comp.eval z = D₂.eval z ^ n * D₁.eval (N₂.eval z / D₂.eval z) := by
    intro z hz
    rw [hden_comp_def]
    exact r₂.homogenize_eval D₁ n hD₁_natDeg_le_n hz
  have hden_comp_ne_zero : den_comp ≠ 0 := by
    have hbridge : r₁.composeDen r₂ = den_comp := by
      rw [hden_comp_def, RationalData.composeDen]
    rw [← hbridge]; exact r₁.composeDen_ne_zero r₂ h
  -- Unfold composeRational (for degreeOfRational_comp's proof).
  have hcomposeNum_eq2 : r₁.composeNum r₂ = num_comp := by
    rw [hnum_comp_def, RationalData.composeNum]
  have hcomposeDen_eq2 : r₁.composeDen r₂ = den_comp := by
    rw [hden_comp_def, RationalData.composeDen]
  have hcomp_unfold :
      r₁.composeRational r₂ = ⟨num_comp, den_comp, hden_comp_ne_zero⟩ := by
    unfold RationalData.composeRational
    rw [hcomposeDen_eq2]
    rw [dif_pos hden_comp_ne_zero]
    congr 1
  rw [hcomp_unfold]
  -- Now the new work: compute the degree of ⟨num_comp, den_comp, _⟩.
  -- Step A: gcd(num_comp, den_comp).natDegree = 0
  -- We use that ℂ is algebraically closed: a polynomial of positive natDegree
  -- has a root, which would have to be a common root of num_comp and den_comp,
  -- contradicting either IsCoprime N₁ D₁ or the maximality of n.
  set g := gcd num_comp den_comp with hg_def
  have hg_ne_zero : g ≠ 0 := gcd_ne_zero_of_right hden_comp_ne_zero
  have hg_natDeg_zero : g.natDegree = 0 := by
    by_contra hpos
    have hpos' : 0 < g.natDegree := Nat.pos_of_ne_zero hpos
    have hdeg_pos : 0 < g.degree := by
      rw [Polynomial.degree_eq_natDegree hg_ne_zero]
      exact_mod_cast hpos'
    have hdeg_ne_zero : g.degree ≠ 0 := ne_of_gt hdeg_pos
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root g hdeg_ne_zero
    -- α is a common root of num_comp and den_comp
    have hg_dvd_num : g ∣ num_comp := gcd_dvd_left _ _
    have hg_dvd_den : g ∣ den_comp := gcd_dvd_right _ _
    have hα_num : num_comp.eval α = 0 := by
      obtain ⟨k, hk⟩ := hg_dvd_num
      rw [hk, Polynomial.eval_mul, hα, zero_mul]
    have hα_den : den_comp.eval α = 0 := by
      obtain ⟨k, hk⟩ := hg_dvd_den
      rw [hk, Polynomial.eval_mul, hα, zero_mul]
    -- Case-split on D₂(α) = 0 or not.
    by_cases hD₂α : D₂.eval α = 0
    · -- D₂(α) = 0. Then N₂(α) ≠ 0 (coprime). num_comp(α) = N₁.coeff n · N₂(α) ^ n etc.
      have hN₂α_ne : N₂.eval α ≠ 0 := by
        intro hN₂α
        obtain ⟨a, b, hab⟩ := hcop_g
        have := congrArg (Polynomial.eval α) hab
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] at this
        rw [hD₂α, hN₂α, mul_zero, mul_zero, add_zero] at this
        exact zero_ne_one this
      -- num_comp(α) at α with D₂(α) = 0: only i = n term survives.
      have hnum_at_α : num_comp.eval α = N₁.coeff n * N₂.eval α ^ n := by
        rw [hnum_comp_def]
        simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
                   Polynomial.eval_pow]
        rw [Finset.sum_eq_single n]
        · rw [hD₂α, Nat.sub_self, pow_zero, mul_one]
        · intro i hi hi_ne
          rw [Finset.mem_range] at hi
          have hki : 1 ≤ n - i := by omega
          rw [hD₂α, zero_pow (by omega : n - i ≠ 0), mul_zero]
        · intro hn_ni
          exfalso; apply hn_ni; rw [Finset.mem_range]; omega
      have hden_at_α : den_comp.eval α = D₁.coeff n * N₂.eval α ^ n := by
        rw [hden_comp_def]
        simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
                   Polynomial.eval_pow]
        rw [Finset.sum_eq_single n]
        · rw [hD₂α, Nat.sub_self, pow_zero, mul_one]
        · intro i hi hi_ne
          rw [Finset.mem_range] at hi
          rw [hD₂α, zero_pow (by omega : n - i ≠ 0), mul_zero]
        · intro hn_ni
          exfalso; apply hn_ni; rw [Finset.mem_range]; omega
      -- Both = 0 ⟹ N₁.coeff n = 0 AND D₁.coeff n = 0
      have hN₂α_pow_ne : N₂.eval α ^ n ≠ 0 := pow_ne_zero _ hN₂α_ne
      have hN₁coeff_zero : N₁.coeff n = 0 := by
        have := hnum_at_α ▸ hα_num
        exact (mul_eq_zero.mp this).resolve_right hN₂α_pow_ne
      have hD₁coeff_zero : D₁.coeff n = 0 := by
        have := hden_at_α ▸ hα_den
        exact (mul_eq_zero.mp this).resolve_right hN₂α_pow_ne
      -- But n = max(N₁.natDegree, D₁.natDegree); at least one coefficient must be lc.
      have hn_eq_max : n = max N₁.natDegree D₁.natDegree := by
        rw [hn_def, RationalData.degree]
      rcases Nat.lt_or_ge N₁.natDegree D₁.natDegree with hND | hND
      · -- n = D₁.natDegree
        have hn_eq_D₁ : n = D₁.natDegree := by rw [hn_eq_max]; exact max_eq_right hND.le
        rw [hn_eq_D₁] at hD₁coeff_zero
        exact (Polynomial.leadingCoeff_ne_zero.mpr hD₁_ne_zero) hD₁coeff_zero
      · -- n = N₁.natDegree
        have hn_eq_N₁ : n = N₁.natDegree := by
          rw [hn_eq_max]; exact max_eq_left hND
        rw [hn_eq_N₁] at hN₁coeff_zero
        -- N₁ might be zero. If N₁ = 0, derive contradiction from D₁.coeff n = 0 (n = 0).
        by_cases hN₁_ne : N₁ = 0
        · have hn_zero : n = 0 := by rw [hn_eq_N₁, hN₁_ne, Polynomial.natDegree_zero]
          rw [hn_zero] at hD₁coeff_zero
          have : D₁.coeff 0 = D₁.leadingCoeff := by
            rw [Polynomial.leadingCoeff]
            have hD₁_natDeg_zero : D₁.natDegree = 0 := by
              have := hD₁_natDeg_le_n; rw [hn_zero] at this; omega
            rw [hD₁_natDeg_zero]
          rw [this] at hD₁coeff_zero
          exact (Polynomial.leadingCoeff_ne_zero.mpr hD₁_ne_zero) hD₁coeff_zero
        · exact (Polynomial.leadingCoeff_ne_zero.mpr hN₁_ne) hN₁coeff_zero
    · -- D₂(α) ≠ 0. Then num_comp(α) = D₂(α) ^ n · N₁(N₂(α)/D₂(α)), similarly den_comp.
      have hnum_at_α : num_comp.eval α = D₂.eval α ^ n * N₁.eval (N₂.eval α / D₂.eval α) :=
        hnum_comp_eval α hD₂α
      have hden_at_α : den_comp.eval α = D₂.eval α ^ n * D₁.eval (N₂.eval α / D₂.eval α) :=
        hden_comp_eval α hD₂α
      have hD₂α_pow_ne : D₂.eval α ^ n ≠ 0 := pow_ne_zero _ hD₂α
      have hN₁_at : N₁.eval (N₂.eval α / D₂.eval α) = 0 := by
        have := hnum_at_α ▸ hα_num
        exact (mul_eq_zero.mp this).resolve_left hD₂α_pow_ne
      have hD₁_at : D₁.eval (N₂.eval α / D₂.eval α) = 0 := by
        have := hden_at_α ▸ hα_den
        exact (mul_eq_zero.mp this).resolve_left hD₂α_pow_ne
      -- N₂(α)/D₂(α) is common root of N₁, D₁, contradicting hcop_f.
      obtain ⟨a, b, hab⟩ := hcop_f
      have := congrArg (Polynomial.eval (N₂.eval α / D₂.eval α)) hab
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] at this
      rw [hN₁_at, hD₁_at, mul_zero, mul_zero, add_zero] at this
      exact zero_ne_one this
  -- Step B: max(num_comp.natDegree, den_comp.natDegree) ≤ n * m
  -- Each summand has natDegree ≤ i * m + (n - i) * m ≤ n * m.
  have hnum_natDeg_le : num_comp.natDegree ≤ n * m := by
    rw [hnum_comp_def]; exact r₂.homogenize_natDegree_le N₁ n
  have hden_natDeg_le : den_comp.natDegree ≤ n * m := by
    rw [hden_comp_def]; exact r₂.homogenize_natDegree_le D₁ n
  -- Step C: max(num_comp.natDegree, den_comp.natDegree) ≥ n * m
  -- via the extracted helper `mul_degree_le_max_natDegree_composeNum_composeDen`.
  have hlb := RationalData.mul_degree_le_max_natDegree_composeNum_composeDen r₁ r₂ h
  -- Bridge: composeNum/composeDen unfold to num_comp/den_comp.
  have hcomposeNum_eq : r₁.composeNum r₂ = num_comp := by
    rw [hnum_comp_def, RationalData.composeNum]
  have hcomposeDen_eq : r₁.composeDen r₂ = den_comp := by
    rw [hden_comp_def, RationalData.composeDen]
  rw [hcomposeNum_eq, hcomposeDen_eq] at hlb
  -- We have: max ≤ n * m (from Step B) and max ≥ n * m (from helper).
  have hmax_eq : max num_comp.natDegree den_comp.natDegree = n * m :=
    le_antisymm (max_le hnum_natDeg_le hden_natDeg_le) hlb
  -- Now conclude r_comp.degree = max numReduced.natDeg denReduced.natDeg = n * m
  -- using gcd.natDeg = 0 and num_comp / gcd preserves natDeg.
  have hgcd_dvd_num : g ∣ num_comp := gcd_dvd_left _ _
  have hgcd_dvd_den : g ∣ den_comp := gcd_dvd_right _ _
  have hnum_factor : num_comp = g * (num_comp / g) :=
    (EuclideanDomain.mul_div_cancel' hg_ne_zero hgcd_dvd_num).symm
  have hden_factor : den_comp = g * (den_comp / g) :=
    (EuclideanDomain.mul_div_cancel' hg_ne_zero hgcd_dvd_den).symm
  have hnum_red : (⟨num_comp, den_comp, hden_comp_ne_zero⟩ : RationalData).numReduced =
      num_comp / g := rfl
  have hden_red : (⟨num_comp, den_comp, hden_comp_ne_zero⟩ : RationalData).denReduced =
      den_comp / g := rfl
  have hden_div_ne : den_comp / g ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hden_factor
    exact hden_comp_ne_zero hden_factor
  have hden_div_natDeg : (den_comp / g).natDegree = den_comp.natDegree := by
    have := congrArg Polynomial.natDegree hden_factor
    rw [Polynomial.natDegree_mul hg_ne_zero hden_div_ne] at this
    omega
  -- For num_comp, we case-split on whether num_comp = 0.
  by_cases hnum_zero : num_comp = 0
  · -- num_comp = 0 case: numReduced = 0/g = 0. Then max = den.natDeg = n * m.
    have hnumDiv_zero : num_comp / g = 0 := by
      rw [hnum_zero]; exact EuclideanDomain.zero_div
    change (⟨num_comp, den_comp, hden_comp_ne_zero⟩ : RationalData).degree = n * m
    unfold RationalData.degree
    rw [hnum_red, hden_red, hnumDiv_zero, Polynomial.natDegree_zero, hden_div_natDeg]
    have : max num_comp.natDegree den_comp.natDegree = den_comp.natDegree := by
      rw [hnum_zero, Polynomial.natDegree_zero, Nat.zero_max]
    rw [this] at hmax_eq
    rw [hmax_eq, Nat.zero_max]
  · have hnum_div_ne : num_comp / g ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hnum_factor
      exact hnum_zero hnum_factor
    have hnum_div_natDeg : (num_comp / g).natDegree = num_comp.natDegree := by
      have := congrArg Polynomial.natDegree hnum_factor
      rw [Polynomial.natDegree_mul hg_ne_zero hnum_div_ne] at this
      omega
    change (⟨num_comp, den_comp, hden_comp_ne_zero⟩ : RationalData).degree = n * m
    unfold RationalData.degree
    rw [hnum_red, hden_red, hnum_div_natDeg, hden_div_natDeg]
    exact hmax_eq

/-- The composition of two rational maps is rational, provided the inner map
is nonconstant. The nonconstancy of `g` (degree at least one) ensures that the
image of `g` is not contained in the finite pole set of `f`, so the composition
is not the (non-representable) constant `∞` map. -/
theorem isRational_comp {f g : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hg : IsRational g)
    (hgd : 1 ≤ degreeOfRational g) :
    IsRational (f ∘ g) := by
  obtain ⟨r_f, hf_eq⟩ := hf
  obtain ⟨r_g, hg_eq⟩ := hg
  have hg_deg : 1 ≤ r_g.degree := by
    rw [← degreeOfRational_eq_of_witness g r_g hg_eq]; exact hgd
  refine ⟨r_f.composeRational r_g, ?_⟩
  rw [hf_eq, hg_eq]
  exact (RationalData.composeRational_toSphereMap_eq r_f r_g hg_deg).symm

/-- Degree multiplicativity under composition for nonconstant rational maps. -/
theorem degreeOfRational_comp {f g : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hg : IsRational g)
    (_hfd : 1 ≤ degreeOfRational f) (hgd : 1 ≤ degreeOfRational g) :
    degreeOfRational (f ∘ g) = degreeOfRational f * degreeOfRational g := by
  obtain ⟨r_f, hf_eq⟩ := hf
  obtain ⟨r_g, hg_eq⟩ := hg
  have hg_deg : 1 ≤ r_g.degree := by
    rw [← degreeOfRational_eq_of_witness g r_g hg_eq]; exact hgd
  have hfg_eq : f ∘ g = (r_f.composeRational r_g).toSphereMap := by
    rw [hf_eq, hg_eq]
    exact (RationalData.composeRational_toSphereMap_eq r_f r_g hg_deg).symm
  rw [degreeOfRational_eq_of_witness (f ∘ g) (r_f.composeRational r_g) hfg_eq]
  rw [RationalData.composeRational_degree_eq r_f r_g hg_deg]
  rw [degreeOfRational_eq_of_witness f r_f hf_eq,
      degreeOfRational_eq_of_witness g r_g hg_eq]

end NoWanderingDomains
