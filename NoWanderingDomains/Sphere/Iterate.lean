/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Function.Iterate
import NoWanderingDomains.Sphere.RationalMap

/-!
# Iteration of rational maps and orbit structures

For a rational self-map `f : ℂ̂ → ℂ̂` we record three dynamical orbit structures.
We use Mathlib's `f^[n]` (= `Nat.iterate f n`) for iteration.

## Main definitions

* `forwardOrbit f z = {f^[n] z | n : ℕ}` — the forward trajectory.
* `backwardOrbit f z = {w : ℂ̂ | ∃ n, f^[n] w = z}` — the preimages under
  iteration.
* `grandOrbit f z = {w : ℂ̂ | ∃ m n, f^[m] z = f^[n] w}` — the smallest fully
  `f`-stable set containing `z`; the equivalence relation Sullivan's deformation
  argument quotients over.
* `grandOrbitSetoid f` — the grand-orbit equivalence relation as a `Setoid`.

## Main results

* `isRational_id`, `degreeOfRational_id` — the identity is rational of degree one.
* `IsRational.iterate`, `degreeOfRational_iterate` — iterates of a nonconstant
  rational map are rational, with degree the corresponding power of the degree.
* `forwardOrbit_finite_of_iterate_fixed` — the forward orbit of a periodic point
  is finite.
-/

open OnePoint Function Polynomial

namespace NoWanderingDomains

variable (f : ℂ̂ → ℂ̂) (z : ℂ̂)

/-- The forward orbit of `z` under `f`: the set of all forward iterates. -/
def forwardOrbit : Set ℂ̂ := {w | ∃ n : ℕ, f^[n] z = w}

/-- The backward orbit of `z` under `f`: the set of all preimages under
iteration. -/
def backwardOrbit : Set ℂ̂ := {w | ∃ n : ℕ, f^[n] w = z}

/-- The grand orbit of `z` under `f`: two points share a grand orbit iff some
forward iterate of one equals some forward iterate of the other. -/
def grandOrbit : Set ℂ̂ := {w | ∃ m n : ℕ, f^[m] z = f^[n] w}

/-- The grand-orbit equivalence relation on `ℂ̂`. -/
def grandOrbitSetoid : Setoid ℂ̂ where
  r z w := ∃ m n : ℕ, f^[m] z = f^[n] w
  iseqv := {
    refl := fun z => ⟨0, 0, rfl⟩
    symm := fun ⟨m, n, h⟩ => ⟨n, m, h.symm⟩
    trans := by
      rintro x y w ⟨m₁, n₁, h₁⟩ ⟨m₂, n₂, h₂⟩
      refine ⟨m₂ + m₁, n₁ + n₂, ?_⟩
      calc f^[m₂ + m₁] x
          = f^[m₂] (f^[m₁] x) := by rw [Function.iterate_add_apply]
        _ = f^[m₂] (f^[n₁] y) := by rw [h₁]
        _ = f^[n₁] (f^[m₂] y) := by rw [← Function.Commute.iterate_iterate_self]
        _ = f^[n₁] (f^[n₂] w) := by rw [h₂]
        _ = f^[n₁ + n₂] w := by rw [← Function.iterate_add_apply]
  }

/-! ## Basic invariance lemmas (signatures) -/

/-- The forward orbit contains the basepoint `z`. -/
theorem mem_forwardOrbit_self : z ∈ forwardOrbit f z := ⟨0, rfl⟩

/-- The forward orbit is closed under `f`. -/
theorem forward_invariant_forwardOrbit :
    ∀ w ∈ forwardOrbit f z, f w ∈ forwardOrbit f z := by
  rintro w ⟨n, rfl⟩
  exact ⟨n + 1, by rw [Function.iterate_succ_apply']⟩

/-- The backward orbit contains the basepoint `z`. -/
theorem mem_backwardOrbit_self : z ∈ backwardOrbit f z := ⟨0, rfl⟩

/-- The backward orbit is `f`-invariant in the sense that preimages stay
inside it. -/
theorem backward_invariant_backwardOrbit
    {w : ℂ̂} (hw : w ∈ backwardOrbit f z) :
    ∀ v, f v = w → v ∈ backwardOrbit f z := by
  obtain ⟨n, hn⟩ := hw
  intro v hv
  exact ⟨n + 1, by rw [Function.iterate_succ_apply, hv]; exact hn⟩

/-- The grand orbit contains the basepoint `z`. -/
theorem mem_grandOrbit_self : z ∈ grandOrbit f z := ⟨0, 0, rfl⟩

/-- The grand orbit is `f`-invariant (closed under `f`). -/
theorem forward_invariant_grandOrbit :
    ∀ w ∈ grandOrbit f z, f w ∈ grandOrbit f z := by
  rintro w ⟨m, n, h⟩
  refine ⟨m + 1, n, ?_⟩
  calc f^[m + 1] z
      = f (f^[m] z) := Function.iterate_succ_apply' f m z
    _ = f (f^[n] w) := by rw [h]
    _ = f^[n + 1] w := (Function.iterate_succ_apply' f n w).symm
    _ = f^[n] (f w) := Function.iterate_succ_apply f n w

/-- The grand orbit is closed under `f`-preimages. -/
theorem backward_invariant_grandOrbit :
    ∀ w ∈ grandOrbit f z, ∀ v, f v = w → v ∈ grandOrbit f z := by
  rintro w ⟨m, n, h⟩ v hv
  refine ⟨m, n + 1, ?_⟩
  calc f^[m] z
      = f^[n] w := h
    _ = f^[n] (f v) := by rw [hv]
    _ = f^[n + 1] v := (Function.iterate_succ_apply f n v).symm

/-- The grand orbit is the union of the forward and backward orbits over the
forward iterates of `z`. -/
theorem grandOrbit_eq_union_iterate :
    grandOrbit f z = ⋃ m : ℕ, backwardOrbit f (f^[m] z) := by
  ext w
  simp only [grandOrbit, backwardOrbit, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, h.symm⟩
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, h.symm⟩

/-! ## Rationality and degree of iterates -/

/-- The identity is a rational map (numerator `X`, denominator `1`). -/
theorem isRational_id : IsRational (id : ℂ̂ → ℂ̂) := by
  refine ⟨⟨Polynomial.X, 1, one_ne_zero⟩, ?_⟩
  have hu : IsUnit (gcd (Polynomial.X : ℂ[X]) 1) := isUnit_of_dvd_one (gcd_dvd_right _ _)
  obtain ⟨c, hc_unit, hc⟩ := Polynomial.isUnit_iff.mp hu
  have hc_ne : c ≠ 0 := hc_unit.ne_zero
  have hC_ne : (Polynomial.C c : ℂ[X]) ≠ 0 := Polynomial.C_ne_zero.mpr hc_ne
  have hXdiv : Polynomial.C c * ((Polynomial.X : ℂ[X]) / Polynomial.C c) = Polynomial.X :=
    EuclideanDomain.mul_div_cancel' hC_ne (Polynomial.isUnit_C.mpr hc_unit).dvd
  have h1div : Polynomial.C c * ((1 : ℂ[X]) / Polynomial.C c) = 1 :=
    EuclideanDomain.mul_div_cancel' hC_ne (Polynomial.isUnit_C.mpr hc_unit).dvd
  have hnumR : (⟨Polynomial.X, 1, one_ne_zero⟩ : RationalData).numReduced
      = Polynomial.X / Polynomial.C c := by
    change Polynomial.X / gcd Polynomial.X 1 = Polynomial.X / Polynomial.C c
    rw [hc]
  have hdenR : (⟨Polynomial.X, 1, one_ne_zero⟩ : RationalData).denReduced
      = 1 / Polynomial.C c := by
    change 1 / gcd Polynomial.X 1 = 1 / Polynomial.C c
    rw [hc]
  funext z
  match z with
  | OnePoint.some w =>
      have hn : c * ((Polynomial.X : ℂ[X]) / Polynomial.C c).eval w = w := by
        have h := congrArg (Polynomial.eval w) hXdiv
        rwa [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at h
      have hd1 : c * ((1 : ℂ[X]) / Polynomial.C c).eval w = 1 := by
        have h := congrArg (Polynomial.eval w) h1div
        rwa [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one] at h
      have hnum_val : ((Polynomial.X : ℂ[X]) / Polynomial.C c).eval w = w / c :=
        (eq_div_iff hc_ne).mpr (by rw [mul_comm]; exact hn)
      have hden_val : ((1 : ℂ[X]) / Polynomial.C c).eval w = 1 / c :=
        (eq_div_iff hc_ne).mpr (by rw [mul_comm]; exact hd1)
      have hden_ne : ((1 : ℂ[X]) / Polynomial.C c).eval w ≠ 0 := by
        rw [hden_val]
        exact one_div_ne_zero hc_ne
      have hval : ((Polynomial.X : ℂ[X]) / Polynomial.C c).eval w
          / ((1 : ℂ[X]) / Polynomial.C c).eval w = w := by
        rw [hnum_val, hden_val, div_div, mul_one_div, div_self hc_ne, div_one]
      simp only [id_eq, RationalData.toSphereMap, hnumR, hdenR]
      rw [if_neg hden_ne, hval]
  | ∞ =>
      have hndeg : ((Polynomial.X : ℂ[X]) / Polynomial.C c).natDegree = 1 := by
        have h := congrArg Polynomial.natDegree hXdiv
        rwa [Polynomial.natDegree_C_mul hc_ne, Polynomial.natDegree_X] at h
      have hddeg : ((1 : ℂ[X]) / Polynomial.C c).natDegree = 0 := by
        have h := congrArg Polynomial.natDegree h1div
        rwa [Polynomial.natDegree_C_mul hc_ne, Polynomial.natDegree_one] at h
      simp only [id_eq, RationalData.toSphereMap, hnumR, hdenR, hndeg, hddeg]
      norm_num

/-- The identity has degree one. -/
theorem degreeOfRational_id : degreeOfRational (id : ℂ̂ → ℂ̂) = 1 := by
  have hu : IsUnit (gcd (Polynomial.X : ℂ[X]) 1) := isUnit_of_dvd_one (gcd_dvd_right _ _)
  obtain ⟨c, hc_unit, hc⟩ := Polynomial.isUnit_iff.mp hu
  have hc_ne : c ≠ 0 := hc_unit.ne_zero
  have hC_ne : (Polynomial.C c : ℂ[X]) ≠ 0 := Polynomial.C_ne_zero.mpr hc_ne
  have hXdiv : Polynomial.C c * ((Polynomial.X : ℂ[X]) / Polynomial.C c) = Polynomial.X :=
    EuclideanDomain.mul_div_cancel' hC_ne (Polynomial.isUnit_C.mpr hc_unit).dvd
  have h1div : Polynomial.C c * ((1 : ℂ[X]) / Polynomial.C c) = 1 :=
    EuclideanDomain.mul_div_cancel' hC_ne (Polynomial.isUnit_C.mpr hc_unit).dvd
  have hnumR : (⟨Polynomial.X, 1, one_ne_zero⟩ : RationalData).numReduced
      = Polynomial.X / Polynomial.C c := by
    change Polynomial.X / gcd Polynomial.X 1 = Polynomial.X / Polynomial.C c
    rw [hc]
  have hdenR : (⟨Polynomial.X, 1, one_ne_zero⟩ : RationalData).denReduced
      = 1 / Polynomial.C c := by
    change 1 / gcd Polynomial.X 1 = 1 / Polynomial.C c
    rw [hc]
  have hndeg : ((Polynomial.X : ℂ[X]) / Polynomial.C c).natDegree = 1 := by
    have h := congrArg Polynomial.natDegree hXdiv
    rwa [Polynomial.natDegree_C_mul hc_ne, Polynomial.natDegree_X] at h
  have hddeg : ((1 : ℂ[X]) / Polynomial.C c).natDegree = 0 := by
    have h := congrArg Polynomial.natDegree h1div
    rwa [Polynomial.natDegree_C_mul hc_ne, Polynomial.natDegree_one] at h
  have hmap : (id : ℂ̂ → ℂ̂)
      = (⟨Polynomial.X, 1, one_ne_zero⟩ : RationalData).toSphereMap := by
    funext z
    match z with
    | OnePoint.some w =>
        have hn : c * ((Polynomial.X : ℂ[X]) / Polynomial.C c).eval w = w := by
          have h := congrArg (Polynomial.eval w) hXdiv
          rwa [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at h
        have hd1 : c * ((1 : ℂ[X]) / Polynomial.C c).eval w = 1 := by
          have h := congrArg (Polynomial.eval w) h1div
          rwa [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one] at h
        have hnum_val : ((Polynomial.X : ℂ[X]) / Polynomial.C c).eval w = w / c :=
          (eq_div_iff hc_ne).mpr (by rw [mul_comm]; exact hn)
        have hden_val : ((1 : ℂ[X]) / Polynomial.C c).eval w = 1 / c :=
          (eq_div_iff hc_ne).mpr (by rw [mul_comm]; exact hd1)
        have hden_ne : ((1 : ℂ[X]) / Polynomial.C c).eval w ≠ 0 := by
          rw [hden_val]
          exact one_div_ne_zero hc_ne
        have hval : ((Polynomial.X : ℂ[X]) / Polynomial.C c).eval w
            / ((1 : ℂ[X]) / Polynomial.C c).eval w = w := by
          rw [hnum_val, hden_val, div_div, mul_one_div, div_self hc_ne, div_one]
        simp only [id_eq, RationalData.toSphereMap, hnumR, hdenR]
        rw [if_neg hden_ne, hval]
    | ∞ =>
        simp only [id_eq, RationalData.toSphereMap, hnumR, hdenR, hndeg, hddeg]
        norm_num
  rw [degreeOfRational_eq_of_witness _ _ hmap]
  change max ((⟨Polynomial.X, 1, one_ne_zero⟩ : RationalData).numReduced.natDegree)
      ((⟨Polynomial.X, 1, one_ne_zero⟩ : RationalData).denReduced.natDegree) = 1
  rw [hnumR, hdenR, hndeg, hddeg]
  rfl

/-- Iterates of a rational map of degree at least one are rational. -/
theorem IsRational.iterate {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hd : 1 ≤ degreeOfRational f) (n : ℕ) : IsRational (f^[n]) := by
  have key : ∀ m : ℕ,
      IsRational (f^[m]) ∧ degreeOfRational (f^[m]) = degreeOfRational f ^ m := by
    intro m
    induction m with
    | zero =>
        refine ⟨?_, ?_⟩
        · simpa using isRational_id
        · simpa using degreeOfRational_id
    | succ k ih =>
        have h1 : 1 ≤ degreeOfRational (f^[k]) := by
          rw [ih.2]
          exact Nat.one_le_pow _ _ hd
        have hcomp : f^[k + 1] = f ∘ f^[k] := Function.iterate_succ' f k
        refine ⟨?_, ?_⟩
        · rw [hcomp]
          exact isRational_comp hf ih.1 h1
        · rw [hcomp, degreeOfRational_comp hf ih.1 hd h1, ih.2, pow_succ]
          exact mul_comm _ _
  exact (key n).1

/-- The degree of an iterate is the power of the degree. -/
theorem degreeOfRational_iterate {f : ℂ̂ → ℂ̂} (hf : IsRational f)
    (hd : 1 ≤ degreeOfRational f) (n : ℕ) :
    degreeOfRational (f^[n]) = degreeOfRational f ^ n := by
  have key : ∀ m : ℕ,
      IsRational (f^[m]) ∧ degreeOfRational (f^[m]) = degreeOfRational f ^ m := by
    intro m
    induction m with
    | zero =>
        refine ⟨?_, ?_⟩
        · simpa using isRational_id
        · simpa using degreeOfRational_id
    | succ k ih =>
        have h1 : 1 ≤ degreeOfRational (f^[k]) := by
          rw [ih.2]
          exact Nat.one_le_pow _ _ hd
        have hcomp : f^[k + 1] = f ∘ f^[k] := Function.iterate_succ' f k
        refine ⟨?_, ?_⟩
        · rw [hcomp]
          exact isRational_comp hf ih.1 h1
        · rw [hcomp, degreeOfRational_comp hf ih.1 hd h1, ih.2, pow_succ]
          exact mul_comm _ _
  exact (key n).2

/-- The forward orbit of a periodic point is finite: it is covered by the
first `k` iterates. -/
theorem forwardOrbit_finite_of_iterate_fixed {f : ℂ̂ → ℂ̂} {z : ℂ̂} {k : ℕ}
    (hk : 1 ≤ k) (hfix : f^[k] z = z) : (forwardOrbit f z).Finite := by
  have hmod : ∀ n : ℕ, f^[n] z = f^[n % k] z := by
    intro n
    calc f^[n] z = f^[n % k + k * (n / k)] z := by rw [Nat.mod_add_div]
      _ = f^[n % k] (f^[k * (n / k)] z) := Function.iterate_add_apply f _ _ z
      _ = f^[n % k] ((f^[k])^[n / k] z) := by rw [Function.iterate_mul]
      _ = f^[n % k] z := by rw [Function.iterate_fixed hfix (n / k)]
  have hsub : forwardOrbit f z ⊆ (fun i => f^[i] z) '' (Set.Iio k) := by
    rintro w ⟨n, rfl⟩
    exact ⟨n % k, Nat.mod_lt n hk, (hmod n).symm⟩
  exact (((Set.finite_Iio k).image _).subset hsub)

end NoWanderingDomains
