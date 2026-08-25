/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.FatouComponents.Def
import NoWanderingDomains.Sphere.Iterate

/-!
# The grand orbit of a Fatou component

Two Fatou components are *grand-orbit equivalent* (`fcEquiv`) when some
forward image component of one coincides with some forward image component
of the other. On Fatou components this is an equivalence relation; the
semigroup law `fcOrbit_add` supplies transitivity.

The *grand orbit* of a component `U` as a subset of the sphere is
`fcGrandOrbit f U = ⋃ z ∈ U, grandOrbit f z`. For a rational map it is a
fully `f`-invariant subset of the Fatou set: closed under `f` and under
`f`-preimages. This is the set over which Sullivan's argument spreads an
`f`-invariant Beltrami coefficient (taking it to be zero on the Julia set).
-/

open Function

namespace NoWanderingDomains

variable {f : ℂ̂ → ℂ̂}

/-- The *grand-orbit equivalence* on Fatou components: some forward image
component of `U` equals some forward image component of `V`. -/
def fcEquiv (f : ℂ̂ → ℂ̂) (U V : Set ℂ̂) : Prop :=
  ∃ m n : ℕ, fcOrbit f U m = fcOrbit f V n

/-- The grand orbit of a component, as a subset of the sphere. -/
def fcGrandOrbit (f : ℂ̂ → ℂ̂) (U : Set ℂ̂) : Set ℂ̂ :=
  ⋃ z ∈ U, grandOrbit f z

/-- `fcEquiv` is reflexive. -/
theorem fcEquiv_refl (U : Set ℂ̂) : fcEquiv f U U :=
  ⟨0, 0, rfl⟩

/-- `fcEquiv` is symmetric. -/
theorem fcEquiv.symm {U V : Set ℂ̂} (h : fcEquiv f U V) : fcEquiv f V U := by
  obtain ⟨m, n, heq⟩ := h
  exact ⟨n, m, heq.symm⟩

/-- `fcEquiv` is transitive on Fatou components. -/
theorem fcEquiv.trans {U V W : Set ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    (hU : IsFatouComponent f U) (hV : IsFatouComponent f V)
    (hW : IsFatouComponent f W)
    (h₁ : fcEquiv f U V) (h₂ : fcEquiv f V W) : fcEquiv f U W := by
  obtain ⟨a, b, hab⟩ := h₁
  obtain ⟨c, d, hcd⟩ := h₂
  have e1 : fcOrbit f U (a + c) = fcOrbit f V (b + c) := by
    rw [fcOrbit_add a c hf hd hU, hab, ← fcOrbit_add b c hf hd hV]
  have e2 : fcOrbit f W (d + b) = fcOrbit f V (c + b) := by
    rw [fcOrbit_add d b hf hd hW, ← hcd, ← fcOrbit_add c b hf hd hV]
  refine ⟨a + c, d + b, ?_⟩
  rw [e1, e2, Nat.add_comm b c]

/-- The grand orbit of a Fatou component lies in the Fatou set. -/
theorem fcGrandOrbit_subset_fatouSet {U : Set ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    (h : IsFatouComponent f U) : fcGrandOrbit f U ⊆ FatouSet f := by
  have hfo : IsOpenMap f := hf.isOpenMap (hf.ne_const hd)
  have hfwd : ∀ k w, w ∈ FatouSet f → f^[k] w ∈ FatouSet f := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
        intro w hw
        rw [Function.iterate_succ_apply']
        exact apply_mem_fatouSet hfo (ih w hw)
  have hbwd : ∀ k w, f^[k] w ∈ FatouSet f → w ∈ FatouSet f := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
        intro w hw
        rw [Function.iterate_succ_apply] at hw
        exact mem_fatouSet_of_apply_mem hf.continuous (ih (f w) hw)
  rintro w hw
  simp only [fcGrandOrbit, Set.mem_iUnion, exists_prop] at hw
  obtain ⟨z, hzU, hwGO⟩ := hw
  obtain ⟨m, n, heq⟩ := hwGO
  have hzF : z ∈ FatouSet f := h.subset_fatouSet hzU
  have hnw : f^[n] w ∈ FatouSet f := heq ▸ hfwd m z hzF
  exact hbwd n w hnw

/-- The grand orbit of a component is closed under `f`. -/
theorem forward_invariant_fcGrandOrbit {U : Set ℂ̂} :
    ∀ w ∈ fcGrandOrbit f U, f w ∈ fcGrandOrbit f U := by
  rintro w hw
  simp only [fcGrandOrbit, Set.mem_iUnion, exists_prop] at hw ⊢
  obtain ⟨z, hzU, hwGO⟩ := hw
  exact ⟨z, hzU, forward_invariant_grandOrbit f z w hwGO⟩

/-- The grand orbit of a component is closed under `f`-preimages. -/
theorem backward_invariant_fcGrandOrbit {U : Set ℂ̂} :
    ∀ w ∈ fcGrandOrbit f U, ∀ v, f v = w → v ∈ fcGrandOrbit f U := by
  rintro w hw v hv
  simp only [fcGrandOrbit, Set.mem_iUnion, exists_prop] at hw ⊢
  obtain ⟨z, hzU, hwGO⟩ := hw
  exact ⟨z, hzU, backward_invariant_grandOrbit f z w hwGO v hv⟩

end NoWanderingDomains
