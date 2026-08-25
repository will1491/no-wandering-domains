/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.JuliaFatou.Basic
import NoWanderingDomains.Dynamics.JuliaFatou.Invariance
import NoWanderingDomains.Sphere.LocallyConnected

/-!
# Fatou components

A *Fatou component* of `f : ℂ̂ → ℂ̂` is a connected component of the Fatou
set: a set of the form `connectedComponentIn (FatouSet f) z` for some Fatou
point `z`. Because the sphere is locally connected
(`Sphere/LocallyConnected.lean`) and the Fatou set is open, every Fatou
component is an open, connected domain.

For a rational map `f` of degree `≥ 1` the Fatou set is completely invariant
(`Dynamics/JuliaFatou/Invariance.lean`), so `f` carries each Fatou component
into a single Fatou component. We package the resulting dynamics on
components through

`fcOrbit f U n` — the Fatou component containing the `n`-th image
`f^[n] '' U`.

It is defined basepoint-free as `⋃ z ∈ U, connectedComponentIn (FatouSet f)
(f^[n] z)`; on a genuine component this union collapses to a single
component, the one containing the image. The orbit satisfies `fcOrbit f U 0 =
U` and the semigroup law `fcOrbit f U (m + n) = fcOrbit f (fcOrbit f U m) n`,
and these are the structural facts the wandering / eventually-periodic
dichotomy and Sullivan's deformation argument are built on.
-/

open Function

namespace NoWanderingDomains

variable {f : ℂ̂ → ℂ̂}

/-- A *Fatou component* of `f`: a connected component of the Fatou set. -/
def IsFatouComponent (f : ℂ̂ → ℂ̂) (U : Set ℂ̂) : Prop :=
  ∃ z ∈ FatouSet f, U = connectedComponentIn (FatouSet f) z

/-- The Fatou component containing the `n`-th image of `U`, defined
basepoint-free. On a genuine Fatou component this is the single component
containing `f^[n] '' U`. -/
def fcOrbit (f : ℂ̂ → ℂ̂) (U : Set ℂ̂) (n : ℕ) : Set ℂ̂ :=
  ⋃ z ∈ U, connectedComponentIn (FatouSet f) (f^[n] z)

/-- A Fatou component is contained in the Fatou set. -/
theorem IsFatouComponent.subset_fatouSet {U : Set ℂ̂}
    (h : IsFatouComponent f U) : U ⊆ FatouSet f := by
  obtain ⟨z, hz, rfl⟩ := h
  exact connectedComponentIn_subset _ _

/-- A Fatou component is nonempty. -/
theorem IsFatouComponent.nonempty {U : Set ℂ̂} (h : IsFatouComponent f U) :
    U.Nonempty := by
  obtain ⟨z, hz, rfl⟩ := h
  exact ⟨z, mem_connectedComponentIn hz⟩

/-- A Fatou component is connected. -/
theorem IsFatouComponent.isConnected {U : Set ℂ̂} (h : IsFatouComponent f U) :
    IsConnected U := by
  obtain ⟨z, hz, rfl⟩ := h
  exact isConnected_connectedComponentIn_iff.mpr hz

/-- A Fatou component is open (local connectedness of the sphere + openness
of the Fatou set). -/
theorem IsFatouComponent.isOpen {U : Set ℂ̂} (h : IsFatouComponent f U) :
    IsOpen U := by
  obtain ⟨z, hz, rfl⟩ := h
  exact (isOpen_fatouSet f).connectedComponentIn

/-- The connected component of the Fatou set through a Fatou point is a Fatou
component. -/
theorem isFatouComponent_connectedComponentIn {z : ℂ̂} (hz : z ∈ FatouSet f) :
    IsFatouComponent f (connectedComponentIn (FatouSet f) z) :=
  ⟨z, hz, rfl⟩

/-- Two Fatou components are equal or disjoint. -/
theorem IsFatouComponent.eq_or_disjoint {U V : Set ℂ̂}
    (hU : IsFatouComponent f U) (hV : IsFatouComponent f V) :
    U = V ∨ Disjoint U V := by
  obtain ⟨z, hz, rfl⟩ := hU
  obtain ⟨w, hw, rfl⟩ := hV
  by_cases hd : Disjoint (connectedComponentIn (FatouSet f) z)
      (connectedComponentIn (FatouSet f) w)
  · right; exact hd
  · left
    obtain ⟨x, hxz, hxw⟩ := Set.not_disjoint_iff.mp hd
    rw [connectedComponentIn_eq hxz, connectedComponentIn_eq hxw]

/-- A Fatou component that meets another equals it. -/
theorem IsFatouComponent.eq_of_mem {U V : Set ℂ̂} {z : ℂ̂}
    (hU : IsFatouComponent f U) (hV : IsFatouComponent f V)
    (hzU : z ∈ U) (hzV : z ∈ V) : U = V := by
  rcases hU.eq_or_disjoint hV with heq | hdisj
  · exact heq
  · exact absurd hzV (Set.disjoint_left.mp hdisj hzU)

/-- The zeroth orbit component of a Fatou component is the component itself. -/
theorem fcOrbit_zero {U : Set ℂ̂} (h : IsFatouComponent f U) :
    fcOrbit f U 0 = U := by
  obtain ⟨w₀, hw₀, rfl⟩ := h
  set F := FatouSet f with hF
  set U := connectedComponentIn F w₀ with hU
  ext x
  simp only [fcOrbit, Function.iterate_zero, id_eq, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨z, hzU, hx⟩
    rwa [(connectedComponentIn_eq hzU).symm] at hx
  · intro hxU
    refine ⟨x, hxU, ?_⟩
    exact mem_connectedComponentIn (connectedComponentIn_subset F w₀ hxU)

/-- On a Fatou component of a nonconstant rational map the orbit set collapses to the
connected component of the Fatou set through the image of any representative point — so
`fcOrbit f U n` really is a single Fatou component, not a union of several. Rationality is
needed, not incidental: the proof runs on `f` being an open map, which is what carries the
connected set `f^[n] '' U` into one component and keeps it inside the Fatou set. For a
general continuous `f` the union need not collapse. -/
theorem fcOrbit_eq_connectedComponentIn {U : Set ℂ̂} {z : ℂ̂} (n : ℕ)
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    (h : IsFatouComponent f U) (hz : z ∈ U) :
    fcOrbit f U n = connectedComponentIn (FatouSet f) (f^[n] z) := by
  have hfo : IsOpenMap f := hf.isOpenMap (hf.ne_const hd)
  have hcont : Continuous (f^[n]) := hf.continuous.iterate n
  have hfwd : ∀ k w, w ∈ FatouSet f → f^[k] w ∈ FatouSet f := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
        intro w hw
        rw [Function.iterate_succ_apply']
        exact apply_mem_fatouSet hfo (ih w hw)
  have hUsub := h.subset_fatouSet
  have hUconn := h.isConnected
  have himg : IsConnected (f^[n] '' U) := hUconn.image _ hcont.continuousOn
  have hsubF : f^[n] '' U ⊆ FatouSet f := by
    rintro _ ⟨w, hwU, rfl⟩; exact hfwd n w (hUsub hwU)
  have hmem : f^[n] z ∈ f^[n] '' U := ⟨z, hz, rfl⟩
  have hcc : f^[n] '' U ⊆ connectedComponentIn (FatouSet f) (f^[n] z) :=
    himg.isPreconnected.subset_connectedComponentIn hmem hsubF
  ext x
  simp only [fcOrbit, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨w, hwU, hx⟩
    have hwmem : f^[n] w ∈ connectedComponentIn (FatouSet f) (f^[n] z) :=
      hcc ⟨w, hwU, rfl⟩
    rwa [connectedComponentIn_eq hwmem]
  · intro hx
    exact ⟨z, hz, hx⟩

/-- Each orbit component of a Fatou component is again a Fatou component. -/
theorem isFatouComponent_fcOrbit {U : Set ℂ̂} (n : ℕ)
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    (h : IsFatouComponent f U) : IsFatouComponent f (fcOrbit f U n) := by
  obtain ⟨z, hzU⟩ := h.nonempty
  have hzU' : z ∈ U := hzU
  rw [fcOrbit_eq_connectedComponentIn n hf hd h hzU']
  have hfo : IsOpenMap f := hf.isOpenMap (hf.ne_const hd)
  have hfwd : ∀ k w, w ∈ FatouSet f → f^[k] w ∈ FatouSet f := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
        intro w hw
        rw [Function.iterate_succ_apply']
        exact apply_mem_fatouSet hfo (ih w hw)
  exact isFatouComponent_connectedComponentIn (hfwd n z (h.subset_fatouSet hzU'))

/-- The semigroup law for the dynamics on components:
`fcOrbit f U (m + n) = fcOrbit f (fcOrbit f U m) n`. -/
theorem fcOrbit_add {U : Set ℂ̂} (m n : ℕ)
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    (h : IsFatouComponent f U) :
    fcOrbit f U (m + n) = fcOrbit f (fcOrbit f U m) n := by
  obtain ⟨z, hzU⟩ := h.nonempty
  set F := FatouSet f with hF
  have hzF : z ∈ F := h.subset_fatouSet hzU
  have hfo : IsOpenMap f := hf.isOpenMap (hf.ne_const hd)
  have hfwd : ∀ k w, w ∈ F → f^[k] w ∈ F := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
        intro w hw
        rw [Function.iterate_succ_apply']
        exact apply_mem_fatouSet hfo (ih w hw)
  have hL : fcOrbit f U (m + n) = connectedComponentIn F (f^[m + n] z) :=
    fcOrbit_eq_connectedComponentIn (m + n) hf hd h hzU
  have hVfc : IsFatouComponent f (fcOrbit f U m) := isFatouComponent_fcOrbit m hf hd h
  have hVeq : fcOrbit f U m = connectedComponentIn F (f^[m] z) :=
    fcOrbit_eq_connectedComponentIn m hf hd h hzU
  have hwV : f^[m] z ∈ fcOrbit f U m := by
    rw [hVeq]; exact mem_connectedComponentIn (hfwd m z hzF)
  have hR : fcOrbit f (fcOrbit f U m) n =
      connectedComponentIn F (f^[n] (f^[m] z)) :=
    fcOrbit_eq_connectedComponentIn n hf hd hVfc hwV
  rw [hL, hR]
  congr 1
  rw [← Function.iterate_add_apply f n m z, Nat.add_comm n m]

end NoWanderingDomains
