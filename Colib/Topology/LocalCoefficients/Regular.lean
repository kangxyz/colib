/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.LocalCoefficients.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Regular local coefficient systems

The regular system based at `b` has the free integral module on homotopy
classes of paths from `b` to each point as its fiber. Transport is actual
postcomposition of path classes. No choice of paths to other points and no
commutativity hypothesis on the fundamental group are used.

Mathlib multiplies fundamental-group elements in reverse path-concatenation
order. Consequently postcomposition gives left regular monodromy at `b`.
This file proves its faithfulness; it does not assert a covering-space or
homological Whitehead comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]

/-- The free integral system on paths from the specified basepoint.
Its coefficient universe is precisely the universe of the space. -/
def regular (b : X) : System.{u, u} X where
  obj x := ModuleCat.of ℤ ((FundamentalGroupoid.mk b ⟶ x) →₀ ℤ)
  map q := ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ (fun p => p ≫ q))
  map_id x := by
    apply ModuleCat.hom_ext
    ext p : 2
    simp
  map_comp q r := by
    apply ModuleCat.hom_ext
    simpa only [Function.comp_def, Category.assoc, ModuleCat.hom_ofHom,
      ModuleCat.hom_comp] using
      (Finsupp.lmapDomain_comp ℤ ℤ (fun p => p ≫ q) (fun p => p ≫ r))

/-- A basis path class with an arbitrary integral coefficient. -/
def regularSingle (b : X) {x : FundamentalGroupoid X}
    (p : FundamentalGroupoid.mk b ⟶ x) (n : ℤ) : (regular b).obj x :=
  Finsupp.single p n

/-- Each groupoid arrow acts by postcomposition on basis paths. -/
@[simp]
theorem regular_map_single (b : X) {x y : FundamentalGroupoid X}
    (q : x ⟶ y) (p : FundamentalGroupoid.mk b ⟶ x) (n : ℤ) :
    (regular b).map q (regularSingle b p n) = regularSingle b (p ≫ q) n :=
  Finsupp.mapDomain_single

/-- Transport along an actual path retains its homotopy class. -/
@[simp]
theorem regular_transport_single (b : X) {x y : X} (q : Path x y)
    (p : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk x) (n : ℤ) :
    transport (regular b) q (regularSingle b p n) =
      regularSingle b (p ≫ Path.Homotopic.Quotient.mk q) n :=
  regular_map_single b _ p n

/-- The inverse of regular transport is transport along the reversed path. -/
@[simp]
theorem regular_transport_symm_transport (b : X) {x y : X} (q : Path x y)
    (a : fiber (regular b) x) :
    transport (regular b) q.symm (transport (regular b) q a) = a := by
  exact ConcreteCategory.congr_hom (transportIso (regular b) q).hom_inv_id a

/-- Reversed transport is also a right inverse. -/
@[simp]
theorem regular_transport_transport_symm (b : X) {x y : X} (q : Path x y)
    (a : fiber (regular b) y) :
    transport (regular b) q (transport (regular b) q.symm a) = a := by
  exact ConcreteCategory.congr_hom (transportIso (regular b) q).inv_hom_id a

/-- Monodromy as an actual homomorphism into module endomorphisms. -/
def regularMonodromy (b : X) :
    FundamentalGroup X b →* End (fiber (regular b) b) :=
  (regular b).mapEnd (FundamentalGroupoid.mk b)

/-- The group multiplication convention makes this the left regular action. -/
@[simp]
theorem regularMonodromy_single (b : X) (g h : FundamentalGroup X b) (n : ℤ) :
    (regularMonodromy b g).asHom (regularSingle b h.asHom n) = regularSingle b (g * h).asHom n :=
  regular_map_single b g.asHom h.asHom n

/-- The integral regular monodromy distinguishes all fundamental-group elements. -/
theorem regularMonodromy_injective (b : X) : Function.Injective (regularMonodromy b) := by
  intro g h e
  have e' := ConcreteCategory.congr_hom (congrArg End.asHom e)
    (regularSingle b (1 : FundamentalGroup X b).asHom 1)
  simp only [regularMonodromy_single, mul_one] at e'
  apply End.ext
  exact Finsupp.single_left_injective (by decide : (1 : ℤ) ≠ 0) e'

/-- Equal regular monodromy is exactly equality of the original loop classes. -/
@[simp]
theorem regularMonodromy_eq_iff (b : X) (g h : FundamentalGroup X b) :
    regularMonodromy b g = regularMonodromy b h ↔ g = h :=
  (regularMonodromy_injective b).eq_iff

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/Regular.lean:43-54"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regular

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/Regular.lean:57-59"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regularSingle

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/Regular.lean:63-66"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regular_map_single

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/Regular.lean:70-74"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regular_transport_single

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/Regular.lean:78-81"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regular_transport_symm_transport

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/Regular.lean:85-88"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regular_transport_transport_symm

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/Regular.lean:91-93"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regularMonodromy

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/Regular.lean:97-99"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regularMonodromy_single

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/Regular.lean:102-106"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regularMonodromy_injective

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/Regular.lean:110-112"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  regularMonodromy_eq_iff

attribute [colib_tag "COL-0520"] regularMonodromy_injective

end FundamentalGroupoid.LocalCoefficients
