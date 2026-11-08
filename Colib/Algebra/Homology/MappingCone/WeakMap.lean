/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.QuasiIsoExtension
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # Quasi-isomorphisms of actual signed mapping cones

The literal cone-square map is the middle map of the original rotated cone
short exact sequences. The existing short-exact quasi-isomorphism theorem
applies with the original target map and shifted source map.

Implementation provenance: Aglib/Algebra/Homology/MappingCone/WeakMap.lean,
source SHA-256 336476d0843055ffb1fc1b62c31cc9c8747a2bb020892e768f572a412b254e12.
The private short-exact argument is reused from its existing Colib owner.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace CochainComplex
variable {A : Type u} [Category.{v} A] [Abelian A]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The original signed rotated cone triangle is a genuine short exact sequence. -/
theorem mappingCone_triangle_shortExact {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (mappingCone.triangleRotateShortComplex f).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (mappingCone.triangleRotateShortComplexSplitting f n).shortExact)

/-- The actual cone-square map on the original rotated short exact sequences. -/
def mappingConeTriangleShortComplexMap {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) :
    mappingCone.triangleRotateShortComplex f ⟶ mappingCone.triangleRotateShortComplex g where
  τ₁ := b
  τ₂ := mappingCone.map f g a b h
  τ₃ := a⟦(1 : ℤ)⟧'
  comm₁₂ := (mappingCone.triangleMap f g a b h).comm₂.symm
  comm₂₃ := (mappingCone.triangleMap f g a b h).comm₃.symm

/-- Actual quasi-isomorphisms of both endpoints induce a quasi-isomorphism of literal cones. -/
theorem mappingCone_map_quasiIso {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) [QuasiIso a] [QuasiIso b] :
    QuasiIso (mappingCone.map f g a b h) :=
  quasiIso_middle_of_shortExact (mappingConeTriangleShortComplexMap f g a b h)
    (mappingCone_triangle_shortExact f) (mappingCone_triangle_shortExact g)
    (by change QuasiIso b; infer_instance)
    (by change QuasiIso (a⟦(1 : ℤ)⟧'); infer_instance)

end CochainComplex
