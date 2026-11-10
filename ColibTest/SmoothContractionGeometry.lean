/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Presheaf
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RepresentableLarge

/-!
Consumers of the genuine Laurent geometry, including graph restrictions of the
existing large signed representables. These examples do not supply or assume
the missing action of arbitrary finite correspondences on the quotient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers

universe v u

namespace ColibTest.SmoothContractionGeometry

variable {S : Scheme.{u}}

example (X : SmoothSite S) : IsOpenImmersion (Contraction.openInclusion.app X).left := inferInstance

example (X : SmoothSite S) :
    Contraction.unitSection.app X ≫ Contraction.openInclusion.app X =
      Contraction.affineOneSection X :=
  Contraction.unitSection_openInclusion X

example (P : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{v}) :
    Contraction.constant P (SmoothSite.multiplicativeGroupObject S) ≫ Contraction.unit P = 𝟙 P :=
  Contraction.constant_unit P

example (P : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{v}) (X : SmoothSite S) :
    (Contraction.presheaf P).obj (op X) ≅ AddCommGrpCat.of
      (P.obj (op (Contraction.torusCylinder.obj X)) ⧸
        (P.map (Contraction.openInclusion.app X).op).hom.range) :=
  Contraction.sectionsIsoQuotient P X

variable {k : Type u} [Field k]

/-- For a genuine transfer coefficient, restriction is its actual open-graph transfer. -/
example (P : PresheafWithTransfers.{v} k) (X : SmoothSite (Spec (.of k))) :
    (Contraction.restriction ((toPresheaf k).obj P)).app (op X) =
      transfer P ((Cor.graphFunctor k).map (Contraction.openInclusion.app X)) := rfl

/-- The quotient remains in the original large coefficient universe. -/
example (Z : Cor k) : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Contraction.presheaf ((toPresheaf k).obj ((representableLarge k).obj Z))

/-- Restriction of actual large represented classes uses the genuine product graph. -/
example (Z : Cor k) {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y)
    (β : Cor.mk (Contraction.torusCylinder.obj Y) ⟶ Z) :
    (Contraction.presheaf ((toPresheaf k).obj ((representableLarge k).obj Z))).map f.op
        ((Contraction.quotient ((toPresheaf k).obj ((representableLarge k).obj Z))).app
          (op Y) (ULift.up β)) =
      (Contraction.quotient ((toPresheaf k).obj ((representableLarge k).obj Z))).app (op X)
        (ULift.up ((Cor.graphFunctor k).map
          (SmoothSite.productMap f (𝟙 (SmoothSite.multiplicativeGroupObject
            (Spec (.of k))))) ≫ β)) :=
  Contraction.map_quotient_apply
    ((toPresheaf k).obj ((representableLarge k).obj Z)) f (ULift.up β)

/-- The actual quotient retains negative signed-cycle classes. -/
example (Z : Cor k) (X : SmoothSite (Spec (.of k)))
    (β : Cor.mk (Contraction.torusCylinder.obj X) ⟶ Z) :
    (Contraction.quotient ((toPresheaf k).obj ((representableLarge k).obj Z))).app (op X)
        (ULift.up (-β)) =
      -(Contraction.quotient ((toPresheaf k).obj ((representableLarge k).obj Z))).app (op X)
        (ULift.up β) :=
  map_neg _ _

/-- The genuine affine restriction is killed, for the actual large representable coefficient. -/
example (Z : Cor k) :
    Contraction.restriction ((toPresheaf k).obj ((representableLarge k).obj Z)) ≫
      Contraction.quotient ((toPresheaf k).obj ((representableLarge k).obj Z)) = 0 :=
  Contraction.restriction_quotient _

end ColibTest.SmoothContractionGeometry
