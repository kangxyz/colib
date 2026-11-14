/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Units.EtaleSheaf
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.DerivedRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Full-small restriction of actual units and roots of unity -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
attribute [instance] CategoryTheory.sheafIsAbelian
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)

/-- On the separated finite-type basis, both actual presheaves have the same
unit sections and the same pullback. This does not identify the extension
functor on the full site by definitional equality. -/
def basisUnitsPresheafIso :
    ((etaleRestrict X).obj (SmoothSite.largeUnitsEtaleSheaf B)).obj ≅
      (((sheafEquivSmallEtale X).inverse.obj
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left))).obj :=
  NatIso.ofComponents (fun U =>
    AddEquiv.toAddCommGrpIso {
      toFun := fun x => ULift.up x.down
      invFun := fun x => ULift.up x.down
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by cases x; rfl
      map_add' := fun _ _ => rfl }) (by
    intro U V f
    ext x
    rfl)

/-- The genuine sheaf isomorphism on the basis, lifted through the fully faithful
forgetful functor from sheaves. -/
def basisUnitsIso :
    (etaleRestrict X).obj (SmoothSite.largeUnitsEtaleSheaf B) ≅
      (sheafEquivSmallEtale X).inverse.obj
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left) :=
  (fullyFaithfulSheafToPresheaf (etaleTopology X.left) AddCommGrpCat.{u + 1}).preimageIso
    (basisUnitsPresheafIso X)

/-- Genuine full-small units identification: map the basis isomorphism through
its cover-dense sheaf equivalence, then use its actual counit. -/
def fullSmallUnitsIso :
    (fullSmallEtaleRestrict X).obj (SmoothSite.largeUnitsEtaleSheaf B) ≅
      Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left :=
  (sheafEquivSmallEtale X).functor.mapIso (basisUnitsIso X) ≪≫
    (sheafEquivSmallEtale X).counitIso.app _

/-- The units identification commutes with actual multiplication, by additivity
of restriction; no choice of a root of unity is involved. -/
theorem fullSmallUnitsIso_nsmul (n : ℕ) :
    (fullSmallEtaleRestrict X).map (n • 𝟙 (SmoothSite.largeUnitsEtaleSheaf B)) ≫
        (fullSmallUnitsIso X).hom =
      (fullSmallUnitsIso X).hom ≫ Stacks.Kummer.powMap.{u, 0} X.left n := by
  simp [Stacks.Kummer.powMap]

/-- Actual restricted power-map kernel is the existing small-site μ_n.
The first arrow is preserved-kernel comparison, the second uses the real units
iso and its multiplication square. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/EtaleCohomology/KummerTheory/MultiplicativeSheaf.lean:172-181"
  "ingredient" "The original small-site roots-of-unity sheaf is the literal power-map kernel"]
def fullSmallRootsOfUnityIso
    [HasSheafify (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}] (n : ℕ) :
    (fullSmallEtaleRestrict X).obj
      (kernel (n • 𝟙 (SmoothSite.largeUnitsEtaleSheaf B))) ≅
        Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X.left n :=
  PreservesKernel.iso (fullSmallEtaleRestrict X)
      (n • 𝟙 (SmoothSite.largeUnitsEtaleSheaf B)) ≪≫
    kernel.mapIso _ (Stacks.Kummer.powMap.{u, 0} X.left n)
      (fullSmallUnitsIso X) (fullSmallUnitsIso X) (fullSmallUnitsIso_nsmul X n)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
