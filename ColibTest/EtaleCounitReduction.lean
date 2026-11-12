/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.EtaleCounitReduction

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

-- The conservative family consists only of affine-source closed residue-geometric points.
example {S : Scheme.{u}} [IsAffine S] [JacobsonSpace S] :
    (affineClosedEtaleNeighborhoodPointFamily S).IsConservativeFamilyOfPoints :=
  isConservativeFamilyOfPoints_affineClosedEtaleNeighborhood S

-- The resulting criterion detects arbitrary sheaf morphisms, not only the chosen counit.
example {S : Scheme.{u}} [IsAffine S] [JacobsonSpace S]
    {F G : Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    IsIso f ↔ ∀ (X : SmoothSite S) [IsAffine X.left] (x : X.left),
      IsClosed ({x} : Set X.left) →
        IsIso ((etaleNeighborhoodPoint.{u, u + 1} X
          (GeometricPoint.ofPoint X.left x).hom).presheafFiber.map f.hom) :=
  isIso_iff_affineClosedResidueGeometricNeighborhoodValue f

-- Finiteness and characteristic-zero separability use the actual structural residue action.
example {k : Type u} [Field k] [CharZero k]
    (X : SmoothSite (Spec (.of k))) (x : X.left) (hx : IsClosed ({x} : Set X.left)) :
    letI : Algebra k (X.left.residueField x) := (fieldToResidue X.hom x).hom.toAlgebra
    Module.Finite k (X.left.residueField x) ∧
      Algebra.IsSeparable k (X.left.residueField x) := by
  let : Algebra k (X.left.residueField x) := (fieldToResidue X.hom x).hom.toAlgebra
  have : Module.Finite k (X.left.residueField x) :=
    finite_residueField_overField_of_isClosed X.hom x hx
  exact ⟨inferInstance, inferInstance⟩

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)

local instance : IsAffine (base (Spec (.of k))).left :=
  inferInstanceAs (IsAffine (Spec (.of k)))

variable
  (hsep : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X.left),
    IsClosed ({ξ default} : Set X.left) →
      letI : Algebra k (X.left.residueField (ξ default)) :=
        (fieldToResidue X.hom (ξ default)).hom.toAlgebra
      Algebra.IsSeparable k (X.left.residueField (ξ default)) →
        IsIso (etaleNeighborhoodValuePullback
          (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp) :
            X ⟶ base (Spec (.of k))) (ξ := ξ) rfl
              ((PresheafWithTransfers.toPresheaf k).obj P)))

-- No perfection, characteristic, constructibility, or coefficient-finiteness assumption.
example (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (PresheafWithTransfers.sections P (Cor.mk W)) (n : ℤ)) :
    IsIso ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app
      ((presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj ((PresheafWithTransfers.toPresheaf k).obj P))) :=
  (PresheafWithTransfers.isIso_fullSmallEtale_sheafification_counit_iff_separableClosedNeighborhood
    P n hn hP).mpr hsep

-- Exponent one is admitted; the explicit geometric condition is never silently discharged.
example (hP : ∀ W : SmoothSite (Spec (.of k)),
    Module.IsTorsionBy ℤ (PresheafWithTransfers.sections P (Cor.mk W)) (1 : ℤ)) :
    IsIso ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app
      ((presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj ((PresheafWithTransfers.toPresheaf k).obj P))) :=
  (PresheafWithTransfers.isIso_fullSmallEtale_sheafification_counit_iff_separableClosedNeighborhood
    P 1 (by simp) hP).mpr hsep

-- Composite torsion exponents also give the actual full-small essential-image conclusion.
example (h6 : IsUnit (6 : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (PresheafWithTransfers.sections P (Cor.mk W)) (6 : ℤ)) :
    (fullSmallEtaleExtend (base (Spec (.of k)))).essImage
      ((presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj ((PresheafWithTransfers.toPresheaf k).obj P)) :=
  PresheafWithTransfers.fullSmallEtaleExtend_essImage_sheafification_of_separableClosedNeighborhood
    P 6 h6 hP hsep

#print axioms isConservativeFamilyOfPoints_affineClosedEtaleNeighborhood
#print axioms isIso_iff_affineClosedResidueGeometricNeighborhoodValue
#print axioms isIso_iff_affineClosedEtaleNeighborhoodValue
#print axioms
  PresheafWithTransfers.isIso_fullSmallEtale_sheafification_counit_iff_separableClosedNeighborhood
#print axioms
  PresheafWithTransfers.fullSmallEtaleExtend_essImage_sheafification_of_separableClosedNeighborhood
