/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.SpecNaturality
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.AffineExact

/-!
# Actual integral-affine norm and divisor naturality

Every ordinary map is transported by the canonical `isoSpec` isomorphisms.
Its underlying spectrum map is exactly pullback on global sections. The actual
spectrum graph formulas therefore prove naturality of the already constructed
section maps; no naturality proposition is supplied by the caller.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable {k : Type u} [Field k]
  {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]

/-- The actual affine-coordinate arrow retains its two canonical scheme isomorphisms. -/
def affineCoordinateMap (f : X ⟶ Y) :
    AffineSectionCoordinates.obj X ⟶ AffineSectionCoordinates.obj Y :=
  (AffineSectionCoordinates.iso X).hom ≫ f ≫ (AffineSectionCoordinates.iso Y).inv

/-- Its underlying arrow is the spectrum of the original pullback on global sections. -/
theorem affineCoordinateMap_left (f : X ⟶ Y) :
    (affineCoordinateMap f).left = Spec.map f.left.appTop := by
  change X.left.isoSpec.inv ≫ f.left ≫ Y.left.isoSpec.hom = Spec.map f.left.appTop
  rw [← Scheme.isoSpec_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every actual ordinary presheaf restriction commutes with affine coordinates. -/
@[reassoc] theorem affineSectionIso_naturality
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (f : X ⟶ Y) :
    P.map f.op ≫ (affineSectionIso X P).hom =
      (affineSectionIso Y P).hom ≫ P.map (affineCoordinateMap f).op := by
  change P.map f.op ≫ P.map (AffineSectionCoordinates.iso X).hom.op =
    P.map (AffineSectionCoordinates.iso Y).hom.op ≫ P.map (affineCoordinateMap f).op
  rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
  congr 1
  simp [affineCoordinateMap, Category.assoc]

/-- The inverse coordinate comparison preserves the same ordinary restrictions. -/
@[reassoc] theorem affineSectionIso_inv_naturality
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (f : X ⟶ Y) :
    P.map (affineCoordinateMap f).op ≫ (affineSectionIso X P).inv =
      (affineSectionIso Y P).inv ≫ P.map f.op := by
  apply (cancel_mono (affineSectionIso X P).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    affineSectionIso_naturality, Iso.inv_hom_id_assoc]

attribute [local instance] AffineSectionCoordinates.sections_isIntegrallyClosed
  AffineSectionCoordinates.sections_isNoetherianRing

variable [IsIntegral X.left] [IsIntegral Y.left]

/-- The concrete determinant norm is natural on all integral affine smooth objects. -/
@[reassoc] theorem affineReducedNorm_natural (f : X ⟶ Y) :
    ((toPresheaf k).obj (reducedTorus k 1)).map f.op ≫ affineReducedNorm X =
      affineReducedNorm Y ≫ (largeUnitsPresheaf (Spec (.of k))).map f.op := by
  have h := specSectionsReducedNorm_natural
    (AffineSectionCoordinates.structureMap Y) (AffineSectionCoordinates.structureMap X)
    f.left.appTop.hom (affineCoordinateMap f) (affineCoordinateMap_left f)
  dsimp only [affineReducedNorm]
  simp only [Category.assoc]
  rw [affineSectionIso_naturality_assoc]
  rw [← Category.assoc (
    ((toPresheaf k).obj (reducedTorus k 1)).map (affineCoordinateMap f).op)]
  rw [h]
  simp only [Category.assoc, affineSectionIso_inv_naturality]

/-- The genuine reduced boundary divisor is natural for arbitrary affine source maps. -/
@[reassoc] theorem affineReducedBoundaryDivisor_natural (f : X ⟶ Y) :
    (largeBoundaryOnePresheaf k).map f.op ≫ affineReducedBoundaryDivisor X =
      affineReducedBoundaryDivisor Y ≫
        ((toPresheaf k).obj (reducedTorus k 1)).map f.op := by
  have h := specSectionsReducedBoundaryDivisor_natural
    (AffineSectionCoordinates.structureMap Y) (AffineSectionCoordinates.structureMap X)
    f.left.appTop.hom (affineCoordinateMap f) (affineCoordinateMap_left f)
  dsimp only [affineReducedBoundaryDivisor]
  simp only [Category.assoc]
  rw [affineSectionIso_naturality_assoc]
  rw [← Category.assoc ((largeBoundaryOnePresheaf k).map (affineCoordinateMap f).op)]
  rw [h]
  simp only [Category.assoc, affineSectionIso_inv_naturality]

end AlgebraicGeometry.NativeTorusPolynomial
