/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.SpecSectionsExact
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.SectionCoordinates

/-!
# The actual reduced-divisor exact sequence on every integral affine smooth object

All three terms are the original presheaf sections at the original object `X`.
The maps are obtained from the concrete native norm and divisor by the actual
canonical affine isomorphism. Exactness is transported along the three actual
presheaf restriction isomorphisms. No unrestricted norm or exactness premise
is introduced. Ordinary naturality for nonisomorphic source changes, global
descent, and the singular sheaf sequence remain separate theorems.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable {k : Type u} [Field k]
variable (X : SmoothSite (Spec (.of k))) [IsAffine X.left]

private instance sectionsNormal : IsIntegrallyClosed Γ(X.left, ⊤) :=
  AffineSectionCoordinates.sections_isIntegrallyClosed X

private instance sectionsNoetherian : IsNoetherianRing Γ(X.left, ⊤) :=
  AffineSectionCoordinates.sections_isNoetherianRing X

/-- Canonical affine restriction for the actual original ordinary presheaf. -/
def affineSectionIso (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    P.obj (op X) ≅ P.obj (op (AffineSectionCoordinates.obj X)) :=
  P.mapIso (AffineSectionCoordinates.iso X).op

variable [IsIntegral X.left]

/-- Actual reduced divisor with the original boundary-one coefficient at `X`. -/
def affineReducedBoundaryDivisor : (largeBoundaryOnePresheaf k).obj (op X) ⟶
    ((toPresheaf k).obj (reducedTorus k 1)).obj (op X) := by
  letI := AffineSectionCoordinates.sections_isNoetherianRing X
  exact (affineSectionIso X (largeBoundaryOnePresheaf k)).hom ≫
    specSectionsReducedBoundaryDivisor (AffineSectionCoordinates.structureMap X) ≫
      (affineSectionIso X ((toPresheaf k).obj (reducedTorus k 1))).inv

/-- Actual support determinant norm with the original ordinary global-unit coefficient at `X`. -/
def affineReducedNorm : ((toPresheaf k).obj (reducedTorus k 1)).obj (op X) ⟶
    (largeUnitsPresheaf (Spec (.of k))).obj (op X) := by
  letI := AffineSectionCoordinates.sections_isIntegrallyClosed X
  letI := AffineSectionCoordinates.sections_isNoetherianRing X
  exact (affineSectionIso X ((toPresheaf k).obj (reducedTorus k 1))).hom ≫
    specSectionsReducedNorm (AffineSectionCoordinates.structureMap X) ≫
      (affineSectionIso X (largeUnitsPresheaf (Spec (.of k)))).inv

@[reassoc (attr := simp)] theorem affineReducedBoundaryDivisor_norm :
    affineReducedBoundaryDivisor X ≫ affineReducedNorm X = 0 := by
  have := AffineSectionCoordinates.sections_isIntegrallyClosed X
  have := AffineSectionCoordinates.sections_isNoetherianRing X
  simp only [affineReducedBoundaryDivisor, affineReducedNorm, Category.assoc,
    Iso.inv_hom_id_assoc, specSectionsReducedBoundaryDivisor_norm_assoc, zero_comp, comp_zero]

/-- The actual original section groups and the specified geometric maps at `X`. -/
def affineReducedDivisorShortComplex : ShortComplex AddCommGrpCat.{u + 1} :=
  ShortComplex.mk (affineReducedBoundaryDivisor X) (affineReducedNorm X)
    (affineReducedBoundaryDivisor_norm X)

/-- The concrete affine-coordinate comparison retains all three actual coefficient maps. -/
def affineReducedDivisorCoordinatesIso :
    letI := AffineSectionCoordinates.sections_isIntegrallyClosed X
    letI := AffineSectionCoordinates.sections_isNoetherianRing X
    specSectionsReducedDivisorShortComplex (AffineSectionCoordinates.structureMap X) ≅
      affineReducedDivisorShortComplex X := by
  letI := AffineSectionCoordinates.sections_isIntegrallyClosed X
  letI := AffineSectionCoordinates.sections_isNoetherianRing X
  exact ShortComplex.isoMk (affineSectionIso X (largeBoundaryOnePresheaf k)).symm
    (affineSectionIso X ((toPresheaf k).obj (reducedTorus k 1))).symm
    (affineSectionIso X (largeUnitsPresheaf (Spec (.of k)))).symm
    (by simp [specSectionsReducedDivisorShortComplex, affineReducedDivisorShortComplex,
      affineReducedBoundaryDivisor])
    (by simp [specSectionsReducedDivisorShortComplex, affineReducedDivisorShortComplex,
      affineReducedNorm])

/-- Genuine short exactness on every original integral affine smooth object over any field. -/
theorem affineReducedDivisorShortComplex_shortExact :
    (affineReducedDivisorShortComplex X).ShortExact := by
  have := AffineSectionCoordinates.sections_isIntegrallyClosed X
  have := AffineSectionCoordinates.sections_isNoetherianRing X
  exact ShortComplex.shortExact_of_iso (affineReducedDivisorCoordinatesIso X)
    (specSectionsReducedDivisorShortComplex_shortExact (AffineSectionCoordinates.structureMap X))

/-- The actual boundary divisor is injective at the original source object. -/
theorem affineReducedBoundaryDivisor_injective :
    Function.Injective (affineReducedBoundaryDivisor X) :=
  (AddCommGrpCat.mono_iff_injective _).mp
    (affineReducedDivisorShortComplex_shortExact X).mono_f

/-- The actual norm is onto the original ordinary global units. -/
theorem affineReducedNorm_surjective : Function.Surjective (affineReducedNorm X) :=
  (AddCommGrpCat.epi_iff_surjective _).mp
    (affineReducedDivisorShortComplex_shortExact X).epi_g

/-- The actual norm kernel is precisely the image of the specified boundary divisor. -/
theorem affineReducedNorm_eq_zero_iff
    (z : ((toPresheaf k).obj (reducedTorus k 1)).obj (op X)) :
    affineReducedNorm X z = 0 ↔ ∃ m, affineReducedBoundaryDivisor X m = z := by
  constructor
  · exact (ShortComplex.ab_exact_iff _).mp
      (affineReducedDivisorShortComplex_shortExact X).exact z
  · rintro ⟨m, rfl⟩
    exact congrArg (fun h => h m) (affineReducedBoundaryDivisor_norm X)

end AlgebraicGeometry.NativeTorusPolynomial
