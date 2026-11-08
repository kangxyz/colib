/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.AffineCoordinates

/-!
# The literal middle-diagonal coordinate square

The native map from the actual triple product to the four-factor ambient is,
under the constructed affine charts, the spectrum of the actual ring map
`(a ⊗ b) ⊗ (b' ⊗ c) ↦ (a ⊗ (b * b')) ⊗ c`.
The proof identifies both adjacent projections. Neither a comparison square nor
flatness of the quotient map is supplied as a hypothesis.

Background: the affine fibre-product construction in Stacks Project, Tag 01JO.
The diagonal and pullback maps used here are Mathlib's native maps. The result is
the explicit coordinate compatibility needed by the middle-diagonal Tor
comparison; it does not assert the Tor theorem itself.

Implementation provenance: fresh reconstruction for motivic
a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/AlgebraicGeometry/Intersection/AffineMiddleTor.lean`.
No historical byte identity is claimed. Unverified pending the coordinated
native compile.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Algebra.TensorProduct Algebra.TensorProduct.MiddleDiagonal
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

local notation "fA" => Spec.map (CommRingCat.ofHom (algebraMap k A))
local notation "fB" => Spec.map (CommRingCat.ofHom (algebraMap k B))
local notation "fC" => Spec.map (CommRingCat.ofHom (algebraMap k C))

@[reassoc]
private theorem correspondenceAffineQuotientMap_fst :
    Spec.map (CommRingCat.ofHom (quotientMap k A B C).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (includeLeftRingHom : A ⊗[k] B →+* ambientRing k A B C)) =
    Spec.map (CommRingCat.ofHom (leftMap k A B C).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1
  ext p <;> simp [quotientMap]

@[reassoc]
private theorem correspondenceAffineQuotientMap_snd :
    Spec.map (CommRingCat.ofHom (quotientMap k A B C).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (includeRight : B ⊗[k] C →ₐ[k] ambientRing k A B C).toRingHom) =
    Spec.map (CommRingCat.ofHom (rightMap k A B C).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1
  ext p <;> simp [quotientMap]

/-- The actual middle-diagonal inclusion has exactly the prescribed tensor
quotient map in the constructed affine coordinates, over every field. -/
@[reassoc]
theorem correspondenceAffine_middleDiagonal_square :
    (correspondenceAffineTripleIso k A B C).hom ≫
      Spec.map (CommRingCat.ofHom (quotientMap k A B C).toRingHom) =
    correspondenceTripleInclusion fA fB fC ≫
      (correspondenceAffineAmbientIso k A B C).hom := by
  apply (cancel_mono (correspondenceAffineAmbientIso k A B C).inv).1
  apply pullback.hom_ext
  · simp only [Category.assoc, correspondenceAffineAmbientIso_inv_fst,
      correspondenceAffineQuotientMap_fst_assoc,
      correspondenceAffineTripleIso_fst_assoc, correspondenceAffineAmbientIso_fst_assoc,
      correspondenceTripleInclusion_fst_assoc]
  · simp only [Category.assoc, correspondenceAffineAmbientIso_inv_snd,
      correspondenceAffineQuotientMap_snd_assoc,
      correspondenceAffineTripleIso_snd_assoc, correspondenceAffineAmbientIso_snd_assoc,
      correspondenceTripleInclusion_snd_assoc]

end Stacks.Chow
