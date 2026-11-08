/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.AffineCoordinates
public import Colib.AlgebraicGeometry.Correspondences.Composition.PulledSupports

/-!
# Tensor coordinates of the full pulled support schemes

Mathlib's `IdealSheafData.comapIso` identifies each full pulled support with
its actual fibre product. Transport by the original adjacent quotient chart
and `pullbackSpecIso` then gives the tensor-product chart. The displayed
inclusion equations identify the actual map from the triple ring.

The right chart uses precisely `rightMap`, including its middle coordinate.
The quotient and its base change retain their full scheme structures. There
are no flatness, reducedness, integrality or finite-length assumptions on these
base-change constructions. The field hypothesis matches the existing coordinate
ring interface and is not a perfection or algebraic-closure assumption.

Mathematical suppliers: Mathlib `AlgebraicGeometry/IdealSheaf/Functorial.lean`,
`IdealSheafData.comapIso`, and `AlgebraicGeometry/Pullbacks.lean`,
`pullbackSpecIso`, the affine fibre-product construction of Stacks Project,
Tag 01JO. Implementation provenance: fresh reconstruction of the support-chart
interface needed by motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/AlgebraicGeometry/Intersection/AffineMiddleTor.lean` and
`Motivic/AlgebraicGeometry/Correspondences/Composition/Incidence/GlobalAmbientTorComparison.lean`.
No historical byte identity or independent source review is claimed.
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

/-- The actual left pulled support has its full base-change tensor chart. -/
def correspondenceAffineLeftPulledIso
    (z : pullback (C := Scheme) fA fB)
    (I : Ideal (A ⊗[k] B))
    (eI : (integralComponentAt z).subscheme ≅ Spec (.of ((A ⊗[k] B) ⧸ I)))
    (hI : (integralComponentAt z).subschemeι ≫ (pullbackSpecIso k A B).hom =
      eI.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    (correspondenceLeftPulledIdeal fA fB fC z).subscheme ≅
      Spec (.of (tripleRing k A B C ⊗[A ⊗[k] B] ((A ⊗[k] B) ⧸ I))) := by
  exact (integralComponentAt z).comapIso
      (pullback.fst (pullback.snd fA fB) (pullback.fst fB fC)) ≪≫
    asIso (pullback.map _ _
      (Spec.map (CommRingCat.ofHom (algebraMap (A ⊗[k] B) (tripleRing k A B C))))
      (Spec.map (CommRingCat.ofHom (algebraMap (A ⊗[k] B) ((A ⊗[k] B) ⧸ I))))
      (correspondenceAffineTripleIso k A B C).hom eI.hom
      (pullbackSpecIso k A B).hom
      (correspondenceAffineTripleIso_fst k A B C).symm hI) ≪≫
    pullbackSpecIso (A ⊗[k] B) (tripleRing k A B C) ((A ⊗[k] B) ⧸ I)

/-- The left pulled chart identifies its literal inclusion in the actual triple product. -/
@[reassoc (attr := simp)]
theorem correspondenceAffineLeftPulledIso_inclusion
    (z : pullback (C := Scheme) fA fB)
    (I : Ideal (A ⊗[k] B))
    (eI : (integralComponentAt z).subscheme ≅ Spec (.of ((A ⊗[k] B) ⧸ I)))
    (hI : (integralComponentAt z).subschemeι ≫ (pullbackSpecIso k A B).hom =
      eI.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    (correspondenceAffineLeftPulledIso k A B C z I eI hI).hom ≫
      Spec.map (CommRingCat.ofHom
        (includeLeftRingHom : tripleRing k A B C →+*
          tripleRing k A B C ⊗[A ⊗[k] B] ((A ⊗[k] B) ⧸ I))) =
    correspondenceLeftPulledInclusion fA fB fC z ≫
      (correspondenceAffineTripleIso k A B C).hom := by
  simp [correspondenceAffineLeftPulledIso, correspondenceLeftPulledInclusion,
    correspondenceLeftPulledIdeal]

/-- The actual right pulled support has its full base-change tensor chart. -/
def correspondenceAffineRightPulledIso
    (w : pullback (C := Scheme) fB fC)
    (J : Ideal (B ⊗[k] C))
    (eJ : (integralComponentAt w).subscheme ≅ Spec (.of ((B ⊗[k] C) ⧸ J)))
    (hJ : (integralComponentAt w).subschemeι ≫ (pullbackSpecIso k B C).hom =
      eJ.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :
    letI : Algebra (B ⊗[k] C) (tripleRing k A B C) :=
      (rightMap k A B C).toRingHom.toAlgebra
    (correspondenceRightPulledIdeal fA fB fC w).subscheme ≅
      Spec (.of (tripleRing k A B C ⊗[B ⊗[k] C] ((B ⊗[k] C) ⧸ J))) := by
  letI : Algebra (B ⊗[k] C) (tripleRing k A B C) :=
    (rightMap k A B C).toRingHom.toAlgebra
  exact (integralComponentAt w).comapIso
      (pullback.snd (pullback.snd fA fB) (pullback.fst fB fC)) ≪≫
    asIso (pullback.map _ _
      (Spec.map (CommRingCat.ofHom (algebraMap (B ⊗[k] C) (tripleRing k A B C))))
      (Spec.map (CommRingCat.ofHom (algebraMap (B ⊗[k] C) ((B ⊗[k] C) ⧸ J))))
      (correspondenceAffineTripleIso k A B C).hom eJ.hom
      (pullbackSpecIso k B C).hom
      (correspondenceAffineTripleIso_snd k A B C).symm hJ) ≪≫
    pullbackSpecIso (B ⊗[k] C) (tripleRing k A B C) ((B ⊗[k] C) ⧸ J)

/-- The right pulled chart identifies its literal inclusion in the actual triple product. -/
@[reassoc (attr := simp)]
theorem correspondenceAffineRightPulledIso_inclusion
    (w : pullback (C := Scheme) fB fC)
    (J : Ideal (B ⊗[k] C))
    (eJ : (integralComponentAt w).subscheme ≅ Spec (.of ((B ⊗[k] C) ⧸ J)))
    (hJ : (integralComponentAt w).subschemeι ≫ (pullbackSpecIso k B C).hom =
      eJ.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :
    letI : Algebra (B ⊗[k] C) (tripleRing k A B C) :=
      (rightMap k A B C).toRingHom.toAlgebra
    (correspondenceAffineRightPulledIso k A B C w J eJ hJ).hom ≫
      Spec.map (CommRingCat.ofHom
        (includeLeftRingHom : tripleRing k A B C →+*
          tripleRing k A B C ⊗[B ⊗[k] C] ((B ⊗[k] C) ⧸ J))) =
    correspondenceRightPulledInclusion fA fB fC w ≫
      (correspondenceAffineTripleIso k A B C).hom := by
  let : Algebra (B ⊗[k] C) (tripleRing k A B C) :=
    (rightMap k A B C).toRingHom.toAlgebra
  simp [correspondenceAffineRightPulledIso, correspondenceRightPulledInclusion,
    correspondenceRightPulledIdeal]

end Stacks.Chow
