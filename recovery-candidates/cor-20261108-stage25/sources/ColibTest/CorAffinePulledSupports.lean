/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.AffineSupportCoordinates
import Colib.AlgebraicGeometry.Correspondences.Composition.AffinePulledSupports

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Algebra.TensorProduct Algebra.TensorProduct.MiddleDiagonal
open scoped TensorProduct

universe u

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

local notation "fA" => Spec.map (CommRingCat.ofHom (algebraMap k A))
local notation "fB" => Spec.map (CommRingCat.ofHom (algebraMap k B))
local notation "fC" => Spec.map (CommRingCat.ofHom (algebraMap k C))

-- Both tensor charts use the same quotient charts constructed for the product.
example (z : pullback (C := Scheme) fA fB) (w : pullback (C := Scheme) fB fC) :
    ∃ I : Ideal (A ⊗[k] B), ∃ J : Ideal (B ⊗[k] C),
      Nonempty ((correspondenceLeftPulledIdeal fA fB fC z).subscheme ≅
        Spec (.of (tripleRing k A B C ⊗[A ⊗[k] B] ((A ⊗[k] B) ⧸ I)))) ∧
      (letI : Algebra (B ⊗[k] C) (tripleRing k A B C) :=
          (rightMap k A B C).toRingHom.toAlgebra;
        Nonempty ((correspondenceRightPulledIdeal fA fB fC w).subscheme ≅
          Spec (.of (tripleRing k A B C ⊗[B ⊗[k] C] ((B ⊗[k] C) ⧸ J))))) := by
  obtain ⟨I, J, eI, eJ, hI, hJ, eP, hP⟩ :=
    exists_correspondenceAffineSupportProductCoordinates k A B C z w
  exact ⟨I, J, ⟨correspondenceAffineLeftPulledIso k A B C z I eI hI⟩,
    ⟨correspondenceAffineRightPulledIso k A B C w J eJ hJ⟩⟩

-- This is the orientation consumed by the actual pulled-stalk comparison.
example (w : pullback (C := Scheme) fB fC) (J : Ideal (B ⊗[k] C))
    (eJ : (integralComponentAt w).subscheme ≅ Spec (.of ((B ⊗[k] C) ⧸ J)))
    (hJ : (integralComponentAt w).subschemeι ≫ (pullbackSpecIso k B C).hom =
      eJ.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :
    letI : Algebra (B ⊗[k] C) (tripleRing k A B C) :=
      (rightMap k A B C).toRingHom.toAlgebra
    correspondenceRightPulledInclusion fA fB fC w ≫
      (correspondenceAffineTripleIso k A B C).hom =
      (correspondenceAffineRightPulledIso k A B C w J eJ hJ).hom ≫
        Spec.map (CommRingCat.ofHom (includeLeftRingHom : tripleRing k A B C →+*
          tripleRing k A B C ⊗[B ⊗[k] C] ((B ⊗[k] C) ⧸ J))) :=
  (correspondenceAffineRightPulledIso_inclusion k A B C w J eJ hJ).symm

#print axioms Stacks.Chow.correspondenceAffineLeftPulledIso_inclusion
#print axioms Stacks.Chow.correspondenceAffineRightPulledIso_inclusion
