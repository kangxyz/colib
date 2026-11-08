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

-- The quotient ideals and the chart of the full product are constructed, not inputs.
example (z : pullback (C := Scheme) fA fB) (w : pullback (C := Scheme) fB fC) :
    ∃ I : Ideal (A ⊗[k] B), ∃ J : Ideal (B ⊗[k] C),
    ∃ eP : correspondenceSupportProduct fA fB fC z w ≅
      Spec (.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))),
      correspondenceSupportProductInclusion fA fB fC z w ≫
        (correspondenceAffineAmbientIso k A B C).hom =
      eP.hom ≫ Spec.map (CommRingCat.ofHom
        (ModuleCat.Tor.productQuotientMap (k := k) I J).toRingHom) := by
  obtain ⟨I, J, eI, eJ, hI, hJ, eP, hP⟩ :=
    exists_correspondenceAffineSupportProductCoordinates k A B C z w
  exact ⟨I, J, eP, hP⟩

-- The literal quotient tensor, rather than a reduction, receives the actual map.
example (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))
    (a : A ⊗[k] B) (b : B ⊗[k] C) :
    ModuleCat.Tor.productQuotientMap (k := k) I J (a ⊗ₜ[k] b) =
      Ideal.Quotient.mk I a ⊗ₜ[k] Ideal.Quotient.mk J b := rfl

#print axioms Stacks.Chow.exists_correspondenceAffineSupportProductCoordinates
#print axioms Stacks.Chow.correspondenceAffineSupportProductIso_inclusion
