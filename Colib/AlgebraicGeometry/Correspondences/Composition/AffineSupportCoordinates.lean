/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.AffineCoordinates
public import Colib.Algebra.Category.ModuleCat.Tor.ExteriorQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Quotient coordinates for the actual affine support product

Mathlib's `IsClosedImmersion.Spec_iff` constructs quotient coordinates for each
actual adjacent integral support. Native `pullback.map` transports their product,
and `pullbackSpecIso` identifies it with the tensor product of the two quotient
rings. The inclusion is the spectrum of the literal `productQuotientMap`.

The construction retains the full product scheme. In particular, even though
its factors are integral supports, no reduction of their tensor product is
made, and no geometric integrality, perfection or algebraic closure is assumed.
The field hypothesis matches the existing middle-diagonal ring interface.

Mathematical suppliers: Mathlib
`AlgebraicGeometry/Morphisms/ClosedImmersion.lean`, `IsClosedImmersion.Spec_iff`,
and `AlgebraicGeometry/Pullbacks.lean`, `pullbackSpecIso`. The latter is the
affine fibre-product construction of Stacks Project, Tag 01JO.
Implementation provenance: fresh reconstruction of the coordinate interface
needed by motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
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

private theorem quotient_spec_base {R : Type u} [CommRing R] [Algebra k R]
    (I : Ideal R) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)) =
    Spec.map (CommRingCat.ofHom (algebraMap k (R ⧸ I))) := by
  rw [← Spec.map_comp]
  rfl

variable
  (z : pullback (C := Scheme)
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (Spec.map (CommRingCat.ofHom (algebraMap k B))))
  (w : pullback (C := Scheme)
    (Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (Spec.map (CommRingCat.ofHom (algebraMap k C))))
  (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))
  (eI : (integralComponentAt z).subscheme ≅ Spec (.of ((A ⊗[k] B) ⧸ I)))
  (eJ : (integralComponentAt w).subscheme ≅ Spec (.of ((B ⊗[k] C) ⧸ J)))
  (hI : (integralComponentAt z).subschemeι ≫ (pullbackSpecIso k A B).hom =
    eI.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  (hJ : (integralComponentAt w).subschemeι ≫ (pullbackSpecIso k B C).hom =
    eJ.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))

include hI in
private theorem left_support_base :
    (integralComponentAt z).subschemeι ≫ pullback.snd fA fB ≫ fB =
      eI.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k ((A ⊗[k] B) ⧸ I))) := by
  calc
    _ = (integralComponentAt z).subschemeι ≫ (pullbackSpecIso k A B).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (A ⊗[k] B))) := by
      rw [pullbackSpecIso_hom_base, pullback.condition]
    _ = ((integralComponentAt z).subschemeι ≫ (pullbackSpecIso k A B).hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (A ⊗[k] B))) :=
      (Category.assoc _ _ _).symm
    _ = (eI.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (A ⊗[k] B))) := by rw [hI]
    _ = _ := by rw [Category.assoc, quotient_spec_base]

include hJ in
private theorem right_support_base :
    (integralComponentAt w).subschemeι ≫ pullback.fst fB fC ≫ fB =
      eJ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k ((B ⊗[k] C) ⧸ J))) := by
  calc
    _ = (integralComponentAt w).subschemeι ≫ (pullbackSpecIso k B C).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (B ⊗[k] C))) := by
      rw [pullbackSpecIso_hom_base]
    _ = ((integralComponentAt w).subschemeι ≫ (pullbackSpecIso k B C).hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (B ⊗[k] C))) :=
      (Category.assoc _ _ _).symm
    _ = (eJ.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (B ⊗[k] C))) := by rw [hJ]
    _ = _ := by rw [Category.assoc, quotient_spec_base]

/-- The actual product of adjacent closed supports has tensor-quotient coordinates.
No reduction of the product is taken. -/
def correspondenceAffineSupportProductIso :
    correspondenceSupportProduct fA fB fC z w ≅
      Spec (.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))) :=
  asIso (pullback.map _ _
    (Spec.map (CommRingCat.ofHom (algebraMap k ((A ⊗[k] B) ⧸ I))))
    (Spec.map (CommRingCat.ofHom (algebraMap k ((B ⊗[k] C) ⧸ J))))
    eI.hom eJ.hom (𝟙 _)
    (by simpa only [Category.comp_id] using left_support_base k A B z I eI hI)
    (by simpa only [Category.comp_id] using right_support_base k B C w J eJ hJ)) ≪≫
    pullbackSpecIso k ((A ⊗[k] B) ⧸ I) ((B ⊗[k] C) ⧸ J)

/-- The product chart preserves the actual first support projection. -/
@[reassoc (attr := simp)]
theorem correspondenceAffineSupportProductIso_fst :
    (correspondenceAffineSupportProductIso k A B C z w I J eI eJ hI hJ).hom ≫
      Spec.map (CommRingCat.ofHom (S := ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
        (includeLeftRingHom : (A ⊗[k] B) ⧸ I →+*
          ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))) =
      pullback.fst _ _ ≫ eI.hom := by
  simp [correspondenceAffineSupportProductIso]

/-- The product chart preserves the actual second support projection. -/
@[reassoc]
theorem correspondenceAffineSupportProductIso_snd :
    (correspondenceAffineSupportProductIso k A B C z w I J eI eJ hI hJ).hom ≫
      Spec.map (CommRingCat.ofHom (S := ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
        (includeRight : (B ⊗[k] C) ⧸ J →ₐ[k]
          ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J)).toRingHom) =
      pullback.snd _ _ ≫ eJ.hom := by
  simp [correspondenceAffineSupportProductIso]

@[reassoc]
private theorem productQuotientMap_spec_fst :
    Spec.map (CommRingCat.ofHom (ModuleCat.Tor.productQuotientMap (k := k) I J).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (includeLeftRingHom : A ⊗[k] B →+* ambientRing k A B C)) =
    Spec.map (CommRingCat.ofHom (S := ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
        (includeLeftRingHom : (A ⊗[k] B) ⧸ I →+*
          ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

@[reassoc]
private theorem productQuotientMap_spec_snd :
    Spec.map (CommRingCat.ofHom (ModuleCat.Tor.productQuotientMap (k := k) I J).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (includeRight : B ⊗[k] C →ₐ[k] ambientRing k A B C).toRingHom) =
    Spec.map (CommRingCat.ofHom (S := ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
        (includeRight : (B ⊗[k] C) ⧸ J →ₐ[k]
          ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- The product-support inclusion is the spectrum of the actual tensor quotient map. -/
theorem correspondenceAffineSupportProductIso_inclusion :
    correspondenceSupportProductInclusion fA fB fC z w ≫
      (correspondenceAffineAmbientIso k A B C).hom =
    (correspondenceAffineSupportProductIso k A B C z w I J eI eJ hI hJ).hom ≫
      Spec.map (CommRingCat.ofHom (ModuleCat.Tor.productQuotientMap (k := k) I J).toRingHom) := by
  apply (cancel_mono (correspondenceAffineAmbientIso k A B C).inv).1
  apply pullback.hom_ext
  · simp only [Category.assoc, correspondenceAffineAmbientIso_inv_fst,
      productQuotientMap_spec_fst_assoc,
      correspondenceAffineSupportProductIso_fst_assoc, Iso.hom_inv_id, Category.comp_id]
    rw [correspondenceSupportProductInclusion_fst fA fB fC z w]
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun q => pullback.fst
        ((integralComponentAt z).subschemeι ≫ pullback.snd fA fB ≫ fB)
        ((integralComponentAt w).subschemeι ≫ pullback.fst fB fC ≫ fB) ≫
        q ≫ (pullbackSpecIso k A B).inv) hI
  · simp only [Category.assoc, correspondenceAffineAmbientIso_inv_snd,
      productQuotientMap_spec_snd_assoc,
      correspondenceAffineSupportProductIso_snd_assoc, Iso.hom_inv_id, Category.comp_id]
    rw [correspondenceSupportProductInclusion_snd fA fB fC z w]
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun q => pullback.snd
        ((integralComponentAt z).subschemeι ≫ pullback.snd fA fB ≫ fB)
        ((integralComponentAt w).subschemeι ≫ pullback.fst fB fC ≫ fB) ≫
        q ≫ (pullbackSpecIso k B C).inv) hJ

/-- Construct quotient coordinates for the actual two adjacent supports and their full product.
The charts, ideals and literal tensor-quotient inclusion square are conclusions. -/
theorem exists_correspondenceAffineSupportProductCoordinates :
    ∃ I : Ideal (A ⊗[k] B), ∃ J : Ideal (B ⊗[k] C),
    ∃ eI : (integralComponentAt z).subscheme ≅ Spec (.of ((A ⊗[k] B) ⧸ I)),
    ∃ eJ : (integralComponentAt w).subscheme ≅ Spec (.of ((B ⊗[k] C) ⧸ J)),
      ((integralComponentAt z).subschemeι ≫ (pullbackSpecIso k A B).hom =
        eI.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ∧
      ((integralComponentAt w).subschemeι ≫ (pullbackSpecIso k B C).hom =
        eJ.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ∧
      ∃ eP : correspondenceSupportProduct fA fB fC z w ≅
        Spec (.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))),
      correspondenceSupportProductInclusion fA fB fC z w ≫
        (correspondenceAffineAmbientIso k A B C).hom =
        eP.hom ≫ Spec.map (CommRingCat.ofHom
          (ModuleCat.Tor.productQuotientMap (k := k) I J).toRingHom) := by
  obtain ⟨I, eI, hI⟩ := IsClosedImmersion.Spec_iff.mp
    (inferInstance : IsClosedImmersion
      ((integralComponentAt z).subschemeι ≫ (pullbackSpecIso k A B).hom))
  obtain ⟨J, eJ, hJ⟩ := IsClosedImmersion.Spec_iff.mp
    (inferInstance : IsClosedImmersion
      ((integralComponentAt w).subschemeι ≫ (pullbackSpecIso k B C).hom))
  exact ⟨I, J, eI, eJ, hI, hJ,
    correspondenceAffineSupportProductIso k A B C z w I J eI eJ hI hJ,
    correspondenceAffineSupportProductIso_inclusion k A B C z w I J eI eJ hI hJ⟩

end Stacks.Chow
