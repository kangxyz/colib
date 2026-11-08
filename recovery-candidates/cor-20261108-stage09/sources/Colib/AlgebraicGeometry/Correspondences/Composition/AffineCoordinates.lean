/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.Diagonal
public import Colib.Algebra.Category.ModuleCat.Tor.MiddleDiagonal.Rings
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Native affine coordinates for the actual correspondence products

The actual four-factor ambient and the actual triple product are identified with
`Spec ((A ⊗[k] B) ⊗[k] (B ⊗[k] C))` and `Spec ((A ⊗[k] B) ⊗[k] C)`.
These are compositions of Mathlib's `pullbackSpecIso`, transport of a pullback
along isomorphisms, and `pullbackRightPullbackFstIso`. The two adjacent
projections are identified with the actual `leftMap` and `rightMap`.

The affine tensor-product construction is the construction in Stacks Project,
Tag 01JO, not a separate equivalence claimed to be a statement of that tag.
The upstream `StacksFrontier.AlgebraicGeometry.Morphisms.Affine.PullbackTensorProduct`
discusses the same source correspondence. We use the lower explicit-spectrum
Mathlib interface because the algebras here are already specified.

Implementation provenance: fresh reconstruction of the affine geometry needed
by motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/AlgebraicGeometry/Intersection/AffineMiddleTor.lean`.
No historical byte identity is claimed. This source is unverified pending the
coordinated native compile. The field hypothesis matches the existing
middle-diagonal ring interface; no perfection or algebraic closure is assumed.
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

/-- The actual product of the two adjacent products has the literal four-factor ring. -/
def correspondenceAffineAmbientIso :
    correspondenceIntersectionAmbient fA fB fC ≅ Spec (.of (ambientRing k A B C)) :=
  asIso (pullback.map _ _
    (Spec.map (CommRingCat.ofHom (algebraMap k (A ⊗[k] B))))
    (Spec.map (CommRingCat.ofHom (algebraMap k (B ⊗[k] C))))
    (pullbackSpecIso k A B).hom (pullbackSpecIso k B C).hom (𝟙 _)
    (by simpa only [Category.comp_id, pullback.condition] using
      (pullbackSpecIso_hom_base k A B).symm)
    (by simpa only [Category.comp_id] using
      (pullbackSpecIso_hom_base k B C).symm)) ≪≫
    pullbackSpecIso k (A ⊗[k] B) (B ⊗[k] C)

/-- The actual triple product has the literal three-factor tensor ring.
The first isomorphism is native pullback pasting over the middle scheme. -/
def correspondenceAffineTripleIso :
    correspondenceTripleProduct fA fB fC ≅ Spec (.of (tripleRing k A B C)) :=
  pullbackRightPullbackFstIso fB fC (pullback.snd fA fB) ≪≫
    asIso (pullback.map _ _
      (Spec.map (CommRingCat.ofHom (algebraMap k (A ⊗[k] B)))) fC
      (pullbackSpecIso k A B).hom (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id, pullback.condition] using
        (pullbackSpecIso_hom_base k A B).symm)
      (by simp)) ≪≫
    pullbackSpecIso k (A ⊗[k] B) C

/-- The first four-factor coordinate is the original left adjacent product. -/
@[reassoc (attr := simp)]
theorem correspondenceAffineAmbientIso_fst :
    (correspondenceAffineAmbientIso k A B C).hom ≫
      Spec.map (CommRingCat.ofHom
        (includeLeftRingHom : A ⊗[k] B →+* ambientRing k A B C)) =
      pullback.fst (pullback.snd fA fB ≫ fB) (pullback.fst fB fC ≫ fB) ≫
        (pullbackSpecIso k A B).hom := by
  simp [correspondenceAffineAmbientIso]

/-- The second four-factor coordinate is the original right adjacent product. -/
@[reassoc (attr := simp)]
theorem correspondenceAffineAmbientIso_snd :
    (correspondenceAffineAmbientIso k A B C).hom ≫
      Spec.map (CommRingCat.ofHom
        (includeRight : B ⊗[k] C →ₐ[k] ambientRing k A B C).toRingHom) =
      pullback.snd (pullback.snd fA fB ≫ fB) (pullback.fst fB fC ≫ fB) ≫
        (pullbackSpecIso k B C).hom := by
  simp [correspondenceAffineAmbientIso]

/-- The left adjacent projection is the spectrum of the actual `leftMap`. -/
@[reassoc (attr := simp)]
theorem correspondenceAffineTripleIso_fst :
    (correspondenceAffineTripleIso k A B C).hom ≫
      Spec.map (CommRingCat.ofHom (leftMap k A B C).toRingHom) =
      pullback.fst (pullback.snd fA fB) (pullback.fst fB fC) ≫
        (pullbackSpecIso k A B).hom := by
  change (correspondenceAffineTripleIso k A B C).hom ≫
    Spec.map (CommRingCat.ofHom
      (includeLeftRingHom : A ⊗[k] B →+* tripleRing k A B C)) = _
  simp [correspondenceAffineTripleIso]

/-- The outer right coordinate is the original projection to `Spec C`. -/
@[reassoc (attr := simp)]
theorem correspondenceAffineTripleIso_snd_snd :
    (correspondenceAffineTripleIso k A B C).hom ≫
      Spec.map (CommRingCat.ofHom
        (includeRight : C →ₐ[k] tripleRing k A B C).toRingHom) =
      pullback.snd (pullback.snd fA fB) (pullback.fst fB fC) ≫
        pullback.snd fB fC := by
  simp [correspondenceAffineTripleIso]

private theorem correspondenceAffineRightMap_fst :
    Spec.map (CommRingCat.ofHom (rightMap k A B C).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (includeLeftRingHom : B →+* B ⊗[k] C)) =
    Spec.map (CommRingCat.ofHom (leftMap k A B C).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (includeRight : B →ₐ[k] A ⊗[k] B).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

private theorem correspondenceAffineRightMap_snd :
    Spec.map (CommRingCat.ofHom (rightMap k A B C).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (includeRight : C →ₐ[k] B ⊗[k] C).toRingHom) =
    Spec.map (CommRingCat.ofHom (includeRight : C →ₐ[k] tripleRing k A B C).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1

/-- The right adjacent projection is the spectrum of the actual `rightMap`.
In particular, it retains the middle coordinate, rather than substituting the
outer `C` projection for the right adjacent product. -/
@[reassoc (attr := simp)]
theorem correspondenceAffineTripleIso_snd :
    (correspondenceAffineTripleIso k A B C).hom ≫
      Spec.map (CommRingCat.ofHom (rightMap k A B C).toRingHom) =
      pullback.snd (pullback.snd fA fB) (pullback.fst fB fC) ≫
        (pullbackSpecIso k B C).hom := by
  apply (cancel_mono (pullbackSpecIso k B C).inv).1
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSpecIso_inv_fst,
      pullbackSpecIso_hom_fst]
    rw [correspondenceAffineRightMap_fst, ← Category.assoc,
      correspondenceAffineTripleIso_fst]
    simpa only [Category.assoc, AlgHom.toRingHom_eq_coe, pullbackSpecIso_hom_snd] using
      (pullback.condition (f := pullback.snd fA fB) (g := pullback.fst fB fC))
  · simp only [Category.assoc, pullbackSpecIso_inv_snd,
      pullbackSpecIso_hom_snd]
    have h := correspondenceAffineRightMap_snd k A B C
    simp only [AlgHom.toRingHom_eq_coe] at h ⊢
    rw [h]
    simpa only [AlgHom.toRingHom_eq_coe] using
      correspondenceAffineTripleIso_snd_snd k A B C

/-- The inverse ambient chart retains the actual left projection. -/
@[reassoc (attr := simp)]
theorem correspondenceAffineAmbientIso_inv_fst :
    (correspondenceAffineAmbientIso k A B C).inv ≫
      pullback.fst (pullback.snd fA fB ≫ fB) (pullback.fst fB fC ≫ fB) =
      Spec.map (CommRingCat.ofHom
        (includeLeftRingHom : A ⊗[k] B →+* ambientRing k A B C)) ≫
        (pullbackSpecIso k A B).inv := by
  apply (cancel_mono (pullbackSpecIso k A B).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← correspondenceAffineAmbientIso_fst, Iso.inv_hom_id_assoc]

/-- The inverse ambient chart retains the actual right projection. -/
@[reassoc (attr := simp)]
theorem correspondenceAffineAmbientIso_inv_snd :
    (correspondenceAffineAmbientIso k A B C).inv ≫
      pullback.snd (pullback.snd fA fB ≫ fB) (pullback.fst fB fC ≫ fB) =
      Spec.map (CommRingCat.ofHom
        (includeRight : B ⊗[k] C →ₐ[k] ambientRing k A B C).toRingHom) ≫
        (pullbackSpecIso k B C).inv := by
  apply (cancel_mono (pullbackSpecIso k B C).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← correspondenceAffineAmbientIso_snd, Iso.inv_hom_id_assoc]

end Stacks.Chow
