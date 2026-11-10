/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.BaseChange
public import Colib.AlgebraicGeometry.Simplex.OrdinaryChains
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Affine coordinates on the actual relative algebraic simplex

The relative object is the literal pullback of the existing simplex structure
map. The comparison uses the actual coefficient pullback square, the canonical
affine chart and pullback symmetry. All comparisons are natural in the whole
simplex category, including faces and degeneracies. No reducedness, normality,
integrality or finite-type condition on the coefficient map is used.

Adapted from the affine-relative definitions in `AffineSimplexUnitComplex`,
`AffineSchemeUnitProjection` and `AffineSchemeSimplexComparison` at motivic
revision a6805c4a87cdfd7717dd7a94039246a167f15380. The native ordinary chains use
literal relative products, so no categorical parameter-object wrapper is needed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicSimplex

variable {k R : Type u} [CommRing k] [CommRing R]

/-- The literal relative simplex with the simplex factor first. -/
def relativeSimplexScheme {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    CosimplicialObject Scheme.{u} where
  obj n := CategoryTheory.Limits.pullback (structureMap k n.len) p
  map {m n} f := pullback.map (structureMap k m.len) p (structureMap k n.len) p
    ((cosimplicialScheme k).map f) (𝟙 X) (𝟙 _) (by
      simpa using (structureMap_naturality k f).symm) (by simp)
  map_id n := by
    apply pullback.hom_ext <;> simp
  map_comp f g := by
    apply pullback.hom_ext <;>
      simp only [Functor.map_comp, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc,
        Category.comp_id]

/-- The relative simplex retains the original first projection under every operator. -/
@[reassoc (attr := simp)]
theorem relativeSimplexScheme_map_fst {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    {m n : SimplexCategory} (f : m ⟶ n) :
    (relativeSimplexScheme p).map f ≫ pullback.fst (structureMap k n.len) p =
      pullback.fst (structureMap k m.len) p ≫ (cosimplicialScheme k).map f :=
  pullback.lift_fst _ _ _

/-- Every simplex operator is over the original source scheme. -/
@[reassoc (attr := simp)]
theorem relativeSimplexScheme_map_snd {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    {m n : SimplexCategory} (f : m ⟶ n) :
    (relativeSimplexScheme p).map f ≫ pullback.snd (structureMap k n.len) p =
      pullback.snd (structureMap k m.len) p := by
  simp [relativeSimplexScheme]

/-- The original relative products over an arbitrary affine coefficient map. -/
def affineRelativeSimplex (c : k →+* R) : CosimplicialObject Scheme.{u} :=
  relativeSimplexScheme (Spec.map (CommRingCat.ofHom c))

/-- Every face and degeneracy commutes with the genuine coefficient pullback comparison. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Simplex/AffineSimplexUnitComplex.lean:29-37"
  "adaptation" "Natural comparison of the literal relative simplex with its coordinate spectrum"]
def affineRelativeSimplexIso (c : k →+* R) :
    affineRelativeSimplex c ≅ cosimplicialScheme R :=
  (NatIso.ofComponents (fun n => coefficientPullbackIso c n.len) (fun {m n} f => by
    apply pullback.hom_ext
    · simpa [affineRelativeSimplex, Category.assoc] using
        (cosimplicialSchemeMap c).naturality f
    · simp only [affineRelativeSimplex, relativeSimplexScheme, Category.assoc,
        pullback.lift_snd, Category.comp_id, coefficientPullbackIso_hom_snd]
      exact structureMap_naturality R f) :
      cosimplicialScheme R ≅ affineRelativeSimplex c).symm

/-- The canonical affine chart keeps the original morphism to the affine base. -/
theorem isoSpec_inv_map {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (.of k)) :
    X.isoSpec.inv ≫ p = Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop) := by
  rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]

/-- The actual coefficient map on the canonical global-sections ring of the source. -/
def affineSourceCoefficient (X : SmoothSite (Spec (.of k))) : k →+* Γ(X.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom

/-- The affine chart induces a natural isomorphism of the actual relative pullbacks. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Simplex/AffineSchemeSimplexComparison.lean:35-47"
  "adaptation" "Canonical affine-source comparison with every relative simplex operator"]
def affineSourceRelativeSimplexIso (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    affineRelativeSimplex (affineSourceCoefficient X) ≅ relativeSimplexScheme X.hom :=
  NatIso.ofComponents (fun n => asIso
    (pullback.map (structureMap k n.len)
      (Spec.map (CommRingCat.ofHom (affineSourceCoefficient X)))
      (structureMap k n.len) X.hom (𝟙 _) X.left.isoSpec.inv (𝟙 _) (by simp)
      (by simpa [affineSourceCoefficient] using (isoSpec_inv_map (X := X.left) X.hom).symm))) (by
    intro m n f
    apply pullback.hom_ext <;>
      simp [affineRelativeSimplex, relativeSimplexScheme, Category.assoc])

/-- The literal smooth-site products occurring in the existing ordinary singular chains. -/
def productSimplexScheme (X : SmoothSite (Spec (.of k))) : CosimplicialObject Scheme.{u} where
  obj n := (SmoothSite.product X ((cosimplicialSmoothSite k).obj n)).left
  map f := (SmoothSite.productMap (𝟙 X) ((cosimplicialSmoothSite k).map f)).left
  map_id n := by simp
  map_comp f g := by
    rw [Functor.map_comp]
    have h := SmoothSite.productMap_comp (𝟙 X) (𝟙 X)
      ((cosimplicialSmoothSite k).map f) ((cosimplicialSmoothSite k).map g)
    simpa only [Category.id_comp, MorphismProperty.Comma.comp_left] using
      congrArg (fun h => h.left) h

/-- Switching the two actual pullback factors identifies the ordinary-chain products. -/
def productRelativeSimplexIso (X : SmoothSite (Spec (.of k))) :
    productSimplexScheme X ≅ relativeSimplexScheme X.hom :=
  NatIso.ofComponents (fun n => pullbackSymmetry X.hom (structureMap k n.len)) (by
    intro m n f
    apply pullback.hom_ext <;>
      simp [productSimplexScheme, relativeSimplexScheme, SmoothSite.productMap,
        SmoothSite.productLift, SmoothSite.homMk, SmoothSite.productFst,
        SmoothSite.productSnd, cosimplicialSmoothSite, smoothSiteObj, Category.assoc])

/-- Canonical coordinates for the actual ordinary-chain products on every affine source. -/
def productSimplexAffineIso (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    productSimplexScheme X ≅ cosimplicialScheme Γ(X.left, ⊤) :=
  productRelativeSimplexIso X ≪≫ (affineSourceRelativeSimplexIso X).symm ≪≫
    affineRelativeSimplexIso (affineSourceCoefficient X)

end AlgebraicSimplex
