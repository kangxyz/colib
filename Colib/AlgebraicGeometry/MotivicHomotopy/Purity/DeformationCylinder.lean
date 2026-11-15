/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffinePairContraction
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.CoordinateFibreMaps
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ComplementComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationEtaleCoordinates

/-!
# Cylinder comparisons of closed-pair deformation fibres

On a cylinder chart the original deformation fibre maps are the constant
sections of the affine cylinder.
-/

public noncomputable section

set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.Contraction
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open Stacks.Deformation Stacks.MoreMorphisms

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

variable {C D : Type*} [Category C] [Category D]

/-- A square of arrows with invertible horizontal pair comparisons preserves
invertibility of the images of its vertical arrows. -/
theorem isIso_map_arrow_of_comparison (F : Arrow C ⥤ D)
    {A B A' B' : Arrow C} (f : A ⟶ B) (f' : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f')
    (ha : IsIso (F.map a)) (hb : IsIso (F.map b)) (hf' : IsIso (F.map f')) :
    IsIso (F.map f) := by
  let : IsIso (F.map a) := ha
  let : IsIso (F.map b) := hb
  let : IsIso (F.map f') := hf'
  have h' : F.map f ≫ F.map b = F.map a ≫ F.map f' := by
    rw [← F.map_comp, ← F.map_comp, h]
  have : IsIso (F.map f ≫ F.map b) := by
    rw [h']
    infer_instance
  exact IsIso.of_isIso_comp_right (F.map f) (F.map b)

/-- A commutative comparison through invertible images of the horizontal maps
detects invertibility in either direction. -/
theorem isIso_map_arrow_iff_of_comparison (F : Arrow C ⥤ D)
    {A B A' B' : Arrow C} (f : A ⟶ B) (f' : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f')
    (ha : IsIso (F.map a)) (hb : IsIso (F.map b)) :
    IsIso (F.map f) ↔ IsIso (F.map f') := by
  refine ⟨?_, isIso_map_arrow_of_comparison F f f' a b h ha hb⟩
  intro hf
  let : IsIso (F.map f) := hf
  let : IsIso (F.map a) := ha
  let : IsIso (F.map b) := hb
  have h' : F.map a ≫ F.map f' = F.map f ≫ F.map b := by
    rw [← F.map_comp, ← F.map_comp, h]
  have : IsIso (F.map a ≫ F.map f') := by
    rw [h']
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map a) (F.map f')

/-- A map between open pairs whose square is cartesian and whose ambient
arrow is invertible is an isomorphism in the original arrow category. -/
def openPairArrowIsoOfAmbientIso {S : Scheme.{u}} (sq : Square (SmoothSite S))
    (h : sq.IsPullback) [IsIso sq.f₃₄] : Arrow.mk sq.f₁₃ ≅ Arrow.mk sq.f₂₄ := by
  let : IsIso sq.f₁₂ := h.isIso_fst_of_isIso
  exact Arrow.isoMk (asIso sq.f₁₂) (asIso sq.f₃₄) sq.fac

/-- The open-pair isomorphism has the given isomorphism on ambient schemes. -/
theorem openPairArrowIsoOfAmbientIso_right {S : Scheme.{u}} (sq : Square (SmoothSite S))
    (h : sq.IsPullback) [IsIso sq.f₃₄] :
    (openPairArrowIsoOfAmbientIso sq h).hom.right = sq.f₃₄ := (rfl)

open SheafWithTransfers

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" field ")" =>
  AlgebraicGeometry.Scheme.SmoothSite (Spec (CommRingCat.of field))
local notation "P" => effectivePairMotiveFunctor k

/-- A cartesian map of open pairs over an isomorphism of ambient schemes
induces an isomorphism on the actual relative motives. -/
theorem isIso_effectivePairMotiveMap_of_ambientIso (sq : Square Sm(k))
    (h : sq.IsPullback) [IsIso sq.f₃₄] : IsIso (effectivePairMotiveMap k sq) :=
  inferInstanceAs (IsIso ((P).map (openPairArrowIsoOfAmbientIso sq h).hom))

/-- An actual fibre square becomes invertible when a cartesian cylinder
comparison identifies its ambient fibre arrow with the constant section.
The equation on the complementary opens follows by cancelling their inclusion. -/
theorem isIso_effectivePairMotiveMap_of_cylinder
    (sq : Square Sm(k)) {U X : Sm(k)} (j : U ⟶ X) [IsOpenImmersion j.left] (r : k)
    (a : Arrow.mk sq.f₁₃ ≅ Arrow.mk j) (b : Arrow.mk sq.f₂₄ ≅
      Arrow.mk (affineLineCylinder.map j))
    (h : sq.f₃₄ ≫ b.hom.right = a.hom.right ≫ nativeAffineSection (.of k) X r) :
    IsIso (effectivePairMotiveMap k sq) := by
  let f : Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄ := Arrow.homMk' sq.f₁₂ sq.f₃₄ sq.fac
  let t : Arrow.mk j ⟶ Arrow.mk (affineLineCylinder.map j) :=
    Arrow.homMk' (nativeAffineSection (.of k) U r) (nativeAffineSection (.of k) X r)
      (nativeAffineSection_naturality (.of k) j r)
  have hn : f ≫ b.hom = a.hom ≫ t := by
    apply Arrow.hom_ext
    · have hm : Mono (affineLineCylinder.map j) :=
        (SmoothSite.forgetScheme _).mono_of_mono_map (by
          change Mono (affineLineCylinder.map j).left
          let : IsOpenImmersion (affineLineCylinder.map j).left :=
            MorphismProperty.of_isPullback (affineLineCylinder_map_isPullback j).flip inferInstance
          infer_instance)
      apply (cancel_mono (affineLineCylinder.map j)).1
      change (sq.f₁₂ ≫ b.hom.left) ≫ affineLineCylinder.map j =
        (a.hom.left ≫ nativeAffineSection (.of k) U r) ≫ affineLineCylinder.map j
      have ha : a.hom.left ≫ j = sq.f₁₃ ≫ a.hom.right := Arrow.w a.hom
      have hb : b.hom.left ≫ affineLineCylinder.map j = sq.f₂₄ ≫ b.hom.right :=
        Arrow.w b.hom
      calc
        _ = sq.f₁₂ ≫ sq.f₂₄ ≫ b.hom.right := by rw [Category.assoc, hb]
        _ = sq.f₁₃ ≫ sq.f₃₄ ≫ b.hom.right := by
          rw [← Category.assoc, sq.fac, Category.assoc]
        _ = (sq.f₁₃ ≫ a.hom.right) ≫ nativeAffineSection (.of k) X r := by
          rw [h, Category.assoc]
        _ = _ := by
          rw [← ha, Category.assoc, Category.assoc]
          exact congrArg (a.hom.left ≫ ·) (nativeAffineSection_naturality (.of k) j r).symm
    · exact h
  exact isIso_map_arrow_of_comparison (P) f t a.hom b.hom hn inferInstance inferInstance
    (isIso_effectivePairMotiveMap_affinePairSection k j r)

/-- The genuine fibre-one map on a cylinder chart is the relative affine section. -/
theorem isIso_effectivePairMotiveMap_deformationOne_of_cylinder
    {Z X U Y : Sm(k)} (i : Z ⟶ X) [IsClosedImmersion i.left]
    (j : U ⟶ Y) [IsOpenImmersion j.left]
    (a : Arrow.mk (deformationOneSquare i).f₁₃ ≅ Arrow.mk j)
    (b : Arrow.mk (deformationOneSquare i).f₂₄ ≅ Arrow.mk (affineLineCylinder.map j))
    (h : (deformationOneSquare i).f₃₄ ≫ b.hom.right =
      a.hom.right ≫ nativeAffineSection (.of k) Y 1) :
    IsIso (effectivePairMotiveMap k (deformationOneSquare i)) :=
  isIso_effectivePairMotiveMap_of_cylinder k (deformationOneSquare i) j 1 a b h

/-- The genuine normal-bundle fibre map on a cylinder chart is the relative zero section. -/
theorem isIso_effectivePairMotiveMap_deformationZero_of_cylinder
    {Z X U Y : Sm(k)} (i : Z ⟶ X) [IsClosedImmersion i.left]
    (j : U ⟶ Y) [IsOpenImmersion j.left]
    (a : Arrow.mk (deformationZeroSquareOfSmooth i).f₁₃ ≅ Arrow.mk j)
    (b : Arrow.mk (deformationZeroSquareOfSmooth i).f₂₄ ≅
      Arrow.mk (affineLineCylinder.map j))
    (h : (deformationZeroSquareOfSmooth i).f₃₄ ≫ b.hom.right =
      a.hom.right ≫ nativeAffineSection (.of k) Y 0) :
    IsIso (effectivePairMotiveMap k (deformationZeroSquareOfSmooth i)) :=
  isIso_effectivePairMotiveMap_of_cylinder k (deformationZeroSquareOfSmooth i) j 0 a b h

section Coordinate

variable (m n : ℕ)

local notation "A" => MvPolynomial (Fin m ⊕ Fin n) k
local notation "B" => MvPolynomial (Fin m) k
local notation "Xc" => affineSite k A
local notation "Zc" => affineSite k B

local notation "ιc" => coordinatePairImmersion k m n

local instance : IsClosedImmersion (ιc).left :=
  coordinateEmbedding_isClosedImmersion k m n

/-- The coordinate deformation is the actual affine cylinder over the base field. -/
@[expose] def coordinateDeformationCylinderOverIso : closedPairDeformation ιc ≅
    affineLineCylinder.obj Xc := by
  refine MorphismProperty.Over.isoMk (coordinateDeformationCylinderIso k m n) ?_
  unfold coordinateDeformationCylinderIso
  change ((coordinateDeformationPolynomialIso k m n).hom ≫
    (lineCylinderIso (k := k) (R := A)).hom.left) ≫ (affineLineCylinder.obj Xc).hom = _
  rw [Category.assoc, MorphismProperty.Over.w (lineCylinderIso (k := k) (R := A)).hom]
  change _ ≫ (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* A))) = _
  rw [← Spec.map_comp]
  exact coordinateDeformationPolynomialIso_over k m n

/-- The extended-Rees deformation of the coordinate centre is its actual affine cylinder. -/
@[expose] def coordinateSupportCylinderOverIso :
    deformationSupport Zc ≅ affineLineCylinder.obj Zc :=
  MorphismProperty.Over.isoMk (coordinateSupportCylinderIso k m) (by
    unfold coordinateSupportCylinderIso
    change ((coordinateSupportPolynomialIso k m).hom ≫
      (lineCylinderIso (k := k) (R := B)).hom.left) ≫ (affineLineCylinder.obj Zc).hom = _
    rw [Category.assoc, MorphismProperty.Over.w (lineCylinderIso (k := k) (R := B)).hom]
    exact coordinateSupportPolynomialIso_over k m)

omit [PerfectField k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)] [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- The cylinder identifications intertwine the original map of closed supports. -/
theorem coordinateSupportCylinderOverIso_comm :
    (deformationSupportInclusion ιc).left ≫
        (coordinateDeformationCylinderOverIso k m n).hom.left =
      (coordinateSupportCylinderOverIso k m).hom.left ≫ (affineLineCylinder.map ιc).left :=
  coordinateDeformationSupportMap_cylinderIso k m n

/-- Compatible identifications of the ambient deformation and its closed support
with cylinders induce the identification of their open complements. -/
def deformationPairCylinderIsoOfMaps {Z X : Sm(k)} (i : Z ⟶ X)
    [IsClosedImmersion i.left] (E : closedPairDeformation i ≅ affineLineCylinder.obj X)
    (e : deformationSupport Z ≅ affineLineCylinder.obj Z)
    (comm : (deformationSupportInclusion i).left ≫ E.hom.left =
      e.hom.left ≫ (affineLineCylinder.map i).left) :
    Arrow.mk (closedPairOpenInclusion (deformationSupportInclusion i).left) ≅
      Arrow.mk (affineLineCylinder.map (closedPairOpenInclusion i.left)) := by
  let j := closedPairOpenInclusion i.left
  have h₀ : IsPullback (deformationSupportInclusion i).left e.hom.left E.hom.left
      (affineLineCylinder.map i).left := by
    have : IsIso E.hom.left := (forgetScheme _).map_isIso E.hom
    have : IsIso e.hom.left := (forgetScheme _).map_isIso e.hom
    exact IsPullback.of_vert_isIso ⟨comm⟩
  let g := affineLineCylinder.map i
  let : IsClosedImmersion g.left :=
    MorphismProperty.of_isPullback (affineLineCylinder_map_isPullback i).flip inferInstance
  let sq := closedPairSquare (f := E.hom) h₀
  let : IsIso sq.f₃₄ := inferInstanceAs (IsIso E.hom)
  let a := openPairArrowIsoOfAmbientIso sq (closedPairSquare_isPullback (f := E.hom) h₀)
  let : IsOpenImmersion (affineLineCylinder.map j).left :=
    MorphismProperty.of_isPullback (affineLineCylinder_map_isPullback j).flip inferInstance
  have hr : Set.range (closedPairOpenInclusion g.left).left =
      Set.range (affineLineCylinder.map j).left := by
    rw [range_closedPairOpenInclusion,
      range_fst_of_cartesian (affineLineCylinder_map_isPullback i),
      range_fst_of_cartesian (affineLineCylinder_map_isPullback j), ← Set.preimage_compl]
    exact congrArg
      (fun W => ((projection (additiveGroupObject (Spec (.of k)))).app X).left ⁻¹' W)
      (range_closedPairOpenInclusion i.left).symm
  exact a ≪≫
    openInclusionArrowIso (closedPairOpenInclusion g.left) (affineLineCylinder.map j) hr

omit [PerfectField k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)] [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- The open-pair cylinder comparison retains the given ambient cylinder map. -/
theorem deformationPairCylinderIsoOfMaps_right {Z X : Sm(k)} (i : Z ⟶ X)
    [IsClosedImmersion i.left] (E : closedPairDeformation i ≅ affineLineCylinder.obj X)
    (e : deformationSupport Z ≅ affineLineCylinder.obj Z)
    (comm : (deformationSupportInclusion i).left ≫ E.hom.left =
      e.hom.left ≫ (affineLineCylinder.map i).left) :
    (deformationPairCylinderIsoOfMaps k i E e comm).hom.right = E.hom := by
  change E.hom ≫ 𝟙 _ = E.hom
  exact Category.comp_id _

/-- The cylinder realizes the actual deformation pair in the coordinate model. -/
def coordinateDeformationPairCylinderIso :
    Arrow.mk (closedPairOpenInclusion (deformationSupportInclusion ιc).left) ≅
      Arrow.mk (affineLineCylinder.map (closedPairOpenInclusion (ιc).left)) :=
  deformationPairCylinderIsoOfMaps k ιc (coordinateDeformationCylinderOverIso k m n)
    (coordinateSupportCylinderOverIso k m) (coordinateSupportCylinderOverIso_comm k m n)

/-- The motive of the coordinate fibre at one maps isomorphically to the
actual deformation pair. -/
theorem isIso_effectivePairMotiveMap_coordinateDeformationOne :
    IsIso (effectivePairMotiveMap k (deformationOneSquare ιc)) := by
  let b := coordinateDeformationPairCylinderIso k m n
  apply isIso_effectivePairMotiveMap_deformationOne_of_cylinder k ιc
    (closedPairOpenInclusion (ιc).left) (Iso.refl _) b
  apply MorphismProperty.Over.Hom.ext
  change closedPairOneSection (ιc).left ≫ (coordinateDeformationCylinderIso k m n).hom =
    (𝟙 (Xc).left) ≫ (nativeAffineSection (.of k) Xc 1).left
  rw [Category.id_comp]
  exact coordinateClosedPairOneSection_cylinderIso k m n

/-- The motive of the coordinate normal-bundle fibre maps isomorphically to
the actual deformation pair, with its original zero section as support. -/
theorem isIso_effectivePairMotiveMap_coordinateDeformationZero :
    IsIso (effectivePairMotiveMap k (deformationZeroSquareOfSmooth ιc)) := by
  let N := normalBundleOfSmooth ιc
  let z := normalBundleZeroSectionOfSmooth ιc
  let : IsClosedImmersion z.left := normalBundleZeroSectionOfSmooth_isClosedImmersion ιc
  let : Smooth (coordinateEmbedding k m n ≫ (Xc).hom) := smooth_closedPair_comp ιc
  let E : N ≅ Xc := MorphismProperty.Over.isoMk (coordinateNormalBundleIso k m n (Xc).hom) (by
    change (coordinateNormalBundleIso k m n (Xc).hom).hom ≫ (Xc).hom =
      Stacks.Conormal.normalBundleToBase (ιc).left ≫ (Zc).hom
    have h := coordinateNormalBundleIso_toBase k m n (Xc).hom
    change (coordinateNormalBundleIso k m n (Xc).hom).hom ≫ (Xc).hom =
      Stacks.Conormal.normalBundleToBase (ιc).left ≫ (ιc).left ≫ (Xc).hom at h
    exact h.trans (congrArg (Stacks.Conormal.normalBundleToBase (ιc).left ≫ ·)
      (MorphismProperty.Over.w ιc)))
  have he : IsIso E.hom.left := (forgetScheme _).map_isIso E.hom
  have h₀ : IsPullback z.left (𝟙 (Zc).left) E.hom.left (ιc).left := by
    apply IsPullback.of_vert_isIso
    exact ⟨(coordinateNormalBundleIso_zeroSection k m n (Xc).hom).trans
      (Category.id_comp (ιc).left).symm⟩
  let sq := closedPairSquare (f := E.hom) h₀
  let : IsIso sq.f₃₄ := inferInstanceAs (IsIso E.hom)
  let a := openPairArrowIsoOfAmbientIso sq (closedPairSquare_isPullback (f := E.hom) h₀)
  let b := coordinateDeformationPairCylinderIso k m n
  apply isIso_effectivePairMotiveMap_deformationZero_of_cylinder k ιc
    (closedPairOpenInclusion (ιc).left) a b
  apply MorphismProperty.Over.Hom.ext
  exact coordinateNormalBundleToDeformation_cylinderIso k m n (Xc).hom

end Coordinate

end AlgebraicGeometry.MotivicHomotopy
