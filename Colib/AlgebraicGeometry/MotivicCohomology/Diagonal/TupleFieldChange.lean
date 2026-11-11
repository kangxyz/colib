/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CycleSymbols
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.ReducedPushforward

/-!
# Scalar projections of rational torus tuples

Each original affine unit point has the same absolute multiplicative-group
coordinate after changing the torus base. This identifies the actual tuple
maps used in field change and transport across finite-field presentations.

Adapted from `Motivic/Cohomology/Diagonal/FieldChange.lean:43-57` and
`Motivic/Cohomology/Diagonal/CorestrictionPresentationTransport.lean:39-82`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalFieldChange

open _root_.AlgebraicGeometry.Scheme SmoothSite
open DiagonalCycleSymbols (rationalTuple rationalTuple_coordinate)
open DiagonalFiniteCyclePushforward (scalarMap multiplicativeGroupMap torusMap torusMap_isPullback)
open DiagonalReducedPushforward (torusMap_coordinate torusPower_left_hom_ext)

/-- Projection of the native affine unit point retains the unit over the original base. -/
theorem affineUnitPoint_scalar {k E : Type u} [Field k] [Field E] [Algebra k E] (a : Eˣ) :
    (nativeAffineTorusPoint (𝟙 (Spec (.of E))) a).left ≫
      multiplicativeGroupMap (k := k) (E := E) =
    (nativeAffineTorusPoint (scalarMap (k := k) (E := E)) a).left := by
  let p := multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ))
  let b (S : Scheme.{u}) := specULiftZIsTerminal.from S
  have hfst : multiplicativeGroupMap (k := k) (E := E) ≫ pullback.fst p (b (Spec (.of k))) =
      pullback.fst p (b (Spec (.of E))) := pullback.lift_fst _ _ _
  have hcoord {S : Scheme.{u}} (f : Spec (.of E) ⟶ S) :
      (nativeAffineTorusPoint f a).left ≫ pullback.fst p (b S) =
        (unitsOfGlobalSectionsCanonicalRepresentation.homEquiv
          (X := Spec (.of E))).symm (specGlobalUnit a) := by
    let e := unitsOfGlobalSectionsCanonicalRepresentation.homEquiv (X := Spec (.of E))
    apply e.injective
    have h : e ((nativeAffineTorusPoint f a).left ≫ pullback.fst p (b S)) =
        specGlobalUnit a := nativeTorusPoint_represents f (specGlobalUnit a)
    exact h.trans (e.apply_symm_apply _).symm
  apply pullback.hom_ext (f := p) (g := b (Spec (.of k)))
  · simp only [Category.assoc, hfst, hcoord]
  · have hsnd : multiplicativeGroupMap (k := k) (E := E) ≫ pullback.snd p (b (Spec (.of k))) =
        pullback.snd p (b (Spec (.of E))) ≫ scalarMap (k := k) (E := E) :=
      pullback.lift_snd _ _ _
    simp only [Category.assoc, hsnd]
    change (nativeAffineTorusPoint (𝟙 (Spec (.of E))) a).left ≫
        (multiplicativeGroupBaseChange (Spec (.of E)) ↘ Spec (.of E)) ≫
        scalarMap (k := k) (E := E) =
      (nativeAffineTorusPoint (scalarMap (k := k) (E := E)) a).left ≫
        (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))
    rw [← Category.assoc, NativeTorusPolynomial.affineUnitPoint_over,
      NativeTorusPolynomial.affineUnitPoint_over]
    exact Category.id_comp _

/-- Every underlying scheme coordinate is the native point of the specified unit. -/
@[reassoc]
theorem rationalTuple_left_coordinate (k : Type u) [Field k]
    (q : ℕ) (a : Fin q → kˣ) (i : Fin q) :
    (rationalTuple k q a).left ≫ (torusCoordinate (Spec (.of k)) q i).left =
      (nativeAffineTorusPoint (𝟙 (Spec (.of k))) (a i)).left :=
  congrArg (fun f => f.left) (rationalTuple_coordinate k q a i)

@[reassoc]
private theorem rationalTuple_structure (k : Type u) [Field k]
    (q : ℕ) (a : Fin q → kˣ) :
    (rationalTuple k q a).left ≫ (torusPower (Spec (.of k)) q).hom = 𝟙 (Spec (.of k)) :=
  MorphismProperty.Over.w (rationalTuple k q a)

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- The changed tuple and its original tuple have the same actual scalar projection. -/
theorem rationalTuple_scalar (q : ℕ) (a : Fin q → kˣ) :
    (rationalTuple E q (fun i => Units.map (algebraMap k E).toMonoidHom (a i))).left ≫
        torusMap (k := k) (E := E) q =
      scalarMap (k := k) (E := E) ≫ (rationalTuple k q a).left := by
  apply torusPower_left_hom_ext q
  · simp only [Category.assoc, (torusMap_isPullback q).w, rationalTuple_structure,
      rationalTuple_structure_assoc, Category.comp_id]
    exact Category.id_comp _
  · intro i
    rw [Category.assoc, torusMap_coordinate, rationalTuple_left_coordinate_assoc,
      affineUnitPoint_scalar, Category.assoc, rationalTuple_left_coordinate]
    let s := scalarMap (k := k) (E := E)
    let b := Units.map (algebraMap k E).toMonoidHom (a i)
    let lift : (Spec (.of E) ⟶ Spec (.of k)) →
        (Spec (.of E) ⟶ (multiplicativeGroupObject (Spec (.of k))).left) :=
      fun f => (nativeAffineTorusPoint f b).left
    change lift s = s ≫ (nativeAffineTorusPoint (𝟙 (Spec (.of k))) (a i)).left
    calc
      lift s = lift (s ≫ 𝟙 _) := congrArg lift (Category.comp_id s).symm
      _ = _ := nativeAffineTorusPoint_natural (𝟙 (Spec (.of k))) (algebraMap k E) (a i)

variable {F : Type u} [Field F] [Algebra k F]

/-- A map of extension fields preserves every original tuple coordinate over the base. -/
theorem rationalTuple_algHom (φ : E →ₐ[k] F) (q : ℕ) (a : Fin q → Eˣ) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      (rationalTuple E q a).left ≫ torusMap (k := k) (E := E) q =
    (rationalTuple F q (fun i => Units.map φ.toRingHom.toMonoidHom (a i))).left ≫
      torusMap (k := k) (E := F) q := by
  have hφ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ scalarMap (k := k) (E := E) =
      scalarMap (k := k) (E := F) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact φ.commutes r
  apply torusPower_left_hom_ext q
  · simp only [Category.assoc, (torusMap_isPullback q).w, rationalTuple_structure_assoc]
    exact (congrArg (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ·)
      (Category.id_comp (scalarMap (k := k) (E := E)))).trans
        (hφ.trans (Category.id_comp (scalarMap (k := k) (E := F))).symm)
  · intro i
    simp only [Category.assoc, torusMap_coordinate, rationalTuple_left_coordinate_assoc,
      affineUnitPoint_scalar]
    rw [← nativeAffineTorusPoint_natural, hφ]

end AlgebraicGeometry.MotivicCohomology.DiagonalFieldChange
