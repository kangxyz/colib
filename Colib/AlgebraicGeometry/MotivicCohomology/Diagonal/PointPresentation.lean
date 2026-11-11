/-
Copyright (c) 2026 Motivic Cohomology contributors and Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionPoints
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FinitePointEvaluation
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.TupleFieldChange

/-!
# Evaluation and whole-support presentation of diagonal point cycles

A literal rational tuple graph evaluates to its native Milnor symbol. A general point
is presented by the same tuple over the field of global functions on its original
integral support.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalPointPresentation

open _root_.AlgebraicGeometry.Scheme
open DiagonalCycleSymbols DiagonalPointNorm DiagonalFinitePointEvaluation
open DiagonalCorestriction
open DiagonalFiniteCyclePushforward (torusMap torusMap_isPullback)
open DiagonalReducedPushforward (torusMap_coordinate torusPower_left_hom_ext)
open DiagonalFieldChange (rationalTuple_left_coordinate rationalTuple_left_coordinate_assoc
  affineUnitPoint_scalar)

variable {k : Type u} [Field k] {q : ℕ}

private def unitPullback {T S : Scheme.{u}}
    (f : T ⟶ (SmoothSite.multiplicativeGroupObject S).left) : Γ(T, ⊤)ˣ :=
  Units.map f.appTop.hom.toMonoidHom (multiplicativeGroupBaseChangeCoordinate S)

/-- The actual rational graph evaluates to its ordered Milnor symbol over the base. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/PointNorm.lean:186-240" "adaptation"
  "Evaluation of the actual coefficient-one graph of a rational tuple"]
theorem cycleValue_rationalTuple (a : Fin q → kˣ) :
    cycleValue k q ((Cor.graphFunctor k).map (rationalTuple k q a)) =
      milnorKTupleSymbol a := by
  let A := SmoothSite.base (Spec (.of k))
  let B := SmoothSite.torusPower (Spec (.of k)) q
  let f : A ⟶ B := rationalTuple k q a
  let j : A.left ⟶ pullback A.hom B.hom :=
    correspondenceGraphMap A.hom B.hom f.left (MorphismProperty.Over.w f)
  let : IsClosedImmersion j := isClosedImmersion_correspondenceGraphMap _ _ _ _
  have hj : j ≫ pullback.fst A.hom B.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
    refine (correspondenceGraphMap_fst A.hom B.hom f.left (MorphismProperty.Over.w f)).trans ?_
    change 𝟙 (Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k k))
    simp
  have hc (i : Fin q) : affineCoordinateUnit j i = a i := by
    let τ := (SmoothSite.torusCoordinate (Spec (.of k)) q i).left
    have hsnd : j ≫ pullback.snd A.hom B.hom = f.left :=
      correspondenceGraphMap_snd A.hom B.hom f.left (MorphismProperty.Over.w f)
    have hcoord : j ≫ ambientCoordinate k q i =
        (nativeAffineTorusPoint (𝟙 (Spec (.of k))) (a i)).left := by
      calc
        _ = (j ≫ pullback.snd A.hom B.hom) ≫ τ :=
          (Category.assoc j (pullback.snd A.hom B.hom) τ).symm
        _ = f.left ≫ τ := congrArg (fun g : A.left ⟶ B.left => g ≫ τ) hsnd
        _ = _ := rationalTuple_left_coordinate k q a i
    have hunit := congrArg
      (fun t : Spec (.of k) ⟶ (SmoothSite.multiplicativeGroupObject (Spec (.of k))).left =>
        Units.map (Scheme.ΓSpecIso (.of k)).hom.hom.toMonoidHom (unitPullback t)) hcoord
    exact hunit.trans (nativeAffineTorusPoint_coordinate _ _)
  have hgraph : ((Cor.graphFunctor k).map f).val =
      finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle (Spec (.of k))) := by
    let : IsNoetherian ((𝟭 Scheme).obj A.left) := inferInstanceAs (IsNoetherian (Spec (.of k)))
    let : IsReduced ((𝟭 Scheme).obj A.left) := inferInstanceAs (IsReduced (Spec (.of k)))
    exact (finiteCyclePushforward_fundamentalCycle_graph A.hom B.hom f.left
      (MorphismProperty.Over.w f)).symm
  calc
    _ = milnorKNorm k k q (milnorKTupleSymbol (affineCoordinateUnit j)) :=
      cycleValue_eq_norm_of_finite_fundamental (E := k) j hj _ hgraph
    _ = milnorKNorm k k q (milnorKTupleSymbol a) :=
      congrArg (fun b : Fin q → kˣ => milnorKNorm k k q (milnorKTupleSymbol b)) (funext hc)
    _ = _ := by
      simpa only [Algebra.algebraMap_self, milnorKTransport_id_apply, Module.finrank_self,
        Nat.cast_one, one_zsmul] using norm_restriction k k q (milnorKTupleSymbol a)

private theorem unitPullback_comp {T U S : Scheme.{u}} (f : T ⟶ U)
    (g : U ⟶ (SmoothSite.multiplicativeGroupObject S).left) :
    unitPullback (f ≫ g) = Units.map f.appTop.hom.toMonoidHom (unitPullback g) := by
  apply Units.ext
  change (f ≫ g).appTop (multiplicativeGroupBaseChangeCoordinate S).val =
    f.appTop (g.appTop (multiplicativeGroupBaseChangeCoordinate S).val)
  rw [Scheme.Hom.comp_appTop]
  rfl

private theorem eq_nativeTorusPoint {T S : Scheme.{u}} (p : T ⟶ S)
    {f : T ⟶ (SmoothSite.multiplicativeGroupObject S).left}
    (hf : f ≫ (SmoothSite.multiplicativeGroupObject S).hom = p)
    {v : Γ(T, ⊤)ˣ} (h : unitPullback f = v) : f = (nativeTorusPoint p v).left := by
  let f' : Over.mk p ⟶ Scheme.asOver (multiplicativeGroupBaseChange S) S := Over.homMk f hf
  have he := _root_.AlgebraicGeometry.NativeTorusPolynomial.nativeTorusPoint_recover p f'
  change nativeTorusPoint p (unitPullback f) = f' at he
  rw [h] at he
  exact congrArg (fun t : Over.mk p ⟶ Scheme.asOver (multiplicativeGroupBaseChange S) S =>
    t.left) he.symm

private theorem projectedTuple_toBase {E : Type u} [Field E] [Algebra k E]
    (a : Fin q → Eˣ) :
    ((rationalTuple E q a).left ≫ torusMap (k := k) q) ≫
        (SmoothSite.torusPower (Spec (.of k)) q).hom =
      DiagonalFiniteCyclePushforward.scalarMap (k := k) (E := E) := by
  have hbase : (rationalTuple E q a).left ≫ (SmoothSite.torusPower (Spec (.of E)) q).hom =
      𝟙 (Spec (.of E)) := MorphismProperty.Over.w (rationalTuple E q a)
  rw [Category.assoc, (torusMap_isPullback (k := k) (E := E) q).w, ← Category.assoc, hbase]
  exact Category.id_comp _

private theorem projectedTuple_coordinate {E : Type u} [Field E] [Algebra k E]
    (a : Fin q → Eˣ) (i : Fin q) :
    ((rationalTuple E q a).left ≫ torusMap (k := k) q) ≫
        (SmoothSite.torusCoordinate (Spec (.of k)) q i).left =
      (nativeAffineTorusPoint (DiagonalFiniteCyclePushforward.scalarMap (k := k) (E := E))
        (a i)).left := by
  rw [Category.assoc, torusMap_coordinate, rationalTuple_left_coordinate_assoc,
    affineUnitPoint_scalar]

variable (Z : Generator k q)

private theorem targetProjection_toBase :
    targetProjection Z ≫ (SmoothSite.torusPower (Spec (.of k)) q).hom = projection Z := by
  rw [targetProjection, projection, Category.assoc, ← pullback.condition, Category.comp_id]

private theorem supportIsoSpec_inv_appTop :
    (supportIsoSpec Z).inv.appTop = (Scheme.ΓSpecIso (coordinateRing Z)).inv := by
  apply (cancel_mono (Scheme.ΓSpecIso (coordinateRing Z)).hom).mp
  rw [Iso.inv_hom_id, ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
  change ((supportIsoSpec Z).hom ≫ (supportIsoSpec Z).inv).appTop = _
  rw [Iso.hom_inv_id]
  rfl

private theorem supportIsoSpec_inv_coordinate (i : Fin q) :
    (supportIsoSpec Z).inv ≫ targetProjection Z ≫
        (SmoothSite.torusCoordinate (Spec (.of k)) q i).left =
      (nativeAffineTorusPoint
        (DiagonalFiniteCyclePushforward.scalarMap (k := k) (E := coordinateRing Z))
        (coordinateUnit Z i)).left := by
  let τ := SmoothSite.torusCoordinate (Spec (.of k)) q i
  let t : support Z ⟶ (SmoothSite.multiplicativeGroupObject (Spec (.of k))).left :=
    targetProjection Z ≫ τ.left
  let d := (SmoothSite.multiplicativeGroupObject (Spec (.of k))).hom
  let p := DiagonalFiniteCyclePushforward.scalarMap (k := k) (E := coordinateRing Z)
  have hτ : τ.left ≫ d = (SmoothSite.torusPower (Spec (.of k)) q).hom :=
    MorphismProperty.Over.w τ
  have ht : t ≫ d = projection Z := by
    change (targetProjection Z ≫ τ.left) ≫ d = _
    rw [Category.assoc, hτ, targetProjection_toBase]
  have hbase : ((supportIsoSpec Z).inv ≫ t) ≫ d = p := by
    calc
      _ = (supportIsoSpec Z).inv ≫ t ≫ d := Category.assoc _ _ _
      _ = (supportIsoSpec Z).inv ≫ projection Z := congrArg ((supportIsoSpec Z).inv ≫ ·) ht
      _ = p := supportIsoSpec_inv_projection Z
  change (supportIsoSpec Z).inv ≫ t =
    (nativeTorusPoint p (specGlobalUnit (coordinateUnit Z i))).left
  apply eq_nativeTorusPoint p hbase
  rw [unitPullback_comp]
  change Units.map (supportIsoSpec Z).inv.appTop.hom.toMonoidHom (coordinateUnit Z i) =
    Units.map (Scheme.ΓSpecIso (coordinateRing Z)).inv.hom.toMonoidHom (coordinateUnit Z i)
  rw [supportIsoSpec_inv_appTop]

private theorem supportIsoSpec_inv_targetProjection :
    (supportIsoSpec Z).inv ≫ targetProjection Z =
      (rationalTuple (coordinateRing Z) q (coordinateUnit Z)).left ≫ torusMap (k := k) q := by
  let g := (SmoothSite.torusPower (Spec (.of k)) q).hom
  let p := DiagonalFiniteCyclePushforward.scalarMap (k := k) (E := coordinateRing Z)
  have hbase : ((supportIsoSpec Z).inv ≫ targetProjection Z) ≫ g = p := by
    calc
      _ = (supportIsoSpec Z).inv ≫ targetProjection Z ≫ g := Category.assoc _ _ _
      _ = (supportIsoSpec Z).inv ≫ projection Z :=
        congrArg ((supportIsoSpec Z).inv ≫ ·) (targetProjection_toBase Z)
      _ = p := supportIsoSpec_inv_projection Z
  apply torusPower_left_hom_ext q (hbase.trans (projectedTuple_toBase (coordinateUnit Z)).symm)
  intro i
  exact (Category.assoc _ _ _).trans ((supportIsoSpec_inv_coordinate Z i).trans
    (projectedTuple_coordinate (k := k) (coordinateUnit Z) i).symm)

/-- The canonical affine chart retains the original inclusion with every coordinate. -/
theorem supportIsoSpec_inv_inclusion :
    (supportIsoSpec Z).inv ≫ (integralComponentAt Z.val).subschemeι =
      finitePointMap (k := k) q (rationalTuple (coordinateRing Z) q (coordinateUnit Z)) := by
  let f := rationalTuple (coordinateRing Z) q (coordinateUnit Z)
  apply pullback.hom_ext
  · rw [Category.assoc]
    exact (supportIsoSpec_inv_projection Z).trans (finitePointMap_fst (k := k) q f).symm
  · rw [Category.assoc]
    exact (supportIsoSpec_inv_targetProjection Z).trans (finitePointMap_snd (k := k) q f).symm

/-- The native coefficient-one point is the full pushforward of its support-field graph. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/PointPresentation.lean:114-147" "adaptation"
  "The original native support, projection, coordinates and whole prime coefficient"]
theorem generator_cycle_eq_pointPushforward :
    singleFiniteCorrespondence _ _ Z.val Z.property 1 =
      pointPushforward (k := k) q ((Cor.graphFunctor (coordinateRing Z)).map
        (rationalTuple (coordinateRing Z) q (coordinateUnit Z))) := by
  let : IsNoetherian (support Z) :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (projection Z)
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (projection Z) }
  let e := supportIsoSpec Z
  let i : support Z ⟶ ambient k q := (integralComponentAt Z.val).subschemeι
  let f := rationalTuple (coordinateRing Z) q (coordinateUnit Z)
  let j : Spec (coordinateRing Z) ⟶ ambient k q := finitePointMap (k := k) q f
  let c := AlgebraicCycle.fundamentalCycle (Spec (coordinateRing Z))
  have hi : i (genericPoint (support Z)) = Z.val := genericPointOf_integralComponentAt Z.val
  have hprime := finiteCyclePushforward_fundamentalCycle_integral i
  apply Subtype.ext
  change single Z.val (1 : ℤ) = _
  calc
    _ = single (i (genericPoint (support Z))) 1 := congrArg (fun x => single x (1 : ℤ)) hi.symm
    _ = finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle (support Z)) := hprime.symm
    _ = finiteCyclePushforward i (finiteCyclePushforward e.inv c) :=
      congrArg (finiteCyclePushforward i) (finiteCyclePushforward_fundamentalCycle_iso e.symm).symm
    _ = finiteCyclePushforward (e.inv ≫ i) c := finiteCyclePushforward_comp_apply e.inv i c
    _ = finiteCyclePushforward j c :=
      finiteCyclePushforward_congr_map _ _ (supportIsoSpec_inv_inclusion Z) c
    _ = _ := (pointPushforward_graph_fundamental (k := k) q f).symm

/-- The actual prime class is the corestriction of its support-field tuple graph. -/
theorem cycleClass_generator :
    cycleClass k q (singleFiniteCorrespondence _ _ Z.val Z.property 1) =
      corestriction (k := k) q
        (graphSymbol (coordinateRing Z) q (coordinateUnit Z)) := by
  let f := rationalTuple (coordinateRing Z) q (coordinateUnit Z)
  let α := (Cor.graphFunctor (coordinateRing Z)).map f
  calc
    _ = cycleClass k q (pointPushforward (k := k) q α) :=
      congrArg (cycleClass k q) (generator_cycle_eq_pointPushforward Z)
    _ = _ := (corestriction_cycleClass (k := k) q α).symm

end AlgebraicGeometry.MotivicCohomology.DiagonalPointPresentation
