/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleEvaluation

/-!
# The first right face of the split pullback triple

Source transport uses the scheme composition associator on the actual normalized small
exact map. The whole triangle evaluates to the original binary comparison, without
collapsing either time or excluding level zero.

Adapted from Quillen `BoundedFlat/RightFirstNative.lean` and
`Iterated/SimplexTriangleSourceTransport.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen Convexity
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open scoped Simplicial Topology unitInterval

universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory

private theorem triangle_source_transport {V W : WideSubcategory preservesZero.{u}}
    {F F' G H : V ⟶ W} (e : F = F') (η : F'.hom.toFunctor ⟶ G.hom.toFunctor)
    (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq
      ((eqToHom (congrArg (fun k : V ⟶ W ↦ k.hom.toFunctor) e) ≫ η).app A)) :
    ModelSimplex.triangle (F := F)
        (eqToHom (congrArg (fun k : V ⟶ W ↦ k.hom.toFunctor) e) ≫ η) θ hη' hθ =
      ModelSimplex.triangle η θ hη hθ := by
  subst F'
  simp only [eqToHom_refl, Category.id_comp]

/-- Transport of the first exact map preserves the two-time triangle evaluation. -/
theorem triangle_source_transport_level {V W : WideSubcategory preservesZero.{u}}
    {F F' G H : V ⟶ W} (e : F = F') (η : F'.hom.toFunctor ⟶ G.hom.toFunctor)
    (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq
      ((eqToHom (congrArg (fun k : V ⟶ W ↦ k.hom.toFunctor) e) ≫ η).app A))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumTransformationCompositionHomotopy (F := F)
        (eqToHom (congrArg (fun k : V ⟶ W ↦ k.hom.toFunctor) e) ≫ η) θ hη' hθ).level n
        (r, (s, x)) =
      (prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (r, (s, x)) := by
  rw [← prespectrumSimplexFamily_triangle, triangle_source_transport e η θ hη hθ hη',
    prespectrumSimplexFamily_triangle]

/-- Replacing the first natural transformation by an equal one retains both native times. -/
theorem triangle_congr_first_level {V W : WideSubcategory preservesZero.{u}}
    {F G H : V ⟶ W} (η η' : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq (η'.app A))
    (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A)) (e : η = η')
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (r, (s, x)) =
      (prespectrumTransformationCompositionHomotopy η' θ hη' hθ).level n (r, (s, x)) := by
  subst η'
  rfl

end CategoryTheory.Waldhausen.IteratedS

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectSplitTripleSimplex

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

private theorem whiskering_eqToHom {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    (L : A ⥤ B) (R : C ⥤ D) {F G : B ⥤ C} (e : F = G) :
    whiskerLeft L (whiskerRight (eqToHom e) R) =
      eqToHom (congrArg (fun K ↦ L ⋙ K ⋙ R) e) := by
  subst G
  ext x
  simp

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

private theorem rightFirst_source_eq :
    BoundedFlatPerfectTripleSimplex.source f g h =
      BoundedFlatPerfectBinarySimplex.sourceMap (f ≫ g) h :=
  congrArg (fun k : X ⟶ T ↦ asSmallCategoryMap (W T) (W X)
    (boundedAboveFlatPerfectNormalizedPullback_exact k)
    (boundedAboveFlatPerfectNormalizedPullback_obj_zero k)) (Category.assoc f g h).symm

private theorem rightFirst_hom :
    (rightFirstGeometric f g h).hom =
      eqToHom (congrArg (fun k : asSmallCategory (W T) ⟶ asSmallCategory (W X) ↦
        k.hom.toFunctor) (rightFirst_source_eq f g h)) ≫
        (BoundedFlatPerfectBinarySimplex.first (f ≫ g) h).hom := by
  unfold rightFirstGeometric BoundedFlatPerfectBinarySimplex.first
  simp only [isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.trans_hom, eqToIso.hom,
    whiskerRight_comp, whiskerLeft_comp, whiskering_eqToHom]

/-- The first right face evaluates to the original binary comparison at every level. -/
theorem rightFirst_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n
        (StdSimplex.map (triangleFace 0 4 5 (by decide) (by decide)).toOrderHom
          (TheoremB.compositionTriangleHomotopy (r, s)), x) =
      (boundedAboveFlatPerfectNormalizedCompTrackComparison (f ≫ g) h).level n
        (r, (s, x)) := by
  refine (rightFirst_scalar f g h n r s x).trans ?_
  let e := rightFirst_source_eq f g h
  let η := (BoundedFlatPerfectBinarySimplex.first (f ≫ g) h).hom
  let θ := (BoundedFlatPerfectBinarySimplex.second (f ≫ g) h).hom
  let η' :=
    eqToHom (congrArg (fun k : asSmallCategory (W T) ⟶ asSmallCategory (W X) ↦
      k.hom.toFunctor) e) ≫ η
  have hη' : ∀ A, (W X).asSmall.weq (η'.app A) := by
    intro A
    have hw := (W X).asSmall.weq_iso ((rightFirstGeometric f g h).hom.app A) inferInstance
    rw [rightFirst_hom f g h] at hw
    exact hw
  refine (triangle_congr_first_level (F := BoundedFlatPerfectTripleSimplex.source f g h)
    (G := rightFirstMap f g h) (H := BoundedFlatPerfectTripleSimplex.right f g h)
    (rightFirstGeometric f g h).hom η' θ
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) hη'
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) (rightFirst_hom f g h) n r s x).trans ?_
  refine (triangle_source_transport_level (G := rightFirstMap f g h)
    (H := BoundedFlatPerfectTripleSimplex.right f g h) e η θ
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) hη' n r s x).trans ?_
  exact (BoundedFlatPerfectBinarySimplex.native_apply (f ≫ g) h n r s x).symm

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectSplitTripleSimplex
