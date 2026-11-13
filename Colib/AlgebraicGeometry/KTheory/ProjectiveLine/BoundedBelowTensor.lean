/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectVectorBundleTensor
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BoundedBelowComparison

/-! # Vector bundle tensor on bounded below perfect complexes

Termwise tensor by a finite locally free sheaf preserves the actual strict lower bound.
This does not assert preservation of flasqueness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

variable {X : Scheme.{u}} (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L]

local instance tensorMonoidal : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategorySheafTensor X.sheaf

local instance tensorAdditive : MonoidalPreadditive X.Modules := by
  let := Abelian.hasFiniteBiproducts (C := X.Modules)
  exact SheafOfModules.monoidalPreadditiveSheafTensor X.sheaf

local instance tensorSymmetric : SymmetricCategory X.Modules :=
  SheafOfModules.symmetricCategorySheafTensor X.sheaf

local notation "T" => (tensorRight L)
local notation "F" => (Functor.mapHomologicalComplex (tensorRight L) (ComplexShape.up ℤ))

set_option maxHeartbeats 1000000 in
-- Comparing the sheaf tensor with its termwise realization unfolds large instances.
/-- Right tensor by a vector bundle preserves perfectness and a strict lower bound. -/
theorem tensorVectorBundleRight_mem (K : Obj X) : objects X ((F).obj K.obj) := by
  obtain ⟨a, ha⟩ := K.property.2
  let := ha
  refine ⟨Complex.isPerfectComplex_tensorRight L K.obj K.property.1, a,
    (CochainComplex.isStrictlyGE_iff _ _).mpr ?_⟩
  intro i hi
  change IsZero ((T).obj (K.obj.X i))
  exact (T).map_isZero (K.obj.isZero_of_isStrictlyGE a i hi)

/-- Literal right tensor with a finite locally free sheaf, with the same term bound. -/
def tensorVectorBundleRight : Obj X ⥤ Obj X :=
  ObjectProperty.lift (objects X) ((objects X).ι ⋙ (F)) (tensorVectorBundleRight_mem L)

instance tensorVectorBundleRight_additive : (tensorVectorBundleRight L).Additive where
  map_add {K L₁ f g} := by
    apply ObjectProperty.hom_ext
    exact (F).map_add (f := f.hom) (g := g.hom)

private theorem tensorVectorBundleRight_shortExact {S : ShortComplex (Obj X)}
    (hS : (S.map (objects X).ι).ShortExact) :
    ((S.map (tensorVectorBundleRight L)).map (objects X).ι).ShortExact := by
  have h : exactFunctor _ _ (T) := by
    change exactFunctor _ _ ((curriedTensor X.Modules).flip.obj L)
    exact Stacks.SheafOfModules.exactFunctor_sheafTensorFlip_of_isFlat X.sheaf L
      (isFlat_of_isFiniteLocallyFree L)
  obtain ⟨hlim, hcolim⟩ := (exactFunctor_iff _).mp h
  let U := S.map (objects X).ι
  change (U.map (F)).ShortExact
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  change ((U.map (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) i)).map (T)).ShortExact
  exact (hS.map_of_exact _).map_of_exact _

/-- Right vector bundle tensor is exact on the bounded below Waldhausen category. -/
theorem tensorVectorBundleRight_exact :
    Waldhausen.IsExact (waldhausen X).cof (waldhausen X).weq (waldhausen X).cof (waldhausen X).weq
      (tensorVectorBundleRight L) := by
  let E : ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
        (objects X))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
        (objects X)) :=
    { toFunctor := tensorVectorBundleRight L
      map_conflation := fun _ hS => tensorVectorBundleRight_shortExact L hS }
  refine { zero := fun h => (tensorVectorBundleRight L).map_isZero h
           cofibration := fun f hf => E.map_inflation f hf
           weak := ?_
           pushout := fun hi hp => E.map_isPushout hi hp }
  intro K K' f hf
  exact (perfectTensorRight_waldhausenExact L).weak ((inclusion X).map f) hf

/-- Right tensor on bounded below complexes agrees with ambient left tensor by the braiding. -/
def tensorVectorBundleRightInclusionIso :
    tensorVectorBundleRight L ⋙ inclusion X ≅ inclusion X ⋙ perfectTensorLeft L :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk
      (P := RingedSpace.IsPerfectComplex (X := X.toRingedSpace))
      ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight L)
        (ComplexShape.up ℤ)).app K.obj).symm)
    (fun {_ _} g => by
      apply ObjectProperty.hom_ext
      exact (NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight L)
        (ComplexShape.up ℤ)).inv.naturality g.hom)

end AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect
