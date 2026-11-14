/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BoundedBelowPullback
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BoundedBelowTensor
public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalCochainSequence
public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalIdealLine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Module
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RepresentativeIndependence
public import StacksFrontier.Topology.Sheaves.Modules.Flat.PullbackTensorExact
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # The projective-line diagonal sequence of bounded-below perfect complexes

The first two terms are perfect by flat pullback and tensor by an invertible
sheaf. The third is perfect by the distinguished triangle of the actual short
exact sequence. The same strict lower bound works for all three terms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ExactCategory
open AlgebraicGeometry.RingedSpace
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect

universe u

attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => Limits.pullback π π
local notation "p₂" => Limits.pullback.snd π π
local notation "S" => projectiveLineDiagonalSequence X
local notation "L" => twistOver 1 X (-1)
local notation "c" => ComplexShape.up ℤ

local instance : Flat (p₂) := inferInstance

local instance : MonoidalCategory (Q).Modules :=
  SheafOfModules.monoidalCategorySheafTensor (Q).sheaf

local instance : MonoidalPreadditive (Q).Modules := by
  let := Abelian.hasFiniteBiproducts (C := (Q).Modules)
  exact SheafOfModules.monoidalPreadditiveSheafTensor (Q).sheaf

/-- The first module of the diagonal sequence is the invertible negative twist. -/
theorem projectiveLineDiagonalFirstModule_isInvertible :
    Stacks.Ample.IsInvertibleModule Q (S).X₁ := by
  let := Stacks.InvertiblePullback.isInvertibleModule_pullback (Limits.pullback.fst π π) L
  let := Stacks.InvertiblePullback.isInvertibleModule_pullback p₂ L
  let : Stacks.Ample.IsInvertibleModule Q (projectiveLineDiagonalNegativeTwist X) :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules Q _ _
  exact Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _
    (projectiveLineDiagonalSequenceFirstIso X)

/-- The middle module of the diagonal sequence is the invertible structure sheaf. -/
theorem projectiveLineDiagonalMiddleModule_isInvertible :
    Stacks.Ample.IsInvertibleModule Q (S).X₂ :=
  Stacks.SheafOfModules.isInvertible_unit _ _

/-- An invertible diagonal term preserves perfectness of the pulled-back coefficient. -/
theorem projectiveLineDiagonalCochainTerm_isPerfect (K : Obj P) (A : (Q).Modules)
    (hA : Stacks.Ample.IsInvertibleModule Q A) :
    IsPerfectComplex (X := (Q).toRingedSpace)
      ((projectiveLineDiagonalCochainTerm X A).obj K.obj) := by
  have : Stacks.Ample.IsInvertibleModule Q A := hA
  let : SheafOfModules.IsFiniteLocallyFree (R := (Q).ringCatSheaf) A :=
    let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := (Q).ringCatSheaf) A 1 :=
      Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Q A
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  exact Complex.isPerfectComplex_tensorLeft A _ ((flatPullback p₂).obj K).property.1

/-- The diagonal quotient is perfect by the distinguished triangle of the coefficient sequence. -/
theorem projectiveLineDiagonalCochainQuotient_isPerfect (K : Obj P) :
    IsPerfectComplex (X := (Q).toRingedSpace)
      (projectiveLineDiagonalCochainSequence X K.obj).X₃ := by
  let h := projectiveLineDiagonalCochainSequence_shortExact X K.obj
  have h₁ := (projectiveLineDiagonalCochainTerm_isPerfect X K (S).X₁
    (projectiveLineDiagonalFirstModule_isInvertible X)).isPerfect
  have h₂ := (projectiveLineDiagonalCochainTerm_isPerfect X K (S).X₂
    (projectiveLineDiagonalMiddleModule_isInvertible X)).isPerfect
  have h₃ := Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
    (DerivedCategory.triangleOfSES h) (DerivedCategory.triangleOfSES_distinguished h) h₁ h₂
  exact isPerfectComplex_of_isPerfect_representation h₃ ⟨Iso.refl _⟩

/-- Tensoring after flat pullback preserves the strict lower bound of the coefficient. -/
theorem projectiveLineDiagonalCochainTerm_boundedBelow (K : Obj P) (A : (Q).Modules) :
    CochainComplex.plus (Q).Modules ((projectiveLineDiagonalCochainTerm X A).obj K.obj) := by
  obtain ⟨a, ha⟩ := K.property.2
  let := ha
  refine ⟨a, (CochainComplex.isStrictlyGE_iff _ _).mpr fun j hj => ?_⟩
  exact ((Stacks.SheafOfModules.Tensor.sheafTensor (Q).sheaf).obj A).map_isZero
    ((pullback p₂).map_isZero (K.obj.isZero_of_isStrictlyGE a j hj))

/-- The actual cochain sequence lifted to the full subcategory of bounded-below perfect
complexes. Its arrows are unchanged. -/
def projectiveLineDiagonalBoundedSequence (K : Obj P) : ShortComplex (Obj Q) := by
  let T := projectiveLineDiagonalCochainSequence X K.obj
  let A : Obj Q := ⟨T.X₁,
    projectiveLineDiagonalCochainTerm_isPerfect X K (S).X₁
      (projectiveLineDiagonalFirstModule_isInvertible X),
    projectiveLineDiagonalCochainTerm_boundedBelow X K (S).X₁⟩
  let B : Obj Q := ⟨T.X₂,
    projectiveLineDiagonalCochainTerm_isPerfect X K (S).X₂
      (projectiveLineDiagonalMiddleModule_isInvertible X),
    projectiveLineDiagonalCochainTerm_boundedBelow X K (S).X₂⟩
  let C : Obj Q := ⟨T.X₃, projectiveLineDiagonalCochainQuotient_isPerfect X K,
    projectiveLineDiagonalCochainTerm_boundedBelow X K (S).X₃⟩
  exact ShortComplex.mk (ObjectProperty.homMk (X := A) (Y := B) T.f)
    (ObjectProperty.homMk (X := B) (Y := C) T.g)
    (by
      apply ObjectProperty.hom_ext
      exact T.zero)

/-- The lifted diagonal sequence is a conflation in the inherited exact structure. -/
theorem projectiveLineDiagonalBoundedSequence_shortExact (K : Obj P) :
    ((projectiveLineDiagonalBoundedSequence X K).map (objects Q).ι).ShortExact :=
  projectiveLineDiagonalCochainSequence_shortExact X K.obj

/-- The bounded-below lift of the degreewise coefficient functor at a fixed module. -/
def projectiveLineDiagonalBoundedTerm (A : (Q).Modules)
    (hA : ∀ K : Obj P, objects Q ((projectiveLineDiagonalCochainTerm X A).obj K.obj)) :
    Obj P ⥤ Obj Q :=
  ObjectProperty.lift (objects Q) ((objects P).ι ⋙ projectiveLineDiagonalCochainTerm X A) hA

instance projectiveLineDiagonalBoundedTerm_additive (A : (Q).Modules)
    (hA : ∀ K : Obj P, objects Q ((projectiveLineDiagonalCochainTerm X A).obj K.obj)) :
    (projectiveLineDiagonalBoundedTerm X A hA).Additive where
  map_add {K J f g} := by
    apply ObjectProperty.hom_ext
    let : ((Stacks.SheafOfModules.Tensor.sheafTensor (Q).sheaf).obj A).Additive :=
      Stacks.Sheaves.ChangeOfRings.additive_sheafTensorObj (Q).sheaf A
    let T := (Stacks.SheafOfModules.Tensor.sheafTensor (Q).sheaf).obj A
    let P₂ := (pullback p₂).mapHomologicalComplex c
    let C := T.mapHomologicalComplex c
    change (C).map ((P₂).map (f.hom + g.hom)) =
      (C).map ((P₂).map f.hom) + (C).map ((P₂).map g.hom)
    rw [(P₂).map_add, (C).map_add]

/-- The actual left term, viewed as a bounded-below perfect coefficient functor. -/
def projectiveLineDiagonalBoundedFirst : Obj P ⥤ Obj Q :=
  projectiveLineDiagonalBoundedTerm X (S).X₁ fun K =>
    ⟨projectiveLineDiagonalCochainTerm_isPerfect X K (S).X₁
        (projectiveLineDiagonalFirstModule_isInvertible X),
      projectiveLineDiagonalCochainTerm_boundedBelow X K (S).X₁⟩

/-- The actual middle term, viewed as a bounded-below perfect coefficient functor. -/
def projectiveLineDiagonalBoundedMiddle : Obj P ⥤ Obj Q :=
  projectiveLineDiagonalBoundedTerm X (S).X₂ fun K =>
    ⟨projectiveLineDiagonalCochainTerm_isPerfect X K (S).X₂
        (projectiveLineDiagonalMiddleModule_isInvertible X),
      projectiveLineDiagonalCochainTerm_boundedBelow X K (S).X₂⟩

/-- The actual quotient term, viewed as a bounded-below perfect coefficient functor. -/
def projectiveLineDiagonalBoundedLast : Obj P ⥤ Obj Q :=
  projectiveLineDiagonalBoundedTerm X (S).X₃ fun K =>
    ⟨projectiveLineDiagonalCochainQuotient_isPerfect X K,
      projectiveLineDiagonalCochainTerm_boundedBelow X K (S).X₃⟩

/-- The actual ideal inclusion on bounded-below perfect complexes. -/
def projectiveLineDiagonalBoundedInclusion :
    projectiveLineDiagonalBoundedFirst X ⟶ projectiveLineDiagonalBoundedMiddle X where
  app K := ObjectProperty.homMk ((projectiveLineDiagonalCochainTermMap X (S).f).app K.obj)
  naturality {_ _} g := by
    apply ObjectProperty.hom_ext
    exact (projectiveLineDiagonalCochainTermMap X (S).f).naturality g.hom

/-- The actual quotient on bounded-below perfect complexes. -/
def projectiveLineDiagonalBoundedQuotient :
    projectiveLineDiagonalBoundedMiddle X ⟶ projectiveLineDiagonalBoundedLast X where
  app K := ObjectProperty.homMk ((projectiveLineDiagonalCochainTermMap X (S).g).app K.obj)
  naturality {_ _} g := by
    apply ObjectProperty.hom_ext
    exact (projectiveLineDiagonalCochainTermMap X (S).g).naturality g.hom

/-- The natural bounded-below inclusion and quotient compose to zero. -/
theorem projectiveLineDiagonalBounded_comp_zero :
    projectiveLineDiagonalBoundedInclusion X ≫ projectiveLineDiagonalBoundedQuotient X = 0 := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact NatTrans.congr_app (projectiveLineDiagonalCochainTermMap_comp_zero X) K.obj

private theorem relativeFlat_of_invertible (A : (Q).Modules)
    (hA : Stacks.Ample.IsInvertibleModule Q A) :
    IsFlatOver (p₂).toLRSHom.toShHom A := by
  have : Stacks.Ample.IsInvertibleModule Q A := hA
  let : SheafOfModules.IsFiniteLocallyFree (R := (Q).ringCatSheaf) A :=
    let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := (Q).ringCatSheaf) A 1 :=
      Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Q A
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  intro x
  let R := (Q).toRingedSpace.presheaf.stalk x
  let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) A.val.presheaf x
  let _ : Module R M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier A.val x
  have h := (SheafOfModules.isFlat_iff_stalk_flat (Q).sheaf A).mp
    (isFlat_of_isFiniteLocallyFree A) x
  have hId : IsFlatOverAt (𝟙 (Q).toRingedSpace) A x := by
    change @Module.Flat R M _ _
      (Module.compHom M (PresheafedSpace.Hom.stalkMap
        (𝟙 (Q).toRingedSpace.toPresheafedSpace) x).hom)
    have hmap : (PresheafedSpace.Hom.stalkMap
        (𝟙 (Q).toRingedSpace.toPresheafedSpace) x).hom = RingHom.id R := by
      change ((𝟙 Q : Q ⟶ Q).stalkMap x).hom = _
      exact congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_id Q x)
    have hmod : (Module.compHom M (RingHom.id R) : Module R M) =
        (inferInstance : Module R M) := by
      apply Module.ext
      funext r m
      rfl
    rw [hmap, hmod]
    exact h
  simpa using IsFlatOverAt.comp (𝟙 (Q).toRingedSpace) (p₂).toLRSHom.toShHom A x hId
    (Flat.stalkMap p₂ x)

/-- A relatively flat diagonal coefficient gives a Waldhausen exact functor on the actual
bounded-below perfect complexes whenever it preserves the object predicate. -/
theorem projectiveLineDiagonalBoundedTerm_exact (A : (Q).Modules)
    (hA : ∀ K : Obj P, objects Q ((projectiveLineDiagonalCochainTerm X A).obj K.obj))
    (hflat : IsFlatOver (p₂).toLRSHom.toShHom A) :
    Waldhausen.IsExact (waldhausen P).cof (waldhausen P).weq
      (waldhausen Q).cof (waldhausen Q).weq (projectiveLineDiagonalBoundedTerm X A hA) := by
  let F := Modules.pullback p₂ ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor (Q).sheaf).obj A
  let G := Stacks.SheafOfModules.pullbackTensorFunctor (p₂).toLRSHom.toShHom A
  let e : F ≅ G := Functor.isoWhiskerLeft (Modules.pullback p₂)
    ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding (Q).sheaf).app A)
  obtain ⟨hG₁, hG₂⟩ := (exactFunctor_iff G).1
    (Stacks.SheafOfModules.pullbackTensorFunctor_exact (p₂).toLRSHom.toShHom A hflat)
  let : PreservesFiniteLimits G := hG₁
  let : PreservesFiniteColimits G := hG₂
  let : ((Stacks.SheafOfModules.Tensor.sheafTensor (Q).sheaf).obj A).Additive :=
    Stacks.Sheaves.ChangeOfRings.additive_sheafTensorObj (Q).sheaf A
  let : F.Additive := by
    dsimp [F]
    infer_instance
  let : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso e.symm
  let : PreservesFiniteColimits F := preservesFiniteColimits_of_natIso e.symm
  let B := projectiveLineDiagonalBoundedTerm X A hA
  let E : ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex (P).Modules ℤ))
        (objects P))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex (Q).Modules ℤ))
        (objects Q)) :=
    { toFunctor := B
      map_conflation := fun U hU => by
        apply HomologicalComplex.shortExact_of_degreewise_shortExact
        intro j
        exact ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hU j).map_of_exact F }
  refine { zero := fun h => B.map_isZero h
           cofibration := fun g hg => E.map_inflation g hg
           weak := ?_
           pushout := fun hi hp => E.map_isPushout hi hp }
  intro K J g hg
  have : QuasiIso g.hom := hg
  exact HomologicalComplex.quasiIso_map_of_preservesHomology g.hom F

/-- The first coefficient functor is exact. -/
theorem projectiveLineDiagonalBoundedFirst_exact :
    Waldhausen.IsExact (waldhausen P).cof (waldhausen P).weq
      (waldhausen Q).cof (waldhausen Q).weq (projectiveLineDiagonalBoundedFirst X) :=
  projectiveLineDiagonalBoundedTerm_exact X _ _
    (relativeFlat_of_invertible X _ (projectiveLineDiagonalFirstModule_isInvertible X))

/-- The middle coefficient functor is exact. -/
theorem projectiveLineDiagonalBoundedMiddle_exact :
    Waldhausen.IsExact (waldhausen P).cof (waldhausen P).weq
      (waldhausen Q).cof (waldhausen Q).weq (projectiveLineDiagonalBoundedMiddle X) :=
  projectiveLineDiagonalBoundedTerm_exact X _ _
    (relativeFlat_of_invertible X _ (projectiveLineDiagonalMiddleModule_isInvertible X))

/-- The quotient coefficient functor is exact by its flatness over the second factor. -/
theorem projectiveLineDiagonalBoundedLast_exact :
    Waldhausen.IsExact (waldhausen P).cof (waldhausen P).weq
      (waldhausen Q).cof (waldhausen Q).weq (projectiveLineDiagonalBoundedLast X) :=
  projectiveLineDiagonalBoundedTerm_exact X _ _ (projectiveLineDiagonalQuotient_isFlatOver X)

end AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect
