/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Basic
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupport
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullbackCoherence

/-!
# Actual bounded-flat supported pullback across arbitrary open squares

The geometric restriction square transports acyclicity. Exactness uses the original
flat quotient in each degree and does not require a flat ambient morphism.

Adapted from Quillen
`Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/PairPullback.lean:42-126`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicGeometry.RingedSpace
open scoped ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual restriction retains boundedness, flatness and perfectness. -/
theorem boundedAboveFlatPerfectComplex_restrict {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {K : CochainComplex X.Modules ℤ}
    (hK : boundedAboveFlatPerfectComplex X.toRingedSpace K) :
    boundedAboveFlatPerfectComplex U.toRingedSpace
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  boundedAboveFlatPerfectComplex_of_iso
    ((NatIso.mapHomologicalComplex (restrictFunctorIsoPullback j)
      (ComplexShape.up ℤ)).app K).symm (boundedAboveFlatPerfectComplex_pullback j hK)

/-- Acyclic bounded-flat complexes remain acyclic under the original arbitrary pullback. -/
theorem acyclic_pullback_of_boundedAboveFlatPerfect {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : CochainComplex Y.Modules ℤ}
    (hK : boundedAboveFlatPerfectComplex Y.toRingedSpace K) (hA : K.Acyclic) :
    (((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  let z : (0 : CochainComplex Y.Modules ℤ) ⟶ K := 0
  have hz : (0 : CochainComplex Y.Modules ℤ).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)
  have hzq : QuasiIso z := (quasiIso_iff z).2 fun n =>
    (quasiIsoAt_iff_exactAt z n (hz n)).2 (hA n)
  have hZ : boundedAboveFlatPerfectComplex Y.toRingedSpace
      (0 : CochainComplex Y.Modules ℤ) :=
    boundedAboveFlatPerfectComplex_of_isZero (isZero_zero _)
  have hpq : QuasiIso (((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map z) :=
    @quasiIso_pullback_of_boundedAboveFlatPerfect X Y f
      (0 : CochainComplex Y.Modules ℤ) K hZ hK z hzq
  intro n
  exact (quasiIsoAt_iff_exactAt
    (((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map z) n
    (HomologicalComplex.acyclic_of_isZero _
      (((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
        (isZero_zero _)) n)).1 ((quasiIso_iff _).1 hpq n)

variable {A B : Scheme.OpenPairs.{u}}

/-- The actual geometric comparison for the supplied commuting square of opens. -/
def pullbackComplexOpenPairIso (f : A ⟶ B) :
    (pullback f.right).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (restrictFunctor A.hom).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (restrictFunctor B.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (pullback f.left).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.isoWhiskerLeft _
      (NatIso.mapHomologicalComplex (restrictFunctorIsoPullback A.hom) (.up ℤ)) ≪≫
    Functor.mapHomologicalComplexCompIso (pullbackComp A.hom f.right) (.up ℤ) ≪≫
    eqToIso (congrArg (fun h => (pullback h).mapHomologicalComplex (.up ℤ))
      (MorphismProperty.Arrow.w f).symm) ≪≫
    (Functor.mapHomologicalComplexCompIso (pullbackComp f.left B.hom) (.up ℤ)).symm ≪≫
    Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (restrictFunctorIsoPullback B.hom) (.up ℤ)).symm _

/-- Pullback preserves actual support by the geometric square and native K-flat acyclicity. -/
theorem boundedAboveFlatPerfectSupported_pairPullback (f : A ⟶ B)
    {K : CochainComplex B.right.Modules ℤ}
    (hK : boundedAboveFlatPerfectSupported B.hom K) :
    boundedAboveFlatPerfectSupported A.hom
      (((pullback f.right).mapHomologicalComplex (.up ℤ)).obj K) := by
  refine ⟨boundedAboveFlatPerfectComplex_pullback f.right hK.1, ?_⟩
  have h := acyclic_pullback_of_boundedAboveFlatPerfect f.left
    (boundedAboveFlatPerfectComplex_restrict B.hom hK.1) hK.2
  intro n
  exact (h n).of_iso ((pullbackComplexOpenPairIso f).app K).symm

/-- The supported functor retains the original pulled-back chain objects and morphisms. -/
def boundedAboveFlatPerfectSupportedPullback (f : A ⟶ B) :
    (boundedAboveFlatPerfectSupported B.hom).FullSubcategory ⥤
      (boundedAboveFlatPerfectSupported A.hom).FullSubcategory :=
  (boundedAboveFlatPerfectSupported A.hom).lift
    ((boundedAboveFlatPerfectSupported B.hom).ι ⋙
      (pullback f.right).mapHomologicalComplex (.up ℤ))
    (fun K => boundedAboveFlatPerfectSupported_pairPullback f K.property)

instance boundedAboveFlatPerfectSupportedPullback_additive (f : A ⟶ B) :
    (boundedAboveFlatPerfectSupportedPullback f).Additive := by
  unfold boundedAboveFlatPerfectSupportedPullback
  infer_instance

/-- The same admissible quotient gives the pulled-back supported conflation degreewise. -/
def boundedAboveFlatPerfectSupportedExactPullback (f : A ⟶ B) :
    ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex B.right.Modules ℤ))
        (boundedAboveFlatPerfectSupported B.hom))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A.right.Modules ℤ))
        (boundedAboveFlatPerfectSupported A.hom)) where
  toFunctor := boundedAboveFlatPerfectSupportedPullback f
  additive := boundedAboveFlatPerfectSupportedPullback_additive f
  map_conflation S hS := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    exact shortExact_pullback_of_flat_quotient f.right
      ((S.map (boundedAboveFlatPerfectSupported B.hom).ι).map
        (HomologicalComplex.eval B.right.Modules (.up ℤ) n))
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hS n)
      (S.X₃.property.1.2.2 n)

/-- Relative quasi-isomorphisms remain weak on the actual restricted pulled-back map. -/
theorem boundedAboveFlatPerfect_pairPullback_quasiIso (f : A ⟶ B)
    {K L : CochainComplex B.right.Modules ℤ}
    (hK : boundedAboveFlatPerfectComplex B.right.toRingedSpace K)
    (hL : boundedAboveFlatPerfectComplex B.right.toRingedSpace L) (p : K ⟶ L)
    [QuasiIso (((restrictFunctor B.hom).mapHomologicalComplex (.up ℤ)).map p)] :
    QuasiIso (((restrictFunctor A.hom).mapHomologicalComplex (.up ℤ)).map
      (((pullback f.right).mapHomologicalComplex (.up ℤ)).map p)) := by
  have : QuasiIso (((pullback f.left).mapHomologicalComplex (.up ℤ)).map
      (((restrictFunctor B.hom).mapHomologicalComplex (.up ℤ)).map p)) :=
    quasiIso_pullback_of_boundedAboveFlatPerfect f.left
      (boundedAboveFlatPerfectComplex_restrict B.hom hK)
      (boundedAboveFlatPerfectComplex_restrict B.hom hL)
      (((restrictFunctor B.hom).mapHomologicalComplex (.up ℤ)).map p)
  let e := pullbackComplexOpenPairIso f
  rw [← quasiIso_iff_comp_right _ (e.hom.app L)]
  change QuasiIso (((pullback f.right).mapHomologicalComplex (.up ℤ) ⋙
    (restrictFunctor A.hom).mapHomologicalComplex (.up ℤ)).map p ≫ e.hom.app L)
  rw [e.hom.naturality p]
  change QuasiIso (e.hom.app K ≫ ((pullback f.left).mapHomologicalComplex (.up ℤ)).map
    (((restrictFunctor B.hom).mapHomologicalComplex (.up ℤ)).map p))
  have : QuasiIso (e.hom.app K) := quasiIso_of_isIso _
  infer_instance

/-- Identity preserves the actual geometric supported functor up to its native pullback iso. -/
def boundedAboveFlatPerfectSupportedPullbackIdIso (A : Scheme.OpenPairs.{u}) :
    boundedAboveFlatPerfectSupportedPullback (𝟙 A) ≅
      𝟭 (boundedAboveFlatPerfectSupported A.hom).FullSubcategory :=
  Functor.fullyFaithfulCancelRight (boundedAboveFlatPerfectSupported A.hom).ι
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectSupported A.hom).ι
      (NatIso.mapHomologicalComplex (pullbackId A.right) (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso A.right.Modules (.up ℤ)))

/-- Composition uses the native pullback comparison on the original chain complexes. -/
def boundedAboveFlatPerfectSupportedPullbackCompIso {C : Scheme.OpenPairs.{u}}
    (f : A ⟶ B) (g : B ⟶ C) :
    boundedAboveFlatPerfectSupportedPullback (f ≫ g) ≅
      boundedAboveFlatPerfectSupportedPullback g ⋙ boundedAboveFlatPerfectSupportedPullback f :=
  Functor.fullyFaithfulCancelRight (boundedAboveFlatPerfectSupported A.hom).ι
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectSupported C.hom).ι
      (Functor.mapHomologicalComplexCompIso (pullbackComp f.right g.right) (.up ℤ)).symm)

end AlgebraicGeometry.Scheme.Modules
