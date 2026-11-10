/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentSquare
public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenDiagramLaurent

/-!
# Changing section weaknesses preserves the original Laurent track

The actual fine-to-coarse maps use identity section functors and the identical chosen zeros.
Their actual coefficient Model square intertwines the same original Laurent automorphism.
Consequently every realized homotopy value, including degree zero, is carried to the coarse
track without reparameterization or an assumed seed compatibility.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Topology CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.AffineOpenPair Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

private theorem identityActionSquare
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F G : C ⥤ D) (η : F ⋙ 𝟭 D ⟶ 𝟭 C ⋙ G) (e : 𝟭 D ≅ 𝟭 D) :
    Functor.whiskerRight (Functor.IdentityAutomorphism.onFunctor F e).hom (𝟭 D) ≫ η =
      η ≫ Functor.whiskerLeft (𝟭 C)
        (Functor.IdentityAutomorphism.onFunctor G e).hom :=
  Functor.IdentityAutomorphism.onFunctor_whisker_square
    F G (𝟭 C) (𝟭 D) η e e (by
      apply NatTrans.ext
      funext X
      rfl)

/-- Original fine-to-coarse Model maps retain the same Laurent coefficient square. -/
theorem boundedAboveFlatAffineSectionOpenLaurentChangeWeakModelSquare (a : Under R) :
    boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion a.right) ≫
        boundedAboveFlatAffineSectionOpenModelMap (inclusion j ((laurentUnderFunctor R).obj a)) =
      boundedAboveFlatAffineSectionOpenModelMap (inclusion j a) ≫
        (boundedAboveFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app a) :=
  (boundedAboveFlatAffineSectionOpenModelTransformation j).naturality
    ((laurentUnderCoefficient R).app a)

/-- The identity section functors preserve the original scalar automorphism literally. -/
theorem boundedAboveFlatAffineSectionOpenLaurentChangeWeakUnitSquare (a : Under R) :
    Functor.whiskerRight (boundedAboveFlatAffineSectionLaurentPullbackUnitIso a.right).hom
        (boundedAboveFlatAffineSectionOpenModelMap
          (inclusion j ((laurentUnderFunctor R).obj a))).hom.toFunctor ≫
        eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
          (boundedAboveFlatAffineSectionOpenLaurentChangeWeakModelSquare j a)) =
      eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
          (boundedAboveFlatAffineSectionOpenLaurentChangeWeakModelSquare j a)) ≫
        Functor.whiskerLeft
          (boundedAboveFlatAffineSectionOpenModelMap (inclusion j a)).hom.toFunctor
          (boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a).hom :=
  identityActionSquare _ _ _ _

/-- Changing weakness preserves every original interval value of the actual Laurent loop. -/
theorem boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy_changeWeak_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj a.right).space n) :
    (boundedAboveFlatAffineSectionOpenPrespectrumMap
        (inclusion j ((laurentUnderFunctor R).obj a))).map n
        ((boundedAboveFlatAffineSectionLaurentUnitHomotopy a.right).level n (t, x)) =
      (boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n
        (t, (boundedAboveFlatAffineSectionOpenPrespectrumMap (inclusion j a)).map n x) :=
  prespectrumIsoHomotopy_square_apply
    (boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion a.right))
    ((boundedAboveFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app a))
    (boundedAboveFlatAffineSectionOpenModelMap (inclusion j a))
    (boundedAboveFlatAffineSectionOpenModelMap (inclusion j ((laurentUnderFunctor R).obj a)))
    (boundedAboveFlatAffineSectionLaurentPullbackUnitIso a.right)
    (boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a)
    (boundedAboveFlatAffineSectionOpenLaurentChangeWeakModelSquare j a)
    (boundedAboveFlatAffineSectionOpenLaurentChangeWeakUnitSquare j a) n t x

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionOpenLaurentChangeWeak.lean:44-82"
  "adaptation" "Actual relative-open section construction with the original maps and weak class"]
  boundedAboveFlatAffineSectionOpenLaurentChangeWeakModelSquare
  boundedAboveFlatAffineSectionOpenLaurentChangeWeakUnitSquare
  boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy_changeWeak_apply

end AlgebraicGeometry.Scheme.Modules
