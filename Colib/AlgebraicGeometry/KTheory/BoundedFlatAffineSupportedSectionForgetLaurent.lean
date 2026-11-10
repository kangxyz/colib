/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.LaurentInclusionSquare
public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetModel
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionDiagramLaurent
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionLaurentHomotopy

/-!
# Forgetting support preserves the whole original Laurent-unit loop

The actual scalar forget identity gives the automorphism square of the unchanged coefficient
Model arrows. Its realized square preserves every level and interval value of the original
Laurent track. The specified fixed pullbacks and original Laurent coordinate remain explicit.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.AffineOpenPair Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

attribute [local irreducible] boundedAboveFlatAffineSupportedSectionUnitIso
  boundedAboveFlatAffineSectionUnitIso boundedAboveFlatAffineOriginalEvaluation

/-- The original target scalar action commutes literally with forgetting support. -/
theorem boundedAboveFlatAffineSupportedSectionUnitIso_forget (r : (Γ(Spec R, ⊤))ˣ) :
    Functor.whiskerRight (boundedAboveFlatAffineSupportedSectionUnitIso j r).hom
        (boundedAboveFlatAffineSectionSupported j).ι =
      Functor.whiskerLeft (boundedAboveFlatAffineSectionSupported j).ι
        (boundedAboveFlatAffineSectionUnitIso R r).hom :=
  Functor.IdentityAutomorphism.whisker_hom_eq_of_evaluation
    (boundedAboveFlatAffineSectionSupported j).ι (𝟭 _)
    (boundedAboveFlatAffineSectionSupported j).ι rfl
    (boundedAboveFlatAffineSupportedSectionUnitIso j r)
    (boundedAboveFlatAffineSectionUnitIso R r) (boundedAboveFlatAffineSectionUnitIso R r)
    (boundedAboveFlatAffineSupportedSectionUnitIso_hom j r) (fun _ ↦ rfl)

/-- The exact original Laurent Model coefficient square commutes with the actual inclusion. -/
theorem boundedAboveFlatAffineSupportedDiagramLaurentForgetModelSquare (a : Under R) :
    (boundedAboveFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderCoefficient R).app a) ≫
        boundedAboveFlatAffineSupportedSectionForgetModelMap
          (inclusion j ((laurentUnderFunctor R).obj a)) =
      boundedAboveFlatAffineSupportedSectionForgetModelMap (inclusion j a) ≫
        boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion a.right) :=
  (boundedAboveFlatAffineSupportedSectionForgetModelTransformation j).naturality
    ((laurentUnderCoefficient R).app a)

/-- The actual forget square intertwines the original forward Laurent automorphisms. -/
theorem boundedAboveFlatAffineSupportedDiagramLaurentForgetUnitSquare (a : Under R) :
    Functor.whiskerRight (boundedAboveFlatAffineSupportedDiagramLaurentPullbackUnitIso j a).hom
        (boundedAboveFlatAffineSupportedSectionForgetModelMap
          (inclusion j ((laurentUnderFunctor R).obj a))).hom.toFunctor ≫
        eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
          (boundedAboveFlatAffineSupportedDiagramLaurentForgetModelSquare j a)) =
      eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
          (boundedAboveFlatAffineSupportedDiagramLaurentForgetModelSquare j a)) ≫
        Functor.whiskerLeft
          (boundedAboveFlatAffineSupportedSectionForgetModelMap (inclusion j a)).hom.toFunctor
          (boundedAboveFlatAffineSectionLaurentPullbackUnitIso a.right).hom :=
  Functor.IdentityAutomorphism.onFunctor_whisker_square
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).hom.toFunctor
    (boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion a.right)).hom.toFunctor
    (boundedAboveFlatAffineSupportedSectionForgetModelMap (inclusion j a)).hom.toFunctor
    (boundedAboveFlatAffineSupportedSectionForgetModelMap
      (inclusion j ((laurentUnderFunctor R).obj a))).hom.toFunctor
    (eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
      (boundedAboveFlatAffineSupportedDiagramLaurentForgetModelSquare j a)))
    (boundedAboveFlatAffineSupportedSectionUnitIso
      (inclusion j ((laurentUnderFunctor R).obj a)) (laurentCoordinate a.right))
    (boundedAboveFlatAffineSectionLaurentUnitIso a.right)
    (boundedAboveFlatAffineSupportedSectionUnitIso_forget
      (inclusion j ((laurentUnderFunctor R).obj a))
      (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentCoordinate a.right))

/-- Forgetting support retains every original time value of the realized Laurent action. -/
theorem boundedAboveFlatAffineSupportedDiagramLaurentHomotopy_forget_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap
        (inclusion j ((laurentUnderFunctor R).obj a))).map n
        ((boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedAboveFlatAffineSectionLaurentUnitHomotopy a.right).level n
        (t, (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a)).map n x) :=
  prespectrumIsoHomotopy_square_apply
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderCoefficient R).app a))
    (boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion a.right))
    (boundedAboveFlatAffineSupportedSectionForgetModelMap (inclusion j a))
    (boundedAboveFlatAffineSupportedSectionForgetModelMap
      (inclusion j ((laurentUnderFunctor R).obj a)))
    (boundedAboveFlatAffineSupportedDiagramLaurentPullbackUnitIso j a)
    (boundedAboveFlatAffineSectionLaurentPullbackUnitIso a.right)
    (boundedAboveFlatAffineSupportedDiagramLaurentForgetModelSquare j a)
    (boundedAboveFlatAffineSupportedDiagramLaurentForgetUnitSquare j a) n t x

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SupportedSectionForgetLaurent.lean:38-94"
  "adaptation" "Actual support-forgetting unit square and unchanged Laurent loop at every level"]
  boundedAboveFlatAffineSupportedSectionUnitIso_forget
  boundedAboveFlatAffineSupportedDiagramLaurentForgetModelSquare
  boundedAboveFlatAffineSupportedDiagramLaurentForgetUnitSquare
  boundedAboveFlatAffineSupportedDiagramLaurentHomotopy_forget_apply

end AlgebraicGeometry.Scheme.Modules
