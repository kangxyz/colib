/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientRestriction
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationEquivalence


/-! # Stable equivalences of the actual three auxiliary coefficient comparisons -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection

/-- Original supported coefficient restriction is stable with its actual forward Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientEquivalence.lean:26"
  "adaptation" "Actual original three auxiliary Spec maps and finite stable comparisons"]
theorem supportedRestriction_stable (R : CommRingCat.{u}) (c : Index R)
    {U : Scheme.{u}} (j : U ⟶ space c) [IsOpenImmersion j] :
    IsStableEquivalence (prespectrumMap (supportedRestrictionModel R c j)) := by
  let e := (supportedRestriction R c j).asEquivalence
  have h := ExactModelEquivalence.isStableEquivalence
    (V := boundedAboveFlatGlobalSupportedSectionModel (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j)
    (W := boundedAboveFlatCoefficientSupportedSectionModel j) e
    (supportedRestrictionModel R c j).hom.isExact
    (supportedRestriction_inverse_exact R c j) (supportedRestrictionModel R c j).property
  exact h

/-- The actual ambient component is stable, using its pair iso and original exact inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientEquivalence.lean:39"
  "adaptation" "Actual original three auxiliary Spec maps and finite stable comparisons"]
theorem ambientComponent_stable
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (prespectrumMap (ambientComponent Q T a)) := by
  change IsStableEquivalence (prespectrumFunctor.map
    (pairSupported.map (parameterSupportPairIso Q T a).hom.op ≫
      supportedRestrictionModel _ (op Q, a) (boundedAboveFlatCoefficientSupportOpen Q T a).ι))
  rw [CategoryTheory.Functor.map_comp]
  apply IsStableEquivalence.comp
  · intro d
    infer_instance
  · exact supportedRestriction_stable _ _ _

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The fiber comparison remains stable through the original union-support equality. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientEquivalence.lean:56"
  "adaptation" "Actual original three auxiliary Spec maps and finite stable comparisons"]
theorem fiberComponent_stable (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (prespectrumMap (fiberComponent f T a)) := by
  change IsStableEquivalence (prespectrumFunctor.map
    (ambientComponent Q (T ⊔ f.left.opensRange) a ≫ eqToHom (fiberModel_eq f T a)))
  rw [CategoryTheory.Functor.map_comp]
  apply (ambientComponent_stable Q (T ⊔ f.left.opensRange) a).comp
  intro d
  infer_instance

omit [IsOpenImmersion f.left] in
/-- The full-open comparison remains stable through the actual preimage-support equality. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientEquivalence.lean:67"
  "adaptation" "Actual original three auxiliary Spec maps and finite stable comparisons"]
theorem openComponent_stable (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (prespectrumMap (openComponent f T a)) := by
  change IsStableEquivalence (prespectrumFunctor.map
    (ambientComponent P (f.left ⁻¹ᵁ T) a ≫ eqToHom (openModel_eq f T a)))
  rw [CategoryTheory.Functor.map_comp]
  apply (ambientComponent_stable P (f.left ⁻¹ᵁ T) a).comp
  intro d
  infer_instance

/-- Every finite Bass iterate of the actual fiber comparison is stable. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientEquivalence.lean:77"
  "adaptation" "Actual original three auxiliary Spec maps and finite stable comparisons"]
theorem fiberComparison_iterate_stable
    (S : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤
      Arrow (Arrow (Under (CommRingCat.of (ULift.{u} ℤ)))))
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (((strictDiagramIterate S i).map
      (Functor.whiskerRight (fiberComparison f T) prespectrumFunctor)).app a) := by
  exact modelDiagramIterate_map_isStableEquivalence S i
    (specUnder ⋙ ParameterAuxiliarySupport.fiber f.left T)
    (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T)
    (Functor.whiskerRight (fiberComparison f T) prespectrumFunctor)
    (fiberComponent_stable f T) a

/-- Every finite Bass iterate of the actual ambient comparison is stable. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientEquivalence.lean:90"
  "adaptation" "Actual original three auxiliary Spec maps and finite stable comparisons"]
theorem ambientComparison_iterate_stable
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)
    (S : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤
      Arrow (Arrow (Under (CommRingCat.of (ULift.{u} ℤ)))))
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (((strictDiagramIterate S i).map
      (Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor)).app a) := by
  exact modelDiagramIterate_map_isStableEquivalence S i
    (specUnder ⋙ ParameterAuxiliarySupport.ambient T)
    (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T)
    (Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor)
    (ambientComponent_stable Q T) a

omit [IsOpenImmersion f.left] in
/-- Every finite Bass iterate of the actual full-open comparison is stable. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientEquivalence.lean:105"
  "adaptation" "Actual original three auxiliary Spec maps and finite stable comparisons"]
theorem openComparison_iterate_stable
    (S : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤
      Arrow (Arrow (Under (CommRingCat.of (ULift.{u} ℤ)))))
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (((strictDiagramIterate S i).map
      (Functor.whiskerRight (openComparison f T) prespectrumFunctor)).app a) := by
  exact modelDiagramIterate_map_isStableEquivalence S i
    (specUnder ⋙ ParameterAuxiliarySupport.openModel f.left T)
    (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T)
    (Functor.whiskerRight (openComparison f T) prespectrumFunctor)
    (openComponent_stable f T) a

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
