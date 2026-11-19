/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.EtaleNativeParameterExtension
public import Colib.Algebra.Homology.SignedParameterTransport

/-! # Native signed topology transport of the original parameter arrow

The source and target are the ordinary cochains at weights `-q` and `-(q+1)`.
The comparison retains the shift and topology maps without identifying these
cochains with a motivic model or a tensor construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]
/-- The signed endpoint retains the native topology/shift comparison. -/
def reducedTorusEtaleTopologySignedIso (q : ℕ) :
    (((SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k)) AddCommGrpCat.{u +
        1}).mapHomologicalComplex (.up ℤ))).obj (reducedTorusNisnevichOrdinarySigned k q) ≅
        reducedTorusEtaleOrdinarySigned k q :=
  ((((SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k)) AddCommGrpCat.{u +
      1}).mapHomologicalComplex (.up ℤ))).commShiftIso (-(q : ℤ))).app
      (reducedTorusNisnevichOrdinaryCochain k q) ≪≫
    (shiftFunctor _ (-(q : ℤ))).mapIso (reducedTorusEtaleTopologyCochainIso k q)

/-- Native signed transport uses the actual one-way topology target comparison. -/
theorem reducedTorusEtaleTopologySignedTransport (q : ℕ) :
    (((SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k)) AddCommGrpCat.{u +
        1}).mapHomologicalComplex (.up ℤ))).map (reducedTorusNisnevichParameterSigned k q) ≫
      ((SmoothSite.parameterChangeOfTopologyComplexComparison (Spec (CommRingCat.of k))
          (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1}
          (.up ℤ))).app ((reducedTorusNisnevichOrdinarySigned k (q + 1))⟦(1 : ℤ)⟧) ≫
      (((reducedTorusEtaleParameterFunctor k).mapHomologicalComplex (.up ℤ))).map
          (((((SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k)) AddCommGrpCat.{u +
          1}).mapHomologicalComplex (.up ℤ))).commShiftIso (1 : ℤ)).hom.app
        (reducedTorusNisnevichOrdinarySigned k (q + 1))) =
    signedParameterArrow ((reducedTorusEtaleParameterFunctor k).mapHomologicalComplex (.up ℤ))
        (reducedTorusEtaleParameterCochain k q)
      (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) (by omega)
      (reducedTorusEtaleTopologySignedIso k q)
      (reducedTorusEtaleTopologySignedIso k (q + 1)) := by
  let N := reducedTorusNisnevichOrdinaryCochain k (q + 1)
  have ht : ((SmoothSite.parameterChangeOfTopologyComplexComparison (Spec (CommRingCat.of k))
      (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} (.up
      ℤ))).app N = (NatTrans.mapHomologicalComplex
      (SmoothSite.parameterNisnevichToEtaleComparison (Spec (CommRingCat.of k)) AddCommGrpCat.{u +
          1} (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))) (.up ℤ)).app N := by
    apply HomologicalComplex.hom_ext
    intro i
    exact SmoothSite.parameterChangeOfTopologyComplexComparison_app_f
      (Spec (CommRingCat.of k)) (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))
          AddCommGrpCat.{u + 1} (.up ℤ) N i
  have hext : (((SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k)) AddCommGrpCat.{u +
      1}).mapHomologicalComplex (.up ℤ))).map (reducedTorusNisnevichParameterCochain k q) ≫
      ((SmoothSite.parameterChangeOfTopologyComplexComparison (Spec (CommRingCat.of k))
          (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1}
          (.up ℤ))).app N ≫ (((reducedTorusEtaleParameterFunctor k).mapHomologicalComplex (.up
          ℤ))).map (reducedTorusEtaleTopologyCochainIso k (q + 1)).hom =
    (reducedTorusEtaleTopologyCochainIso k q).hom ≫ reducedTorusEtaleParameterCochain k q := by
    rw [ht]
    exact reducedTorusEtaleTopologyCochainSquare k q
  simpa only [reducedTorusNisnevichParameterSigned, reducedTorusEtaleTopologySignedIso,
    Functor.mapIso_refl, Iso.refl_trans] using
    (signedParameterArrow_transport ((SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k))
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)) ((torusParameterSheafFunctor
        k).mapHomologicalComplex (.up ℤ)) ((reducedTorusEtaleParameterFunctor
        k).mapHomologicalComplex (.up ℤ)) (SmoothSite.parameterChangeOfTopologyComplexComparison
        (Spec (CommRingCat.of k)) (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))
        AddCommGrpCat.{u + 1} (.up ℤ))
      (reducedTorusNisnevichParameterCochain k q) (reducedTorusEtaleParameterCochain k q)
      (reducedTorusEtaleTopologyCochainIso k q)
      (reducedTorusEtaleTopologyCochainIso k (q + 1)) hext
      (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) (by omega) (Iso.refl _) (Iso.refl _))

end AlgebraicGeometry.PresheafWithTransfers
