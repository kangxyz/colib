/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalOpenPairDiagram
public import Colib.KTheory.Waldhausen.Iterated.DiagramZeroNull

/-! # The original selected-zero null for genuine global open-pair Models -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection

/-- Actual supported sections have acyclic original evaluation after geometric restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenPairNull.lean:23-31"
  "adaptation" "All-scheme evaluated support, weak zero arrow and reversed whole null track"]
theorem pairRestriction_acyclic (A : Scheme.OpenPairs.{u})
    (S : (boundedAboveFlatGlobalSectionSupported (X := op A.right) A.hom).FullSubcategory) :
    (((boundedAboveFlatGlobalSectionEvaluation (op A.left)).obj
      ((boundedAboveFlatGlobalSectionModelFunctor.map A.hom.op).hom.toFunctor.obj
        S.obj)).obj).Acyclic := by
  let e := (NatIso.mapHomologicalComplex (restrictFunctorIsoPullback A.hom) (ComplexShape.up ℤ)).app
      (((boundedAboveFlatGlobalSectionEvaluation (op A.right)).obj S.obj).obj) ≪≫
    (boundedAboveFlatPerfectComplex A.left.toRingedSpace).ι.mapIso
      ((boundedAboveFlatGlobalEvaluationPullbackIso A.hom).app S.obj)
  intro n
  exact (S.property n).of_iso e

/-- The unique map from the unchanged original global zero to supported inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenPairNull.lean:34-39"
  "adaptation" "All-scheme evaluated support, weak zero arrow and reversed whole null track"]
def pairZeroToOpen (A : Scheme.OpenPairs.{u}ᵒᵖ) :
    (zeroHom (pairSupported.obj A) (pairOpen.obj A)).hom.toFunctor ⟶
      (pairForget.app A ≫ pairChangeWeak.app A).hom.toFunctor where
  app S := (pairOpen.obj A).obj.waldhausen.isZero.to_
    ((pairForget.app A ≫ pairChangeWeak.app A).hom.toFunctor.obj S)
  naturality _ _ _ := (pairOpen.obj A).obj.waldhausen.isZero.eq_of_src _ _

/-- The original zero-to-inclusion map is weak for actual geometric open detection. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenPairNull.lean:42-55"
  "adaptation" "All-scheme evaluated support, weak zero arrow and reversed whole null track"]
theorem pairZeroToOpen_weak (A : Scheme.OpenPairs.{u}ᵒᵖ) (S : (pairSupported.obj A).obj.Obj) :
    (pairOpen.obj A).obj.waldhausen.weq ((pairZeroToOpen A).app S) := by
  apply (Structure.withInverseImageWeak_weq_iff (pairRestriction.app A).hom.isExact _).mpr
  have hZ : IsZero (((boundedAboveFlatGlobalSectionEvaluation (op A.unop.left)).obj
      ((pairRestriction.app A).hom.toFunctor.obj (pairAmbient.obj A).obj.waldhausen.zero)).obj) :=
    (boundedAboveFlatPerfectComplex A.unop.left.toRingedSpace).ι.map_isZero
      ((boundedAboveFlatGlobalSectionEvaluation_exact (op A.unop.left)).zero
        ((pairRestriction.app A).hom.isExact.zero (pairAmbient.obj A).obj.waldhausen.isZero))
  change QuasiIso ((boundedAboveFlatGlobalSectionEvaluation (op A.unop.left)).map
    ((pairRestriction.app A).hom.toFunctor.map ((pairZeroToOpen A).app S))).hom
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt _ n
    (HomologicalComplex.acyclic_of_isZero _ hZ n)).mpr (pairRestriction_acyclic A.unop S n)

/-- Reverse the same original weak zero-to-inclusion realization, at every open pair. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenPairNull.lean:58-62"
  "adaptation" "All-scheme evaluated support, weak zero arrow and reversed whole null track"]
def pairSupportedOpenNull :
    DiagramNullHomotopy (Functor.whiskerRight pairForget prespectrumFunctor)
      (Functor.whiskerRight pairChangeWeak prespectrumFunctor) :=
  modelDiagramZeroNull (C := pairSupported) (F := pairAmbient) (G := pairOpen)
    pairForget pairChangeWeak pairZeroToOpen pairZeroToOpen_weak

namespace ParameterModels
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The same original zero transformation on the actual parameter pair. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenPairNull.lean:68-71"
  "adaptation" "All-scheme evaluated support, weak zero arrow and reversed whole null track"]
def zeroToOpen (X : Scheme.{u}ᵒᵖ) :
    (zeroHom ((supported f).obj X) ((openModel f).obj X)).hom.toFunctor ⟶
      ((forget f).app X ≫ (changeWeak f).app X).hom.toFunctor :=
  pairZeroToOpen (op (GlobalSupportedParameter.pair f X.unop))

/-- Actual geometric support proves weak zero-to-inclusion at every parameter. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenPairNull.lean:74-76"
  "adaptation" "All-scheme evaluated support, weak zero arrow and reversed whole null track"]
theorem zeroToOpen_weak (X : Scheme.{u}ᵒᵖ) (S : ((supported f).obj X).obj.Obj) :
    ((openModel f).obj X).obj.waldhausen.weq ((zeroToOpen f X).app S) :=
  pairZeroToOpen_weak (op (GlobalSupportedParameter.pair f X.unop)) S

/-- The original reversed weak-zero realization on the complete scheme-parameter diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenPairNull.lean:79-83"
  "adaptation" "All-scheme evaluated support, weak zero arrow and reversed whole null track"]
def supportedOpenNull :
    DiagramNullHomotopy (Functor.whiskerRight (forget f) prespectrumFunctor)
      (Functor.whiskerRight (changeWeak f) prespectrumFunctor) :=
  modelDiagramZeroNull (C := supported f) (F := ambient Q) (G := openModel f)
    (forget f) (changeWeak f) (zeroToOpen f) (zeroToOpen_weak f)

end ParameterModels
end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
