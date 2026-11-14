/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSectionEvaluationNaturality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientBassTelescope
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula

/-!
# Connective groups of the original coefficient spectra

The comparison uses the actual section evaluation, the bounded-flat inclusion,
and the original stable homotopy description of connective K-groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Topology.LoopPrespectrum

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] Waldhausen.Additivity.KCommGroup

/-- Perfect K-groups in additive notation, with the original derived pullbacks. -/
def connectivePerfectKFunctor (n : ℕ) :
    QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  let F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ CommGrpCat.{u + 1} :=
    { obj X := .of ((perfectComplexesWaldhausen X.unop.obj.toRingedSpace).K n)
      map f := CommGrpCat.ofHom (perfectKPullback f.unop.hom n)
      map_id X := by apply CommGrpCat.hom_ext; exact perfectKPullback_id X.unop.obj n
      map_comp f g := by
        apply CommGrpCat.hom_ext
        exact perfectKPullback_comp g.unop.hom f.unop.hom n }
  F ⋙ CommGrpCat.toAddCommGrp

/-- The original connective group at each compact scheme is the stable group of its spectrum. -/
def connectivePerfectKLocalizedStableIso (n : ℕ) (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (connectivePerfectKFunctor n).obj X ≅
      (perfectLocalizedSpectrumFunctor ⋙ localizedStableHomotopyFunctor (n : ℤ)).obj X :=
  (originalKStableEquiv (perfectComplexesWaldhausen X.unop.obj.toRingedSpace) n).toAddCommGrpIso

/-- The connective group comparison commutes with each actual derived pullback. -/
def connectivePerfectKLocalizedStableNatIso (n : ℕ) :
    connectivePerfectKFunctor.{u} n ≅
      perfectLocalizedSpectrumFunctor ⋙ localizedStableHomotopyFunctor (n : ℤ) :=
  NatIso.ofComponents (connectivePerfectKLocalizedStableIso n) (fun {X Y} f => by
    ext a
    exact perfectLocalizedPullback_originalK_naturality f.unop.hom n a.toMul)

/-- The connective stable groups on the literal stage-zero ambient row. -/
def boundedAboveFlatCoefficientAmbientBassConnectiveNatIso {R : CommRingCat.{u}}
    (P : Over (Spec R)) [CompactSpace P.left] (n : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactRow P ⋙ connectivePerfectKFunctor n ≅
      boundedAboveFlatCoefficientAmbientBassDiagram P 0 ⋙ stableHomotopyFunctor (n : ℤ) :=
  Functor.isoWhiskerLeft (boundedAboveFlatCoefficientQuasiCompactRow P)
      (connectivePerfectKLocalizedStableNatIso n) ≪≫
    (Functor.isoWhiskerRight
      (boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P)
      (localizedStableHomotopyFunctor (n : ℤ))).symm

end AlgebraicGeometry.Scheme.Modules
