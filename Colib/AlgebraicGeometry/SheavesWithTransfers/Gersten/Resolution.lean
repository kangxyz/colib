/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Cohomology.Absolute
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.StageZero
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.Tower
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.Opens.LocalZero
public import Colib.CategoryTheory.Sites.Cousin
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE

/-! # The augmented Cousin complex on ordinary Zariski opens -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme Opposite TopologicalSpace
open Stacks.Cohomology.FreeYonedaUnivLE

universe u w

namespace AlgebraicGeometry.Gersten

open MotivicHomotopy SheafWithTransfers

attribute [local instance] hasSheafify_zariskiOpens

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{u + 1} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

set_option hygiene false in
set_option quotPrecheck false in
local notation "Ab" => AddCommGrpCat.{u + 1}

variable (X : SmoothSite (Spec (CommRingCat.of k)))
  (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

local notation "K" => effectiveHICoefficient k F hF
local notation "O" => SmoothSite.opensFunctor X
local notation "J" => _root_.Opens.grothendieckTopology X.left.carrier
local notation "N" => Functor.obj (toSheaf k) F

/-- Use the original transfer coefficient category in the stage-zero comparison. -/
local instance gerstenResolutionAbelian : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

/-- The stage zero presheaf is cohomology of the original smooth motives. -/
private def coniveauStageZeroIso (K' : EffectiveMotivesMinus k) (n : ℤ) :
    coniveauStagePresheaf k X K' 0 n ≅
      (O).op ⋙ (effectiveSmoothMotive k).op ⋙ preadditiveYoneda.obj (K'⟦n⟧) :=
  NatIso.ofComponents (fun U ↦ coniveauCohomologyZeroIso k ((O).obj U.unop) K' n) (fun f ↦
    (coniveauCohomologyZeroIso_hom_openMap_naturality k X K' n f.unop).symm)

/-- At codimension zero the tower gives the actual ordinary Nisnevich
cohomology presheaf restricted to the opens of the scheme. -/
@[no_expose]
def coniveauStageZeroNisnevichIso (n : ℕ) :
    coniveauStagePresheaf k X K 0 (n : ℤ) ≅
      (O).op ⋙ cohomologyPresheaf.{u + 1, u + 1} (N) n :=
  coniveauStageZeroIso k X K n ≪≫ NatIso.ofComponents (fun U ↦
    (effectiveSmoothCohomologyEquiv k ((O).obj U.unop) F hF n).toAddCommGrpIso) (by
      intro U V g
      ext a
      exact effectiveSmoothCohomologyEquiv_precomp k ((O).map g.unop) F hF n a)

variable (h : ∀ (U : X.left.Opens) (p n : ℕ), p ≠ n →
      IsZero (coniveauRelativeSupportCohomology k ((SmoothSite.opensFunctor X).obj U)
        (effectiveHICoefficient k F hF) (n : ℤ) p (p + 1)))

/-- Sheafify the original support tower on ordinary Zariski opens with its
localization maps. -/
def zariskiSupportTower : ExactSupportTower (Sheaf J Ab) :=
  (coniveauExactSupportTower k X K h).map (presheafToSheaf J Ab)

/-- The Cousin differentials of the original support tower after Zariski sheafification. -/
abbrev zariskiCousinComplex : CochainComplex (Sheaf J Ab) ℕ :=
  (zariskiSupportTower k X F hF h).cochainComplex

/-- Its unrestricted degree-zero stage is the original Zariski coefficient. -/
@[no_expose]
def zariskiSupportStageZeroIso :
    (zariskiSupportTower k X F hF h).stage 0 0 ≅ zariskiSheafOnOpens k X F := by
  let a := presheafToSheaf J Ab
  let z := zariskiSheafOnOpens k X F
  let e : coniveauStagePresheaf k X K 0 0 ≅ z.obj :=
    coniveauStageZeroNisnevichIso k X F hF 0 ≪≫
      Functor.isoWhiskerLeft (O).op (cohomologyPresheafIsoSections.{u + 1} (N))
  exact a.mapIso e ≪≫ asIso ((sheafificationAdjunction J Ab).counit.app z)

/-- The augmentation is restriction from the unrestricted stage to its first window. -/
def zariskiCousinAugmentation :
    zariskiSheafOnOpens k X F ⟶ (zariskiCousinComplex k X F hF h).X 0 :=
  (zariskiSupportStageZeroIso k X F hF h).inv ≫ (zariskiSupportTower k X F hF h).toLayer 0 0

theorem zariskiCousinAugmentation_comp_d :
    zariskiCousinAugmentation k X F hF h ≫ (zariskiCousinComplex k X F hF h).d 0 1 = 0 := by
  let T := zariskiSupportTower k X F hF h
  let e := zariskiSupportStageZeroIso k X F hF h
  change (e.inv ≫ T.toLayer 0 0) ≫ T.differential 0 = 0
  rw [Category.assoc, T.toLayer_differential_zero, comp_zero]

/-- The actual coefficient is the kernel of the first Cousin differential. -/
@[no_expose]
def zariskiCousinAugmentationIsKernel :
    IsLimit (KernelFork.ofι (zariskiCousinAugmentation k X F hF h)
      (zariskiCousinAugmentation_comp_d k X F hF h)) := by
  let T := zariskiSupportTower k X F hF h
  let e := zariskiSupportStageZeroIso k X F hF h
  change IsLimit (KernelFork.ofι (e.inv ≫ T.toLayer 0 0) (f := T.differential 0) _)
  exact IsLimit.ofIsoLimit (T.isKernelDifferential 0)
    (Fork.ext e (by
      change e.hom ≫ e.inv ≫ T.toLayer 0 0 = T.toLayer 0 0
      exact e.hom_inv_id_assoc _))

/-- The Cousin sheaf complex is exact in positive degrees once the original
support windows are concentrated on the diagonal. -/
theorem zariskiCousinComplex_exactAt_succ (n : ℕ) :
    (zariskiCousinComplex k X F hF h).ExactAt (n + 1) := by
  let T := zariskiSupportTower k X F hF h
  let a := presheafToSheaf J Ab
  exact T.exactAt_succ n
    ((isZero_zariskiSheafify_nisCohomologyOnOpens_succ k X F hF n).of_iso
      (a.mapIso (coniveauStageZeroNisnevichIso k X F hF (n + 1))))

/-- Taking sections of the Cousin complex computes the original cohomology
when its diagonal window presheaves are already sheaves. The sheafification
unit identifies the complexes term by term and respects the original maps. -/
@[no_expose]
def zariskiCousinSectionsHomologySuccIso
    (hSheaf : ∀ p : ℕ, Presheaf.IsSheaf J (coniveauWindowPresheaf k X K p (p : ℤ)))
    (U : X.left.Opens) (n : ℕ) :
    (((sheafToPresheaf J Ab ⋙ (CategoryTheory.evaluation _ _).obj (op U)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (zariskiCousinComplex k X F hF h)).homology (n + 1) ≅
      (cohomologyPresheaf.{u + 1, u + 1} (N) (n + 1)).obj (op ((O).obj U)) := by
  let T := coniveauExactSupportTower k X K h
  exact T.sheafifiedCousinSectionsHomologySuccIso J hSheaf U n ≪≫
    (coniveauStageZeroNisnevichIso k X F hF (n + 1)).app (op U)

end AlgebraicGeometry.Gersten
