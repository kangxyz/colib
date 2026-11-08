/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteModel
public import Colib.RingTheory.Koszul.CoefficientFunctor
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Pullback stalks on the actual full finite model

The projection from the actual local base change to the original exterior is an
isomorphism on stalks. The native pullback-stalk formula (Stacks 0098) therefore
identifies the pulled-back coefficient stalk with its original stalk, linearly
over the original exterior local ring. The action on the pulled-back stalk is
restriction along that same projection stalk map.

This is a specialization to the actual localization projection, not a second
pullback or finite model. No flatness of the finite image map, reduction,
finite-length assumption, or hypothetical coefficient comparison is used.
The resulting linear equivalence acts inside a Koszul complex with the unchanged
ordered list. Compatibility of that list with the original sixfold diagonal
maps remains a separate geometric statement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.ModuleStalkSpecialization
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- Pulling a coefficient to the actual finite model leaves its stalk unchanged
as a module over the original exterior local ring. -/
def correspondenceRemainingFinitePullbackStalkLinearEquiv
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (M : (correspondenceLeftIntermediateSupportProduct f g h i z w v).Modules) :
    let ρ := correspondenceRemainingFiniteModelProjection f g h i z w v x
    let P := (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk (ρ q)
    let M' := (Scheme.Modules.pullback ρ).obj M
    letI := stalkModule M' q
    letI := stalkModule M (ρ q)
    letI : Module P (M'.presheaf.stalk q) := Module.compHom _ (ρ.stalkMap q).hom
    (M'.presheaf.stalk q) ≃ₗ[P] (M.presheaf.stalk (ρ q)) := by
  let ρ := correspondenceRemainingFiniteModelProjection f g h i z w v x
  let E := correspondenceRemainingFiniteModel f g h i z w v x
  let P := (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk (ρ q)
  let Q := E.presheaf.stalk q
  let M' := (Scheme.Modules.pullback ρ).obj M
  letI := stalkModule M' q
  letI := stalkModule M (ρ q)
  letI : Algebra P Q := (ρ.stalkMap q).hom.toAlgebra
  letI : Module P (M'.presheaf.stalk q) := Module.compHom _ (ρ.stalkMap q).hom
  letI := isIso_correspondenceRemainingFiniteModelProjection_stalkMap f g h i z w v x q
  let e : P ≃ₐ[P] Q := AlgEquiv.ofBijective (Algebra.ofId P Q)
    (ConcreteCategory.bijective_of_isIso (ρ.stalkMap q))
  obtain ⟨ePB, _⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    ρ.toLRSHom.toShHom M q
  exact (ePB.restrictScalars P).trans
    ((TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl P _)).trans
      (TensorProduct.lid P _))

/-- The same original ordered equations give isomorphic Koszul complexes under
actual localization pullback of the coefficient sheaf. -/
def correspondenceRemainingFinitePullbackKoszulStalkIso
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (M : (correspondenceLeftIntermediateSupportProduct f g h i z w v).Modules)
    {r : ℕ}
    (s : Fin r → (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
      (correspondenceRemainingFiniteModelProjection f g h i z w v x q)) :
    let ρ := correspondenceRemainingFiniteModelProjection f g h i z w v x
    let P := (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk (ρ q)
    let M' := (Scheme.Modules.pullback ρ).obj M
    letI := stalkModule M' q
    letI := stalkModule M (ρ q)
    letI : Module P (M'.presheaf.stalk q) := Module.compHom _ (ρ.stalkMap q).hom
    Koszul.seqComplexTensor s (ModuleCat.of P (M'.presheaf.stalk q)) ≅
      Koszul.seqComplexTensor s (ModuleCat.of P (M.presheaf.stalk (ρ q))) :=
  (Koszul.seqComplexTensorFunctor s).mapIso
    (correspondenceRemainingFinitePullbackStalkLinearEquiv f g h i z w v x q M).toModuleIso

end Stacks.Chow
