/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.RemainingStalkFamily
public import Colib.RingTheory.Koszul.CoefficientFunctor
public import Mathlib.Data.List.OfFn
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange

/-!
# Flat homology comparison for the actual remaining coefficient equations

SOURCE ONLY, UNCOMPILED. The constructed family's original coefficient list s₀
and exterior coefficient list sD satisfy literally sD = s₀.map α for the flat
actual coefficient-quotient projection stalk map α. Native flat Koszul base
change and the actual tensor right unit give a D-linear equivalence
H_n(K(sD; D)) ≃ D ⊗[C₀] H_n(K(s₀; C₀)) in every degree, including zero.

The endpoint remains Nonempty, as in the public upstream theorem. No canonical
choice or naturality of that homology equivalence is claimed. The explicit
formulas below concern only the common ordered equations and tensor unit.
Neither coefficient list is required to be regular; higher homology remains.

Software references: Stacks 5ed82d14634e8d9576bb844c7bd4e3da66d450e7,
StacksFrontier/RingTheory/Koszul/FlatBaseChange.lean:565-573; Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/LinearAlgebra/TensorProduct/Tower.lean:356-372. The tensor-unit step
follows the public Colib FirstStagePairTorBaseChange.lean:109-117 at
revision e7697ab8164435c7093665d02ac34f021eefb75e, without copying a private helper.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

open AlgebraicGeometry.Scheme

universe u v
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)
  (x : nativeExteriorIncidence X Y Z T z w hz hw)

local notation3 (prettyPrint := false) "I'" => nativeExteriorIncidence X Y Z T z w hz hw
local notation3 (prettyPrint := false) "I₀" =>
  correspondenceIncidence X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "P₀" =>
  correspondenceSupportProduct X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "c" =>
  nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw
local notation3 (prettyPrint := false) "q" =>
  nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw
local notation3 (prettyPrint := false) "π" => nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "C₀" => (P₀).presheaf.stalk (q (c x))
local notation3 (prettyPrint := false) "D" => (Q).presheaf.stalk (c x)
local notation3 (prettyPrint := false) "E₀" => (I₀).presheaf.stalk (π x)
local notation3 (prettyPrint := false) "E" => (I').presheaf.stalk x
local notation3 (prettyPrint := false) "α" => ((q).stalkMap (c x)).hom
local notation3 (prettyPrint := false) "η₀" =>
  (nativeExteriorRemainingOriginalIncidenceStalkMap X Y T z hz Z w hw x).hom
local notation3 (prettyPrint := false) "η" => ((c).stalkMap x).hom
local notation3 (prettyPrint := false) "p" => ((π).stalkMap x).hom

local notation3 (prettyPrint := false) "F" =>
  nativeExteriorRemainingStalkFamily X Y T z hz Z w hw x
local notation3 (prettyPrint := false) "s₀" => (F).originalCoefficientList
local notation3 (prettyPrint := false) "sD" => (F).coefficientList

/-- The common finite index set lists precisely the actual exterior coefficient equations. -/
theorem nativeExteriorRemainingCoefficient_ofFn :
    List.ofFn (fun j => (α) ((s₀).get j)) = sD := by
  rw [List.ofFn_comp', List.ofFn_get, ← (F).coefficientList_eq_original_image]

/-- The actual right tensor unit multiplies the original coefficient through α. -/
theorem nativeExteriorRemainingCoefficient_tensorUnit_tmul (d : D) (a : C₀) :
    let : Algebra C₀ D := (α).toAlgebra
    TensorProduct.AlgebraTensorModule.rid C₀ D D (d ⊗ₜ[C₀] a) = (α) a * d := by
  let : Algebra C₀ D := (α).toAlgebra
  rfl

/-- The inverse tensor unit retains every actual exterior coefficient element. -/
theorem nativeExteriorRemainingCoefficient_tensorUnit_symm (d : D) :
    let : Algebra C₀ D := (α).toAlgebra
    (TensorProduct.AlgebraTensorModule.rid C₀ D D).symm d = d ⊗ₜ[C₀] 1 := rfl

/-- A D-linear flat homology comparison in the common original ordered index set. -/
theorem nativeExteriorRemainingCoefficient_homology_baseChange (n : ℕ) :
    let : Algebra C₀ D := (α).toAlgebra
    Nonempty
      (((Koszul.seqComplexTensor (fun j => (α) ((s₀).get j)) D).homology n) ≃ₗ[D]
        (D ⊗[C₀] ((Koszul.seqComplexTensor (s₀).get C₀).homology n))) := by
  let : Algebra C₀ D := (α).toAlgebra
  have : Module.Flat C₀ D :=
    nativeExteriorCoefficientQuotientProjection_stalkMap_flat X Y T z hz Z w hw (c x)
  let eunit := (Koszul.seqComplexTensorFunctor (fun j => (α) ((s₀).get j))).mapIso
    (TensorProduct.AlgebraTensorModule.rid C₀ D D).symm.toModuleIso
  obtain ⟨eflat⟩ := KoszulC.homology_baseChange_linearEquiv (S := D) (s₀).get C₀ n
  exact ⟨((HomologicalComplex.homologyFunctor _ _ n).mapIso eunit).toLinearEquiv.trans
    eflat⟩

/-- The same comparison with the literal actual exterior list, not a replacement list. -/
theorem nativeExteriorRemainingCoefficient_list_homology_baseChange (n : ℕ) :
    let : Algebra C₀ D := (α).toAlgebra
    Nonempty
      (((Koszul.seqComplexTensor (sD).get D).homology n) ≃ₗ[D]
        (D ⊗[C₀] ((Koszul.seqComplexTensor (s₀).get C₀).homology n))) := by
  let : Algebra C₀ D := (α).toAlgebra
  have heq : Koszul.seqComplexTensor (sD).get D =
      Koszul.seqComplexTensor (fun j => (α) ((s₀).get j)) D := by
    rw [(F).coefficientList_eq_original_image]
    have aux {r₁ r₂ : ℕ} (hlen : r₁ = r₂) (f₁ : Fin r₁ → D) (f₂ : Fin r₂ → D)
        (hfun : HEq f₁ f₂) : Koszul.seqComplexTensor f₁ D = Koszul.seqComplexTensor f₂ D := by
      subst r₂
      cases hfun
      rfl
    apply aux (List.length_map (as := s₀) α)
    apply (Fin.heq_fun_iff (List.length_map (as := s₀) α)).mpr
    intro idx
    simp only [List.get_eq_getElem, List.getElem_map]
  rw [heq]
  exact nativeExteriorRemainingCoefficient_homology_baseChange X Y Z T z w hz hw x n

end Stacks.Chow
