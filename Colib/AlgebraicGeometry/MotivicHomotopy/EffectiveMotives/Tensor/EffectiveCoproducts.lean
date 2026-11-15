/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.EffectiveLocalization
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TorusRightCoproducts
import Colib.CategoryTheory.Preadditive.AdditiveFunctorGrothendieck
import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums

/-! # Effective localization on coproducts with a common upper bound -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST(" K ")" => LargePresheaves K
local notation "NST(" K ")" => LargeSheaves K
local notation "a(" K ")" => derivedNisnevichSheafification K
local notation "q(" K ")" => singularPresheafToEffective K
local notation "j(" K ")" => effectiveMotivesMinusToDerived K
local notation "M(" K ")" => effectiveReflection K

/-- The canonical abelian structure on transfer sheaves. -/
local instance instAbelianEffectiveCoproducts : Abelian NST(k) := SheafWithTransfers.abelian k

/-- Sheafification followed by effective reflection preserves each upper bound. -/
theorem singularPresheafToEffective_isLE (P : DerivedCategory.Minus PST(k)) (b : ℤ)
    (hP : P.obj.IsLE b) : ((j(k)).obj ((q(k)).obj P)).IsLE b := by
  let A := nisnevichSheafify k
  let : P.obj.IsLE b := hP
  have hA : ((a(k)).obj P).obj.IsLE b := by
    apply (DerivedCategory.isLE_iff _ b).2
    intro n hn
    exact (A.map_isZero (DerivedCategory.isZero_of_isLE P.obj b n hn)).of_iso
      ((A.mapDerivedCategoryHomologyIso n).app P.obj)
  let e := (j(k)).mapIso ((sheafificationEffectiveReflectionIso k).app P)
  let : ((j(k)).obj ((a(k) ⋙ M(k)).obj P)).IsLE b := effectiveReflection_isLE k _ b hA
  exact DerivedCategory.TStructure.t.isLE_of_iso e b

omit [PerfectField k]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private theorem derivedNisnevichSheafification_preservesColimit_of_bound {I : Type (u + 1)}
    (K : I → DerivedCategory.Minus PST(k)) (b : ℤ) (hK : ∀ i, (K i).obj.IsLE b) :
    PreservesColimit (Discrete.functor K) (a(k)) := by
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let U := DerivedCategory.Minus.ι (C := NST(k))
  let A := (nisnevichSheafify k).mapDerivedCategory
  let W := fun i => V.obj (K i)
  let : HasCoproductsOfShape I (DerivedCategory PST(k)) :=
    Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory PST(k) I
  let : ReflectsColimitsOfShape (Discrete I) V :=
    (fullyFaithful_reflectsColimits V).reflectsColimitsOfShape
  let : ReflectsColimitsOfShape (Discrete I) U :=
    (fullyFaithful_reflectsColimits U).reflectsColimitsOfShape
  let : A.IsLeftAdjoint := (nisnevichDerivedAdjunction k).isLeftAdjoint
  let P : DerivedCategory.Minus PST(k) := ⟨∐ W, b, Stacks.Duality.isLE_sigmaObj PST(k) W b hK⟩
  let c : Cofan K := Cofan.mk P (fun i => ObjectProperty.homMk (Sigma.ι W i))
  let e : Discrete.functor K ⋙ V ≅ Discrete.functor W := Discrete.natIso (fun _ => Iso.refl _)
  have hc : IsColimit (V.mapCocone c) := by
    refine ((IsColimit.precomposeHomEquiv e _).symm (coproductIsCoproduct W)).ofIsoColimit ?_
    refine Cocone.ext (Iso.refl _) (fun i => ?_)
    change (𝟙 _ ≫ Sigma.ι W i.as) ≫ 𝟙 _ = Sigma.ι W i.as
    rw [Category.id_comp, Category.comp_id]
  refine preservesColimit_of_preserves_colimit_cocone (isColimitOfReflects V hc) ?_
  apply isColimitOfReflects U
  exact isColimitOfPreserves A hc

omit [PerfectField k] [HasDerivedCategory PST(k)]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private theorem effectiveMotivesMinusToDerived_preservesColimit {I : Type (u + 1)}
    (K : I → EffectiveMotivesMinus k) (b : ℤ)
    (hK : ∀ i, ((j(k)).obj (K i)).IsLE b) : PreservesColimit (Discrete.functor K) (j(k)) := by
  let W := fun i => (j(k)).obj (K i)
  let : HasCoproductsOfShape I (DerivedCategory NST(k)) :=
    Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory NST(k) I
  refine preservesColimit_of_preserves_colimit_cocone (effectiveCofanIsColimit k K b hK) ?_
  let d : Discrete.functor K ⋙ j(k) ≅ Discrete.functor W := Discrete.natIso (fun _ => Iso.refl _)
  let hW : IsColimit (Cofan.mk (∐ W) (Sigma.ι W)) := coproductIsCoproduct W
  refine ((IsColimit.precomposeHomEquiv d _).symm hW).ofIsoColimit ?_
  refine Cocone.ext (Iso.refl _) (fun i => ?_)
  change (𝟙 _ ≫ Sigma.ι W i.as) ≫ 𝟙 _ = Sigma.ι W i.as
  rw [Category.id_comp, Category.comp_id]

/-- The sheafified singular localization followed by inclusion preserves
coproducts of derived presheaf complexes with a common upper bound. -/
theorem singularPresheafToEffectiveToDerived_preservesColimit {I : Type (u + 1)}
    (K : I → DerivedCategory.Minus PST(k)) (b : ℤ) (hK : ∀ i, (K i).obj.IsLE b) :
    PreservesColimit (Discrete.functor K) (q(k) ⋙ j(k)) := by
  let : PreservesColimit (Discrete.functor K) (a(k)) :=
    derivedNisnevichSheafification_preservesColimit_of_bound k K b hK
  let : (M(k)).IsLeftAdjoint := (effectiveReflectionAdjunction k).isLeftAdjoint
  let : PreservesColimit (Discrete.functor K) (a(k) ⋙ M(k)) := comp_preservesColimit (a(k)) (M(k))
  let e := sheafificationEffectiveReflectionIso k
  let : PreservesColimit (Discrete.functor K) (q(k)) := preservesColimit_of_natIso _ e
  let W := fun i => (q(k)).obj (K i)
  let d : Discrete.functor K ⋙ q(k) ≅ Discrete.functor W := Discrete.natIso (fun _ => Iso.refl _)
  let : PreservesColimit (Discrete.functor W) (j(k)) :=
    effectiveMotivesMinusToDerived_preservesColimit k W b
      (fun i => singularPresheafToEffective_isLE k (K i) b (hK i))
  let : PreservesColimit (Discrete.functor K ⋙ q(k)) (j(k)) :=
    preservesColimit_of_iso_diagram (j(k)) d.symm
  exact comp_preservesColimit (q(k)) (j(k))

end AlgebraicGeometry.MotivicHomotopy
