/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.EffectiveConvolution
public import StacksFrontier.CategoryTheory.Localization.Monoidal
public import StacksFrontier.CategoryTheory.Localization.BifunctorCommShiftTwoLiftingIso
public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift
import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp

/-!
# Monoidal localization of signed derived convolution

Once signed projective convolution carries its coherent derived monoidal
structure, the effective equivalences are monoidal. The localization
transfers that structure, including its associator, unitors and braiding,
and has the same tensor as the descended effective convolution.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped MonoidalCategory

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST(" K ")" => LargePresheaves K
set_option quotPrecheck false in
local notation "D(" K ")" => DerivedCategory.Minus PST(K)
local notation "DM(" K ")" => EffectiveMotivesMinus K
local notation "q(" K ")" => singularPresheafToEffective K
local notation "W(" K ")" => effectivePresheafEquivalences K

/-- The abelian structure of the transfer sheaves used by the effective localization. -/
local instance : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

variable (F : Cor k ⥤ Cor k ⥤ Cor k) [F.Additive] [∀ X, (F.obj X).Additive]
  (e : ∀ T : SmoothSite (Spec (.of k)), Cor.graphFunctor k ⋙ F.flip.obj (Cor.mk T) ≅
    SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)
  (s : F ≅ F.flip) (hs : ∀ X Y, (s.hom.app X).app Y ≫ (s.hom.app Y).app X = 𝟙 _)
  [MonoidalCategory D(k)]
  (d : MonoidalCategory.curriedTensor D(k) ≅ derivedConvolution F)
  {unit : DM(k)} (ε : (q(k)).obj (𝟙_ D(k)) ≅ unit)

/-- The effective monoidal structure descends the given coherent signed
derived convolution. Its unit is identified by the specified comparison. -/
@[instance_reducible]
def effectiveConvolutionMonoidalCategory : MonoidalCategory DM(k) :=
  letI := effectivePresheafEquivalences_isMonoidal F e s hs d
  Localization.monoidalCategory (q(k)) (W(k)) ε

/-- Effective localization is strong monoidal for the descended structure. -/
def effectiveConvolutionLocalizationCoreMonoidal :
    letI := effectiveConvolutionMonoidalCategory F e s hs d ε
    (q(k)).CoreMonoidal :=
  letI := effectivePresheafEquivalences_isMonoidal F e s hs d
  Localization.coreMonoidal (q(k)) (W(k)) ε

/-- The symmetric structure descends from the actual signed derived
convolution braiding. -/
@[instance_reducible]
def effectiveConvolutionSymmetricCategory [SymmetricCategory D(k)] :
    letI := effectiveConvolutionMonoidalCategory F e s hs d ε
    SymmetricCategory DM(k) :=
  letI := effectivePresheafEquivalences_isMonoidal F e s hs d
  Localization.symmetricCategory (q(k)) (W(k)) ε

/-- The strong localization tensorator compares the actual two-variable tensor. -/
@[instance_reducible]
def effectiveConvolutionMonoidalLifting :
    letI := effectiveConvolutionMonoidalCategory F e s hs d ε
    Localization.Lifting₂ (q(k)) (q(k)) (W(k)) (W(k))
      (MonoidalCategory.curriedTensor D(k) ⋙
        (Functor.whiskeringRight D(k) D(k) DM(k)).obj (q(k)))
      (MonoidalCategory.curriedTensor DM(k)) := by
  letI := effectivePresheafEquivalences_isMonoidal F e s hs d
  letI := effectiveConvolutionMonoidalCategory F e s hs d ε
  constructor
  exact Localization.Monoidal.tensorBifunctorIso (q(k)) (W(k)) ε

/-- The signed compatibility with both shifts descends with the coherent
derived monoidal tensor, including the sign in interchange of shifts. -/
@[instance_reducible]
def effectiveConvolutionMonoidalCommShift₂Int
    [(MonoidalCategory.curriedTensor D(k)).CommShift₂Int] :
    letI := effectiveConvolutionMonoidalCategory F e s hs d ε
    (MonoidalCategory.curriedTensor DM(k)).CommShift₂Int := by
  letI := effectivePresheafEquivalences_isMonoidal F e s hs d
  letI := effectiveConvolutionMonoidalCategory F e s hs d ε
  let B := MonoidalCategory.curriedTensor D(k)
  let E := (Functor.postcompose₂.obj (q(k))).obj B
  let M := Localization.Monoidal.tensorBifunctor (q(k)) (W(k)) ε
  let : Localization.Lifting₂ (q(k)) (q(k)) (W(k)) (W(k)) E M :=
    effectiveConvolutionMonoidalLifting F e s hs d ε
  let : (q(k)).Additive := inferInstance
  let : E.CommShift₂Int := Functor.CommShift₂.postcompInt B (q(k))
  exact Functor.CommShift₂.ofLocalizationInt (q(k)) (q(k)) (W(k)) (W(k)) E M

/-- The effective localization tensorator preserves the specified commutations with shifts. -/
theorem effectiveConvolutionLocalizationMonoidalCommShift
    [(MonoidalCategory.curriedTensor D(k)).CommShift₂Int] :
    letI := effectiveConvolutionMonoidalCategory F e s hs d ε
    letI := effectiveConvolutionMonoidalCommShift₂Int F e s hs d ε
    letI := (effectiveConvolutionLocalizationCoreMonoidal F e s hs d ε).toMonoidal
    Functor.LaxMonoidal.CommShift (q(k)) ℤ := by
  let := effectivePresheafEquivalences_isMonoidal F e s hs d
  let := effectiveConvolutionMonoidalCategory F e s hs d ε
  let := effectiveConvolutionMonoidalCommShift₂Int F e s hs d ε
  let := (effectiveConvolutionLocalizationCoreMonoidal F e s hs d ε).toMonoidal
  let B := MonoidalCategory.curriedTensor D(k)
  let B' := (Functor.postcompose₂.obj (q(k))).obj B
  let M := MonoidalCategory.curriedTensor DM(k)
  let : (q(k)).Additive := inferInstance
  let : B'.CommShift₂Int := Functor.CommShift₂.postcompInt B (q(k))
  let : Localization.Lifting₂ (q(k)) (q(k)) (W(k)) (W(k)) B' M :=
    effectiveConvolutionMonoidalLifting F e s hs d ε
  refine ⟨fun Y => ?_, fun X => ?_⟩
  · exact Localization.lifting₂_iso_hom_app_commShift (q(k)) (q(k))
      (W(k)) (W(k)) B'.flip M.flip Y
  · exact Localization.lifting₂_iso_hom_app_commShift (q(k)) (q(k))
      (W(k)) (W(k)) B' M X

/-- The tensor of the coherent localization agrees naturally with the
two-variable effective convolution already descended from signed totals. -/
def effectiveConvolutionMonoidalTensorIso :
    letI := effectiveConvolutionMonoidalCategory F e s hs d ε
    Functor.uncurry.obj (MonoidalCategory.curriedTensor DM(k)) ≅
      effectiveConvolution F e s hs := by
  letI := effectivePresheafEquivalences_isMonoidal F e s hs d
  letI := effectiveConvolutionMonoidalCategory F e s hs d ε
  let A := (q(k)).prod (q(k))
  let V := (W(k)).prod (W(k))
  let B := MonoidalCategory.curriedTensor D(k)
  let M := MonoidalCategory.curriedTensor DM(k)
  let N := effectiveConvolution F e s hs
  let E := ((Functor.postcompose₂.obj (q(k))).obj B)
  let C := Functor.uncurry.obj (derivedConvolution F) ⋙ q(k)
  let M' := Localization.Monoidal.tensorBifunctor (q(k)) (W(k)) ε
  let : Localization.Lifting₂ (q(k)) (q(k)) (W(k)) (W(k)) E M' :=
    effectiveConvolutionMonoidalLifting F e s hs d ε
  let : Localization.Lifting A V (Functor.uncurry.obj E) (Functor.uncurry.obj M) := by
    change Localization.Lifting A V (Functor.uncurry.obj E) (Functor.uncurry.obj M')
    infer_instance
  let : Localization.Lifting A V C N := ⟨effectiveConvolutionCompIso F e s hs⟩
  let z : Functor.uncurry.obj E ≅ Functor.uncurry.obj B ⋙ q(k) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro X Y f
      change ((q(k)).map ((B.map f.1).app X.2) ≫ (q(k)).map ((B.obj Y.1).map f.2)) ≫
          𝟙 _ = 𝟙 _ ≫ (q(k)).map ((B.map f.1).app X.2 ≫ (B.obj Y.1).map f.2)
      rw [Category.comp_id, Category.id_comp, Functor.map_comp])
  exact Localization.liftNatIso A V (Functor.uncurry.obj E) C (Functor.uncurry.obj M) N
    (z ≪≫ Functor.isoWhiskerRight (Functor.uncurry.mapIso d) (q(k)))

/-- The coherent effective tensor sends the original represented pair to
the motive of its correspondence product. -/
def effectiveConvolutionMonoidalRepresentableIso (X Y : Cor k) :
    letI := effectiveConvolutionMonoidalCategory F e s hs d ε
    (effectiveMotive k).obj X ⊗ (effectiveMotive k).obj Y ≅
      (effectiveMotive k).obj ((F.obj X).obj Y) :=
  (effectiveConvolutionMonoidalTensorIso F e s hs d ε).app
    ((effectiveMotive k).obj X, (effectiveMotive k).obj Y) ≪≫
      effectiveConvolutionRepresentableIso F e s hs X Y

end AlgebraicGeometry.MotivicHomotopy
