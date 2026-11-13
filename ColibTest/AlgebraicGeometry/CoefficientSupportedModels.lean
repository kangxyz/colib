module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenModels
import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientFiberInclusion
import Colib.CategoryTheory.ObjectProperty.LiftInclusion

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules Opposite Topology
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
noncomputable section
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

example (a : Under R) (x : space (op Q, a)) :
    x ∉ boundedAboveFlatCoefficientFiberSupportOpen f T a ↔
      x ∉ boundedAboveFlatCoefficientSupportOpen Q T a ∧ x ∉ (schemeMap f a).opensRange :=
  boundedAboveFlatCoefficientFiberSupportOpen_not_mem f T a x

example {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatCoefficientSupportedAmbientMap T g ⋙
        boundedAboveFlatCoefficientSupportedOpenRestriction f T b =
      boundedAboveFlatCoefficientSupportedOpenRestriction f T a ⋙
        boundedAboveFlatCoefficientSupportedOpenMap f T g :=
  boundedAboveFlatCoefficientSupportedOpenRestriction_square f T g

example (a : Under R) :
    BoundedAboveFlatCoefficientSupportedFiberSections f T a ≌
      (boundedAboveFlatPerfectSupported
        (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι).FullSubcategory :=
  boundedAboveFlatCoefficientSupportedSectionEquivalence
    (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι

example {a b : Under R} (g : a ⟶ b) :
    (boundedAboveFlatCoefficientSupportedFiberModelMap f T g).hom.toFunctor.obj
        (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen.zero =
      (boundedAboveFlatCoefficientSupportedFiberModel f T b).obj.waldhausen.zero :=
  (boundedAboveFlatCoefficientSupportedFiberModelMap f T g).property

example (a : Under R) :
    (boundedAboveFlatCoefficientSupportedOpenChangeWeakModelMap f T a).hom.toFunctor =
      𝟭 (BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a) := rfl

example (a : Under R) :
    (boundedAboveFlatCoefficientSupportedOpenModel f T a).obj.waldhausen.zero =
      (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.zero := rfl

example {a b : Under R} (g : a ⟶ b) :
    (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T).map g ≫
        (boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation f T).app b =
      (boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation f T).app a ≫
        (boundedAboveFlatCoefficientSupportedOpenModelFunctor f T).map g :=
  (boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation f T).naturality g

example (a : Under R)
    {S V : BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a} (p : S ⟶ V) :
    (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).weq p ↔
      (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).weq
        ((boundedAboveFlatCoefficientSupportedEvaluation
          (boundedAboveFlatCoefficientSupportOpen Q T a).ι).map p) :=
  boundedAboveFlatCoefficientSupportedOpenWaldhausen_weq_iff f T a p

example (a : Under R) (S : BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientFiberSupportOpen f T
      a).ι
        S.obj ↔
      (((restrictFunctor (schemeMap f a)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)).obj S.obj).obj).Acyclic :=
  boundedAboveFlatCoefficientFiberSupported_iff f T a S
