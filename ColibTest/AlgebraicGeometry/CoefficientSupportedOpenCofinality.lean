module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenCofinality

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
noncomputable section

example {C : Type (u + 1)} [Category.{u + 1} C]
    {D : Type (u + 1)} [Category.{u} D]
    (V : Structure C) (W : Structure D) (e : C ≌ D)
    (hE : IsExact V.cof V.weq W.cof W.weq e.functor)
    (hEi : IsExact W.cof W.weq V.cof V.weq e.inverse) (n : ℕ) (x : V.K n) :
    boundedAboveFlatCoefficientEvaluationKEquiv V W e hE hEi n x =
      (W.asSmallKEquiv n).symm (KMap (hE.comp W.asSmall_up_exact) n x) := rfl

example {C C' : Type (u + 1)} [Category.{u + 1} C] [Category.{u + 1} C']
    {D D' : Type (u + 1)} [Category.{u} D] [Category.{u} D']
    (V : Structure C) (W : Structure D) (e : C ≌ D)
    (hE : IsExact V.cof V.weq W.cof W.weq e.functor)
    (hEi : IsExact W.cof W.weq V.cof V.weq e.inverse)
    (V' : Structure C') (W' : Structure D') (e' : C' ≌ D')
    (hE' : IsExact V'.cof V'.weq W'.cof W'.weq e'.functor)
    (hEi' : IsExact W'.cof W'.weq V'.cof V'.weq e'.inverse)
    {F : C ⥤ C'} {G : D ⥤ D'}
    (hF : IsExact V.cof V.weq V'.cof V'.weq F)
    (hG : IsExact W.cof W.weq W'.cof W'.weq G)
    (s : F ⋙ e'.functor ≅ e.functor ⋙ G) (n : ℕ) (x : V.K n) :
    boundedAboveFlatCoefficientEvaluationKEquiv V' W' e' hE' hEi' n (KMap hF n x) =
      KMap hG n (boundedAboveFlatCoefficientEvaluationKEquiv V W e hE hEi n x) :=
  boundedAboveFlatCoefficientEvaluationKEquiv_natural V W e hE hEi V' W' e' hE' hEi' hF hG s n x

variable {R : CommRingCat.{u}}
example {i : Index R} {U : Scheme.{u}} (j : U ⟶ space i) [IsOpenImmersion j]
    (S : BoundedAboveFlatCoefficientSupportedSections j) :
    boundedAboveFlatCoefficientSupportedSectionKEquiv j 0
        ((boundedAboveFlatCoefficientSupportedSectionWaldhausen j).kZeroObjectClass S) =
      (boundedAboveFlatPerfectSupportedWaldhausen j).kZeroObjectClass
        ((boundedAboveFlatCoefficientSupportedEvaluation j).obj S) :=
  boundedAboveFlatCoefficientSupportedSectionKEquiv_objectClass j S

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

example (a : Under R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).K n) :
    boundedAboveFlatCoefficientSupportedSectionKEquiv
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι n
        (KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) n x) =
      boundedAboveFlatPerfectSupportedOpenKRestrict (schemeMap f a) n
        (boundedAboveFlatCoefficientSupportedOpenKEquiv f T a n x) :=
  boundedAboveFlatCoefficientSupportedOpenRestriction_KComparison f T a n x

example [CompactSpace P.left] (a : Under R)
    (S : BoundedAboveFlatCoefficientSupportedOpenSections f T a) :
    boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a 0
        ((boundedAboveFlatCoefficientSupportedSectionWaldhausen
          (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).kZeroObjectClass S) =
      (perfectSupportedWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).kZeroObjectClass
          ((boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation f T a).obj
          S) :=
  boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv_objectClass f T a S

example [CompactSpace P.left] [CompactSpace Q.left] (a : Under R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).K n) :
    boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a n
        (KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) n x) =
      perfectSupportedOpenKRestrict (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a) n
        (boundedAboveFlatCoefficientSupportedOpenPerfectKEquiv f T a n x) :=
  boundedAboveFlatCoefficientSupportedOpenRestriction_perfectKComparison f T a n x

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] [CompactSpace T]

example (a : Under R) (n : ℕ) :
    Function.Injective (KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) n) :=
  boundedAboveFlatCoefficientSupportedOpenRestriction_KMap_injective f T a n

example (a : Under R) (n : ℕ) :
    Function.Bijective
      (KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) (n + 1)) :=
  boundedAboveFlatCoefficientSupportedOpenRestriction_KMap_succ_bijective f T a n
