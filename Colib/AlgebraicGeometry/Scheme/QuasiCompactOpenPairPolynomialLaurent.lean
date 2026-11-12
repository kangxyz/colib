/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicGeometry.Scheme.QuasiCompactPolynomialLaurent
public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.QuasiCompact

/-!
Adapted from `Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairs.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

Actual polynomial/Laurent products of scheme/open-support pairs, preserving arbitrary commutative
pair squares. The vanishing open is a genuine inverse image, only the ambient scheme is required qc,
and the ambient-forgetting functor retains the exact two-chart diagram.
This selection excludes the later support-shrinking declarations.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

open AlgebraicGeometry.Scheme.Products

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Forget an open pair to its actual quasi-compact ambient scheme. -/
def quasiCompactOpenPairsBase : QuasiCompactOpenPairs.{u} ⥤ QuasiCompactSchemes.{u} where
  obj X := ⟨X.obj.right, X.property⟩
  map f := ObjectProperty.homMk f.hom.right

end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.Bass

/-- Base product preserves the original map by an actual pullback square. -/
lemma baseProductFunctor_map_isPullback {S : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    IsPullback ((baseProductFunctor p).map f) (pullback.fst (specULiftZIsTerminal.from X) p)
      (pullback.fst (specULiftZIsTerminal.from Y) p) f := by
  apply IsPullback.of_right (h₁₂ := pullback.snd (specULiftZIsTerminal.from Y) p) (h₂₂ :=
      specULiftZIsTerminal.from Y)
  · simpa [baseProductFunctor] using (IsPullback.of_hasPullback (specULiftZIsTerminal.from X)
      p).flip
  · simp [baseProductFunctor]
  · exact (IsPullback.of_hasPullback (specULiftZIsTerminal.from Y) p).flip

instance instIsOpenImmersionBaseProductFunctorMap {S : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [IsOpenImmersion f] :
    IsOpenImmersion ((baseProductFunctor p).map f) :=
  MorphismProperty.of_isPullback (baseProductFunctor_map_isPullback p f).flip inferInstance

/-- Actual products of scheme/open-support pairs; only the ambient scheme is required qc. -/
def pairBaseProductFunctor {S : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact p] : QuasiCompactOpenPairs.{u} ⥤
      QuasiCompactOpenPairs.{u}
      where
  obj A := ⟨{ left := (baseProductFunctor p).obj A.obj.left
              right := (baseProductFunctor p).obj A.obj.right
              hom := (baseProductFunctor p).map A.obj.hom
              prop := inferInstance }, by
      let : CompactSpace A.obj.right := A.property
      change CompactSpace (pullback (specULiftZIsTerminal.from A.obj.right) p : Scheme)
      infer_instance⟩
  map {A B} f := ObjectProperty.homMk
    { left := (baseProductFunctor p).map f.hom.left
      right := (baseProductFunctor p).map f.hom.right
      w := by
        change (baseProductFunctor p).map f.hom.left ≫
          (baseProductFunctor p).map B.obj.hom =
            (baseProductFunctor p).map A.obj.hom ≫ (baseProductFunctor p).map f.hom.right
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (baseProductFunctor p).map f.hom.w
      prop_hom_left := trivial
      prop_hom_right := trivial }
  map_id A := by
    apply ObjectProperty.hom_ext
    ext <;> simp
  map_comp f g := by
    apply ObjectProperty.hom_ext
    ext <;> simp [Functor.map_comp]

/-- The actual chart map is applied to both entries of the original open pair. -/
def pairBaseProductTransformation {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact p]
      [QuasiCompact q]
    (f : S ⟶ T) (hf : f ≫ q = p) : pairBaseProductFunctor p ⟶ pairBaseProductFunctor q where
  app A := ObjectProperty.homMk
    { left := (baseProductTransformation p q f hf).app A.obj.left
      right := (baseProductTransformation p q f hf).app A.obj.right
      w := ((baseProductTransformation p q f hf).naturality A.obj.hom).symm
      prop_hom_left := trivial
      prop_hom_right := trivial }
  naturality {A B} g := by
    apply ObjectProperty.hom_ext
    ext
    · exact (baseProductTransformation p q f hf).naturality g.hom.left
    · exact (baseProductTransformation p q f hf).naturality g.hom.right

/-- Base change of a quasi-compact open pair along the integer polynomial projection. -/
abbrev pairPolynomialFunctor : QuasiCompactOpenPairs.{u} ⥤ QuasiCompactOpenPairs.{u} :=
  pairBaseProductFunctor (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ)))

/-- Base change of a quasi-compact open pair along the integer Laurent projection. -/
abbrev pairLaurentFunctor : QuasiCompactOpenPairs.{u} ⥤ QuasiCompactOpenPairs.{u} :=
  pairBaseProductFunctor (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ)))

/-- The transformation of open pairs induced by the usual Laurent chart map. -/
def pairPlus : pairLaurentFunctor.{u} ⟶ pairPolynomialFunctor :=
  pairBaseProductTransformation _ _ (PolynomialLaurent.laurentToPolynomial (CommRingCat.of
      (ULift.{u} ℤ)))
    (PolynomialLaurent.laurentToPolynomial_projection (CommRingCat.of (ULift.{u} ℤ)))

/-- The transformation of open pairs induced by the inverted Laurent chart map. -/
def pairMinus : pairLaurentFunctor.{u} ⟶ pairPolynomialFunctor :=
  pairBaseProductTransformation _ _ (PolynomialLaurent.laurentMinus (CommRingCat.of (ULift.{u} ℤ)))
    (PolynomialLaurent.laurentMinus_projection (CommRingCat.of (ULift.{u} ℤ)))

@[simp] lemma pairPlus_base (A : QuasiCompactOpenPairs.{u}) :
    quasiCompactOpenPairsBase.map (pairPlus.app A) = plus.app (quasiCompactOpenPairsBase.obj A) :=
      rfl

@[simp] lemma pairMinus_base (A : QuasiCompactOpenPairs.{u}) :
    quasiCompactOpenPairsBase.map (pairMinus.app A) = minus.app (quasiCompactOpenPairsBase.obj A) :=
      rfl

/-- Forgetting the support open preserves the actual polynomial object and every map. -/
def pairPolynomialBaseIso : pairPolynomialFunctor.{u} ⋙ quasiCompactOpenPairsBase ≅
    quasiCompactOpenPairsBase ⋙ polynomialFunctor := Iso.refl _

/-- Forgetting the support open preserves the actual Laurent object and every map. -/
def pairLaurentBaseIso : pairLaurentFunctor.{u} ⋙ quasiCompactOpenPairsBase ≅
    quasiCompactOpenPairsBase ⋙ laurentFunctor := Iso.refl _


end AlgebraicGeometry.Scheme.Bass

end

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairs.lean:31"
  "adaptation" "Actual open-pair products and chart maps on the native arrow category."]
  AlgebraicGeometry.Scheme.Bass.baseProductFunctor_map_isPullback

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairs.lean:40"
  "adaptation" "Actual open-pair products and chart maps on the native arrow category."]
  AlgebraicGeometry.Scheme.Bass.instIsOpenImmersionBaseProductFunctorMap

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairs.lean:46"
  "adaptation" "Actual open-pair products and chart maps on the native arrow category."]
  AlgebraicGeometry.Scheme.Bass.pairBaseProductFunctor

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairs.lean:62"
  "adaptation" "Actual open-pair products and chart maps on the native arrow category."]
  AlgebraicGeometry.Scheme.Bass.pairBaseProductTransformation

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairs.lean:73"
  "adaptation" "Actual open-pair products and chart maps on the native arrow category."]
  AlgebraicGeometry.Scheme.Bass.pairPolynomialFunctor

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairs.lean:77"
  "adaptation" "Actual open-pair products and chart maps on the native arrow category."]
  AlgebraicGeometry.Scheme.Bass.pairLaurentFunctor

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairs.lean:81"
  "adaptation" "Actual open-pair products and chart maps on the native arrow category."]
  AlgebraicGeometry.Scheme.Bass.pairPlus

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairs.lean:86"
  "adaptation" "Actual open-pair products and chart maps on the native arrow category."]
  AlgebraicGeometry.Scheme.Bass.pairMinus

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairs.lean:90"
  "adaptation" "Actual open-pair products and chart maps on the native arrow category."]
  AlgebraicGeometry.Scheme.Bass.pairPlus_base

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairs.lean:94"
  "adaptation" "Actual open-pair products and chart maps on the native arrow category."]
  AlgebraicGeometry.Scheme.Bass.pairMinus_base

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairs.lean:99"
  "adaptation" "Actual open-pair products and chart maps on the native arrow category."]
  AlgebraicGeometry.Scheme.Bass.pairPolynomialBaseIso

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/OpenPairs.lean:103"
  "adaptation" "Actual open-pair products and chart maps on the native arrow category."]
  AlgebraicGeometry.Scheme.Bass.pairLaurentBaseIso
