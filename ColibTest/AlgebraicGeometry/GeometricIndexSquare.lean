/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentIndexSquareFactor
import Colib.AlgebraicGeometry.Scheme.IntegerBaseProducts
import Colib.AlgebraicGeometry.Scheme.IntegerBaseProductInterchange
import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentIndexSquare

/-! # Reconstructed original proof consumers
These checks retain the original hypotheses and coordinate equations.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry.Scheme.PolynomialLaurent
section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
universe u
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
namespace ReconstructedConsumer0532N0

variable {T T' : Scheme.{u}} (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (q' : T' ⟶ (Spec (.of
    (ULift.{u} ℤ))))
  (f : T ⟶ T') (hf : f ≫ q' = q)

/-- Changing the actual fixed factor commutes with all four original swap components. -/
example (X : Scheme.{u}ᵒᵖ) :
    squareFunctor.map ((baseProductTransformation q q' f hf).app X.unop).op ≫
        (squareIso q X).hom =
      (squareIso q' X).hom ≫
        onSquare (NatTrans.op (baseProductTransformation q q' f hf)) (square X) := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext
  · change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl
  · exact Quiver.Hom.unop_inj
      (baseProductSwapIso_transformation_second _ q q' f hf X.unop).symm
  · exact Quiver.Hom.unop_inj
      (baseProductSwapIso_transformation_second _ q q' f hf X.unop).symm
  · exact Quiver.Hom.unop_inj
      (baseProductSwapIso_transformation_second _ q q' f hf X.unop).symm

/-- The actual factor projection gives the unchanged source leg after index interchange. -/
example (X : Scheme.{u}ᵒᵖ) :
    squareFunctor.map ((baseProductProjection q).app X.unop).op ≫
        (squareIso q X).hom =
      onSquare (NatTrans.op (baseProductProjection q)) (square X) := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext
  · change _ ≫ 𝟙 _ = _
    simp only [Category.comp_id]
    rfl
  · exact Quiver.Hom.unop_inj
      (baseProductSwapIso_projection_second _ q X.unop)
  · exact Quiver.Hom.unop_inj
      (baseProductSwapIso_projection_second _ q X.unop)
  · exact Quiver.Hom.unop_inj
      (baseProductSwapIso_projection_second _ q X.unop)

/-- The original positive factor chart retains the same four-corner isomorphisms. -/
example (X : Scheme.{u}ᵒᵖ) :
    squareFunctor.map (plus.app X.unop).op ≫
        (squareIso (laurentProjection (.of (ULift.{u} ℤ))) X).hom =
      (squareIso (polynomialProjection (.of (ULift.{u} ℤ))) X).hom ≫
        onSquare (NatTrans.op plus) (square X) := squareIso_factor _ _ _ _ X

/-- The original inverted factor chart retains the same four-corner isomorphisms. -/
example (X : Scheme.{u}ᵒᵖ) :
    squareFunctor.map (minus.app X.unop).op ≫
        (squareIso (laurentProjection (.of (ULift.{u} ℤ))) X).hom =
      (squareIso (polynomialProjection (.of (ULift.{u} ℤ))) X).hom ≫
        onSquare (NatTrans.op minus) (square X) := squareIso_factor _ _ _ _ X

end ReconstructedConsumer0532N0


end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local simp] pullback.map pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc
universe u

open AlgebraicGeometry.Scheme.Products
namespace ReconstructedConsumer0532N1


variable {A B : Scheme.{u}}
  (p : A ⟶ Spec (.of (ULift.{u} ℤ))) (q : B ⟶ Spec (.of (ULift.{u} ℤ)))
  (f : A ⟶ B) (hf : f ≫ q = p) (X : Scheme.{u})

example : IsPullback ((baseProductTransformation p q f hf).app X)
    (pullback.snd (specULiftZIsTerminal.from X) p)
    (pullback.snd (specULiftZIsTerminal.from X) q) f :=
  baseProductTransformation_isPullback p q f hf X

example [IsOpenImmersion f] :
    IsOpenImmersion ((baseProductTransformation p q f hf).app X) := inferInstance

example [Flat f] : Flat ((baseProductTransformation p q f hf).app X) := inferInstance

end ReconstructedConsumer0532N1


end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local simp] pullback.map pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc
universe u

open AlgebraicGeometry.Scheme.Products
namespace ReconstructedConsumer0532N2

variable {S T S' T' : AlgebraicGeometry.Scheme.{u}}

/-- The shared original base coordinate is unchanged. -/
example (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (X : AlgebraicGeometry.Scheme.{u}) :
    baseProductSwapMap p q X ≫
        pullback.fst (specULiftZIsTerminal.from ((baseProductFunctor q).obj X)) p ≫
          pullback.fst (specULiftZIsTerminal.from X) q =
      pullback.fst (specULiftZIsTerminal.from ((baseProductFunctor p).obj X)) q ≫
        pullback.fst (specULiftZIsTerminal.from X) p := by
  simp [baseProductSwapMap]

/-- The original outer factor becomes the inner second coordinate. -/
example (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (X : AlgebraicGeometry.Scheme.{u}) :
    baseProductSwapMap p q X ≫
        pullback.fst (specULiftZIsTerminal.from ((baseProductFunctor q).obj X)) p ≫
          pullback.snd (specULiftZIsTerminal.from X) q =
      pullback.snd (specULiftZIsTerminal.from ((baseProductFunctor p).obj X)) q := by
  simp [baseProductSwapMap]

/-- The original inner second coordinate becomes the outer factor. -/
example (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (X : AlgebraicGeometry.Scheme.{u}) :
    baseProductSwapMap p q X ≫
        pullback.snd (specULiftZIsTerminal.from ((baseProductFunctor q).obj X)) p =
      pullback.fst (specULiftZIsTerminal.from ((baseProductFunctor p).obj X)) q ≫
        pullback.snd (specULiftZIsTerminal.from X) p := by
  simp [baseProductSwapMap]

/-- Exchanging the same two original factors twice is the original identity map. -/
example (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (X : AlgebraicGeometry.Scheme.{u}) :
    baseProductSwapMap p q X ≫ baseProductSwapMap q p X = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [Category.assoc]
  · simp [Category.assoc]

/-- The swap commutes with every original base-scheme morphism. -/
example (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    (baseProductFunctor q).map ((baseProductFunctor p).map f) ≫ baseProductSwapMap p q Y =
      baseProductSwapMap p q X ≫
        (baseProductFunctor p).map ((baseProductFunctor q).map f) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [baseProductSwapMap, baseProductFunctor, Category.assoc]
  · simp [baseProductSwapMap, baseProductFunctor, Category.assoc]

/-- The forward isomorphism component is exactly the original two-lift map. -/
example (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso p q).hom.app X = baseProductSwapMap p q X := rfl

/-- The chosen reverse component is the same literal swap with factors exchanged. -/
example (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso p q).inv.app X = baseProductSwapMap q p X := rfl

/-- The actual natural isomorphisms are involutive without identifying their pullback objects. -/
example (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) :
    baseProductSwapIso p q ≪≫ baseProductSwapIso q p = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact baseProductSwapMap_comp p q X

/-- Removing the final first factor retains the original map of the other product functor. -/
example (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso p q).hom.app X ≫
        (baseProductProjection p).app ((baseProductFunctor q).obj X) =
      (baseProductFunctor q).map ((baseProductProjection p).app X) := by
  apply pullback.hom_ext <;>
    simp [baseProductSwapMap, baseProductProjection, baseProductFunctor]

/-- Removing the inner second factor retains the original outer projection. -/
example (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso p q).hom.app X ≫
        (baseProductFunctor p).map ((baseProductProjection q).app X) =
      (baseProductProjection q).app ((baseProductFunctor p).obj X) := by
  apply pullback.hom_ext <;>
    simp [baseProductSwapMap, baseProductProjection, baseProductFunctor, Category.assoc]

/-- An actual morphism of the first fixed factor commutes with the whole swap. -/
example (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (p' : S' ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (f : S ⟶ S')
    (hf : f ≫ p' = p) (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductFunctor q).map ((baseProductTransformation p p' f hf).app X) ≫
        (baseProductSwapIso p' q).hom.app X =
      (baseProductSwapIso p q).hom.app X ≫
        (baseProductTransformation p p' f hf).app ((baseProductFunctor q).obj X) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [baseProductSwapMap, baseProductFunctor, baseProductTransformation, Category.assoc]
  · simp [baseProductSwapMap, baseProductFunctor, baseProductTransformation, Category.assoc]

/-- An independent actual morphism of the second factor commutes with the whole swap. -/
example (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (q' : T' ⟶ (Spec (.of (ULift.{u} ℤ)))) (g : T ⟶ T')
    (hg : g ≫ q' = q) (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductTransformation q q' g hg).app ((baseProductFunctor p).obj X) ≫
        (baseProductSwapIso p q').hom.app X =
      (baseProductSwapIso p q).hom.app X ≫
        (baseProductFunctor p).map ((baseProductTransformation q q' g hg).app X) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [baseProductSwapMap, baseProductFunctor, baseProductTransformation, Category.assoc]
  · simp [baseProductSwapMap, baseProductFunctor, baseProductTransformation, Category.assoc]

end ReconstructedConsumer0532N2

end

section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
universe u

open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
namespace ReconstructedConsumer0532N3

/-- Both charts have exactly the same original projection to the base. -/
example (X : Scheme.{u}) :
    plus.app X ≫ projection.app X = minus.app X ≫ projection.app X := by
  change (baseProductTransformation _ _ _ _).app X ≫ (baseProductProjection _).app X =
    (baseProductTransformation _ _ _ _).app X ≫ (baseProductProjection _).app X
  rw [baseProductTransformation_projection, baseProductTransformation_projection]

variable {T : Scheme.{u}} (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))

/-- The positive chart retains the whole original independent-variable swap square. -/
example (X : Scheme.{u}) :
    (baseProductFunctor q).map (plus.app X) ≫
      (baseProductSwapIso (polynomialProjection (.of (ULift.{u} ℤ))) q).hom.app X =
    (baseProductSwapIso (laurentProjection (.of (ULift.{u} ℤ))) q).hom.app X ≫
      plus.app ((baseProductFunctor q).obj X) :=
  baseProductSwapIso_transformation_first _ _ q _ _ X

/-- The inverted chart retains the same literal independent-variable square. -/
example (X : Scheme.{u}) :
    (baseProductFunctor q).map (minus.app X) ≫
      (baseProductSwapIso (polynomialProjection (.of (ULift.{u} ℤ))) q).hom.app X =
    (baseProductSwapIso (laurentProjection (.of (ULift.{u} ℤ))) q).hom.app X ≫
      minus.app ((baseProductFunctor q).obj X) :=
  baseProductSwapIso_transformation_first _ _ q _ _ X

/-- The original base corner is fixed literally. -/
example (X : Scheme.{u}ᵒᵖ) :
    (squareIso q X).hom.left.left = 𝟙 ((baseProductFunctor q).op.obj X) := rfl

/-- The polynomial component has precisely the original swap's contravariant direction. -/
example (X : Scheme.{u}ᵒᵖ) :
    (squareIso q X).hom.left.right =
      (baseProductSwapMap (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).op := rfl

/-- The Laurent corner retains the original, rather than an abstractly chosen, swap. -/
example (X : Scheme.{u}ᵒᵖ) :
    (squareIso q X).hom.right.right =
      (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ))) q X.unop).op := rfl

/-- The four-corner swap commutes with every original base-scheme morphism. -/
example {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    squareFunctor.map ((baseProductFunctor q).op.map f) ≫ (squareIso q Y).hom =
      (squareIso q X).hom ≫ (baseProductFunctor q).op.mapArrow.mapArrow.map
        (squareFunctor.map f) := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext
  · simp [squareIso, squareFunctor, squareMap]
  · exact Quiver.Hom.unop_inj (baseProductSwapMap_naturality _ q f.unop).symm
  · exact Quiver.Hom.unop_inj (baseProductSwapMap_naturality _ q f.unop).symm
  · exact Quiver.Hom.unop_inj (baseProductSwapMap_naturality _ q f.unop).symm

end ReconstructedConsumer0532N3


end

