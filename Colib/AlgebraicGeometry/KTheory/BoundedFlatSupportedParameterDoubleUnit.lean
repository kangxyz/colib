/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedPairUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatProjectionUnitInterchange
public import Colib.KTheory.Waldhausen.Iterated.IdentityActionInterchangeSign
public import Colib.Topology.Prespectrum.SelfTrackStableNaturality

/-!
# The original supported parameter double-unit operation

The two original Laurent projection tracks are retained, including their actual
supported Model maps. Their stable operations factor through the same target
identity actions. Actual parameter interchange swaps both scalar actions and
fixes the double projection, giving its genuine stable sign. This owner does
not identify a coefficient Laurent quotient or a negative-class correction.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedParameterDoubleUnit.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open Topology Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedParameterDoubleUnit
open GlobalSupportedSection AlgebraicGeometry.Scheme.GlobalSupportedParameter
open GlobalSupportedSection.ParameterModels

private theorem four_comp {C : Type*} [Category C] {A B C' D E F : C}
    (p : A ⟶ B) (r : B ⟶ C') (q : C' ⟶ D) (q' : B ⟶ E)
    (i : E ⟶ D) (o : D ⟶ F) (h : r ≫ q = q' ≫ i) :
    (p ≫ r) ≫ (q ≫ o) = p ≫ q' ≫ i ≫ o := by
  rw [Category.assoc, ← Category.assoc r q, h, Category.assoc]

private theorem map_three {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B T : C} (p : A ⟶ B) (q : B ⟶ T) (s : T ⟶ T)
    (h : p ≫ q ≫ s = p ≫ q) :
    (F.map p ≫ F.map q) ≫ F.map s = F.map p ≫ F.map q := by
  simpa only [Functor.map_comp, Category.assoc] using congrArg F.map h

private theorem signed_slide {C : Type*} [Category C] [Preadditive C] {A B₀ B₁ B₂ : C}
    (p : A ⟶ B₀) (r₀ s₀ : B₀ ⟶ B₁) (r₁ s₁ : B₁ ⟶ B₂)
    (z₀ : B₀ ⟶ B₀) (z₁ : B₁ ⟶ B₁) (z₂ : B₂ ⟶ B₂)
    (hs : s₁ ≫ z₂ = z₁ ≫ r₁) (hr : r₀ ≫ z₁ = z₀ ≫ s₀)
    (hp : p ≫ z₀ = p) (ha : s₀ ≫ r₁ = -(r₀ ≫ s₁)) :
    (p ≫ r₀ ≫ s₁) ≫ z₂ = -(p ≫ r₀ ≫ s₁) := by
  calc
    _ = p ≫ r₀ ≫ s₁ ≫ z₂ := by simp only [Category.assoc]
    _ = p ≫ r₀ ≫ z₁ ≫ r₁ := by rw [hs]
    _ = p ≫ (r₀ ≫ z₁) ≫ r₁ := by simp only [Category.assoc]
    _ = p ≫ (z₀ ≫ s₀) ≫ r₁ := by rw [hr]
    _ = (p ≫ z₀) ≫ (s₀ ≫ r₁) := by simp only [Category.assoc]
    _ = p ≫ (s₀ ≫ r₁) := by rw [hp]
    _ = _ := by rw [ha, Preadditive.comp_neg]

/-- Pointwise equality of the original entire tracks gives equality of stable operations. -/
theorem stableOperation_eq_of_levels {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f f) (J : Homotopy g g) (h : ∀ n, H.level n = J.level n) (d : ℤ) :
    H.stableOperation d = J.stableOperation d := by
  have hf : f = g := by
    apply LoopPrespectrum.Hom.ext
    funext k
    ext x
    exact (H.at_zero k x).symm.trans
      ((congrArg (fun p => p (0, x)) (h k)).trans (J.at_zero k x))
  subst g
  have hH : H = J := by
    apply LoopPrespectrum.Homotopy.ext
    funext k
    exact h k
  subst J
  rfl

/-- The canonical supported identity action on its original stable groups. -/
def scalarOperation (A : Scheme.OpenPairs.{u}) (r : (Γ(A.right, ⊤))ˣ) (d : ℤ) :
    (stableHomotopyFunctor d).obj
        (prespectrum (boundedAboveFlatGlobalSupportedSectionModel (X := op A.right) A.hom)) ⟶
      (stableHomotopyFunctor (d + 1)).obj
        (prespectrum (boundedAboveFlatGlobalSupportedSectionModel (X := op A.right) A.hom)) :=
  (prespectrumIsoHomotopy
    (𝟙 (boundedAboveFlatGlobalSupportedSectionModel (X := op A.right) A.hom))
    (SupportedTensorEvaluation.unit (X := op A.right) A.hom r)).stableOperation d

/-- Actual supported pair pullback intertwines the complete stable identity action. -/
theorem scalarOperation_pullback {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)
    (r : (Γ(B.right, ⊤))ˣ) (s : (Γ(A.right, ⊤))ˣ)
    (h : Units.map g.right.appTop.hom.toMonoidHom r = s) (d : ℤ) :
    scalarOperation B r d ≫
        (stableHomotopyFunctor (d + 1)).map
      (prespectrumMap (boundedAboveFlatGlobalSupportedPairModelMap g)) =
      (stableHomotopyFunctor d).map
      (prespectrumMap (boundedAboveFlatGlobalSupportedPairModelMap g)) ≫
        scalarOperation A s d := by
  let M := boundedAboveFlatGlobalSupportedPairModelMap g
  let e := SupportedTensorEvaluation.unit (X := op B.right) B.hom r
  let e' := SupportedTensorEvaluation.unit (X := op A.right) A.hom s
  let H := prespectrumIsoHomotopy (𝟙
      (boundedAboveFlatGlobalSupportedSectionModel (X := op B.right) B.hom)) e
  let J := prespectrumIsoHomotopy (𝟙
      (boundedAboveFlatGlobalSupportedSectionModel (X := op A.right) A.hom)) e'
  have hm : 𝟙 _ ≫ M = M ≫ 𝟙 _ := by simp
  have hl (k : ℕ) : (H.postcomp (prespectrumMap M)).level k =
      (J.precomp (prespectrumMap M)).level k := by
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact prespectrumIsoHomotopy_square_apply (𝟙 _) (𝟙 _) M M e e' hm
      (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg (fun k => k.hom.toFunctor) hm))
        e e' (SupportedPairUnit.pairMap_preserves_of_eq g r s h).whisker) k t x
  exact (H.stableOperation_postcomp (prespectrumMap M) d).symm.trans
    ((stableOperation_eq_of_levels _ _ hl d).trans
      (J.stableOperation_precomp (prespectrumMap M) d))

/-- Two arbitrary canonical supported scalar actions have the stable zero-to-two sign. -/
theorem scalarOperation_interchange (A : Scheme.OpenPairs.{u})
    (r s : (Γ(A.right, ⊤))ˣ) :
    scalarOperation A r 0 ≫ scalarOperation A s 1 =
      -(scalarOperation A s 0 ≫ scalarOperation A r 1) := by
  apply AddCommGrpCat.ext
  intro a
  exact stableIdentityAction_interchange_sign
    (boundedAboveFlatGlobalSupportedSectionModel (X := op A.right) A.hom)
    (SupportedTensorEvaluation.unit (X := op A.right) A.hom r)
    (SupportedTensorEvaluation.unit (X := op A.right) A.hom s) 0 a

private def parameterScalar (Q X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :=
  Units.map ((baseProductProjection (specULiftZIsTerminal.from Q)).app X).appTop.hom.toMonoidHom r

private theorem parameterScalar_map (Q : Scheme.{u}) {X Y : Scheme.{u}} (g : X ⟶ Y)
    (r : (Γ(Y, ⊤))ˣ) :
    Units.map ((baseProductFunctor (specULiftZIsTerminal.from Q)).map g).appTop.hom.toMonoidHom
      (parameterScalar Q Y r) =
    parameterScalar Q X (Units.map g.appTop.hom.toMonoidHom r) := by
  apply Units.ext
  have h := congrArg (fun f => f.appTop)
    ((baseProductProjection (specULiftZIsTerminal.from Q)).naturality g)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (r : Γ(Y, ⊤))

private def innerScalar (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  parameterScalar Q (laurent.obj (laurent.obj X.unop))
    (ProductSwapUnit.innerUnit (laurentProjection (.of (ULift.{u} ℤ)))
      (laurentProjection (.of (ULift.{u} ℤ))) X.unop
      (laurentCoordinate (.of (ULift.{u} ℤ))))

set_option backward.isDefEq.respectTransparency.types false in
private theorem projection_scalar (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    Units.map ((baseProductFunctor (specULiftZIsTerminal.from Q)).map
      (coefficient.app (laurent.op.obj X)).unop).appTop.hom.toMonoidHom
      (ParameterLaurentUnit.projectedLaurentScalar Q X) = innerScalar Q X := by
  have h := parameterScalar_map Q (coefficient.app (laurent.op.obj X)).unop
    (GlobalIndex.laurentScalar X)
  have hi : Units.map (coefficient.app (laurent.op.obj X)).unop.appTop.hom.toMonoidHom
      (GlobalIndex.laurentScalar X) =
    ProductSwapUnit.innerUnit (laurentProjection (.of (ULift.{u} ℤ)))
      (laurentProjection (.of (ULift.{u} ℤ))) X.unop
      (laurentCoordinate (.of (ULift.{u} ℤ))) := by
    apply Units.ext
    change ((coefficient.app (laurent.op.obj X)).unop.appTop.hom
        ((pullback.snd (specULiftZIsTerminal.from X.unop)
          (laurentProjection (.of (ULift.{u} ℤ)))).appTop.hom
            (↑(laurentCoordinate (.of (ULift.{u} ℤ)))))) =
      (ProductSwapUnit.innerProjection (laurentProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) X.unop).appTop.hom
          (↑(laurentCoordinate (.of (ULift.{u} ℤ))))
    rw [ProductSwapUnit.innerProjection, Scheme.Hom.comp_appTop]
    rfl
  exact h.trans (congrArg (parameterScalar Q (laurent.obj (laurent.obj X.unop))) hi)

private def swap (X : Scheme.{u}ᵒᵖ) :
    laurent.obj (laurent.obj X.unop) ⟶ laurent.obj (laurent.obj X.unop) :=
  baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
    (laurentProjection (.of (ULift.{u} ℤ))) X.unop

set_option backward.isDefEq.respectTransparency.types false in
private theorem swap_outer_scalar (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    Units.map
      ((baseProductFunctor (specULiftZIsTerminal.from Q)).map (swap X)).appTop.hom.toMonoidHom
      (ParameterLaurentUnit.projectedLaurentScalar Q (laurent.op.obj X)) = innerScalar Q X := by
  have h := parameterScalar_map Q (swap X)
    (ProductSwapUnit.outerUnit (laurentProjection (.of (ULift.{u} ℤ)))
      (laurentProjection (.of (ULift.{u} ℤ))) X.unop
      (laurentCoordinate (.of (ULift.{u} ℤ))))
  have hs := ProductSwapUnit.swap_unit (laurentProjection (.of (ULift.{u} ℤ)))
    (laurentProjection (.of (ULift.{u} ℤ))) X.unop
    (laurentCoordinate (.of (ULift.{u} ℤ)))
  exact h.trans (congrArg (parameterScalar Q (laurent.obj (laurent.obj X.unop))) hs)

set_option backward.isDefEq.respectTransparency.types false in
private theorem swap_inner_scalar (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    Units.map
      ((baseProductFunctor (specULiftZIsTerminal.from Q)).map (swap X)).appTop.hom.toMonoidHom
      (innerScalar Q X) = ParameterLaurentUnit.projectedLaurentScalar Q (laurent.op.obj X) := by
  have h := parameterScalar_map Q (swap X)
    (ProductSwapUnit.innerUnit (laurentProjection (.of (ULift.{u} ℤ)))
      (laurentProjection (.of (ULift.{u} ℤ))) X.unop
      (laurentCoordinate (.of (ULift.{u} ℤ))))
  have hs := ProductSwapOuterUnit.swap_outer_unit (laurentProjection (.of (ULift.{u} ℤ)))
    (laurentProjection (.of (ULift.{u} ℤ))) X.unop
    (laurentCoordinate (.of (ULift.{u} ℤ)))
  exact h.trans (congrArg (parameterScalar Q (laurent.obj (laurent.obj X.unop))) hs)

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The existing supported projection track retains its exact stable identity-action factor. -/
theorem parameterTrack_operation (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    ((ParameterLaurentTrack.supportedTrack f).homotopy X).stableOperation d =
      (stableHomotopyFunctor d).map
        (prespectrumMap ((ParameterModels.supported f).map (coefficient.app X))) ≫
      scalarOperation (pair f (laurent.op.obj X).unop)
        (ParameterLaurentUnit.projectedLaurentScalar Q X) d := by
  rw [stableOperation_eq_of_levels _ _ (SupportedPairUnit.parameterTrack_level f X)]
  exact Homotopy.stableOperation_precomp _ _ d

/-- The unchanged two original supported Laurent projection operations in stable degrees zero and
one, before taking either Laurent quotient. -/
def doubleUnit (X : Scheme.{u}ᵒᵖ) :
    (stableHomotopyFunctor 0).obj (prespectrum ((ParameterModels.supported f).obj X)) ⟶
      (stableHomotopyFunctor 2).obj
        (prespectrum ((ParameterModels.supported f).obj (laurent.op.obj (laurent.op.obj X)))) :=
  ((ParameterLaurentTrack.supportedTrack f).homotopy X).stableOperation 0 ≫
    ((ParameterLaurentTrack.supportedTrack f).homotopy (laurent.op.obj X)).stableOperation 1

set_option maxHeartbeats 500000 in
-- Stable-group pullbacks at the two iterated supported charts are definitionally identified.
set_option backward.isDefEq.respectTransparency.types false in
private theorem doubleUnit_factor (X : Scheme.{u}ᵒᵖ) :
    doubleUnit f X =
      (stableHomotopyFunctor 0).map
        (prespectrumMap ((ParameterModels.supported f).map (coefficient.app X))) ≫
      (stableHomotopyFunctor 0).map
        (prespectrumMap ((ParameterModels.supported f).map
          (coefficient.app (laurent.op.obj X)))) ≫
      scalarOperation (pair f (laurent.op.obj (laurent.op.obj X)).unop) (innerScalar Q X) 0 ≫
      scalarOperation (pair f (laurent.op.obj (laurent.op.obj X)).unop)
        (ParameterLaurentUnit.projectedLaurentScalar Q (laurent.op.obj X)) 1 := by
  have h :
      scalarOperation (pair f (laurent.op.obj X).unop)
          (ParameterLaurentUnit.projectedLaurentScalar Q X) 0 ≫
        (stableHomotopyFunctor 1).map
          (prespectrumMap ((ParameterModels.supported f).map
            (coefficient.app (laurent.op.obj X)))) =
      (stableHomotopyFunctor 0).map
          (prespectrumMap ((ParameterModels.supported f).map
            (coefficient.app (laurent.op.obj X)))) ≫
        scalarOperation (pair f (laurent.op.obj (laurent.op.obj X)).unop)
          (innerScalar Q X) 0 :=
    scalarOperation_pullback (pairMap f (coefficient.app (laurent.op.obj X)).unop)
      (ParameterLaurentUnit.projectedLaurentScalar Q X) (innerScalar Q X)
      (projection_scalar Q X) 0
  let map (d : ℤ) {Y Z : Scheme.{u}ᵒᵖ} (g : Y ⟶ Z) :=
    (stableHomotopyFunctor d).map (prespectrumMap ((ParameterModels.supported f).map g))
  let LX := laurent.op.obj X
  let LLX := laurent.op.obj LX
  let r := scalarOperation (pair f LX.unop) (ParameterLaurentUnit.projectedLaurentScalar Q X) 0
  let i := scalarOperation (pair f LLX.unop) (innerScalar Q X) 0
  let o := scalarOperation (pair f LLX.unop) (ParameterLaurentUnit.projectedLaurentScalar Q LX) 1
  have h' := four_comp (map 0 (coefficient.app X)) r
    (map 1 (coefficient.app LX)) (map 0 (coefficient.app LX)) i o h
  rw [doubleUnit, parameterTrack_operation, parameterTrack_operation]
  exact h'

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual parameter factor interchange negates the two unchanged original supported Laurent
projection operations on stable groups, before either Laurent quotient is taken. -/
theorem doubleUnit_swap (X : Scheme.{u}ᵒᵖ) :
    doubleUnit f X ≫ (stableHomotopyFunctor 2).map
      (prespectrumMap ((ParameterModels.supported f).map
        (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
          (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op)) = -doubleUnit f X := by
  let F := ParameterModels.supported f ⋙ prespectrumFunctor
  let p := F.map (coefficient.app X)
  let q := F.map (coefficient.app (laurent.op.obj X))
  let σ := F.map (swap X).op
  let A := pair f (laurent.op.obj (laurent.op.obj X)).unop
  let r := innerScalar Q X
  let s := ParameterLaurentUnit.projectedLaurentScalar Q (laurent.op.obj X)
  let P := (stableHomotopyFunctor 0).map p
  let Q' := (stableHomotopyFunctor 0).map q
  let S (d : ℤ) := (stableHomotopyFunctor d).map σ
  have hs : scalarOperation A s 1 ≫ S 2 = S 1 ≫ scalarOperation A r 1 :=
    scalarOperation_pullback (pairMap f (swap X)) s r (swap_outer_scalar Q X) 1
  have hr : scalarOperation A r 0 ≫ S 1 = S 0 ≫ scalarOperation A s 0 :=
    scalarOperation_pullback (pairMap f (swap X)) r s (swap_inner_scalar Q X) 0
  have hb : coefficient.app X ≫ coefficient.app (laurent.op.obj X) ≫ (swap X).op =
      coefficient.app X ≫ coefficient.app (laurent.op.obj X) := by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op, Category.assoc]
    exact baseProductSwapMap_fst_fst (laurentProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) X.unop
  have hbase : (P ≫ Q') ≫ S 0 = P ≫ Q' :=
    map_three (F ⋙ stableHomotopyFunctor 0) (coefficient.app X)
      (coefficient.app (laurent.op.obj X)) (swap X).op hb
  have hf : doubleUnit f X = (P ≫ Q') ≫ scalarOperation A r 0 ≫ scalarOperation A s 1 :=
    (doubleUnit_factor f X).trans (Category.assoc P Q' _).symm
  exact (congrArg (fun k => k ≫ S 2) hf).trans
    ((signed_slide (P ≫ Q') (scalarOperation A r 0) (scalarOperation A s 0)
      (scalarOperation A r 1) (scalarOperation A s 1) (S 0) (S 1) (S 2)
      hs hr hbase (scalarOperation_interchange A s r)).trans (congrArg Neg.neg hf).symm)

end AlgebraicGeometry.Scheme.Modules.SupportedParameterDoubleUnit
