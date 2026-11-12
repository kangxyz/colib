/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Limits.PointedSmashFunctor
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# The pointed internal Hom for the smash product

The pointed internal Hom is the fiber of evaluation at the specified point of
the right factor over the specified point of the codomain. Its point is the
transpose of the constant map. Currying converts the first collapsed axis to
the fiber condition and the second collapsed axis to preservation of the point.
Uncurrying descends along the original smash pushout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

/-- The exponential adjunction for the chosen binary product with a fixed right factor. -/
def prodRightIhomAdjunction [CartesianMonoidalCategory C] (Y : C) [Closed Y] :
    prod.functor.flip.obj Y ⊣ ihom Y :=
  (ihom.adjunction Y).ofNatIsoLeft
    (CartesianMonoidalCategory.tensorLeftIsoProd Y ≪≫
      NatIso.ofComponents (fun X ↦ prod.braiding Y X) (by
        intro X X' f
        exact braid_natural (𝟙 Y) f))

namespace Under

variable [HasTerminal C]
variable (Y : Under (⊤_ C))

private abbrev productLeftAxis (X : C) : X ⟶ X ⨯ Y.right :=
  prod.lift (𝟙 X) (terminal.from X ≫ Y.hom)

private theorem productLeftAxis_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ productLeftAxis Y X' =
      productLeftAxis Y X ≫ prod.map f (𝟙 Y.right) := by
  apply prod.hom_ext <;> simp [productLeftAxis]

variable [CartesianMonoidalCategory C] [Closed Y.right]

/-- Evaluate an exponential at the actual basepoint of its source. -/
def pointedIhomEvaluationAtBasepoint (Z : Under (⊤_ C)) :
    (ihom Y.right).obj Z.right ⟶ Z.right :=
  prod.lift (𝟙 _) (terminal.from _ ≫ Y.hom) ≫
    (prodRightIhomAdjunction Y.right).counit.app Z.right

/-- Restricting an uncurried map to the first axis evaluates its transpose at
the basepoint of the right factor. -/
theorem curry_comp_pointedIhomEvaluationAtBasepoint (Z : Under (⊤_ C)) {X : C}
    (f : X ⨯ Y.right ⟶ Z.right) :
    (prodRightIhomAdjunction Y.right).homEquiv X Z.right f ≫
        pointedIhomEvaluationAtBasepoint Y Z =
      prod.lift (𝟙 X) (terminal.from X ≫ Y.hom) ≫ f := by
  let A := prodRightIhomAdjunction Y.right
  let h := A.homEquiv X Z.right f
  have hEval : prod.map h (𝟙 Y.right) ≫ A.counit.app Z.right = f := by
    exact (A.homEquiv X Z.right).symm_apply_apply f
  change h ≫ (productLeftAxis Y _ ≫ A.counit.app _) = productLeftAxis Y X ≫ f
  rw [← Category.assoc, productLeftAxis_naturality, Category.assoc, hEval]

/-- The point of the exponential is the transpose of the actual constant map. -/
def pointedIhomRawPoint (Z : Under (⊤_ C)) : ⊤_ C ⟶ (ihom Y.right).obj Z.right :=
  (prodRightIhomAdjunction Y.right).homEquiv _ _
    (terminal.from ((⊤_ C) ⨯ Y.right) ≫ Z.hom)

private theorem rightAxis_eq_const_iff (X Z : Under (⊤_ C))
    (f : X.right ⨯ Y.right ⟶ Z.right) :
    prod.lift (terminal.from Y.right ≫ X.hom) (𝟙 Y.right) ≫ f =
        terminal.from Y.right ≫ Z.hom ↔
      X.hom ≫ (prodRightIhomAdjunction Y.right).homEquiv X.right Z.right f =
        pointedIhomRawPoint Y Z := by
  let A := prodRightIhomAdjunction Y.right
  let e := Limits.prod.leftUnitor Y.right
  have ha : prod.lift (terminal.from Y.right ≫ X.hom) (𝟙 Y.right) =
      e.inv ≫ prod.map X.hom (𝟙 Y.right) := by
    change prod.lift (terminal.from Y.right ≫ X.hom) (𝟙 Y.right) =
      prod.lift (terminal.from Y.right) (𝟙 Y.right) ≫ prod.map X.hom (𝟙 Y.right)
    apply prod.hom_ext <;> simp
  have hb : terminal.from Y.right ≫ Z.hom =
      e.inv ≫ (terminal.from ((⊤_ C) ⨯ Y.right) ≫ Z.hom) := by simp
  rw [ha, Category.assoc, hb, cancel_epi]
  change prod.map X.hom (𝟙 Y.right) ≫ f =
      terminal.from ((⊤_ C) ⨯ Y.right) ≫ Z.hom ↔
    X.hom ≫ A.homEquiv X.right Z.right f =
      A.homEquiv (⊤_ C) Z.right (terminal.from ((⊤_ C) ⨯ Y.right) ≫ Z.hom)
  rw [← A.homEquiv_naturality_left X.hom f]
  exact (A.homEquiv (⊤_ C) Z.right).injective.eq_iff.symm

private theorem pointedIhomEvaluationAtBasepoint_naturality {Z Z' : Under (⊤_ C)} (g : Z ⟶ Z') :
    (ihom Y.right).map g.right ≫ pointedIhomEvaluationAtBasepoint Y Z' =
      pointedIhomEvaluationAtBasepoint Y Z ≫ g.right := by
  let A := prodRightIhomAdjunction Y.right
  let h := (ihom Y.right).map g.right
  have he : prod.map h (𝟙 Y.right) ≫ A.counit.app Z'.right =
      A.counit.app Z.right ≫ g.right := A.counit.naturality g.right
  change h ≫ (productLeftAxis Y _ ≫ A.counit.app _) =
    (productLeftAxis Y _ ≫ A.counit.app _) ≫ g.right
  rw [← Category.assoc h, productLeftAxis_naturality, Category.assoc, he, Category.assoc]

private theorem pointedIhomRawPoint_naturality {Z Z' : Under (⊤_ C)} (g : Z ⟶ Z') :
    pointedIhomRawPoint Y Z ≫ (ihom Y.right).map g.right = pointedIhomRawPoint Y Z' := by
  unfold pointedIhomRawPoint
  rw [← (prodRightIhomAdjunction Y.right).homEquiv_naturality_right, Category.assoc, Under.w g]

variable [HasPullbacks C]

/-- The pointed internal Hom is the actual fiber over the basepoint of the codomain. -/
def pointedIhom (Z : Under (⊤_ C)) : Under (⊤_ C) :=
  Under.mk (pullback.lift (f := pointedIhomEvaluationAtBasepoint Y Z) (g := Z.hom)
    (pointedIhomRawPoint Y Z) (𝟙 _) (by
    rw [pointedIhomRawPoint, curry_comp_pointedIhomEvaluationAtBasepoint, terminal.comp_from_assoc]
    exact congrArg (fun h : (⊤_ C) ⟶ (⊤_ C) ↦ h ≫ Z.hom) (terminal.hom_ext _ _)))

/-- Include the pointed internal Hom into the native exponential. -/
abbrev pointedIhomι (Z : Under (⊤_ C)) :
    (pointedIhom Y Z).right ⟶ (ihom Y.right).obj Z.right :=
  pullback.fst (pointedIhomEvaluationAtBasepoint Y Z) Z.hom

@[reassoc (attr := simp)]
theorem pointedIhom_hom_ι (Z : Under (⊤_ C)) :
    (pointedIhom Y Z).hom ≫ pointedIhomι Y Z = pointedIhomRawPoint Y Z :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem pointedIhomι_evaluationAtBasepoint (Z : Under (⊤_ C)) :
    pointedIhomι Y Z ≫ pointedIhomEvaluationAtBasepoint Y Z =
      terminal.from (pointedIhom Y Z).right ≫ Z.hom := by
  calc
    _ = pullback.snd (pointedIhomEvaluationAtBasepoint Y Z) Z.hom ≫ Z.hom :=
      pullback.condition
    _ = _ := congrArg (fun h ↦ h ≫ Z.hom) (terminal.hom_ext _ _)

private theorem pointedIhom_hom_ext {X Z : Under (⊤_ C)} {f g : X ⟶ pointedIhom Y Z}
    (h : f.right ≫ pointedIhomι Y Z = g.right ≫ pointedIhomι Y Z) : f = g := by
  apply (Under.forget (⊤_ C)).map_injective
  apply pullback.hom_ext
  · exact h
  · exact terminal.hom_ext _ _

/-- Postcomposition on the actual pointed internal Hom. -/
@[no_expose]
def pointedIhomMap {Z Z' : Under (⊤_ C)} (g : Z ⟶ Z') : pointedIhom Y Z ⟶ pointedIhom Y Z' := by
  let a := pointedIhomι Y Z ≫ (ihom Y.right).map g.right
  have ha : a ≫ pointedIhomEvaluationAtBasepoint Y Z' =
      terminal.from (pointedIhom Y Z).right ≫ Z'.hom := by
    dsimp only [a]
    rw [Category.assoc, pointedIhomEvaluationAtBasepoint_naturality, ← Category.assoc,
      pointedIhomι_evaluationAtBasepoint, Category.assoc, Under.w g]
  let b : (pointedIhom Y Z).right ⟶ (pointedIhom Y Z').right :=
    pullback.lift a (terminal.from _) ha
  have hb : b ≫ pointedIhomι Y Z' = a := pullback.lift_fst _ _ _
  refine Under.homMk b ?_
  apply pullback.hom_ext
  · change ((pointedIhom Y Z).hom ≫ b) ≫ pointedIhomι Y Z' =
      (pointedIhom Y Z').hom ≫ pointedIhomι Y Z'
    rw [Category.assoc, hb, pointedIhom_hom_ι]
    exact (pointedIhom_hom_ι_assoc Y Z _).trans (pointedIhomRawPoint_naturality Y g)
  · exact terminal.hom_ext _ _

@[reassoc (attr := simp)]
theorem pointedIhomMap_ι {Z Z' : Under (⊤_ C)} (g : Z ⟶ Z') :
    (pointedIhomMap Y g).right ≫ pointedIhomι Y Z' =
      pointedIhomι Y Z ≫ (ihom Y.right).map g.right :=
  pullback.lift_fst _ _ _

/-- The pointed internal Hom functor for a fixed pointed source. -/
def pointedIhomFunctor : Under (⊤_ C) ⥤ Under (⊤_ C) where
  obj := pointedIhom Y
  map := pointedIhomMap Y
  map_id _ := by
    apply pointedIhom_hom_ext Y
    simp
  map_comp _ _ := by
    apply pointedIhom_hom_ext Y
    simp [Category.assoc]

variable [HasBinaryCoproducts C] [HasPushouts C]

/-- Curry a map from the actual smash product into the pointed internal Hom. -/
@[no_expose]
def smashRightCurry {X Z : Under (⊤_ C)} (f : smash X Y ⟶ Z) : X ⟶ pointedIhom Y Z := by
  let m := toSmash X Y ≫ f.right
  let h := (prodRightIhomAdjunction Y.right).homEquiv X.right Z.right m
  have hEval : h ≫ pointedIhomEvaluationAtBasepoint Y Z = terminal.from X.right ≫ Z.hom := by
    dsimp only [h, m]
    rw [curry_comp_pointedIhomEvaluationAtBasepoint, leftAxis_toSmash_assoc, Under.w f]
  have hPoint : X.hom ≫ h = pointedIhomRawPoint Y Z :=
    (rightAxis_eq_const_iff Y X Z m).mp (by
      dsimp only [m]
      rw [rightAxis_toSmash_assoc, Under.w f])
  let b : X.right ⟶ (pointedIhom Y Z).right := pullback.lift h (terminal.from _) hEval
  have hb : b ≫ pointedIhomι Y Z = h := pullback.lift_fst _ _ _
  refine Under.homMk b ?_
  apply pullback.hom_ext
  · change (X.hom ≫ b) ≫ pointedIhomι Y Z =
      (pointedIhom Y Z).hom ≫ pointedIhomι Y Z
    rw [Category.assoc, hb, pointedIhom_hom_ι]
    exact hPoint
  · exact terminal.hom_ext _ _

@[reassoc (attr := simp)]
theorem smashRightCurry_ι {X Z : Under (⊤_ C)} (f : smash X Y ⟶ Z) :
    (smashRightCurry Y f).right ≫ pointedIhomι Y Z =
      (prodRightIhomAdjunction Y.right).homEquiv X.right Z.right (toSmash X Y ≫ f.right) :=
  pullback.lift_fst _ _ _

/-- Uncurry a pointed map into the internal Hom and descend through both axes. -/
@[no_expose]
def smashRightUncurry {X Z : Under (⊤_ C)} (g : X ⟶ pointedIhom Y Z) : smash X Y ⟶ Z := by
  let E := (prodRightIhomAdjunction Y.right).homEquiv X.right Z.right
  let m := E.symm (g.right ≫ pointedIhomι Y Z)
  have hm : (prodRightIhomAdjunction Y.right).homEquiv X.right Z.right m =
      g.right ≫ pointedIhomι Y Z := E.apply_symm_apply _
  have hLeft : prod.lift (𝟙 X.right) (terminal.from X.right ≫ Y.hom) ≫ m =
      terminal.from X.right ≫ Z.hom := by
    rw [← curry_comp_pointedIhomEvaluationAtBasepoint, hm, Category.assoc,
      pointedIhomι_evaluationAtBasepoint, terminal.comp_from_assoc]
  have hRight : prod.lift (terminal.from Y.right ≫ X.hom) (𝟙 Y.right) ≫ m =
      terminal.from Y.right ≫ Z.hom :=
    (rightAxis_eq_const_iff Y X Z m).mpr (by
      rw [hm, ← Category.assoc, Under.w g, pointedIhom_hom_ι])
  have hAxes : axesToProduct X Y ≫ m = terminal.from (X.right ⨿ Y.right) ≫ Z.hom := by
    apply coprod.hom_ext
    · rw [← Category.assoc, axesToProduct, coprod.inl_desc, hLeft, terminal.comp_from_assoc]
    · rw [← Category.assoc, axesToProduct, coprod.inr_desc, hRight, terminal.comp_from_assoc]
  exact Under.homMk (pushout.desc m Z.hom hAxes) (pushout.inr_desc _ _ _)

@[reassoc (attr := simp)]
theorem toSmash_smashRightUncurry {X Z : Under (⊤_ C)} (g : X ⟶ pointedIhom Y Z) :
    toSmash X Y ≫ (smashRightUncurry Y g).right =
      ((prodRightIhomAdjunction Y.right).homEquiv X.right Z.right).symm
        (g.right ≫ pointedIhomι Y Z) :=
  pushout.inl_desc _ _ _

/-- The pointed currying equivalence for the actual smash quotient. -/
def smashRightHomEquiv (X Z : Under (⊤_ C)) :
    (smash X Y ⟶ Z) ≃ (X ⟶ pointedIhom Y Z) where
  toFun := smashRightCurry Y
  invFun := smashRightUncurry Y
  left_inv f := by
    apply smash_hom_ext
    simp
  right_inv g := by
    apply pointedIhom_hom_ext Y
    simp

/-- Smash on the right is left adjoint to the pointed internal Hom. -/
def smashRightAdjunction : smashRightFunctor Y ⊣ pointedIhomFunctor Y :=
  Adjunction.mkOfHomEquiv {
    homEquiv := smashRightHomEquiv Y
    homEquiv_naturality_left_symm := by
      intro X' X Z f g
      let g' : X ⟶ pointedIhom Y Z := g
      let A := prodRightIhomAdjunction Y.right
      apply smash_hom_ext
      change toSmash X' Y ≫ (smashRightUncurry Y (f ≫ g')).right =
        toSmash X' Y ≫ (smashMap f (𝟙 Y) ≫ smashRightUncurry Y g').right
      calc
        _ = (A.homEquiv X'.right Z.right).symm
            (f.right ≫ (g'.right ≫ pointedIhomι Y Z)) := by
          rw [toSmash_smashRightUncurry, Under.comp_right, Category.assoc]
        _ = prod.map f.right (𝟙 Y.right) ≫
            (toSmash X Y ≫ (smashRightUncurry Y g').right) := by
          rw [toSmash_smashRightUncurry]
          exact A.homEquiv_naturality_left_symm f.right _
        _ = _ := by
          rw [Under.comp_right, toSmash_smashMap_assoc]
          rfl
    homEquiv_naturality_right := by
      intro X Z Z' f g
      let f' : smash X Y ⟶ Z := f
      let A := prodRightIhomAdjunction Y.right
      apply pointedIhom_hom_ext Y
      change (smashRightCurry Y (f' ≫ g)).right ≫ pointedIhomι Y Z' =
        (smashRightCurry Y f' ≫ pointedIhomMap Y g).right ≫ pointedIhomι Y Z'
      calc
        _ = A.homEquiv X.right Z'.right ((toSmash X Y ≫ f'.right) ≫ g.right) := by
          rw [smashRightCurry_ι, Under.comp_right, Category.assoc]
        _ = A.homEquiv X.right Z.right (toSmash X Y ≫ f'.right) ≫
            (ihom Y.right).map g.right := A.homEquiv_naturality_right _ _
        _ = _ := by
          rw [Under.comp_right, Category.assoc, pointedIhomMap_ι, ← Category.assoc,
            smashRightCurry_ι] }

/-- The adjunction uses the pointed currying equivalence on the actual maps. -/
@[simp]
theorem smashRightAdjunction_homEquiv (X Z : Under (⊤_ C)) :
    (smashRightAdjunction Y).homEquiv X Z = smashRightHomEquiv Y X Z := by
  rw [smashRightAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

end Under
end CategoryTheory
