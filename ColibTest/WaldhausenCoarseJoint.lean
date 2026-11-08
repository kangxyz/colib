/- Regression tests for the actual coarse joint cylinder and its row consumer. -/
module

import Colib.CategoryTheory.Waldhausen.Fibration.Rows.CoarseJoint

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration RowFactorization

noncomputable section
universe u v
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : JointData N)

-- Coarse source weakness needs only gluing, without two-out-of-three or fine weakness.
example {f g : Arrow C} (α : f ⟶ g)
    (hl : N.coarse.weq α.left) (hr : N.coarse.weq α.right) :
    N.coarse.weq ((D.joint.map α).hom.left) := jointSource_coarseWeak N D α hl hr

example (f : Arrow C) :
    IsPushout (N.coarse.isZero.to_ f.left) (N.coarse.isZero.to_ f.right)
      (D.inl.app f) (D.inr.app f) := jointSource_coarse_isPushout N D f

variable [N.coarse.weq.HasTwoOutOfThreeProperty]

-- The middle map requires weakness of the target component only.
example {f g : Arrow C} (α : f ⟶ g) (hr : N.coarse.weq α.right) :
    N.coarse.weq ((D.joint.map α).hom.right) := jointMiddle_coarseWeak N D α hr

example : JointData (NestedWeakEquivalences.refl N.coarse) := D.coarseReflexive N

example : IsExact (ArrowCategory.waldhausenStructure N.coarse).cof
    (ArrowCategory.waldhausenStructure N.coarse).weq
    (ExtensionCategory.waldhausenStructure N.coarse).cof
    (ExtensionCategory.waldhausenStructure N.coarse).weq (coarseJoint N D) :=
  coarseJoint_exact N D

-- The entire source and middle functors, not just their objects, are unchanged.
example : (D.coarseReflexive N).joint ⋙ ExtensionCategory.source N.coarse =
    D.joint ⋙ ExtensionCategory.source V := rfl

example : (D.coarseReflexive N).joint ⋙ ExtensionCategory.middle N.coarse =
    D.joint ⋙ ExtensionCategory.middle V := rfl

example : (D.coarseReflexive N).inl = D.inl := rfl
example : (D.coarseReflexive N).inr = D.inr := rfl
example : (D.coarseReflexive N).projection = D.projection := rfl

example (f : Arrow C) :
    N.coarse.cof (((D.coarseReflexive N).joint.obj f).obj.hom) :=
  ((D.coarseReflexive N).joint.obj f).property

example {A B E P : Arrow C} {i : A ⟶ B} {f : A ⟶ E} {g : B ⟶ P} {j : E ⟶ P}
    (hi : (ArrowCategory.waldhausenStructure N.coarse).cof i) (h : IsPushout i f g j) :
    IsPushout ((coarseJoint N D).map i) ((coarseJoint N D).map f)
      ((coarseJoint N D).map g) ((coarseJoint N D).map j) :=
  (coarseJoint_exact N D).pushout hi h

-- Existing row factorization consumes the genuinely coarse-exact data directly.
example (n : SimplexCategory) :
    FunctorialFactorization (QuotientRows.waldhausenStructure N.coarse n) :=
  QuotientRows.factorizationOfJointData N.coarse (D.coarseReflexive N) n

example {n : SimplexCategory} (f : Arrow (QuotientRows.Obj N.coarse n)) (p : Interval n) :
    ((QuotientRows.factorizationOfJointData N.coarse (D.coarseReflexive N) n).projection.app
      f).hom.app p = D.projection.app (Arrow.mk (f.hom.hom.app p)) := rfl

example {n : SimplexCategory} (f : Arrow (QuotientRows.Obj N.coarse n)) (p : Interval n) :
    ((QuotientRows.factorizationOfJointData N.coarse (D.coarseReflexive N) n).inclusion.app
      f).hom.app p = D.inl.app (Arrow.mk (f.hom.hom.app p)) ≫
        (D.joint.obj (Arrow.mk (f.hom.hom.app p))).obj.hom := rfl
