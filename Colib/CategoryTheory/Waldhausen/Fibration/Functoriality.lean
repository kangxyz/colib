/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory

/-!
# Actual functors on coarse-acyclic categories

A functor exact for both nested structures restricts to the original full
subcategories. This categorical layer retains exactness and the actual
identity, composition, chosen-zero and natural-isomorphism laws.

Implementation provenance: adapted from
`Quillen/Waldhausen/Fibration/Functoriality.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual objects, functors,
chosen zero data, exactness witnesses and shared universe pair are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D}
  (N : NestedWeakEquivalences V) (M : NestedWeakEquivalences W)
  {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq F)

include hFc in
/-- Coarse exactness preserves actual coarse-acyclic objects. -/
lemma map_acyclic {X : C} (hX : Acyclic N.coarse X) : Acyclic M.coarse (F.obj X) := by
  let e := M.coarse.isZero.iso (hFc.zero N.coarse.isZero)
  have h := M.coarse.weq.comp_mem e.hom (F.map (N.coarse.isZero.to_ X))
    (M.coarse.weq_iso _ inferInstance) (hFc.weak _ hX)
  change M.coarse.weq (M.coarse.isZero.to_ (F.obj X))
  rw [← M.coarse.isZero.eq_of_src (e.hom ≫ F.map (N.coarse.isZero.to_ X))
    (M.coarse.isZero.to_ (F.obj X))]
  exact h

/-- Restrict the original exact functor to the acyclic-object subcategories. -/
def acyclicFunctor : AcyclicCategory N ⥤ AcyclicCategory M :=
  (acyclicObjects M).lift (acyclicInclusion N ⋙ F) (fun X => map_acyclic N M hFc X.property)

include hF in
/-- The acyclic restriction is exact for the inherited fine structures. -/
lemma acyclicFunctor_exact : IsExact (acyclicStructure N).cof (acyclicStructure N).weq
    (acyclicStructure M).cof (acyclicStructure M).weq (acyclicFunctor N M hFc) where
  zero hz := IsZero.of_full_of_faithful_of_isZero (acyclicObjects M).ι _
    (hF.zero ((acyclicInclusion_exact N).zero hz))
  cofibration f hf := hF.cofibration f.hom hf
  weak f hf := hF.weak f.hom hf
  pushout hi hp := IsPushout.of_map_of_faithful (acyclicObjects M).ι
    (hF.pushout hi (acyclicInclusion_map_pushout N hi hp))

/-- Restricting the identity gives the actual identity functor. -/
lemma acyclicFunctor_id : acyclicFunctor N N (IsExact.id N.coarse.cof N.coarse.weq) =
    𝟭 (AcyclicCategory N) := rfl

/-- Restriction preserves composition of the original functors exactly. -/
lemma acyclicFunctor_comp {E : Type u} [Category.{v} E] {T : Structure E}
    (L : NestedWeakEquivalences T) {G : D ⥤ E}
    (hGc : IsExact M.coarse.cof M.coarse.weq L.coarse.cof L.coarse.weq G) :
    acyclicFunctor N L (hFc.comp hGc) =
      acyclicFunctor N M hFc ⋙ acyclicFunctor M L hGc := rfl

/-- The restricted functor commutes strictly with the actual inclusions. -/
lemma acyclicFunctor_inclusion : acyclicFunctor N M hFc ⋙ acyclicInclusion M =
    acyclicInclusion N ⋙ F := rfl

/-- A chosen-zero equality restricts to the inherited chosen zeros. -/
lemma acyclicFunctor_zero (h0 : F.obj V.zero = W.zero) :
    (acyclicFunctor N M hFc).obj (acyclicStructure N).zero = (acyclicStructure M).zero := by
  apply ObjectProperty.FullSubcategory.ext
  exact h0

/-- The same chosen-zero equality holds for the coarse structures. -/
lemma coarse_zero_eq (h0 : F.obj V.zero = W.zero) : F.obj N.coarse.zero = M.coarse.zero := by
  rw [N.zero_eq, M.zero_eq, h0]

/-- Lift an isomorphism of the original functors to their acyclic restrictions. -/
def acyclicFunctorIso {G : C ⥤ D}
    (hGc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq G) (e : F ≅ G) :
    acyclicFunctor N M hFc ≅ acyclicFunctor N M hGc :=
  NatIso.ofComponents (fun X => (acyclicObjects M).isoMk (e.app X.obj)) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    exact e.hom.naturality f.hom)


end CategoryTheory.Waldhausen.Fibration
