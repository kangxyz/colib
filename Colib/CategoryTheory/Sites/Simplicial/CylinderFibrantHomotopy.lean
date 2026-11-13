/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.CylinderHomotopyClasses
public import Colib.CategoryTheory.Sites.Simplicial.CylinderBoundaryTrivial
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseMappingCylinder

/-!
# Cylinder homotopies into an injective fibrant target

Extension against a stalkwise trivial monomorphism gives surjectivity
on homotopy classes. The relative cylinder boundary lets a homotopy
between the restricted maps extend with both endpoints prescribed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {X Y E : PointedSimplicialPresheaf.{w} C}

/-- Maps into an injective fibrant target extend over every stalkwise
trivial monomorphism. -/
theorem surjective_precomp_of_isStalkwiseInjectiveFibrant
    (hE : IsStalkwiseInjectiveFibrant C J E) (i : X ⟶ Y)
    (hi : stalkwiseTrivialMonomorphisms C J i) :
    Function.Surjective (fun f : Y ⟶ E ↦ i ≫ f) := by
  intro f
  let sq : CommSq f i (toPoint C E) (toPoint C Y) :=
    ⟨(point_isZero C).isTerminal.hom_ext _ _⟩
  let : HasLiftingProperty i (toPoint C E) := hE i hi
  exact ⟨sq.lift, sq.fac_left⟩

variable [LocallySmall.{w} C]

/-- A homotopy between the restrictions of two original maps extends
to a homotopy with those maps as its actual endpoints. -/
theorem cylinderHomotopic_of_precomp_of_isStalkwiseInjectiveFibrant
    (hE : IsStalkwiseInjectiveFibrant C J E) {i : X ⟶ Y}
    (hi : stalkwiseTrivialMonomorphisms C J i) {f g : Y ⟶ E}
    (hfg : CylinderHomotopic (i ≫ f) (i ≫ g)) : CylinderHomotopic f g := by
  obtain ⟨h, hf, hg⟩ := hfg
  have hw : simplicialEndpointPair X ≫ h = coprod.map i i ≫ coprod.desc f g := by
    apply coprod.hom_ext
    · simpa only [simplicialEndpointPair, coprod.inl_desc_assoc, coprod.inl_map_assoc,
        coprod.inl_desc] using hf
    · simpa only [simplicialEndpointPair, coprod.inr_desc_assoc, coprod.inr_map_assoc,
        coprod.inr_desc] using hg
  let a := pushout.desc h (coprod.desc f g) hw
  let b := cylinderBoundaryMap i
  let sq : CommSq a b (toPoint C E) (toPoint C (parameterizedCylinder Y (interval C))) :=
    ⟨(point_isZero C).isTerminal.hom_ext _ _⟩
  let : HasLiftingProperty b (toPoint C E) :=
    hE b (stalkwiseTrivialMonomorphisms_cylinderBoundaryMap i J hi)
  let H := sq.lift
  let j := pushout.inr (simplicialEndpointPair X) (coprod.map i i)
  have hb : simplicialEndpointPair Y ≫ H = coprod.desc f g := by
    calc
      _ = j ≫ b ≫ H := ((cylinderBoundary_inr_map_assoc i H)).symm
      _ = j ≫ a := congrArg (j ≫ ·) sq.fac_left
      _ = _ := pushout.inr_desc _ _ _
  refine ⟨H, ?_, ?_⟩
  · simpa only [simplicialEndpointPair, coprod.inl_desc_assoc, coprod.inl_desc] using
      congrArg ((coprod.inl : Y ⟶ Y ⨿ Y) ≫ ·) hb
  · simpa only [simplicialEndpointPair, coprod.inr_desc_assoc, coprod.inr_desc] using
      congrArg ((coprod.inr : Y ⟶ Y ⨿ Y) ≫ ·) hb

omit [LocallySmall.{w} C] in
/-- The actual map of cylinders gives precomposition of their homotopies. -/
theorem cylinderHomotopic_precompose {V : PointedSimplicialPresheaf.{w} C}
    (i : V ⟶ X) {f g : X ⟶ E} (hfg : CylinderHomotopic f g) :
    CylinderHomotopic (i ≫ f) (i ≫ g) := by
  obtain ⟨h, hf, hg⟩ := hfg
  refine ⟨parameterizedCylinderMap i (interval C) ≫ h, ?_, ?_⟩
  · exact (cylinderSection_parameterizedCylinderMap_assoc i (intervalEndpoint C 0) h).trans
      (congrArg (i ≫ ·) hf)
  · exact (cylinderSection_parameterizedCylinderMap_assoc i (intervalEndpoint C 1) h).trans
      (congrArg (i ≫ ·) hg)

/-- Precomposition acts on the actual pointed cylinder homotopy classes. -/
def cylinderHomotopyPrecomp (i : X ⟶ Y) :
    CylinderHomotopyClasses Y E → CylinderHomotopyClasses X E :=
  _root_.Quotient.map (i ≫ ·) (by
    intro f g h
    change Relation.EqvGen CylinderHomotopic f g at h
    change Relation.EqvGen CylinderHomotopic (i ≫ f) (i ≫ g)
    induction h with
    | rel f g h => exact .rel _ _ (cylinderHomotopic_precompose i h)
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih')

/-- On fibrant targets, a trivial monomorphism induces a bijection
on the homotopy classes of the original pointed cylinder. -/
theorem bijective_cylinderHomotopyPrecomp_of_trivialMono
    (hE : IsStalkwiseInjectiveFibrant C J E) (i : X ⟶ Y)
    (hi : stalkwiseTrivialMonomorphisms C J i) :
    Function.Bijective (cylinderHomotopyPrecomp (E := E) i) := by
  have hsurj := surjective_precomp_of_isStalkwiseInjectiveFibrant J hE i hi
  refine ⟨?_, ?_⟩
  · intro f g
    refine _root_.Quotient.inductionOn₂ f g (fun f g eq ↦ ?_)
    change _root_.Quotient.mk _ (i ≫ f) = _root_.Quotient.mk _ (i ≫ g) at eq
    apply _root_.Quotient.sound
    change Relation.EqvGen CylinderHomotopic f g
    have liftClass : ∀ {f g : X ⟶ E}, Relation.EqvGen CylinderHomotopic f g →
        ∀ (a b : Y ⟶ E), i ≫ a = f → i ≫ b = g → Relation.EqvGen CylinderHomotopic a b := by
      intro f g h
      induction h with
      | rel f g h =>
        intro a b ha hb
        exact .rel _ _ (cylinderHomotopic_of_precomp_of_isStalkwiseInjectiveFibrant J hE hi
          (ha.symm ▸ hb.symm ▸ h))
      | refl f =>
        intro a b ha hb
        have h : CylinderHomotopic (i ≫ a) (i ≫ b) := by
          rw [ha, hb]
          exact ⟨cylinderProjection X (interval C) ≫ f,
            cylinderSection_projection_assoc _ _ _, cylinderSection_projection_assoc _ _ _⟩
        exact .rel _ _ (cylinderHomotopic_of_precomp_of_isStalkwiseInjectiveFibrant J hE hi h)
      | symm _ _ _ ih =>
        intro a b ha hb
        exact .symm _ _ (ih b a hb ha)
      | trans _ g _ _ _ ih₁ ih₂ =>
        intro a b ha hb
        obtain ⟨c, hc⟩ := hsurj g
        exact .trans _ _ _ (ih₁ a c ha hc) (ih₂ c b hc hb)
    exact liftClass (_root_.Quotient.exact eq) f g rfl rfl
  · intro f
    refine _root_.Quotient.inductionOn f (fun g ↦ ?_)
    obtain ⟨a, ha⟩ := hsurj g
    exact ⟨_root_.Quotient.mk _ a, congrArg (_root_.Quotient.mk _) ha⟩

/-- Every stalkwise weak equivalence acts bijectively on the original
cylinder homotopy classes into a fibrant pointed presheaf. -/
theorem bijective_cylinderHomotopyPrecomp_of_stalkwiseWeakEquivalence
    (hE : IsStalkwiseInjectiveFibrant C J E) (f : X ⟶ Y)
    (hf : stalkwiseWeakEquivalences C J f) :
    Function.Bijective (cylinderHomotopyPrecomp (E := E) f) := by
  let a := mappingCylinderSource f
  let b := mappingCylinderTarget f
  let p := mappingCylinderProjection f
  let A := cylinderHomotopyPrecomp (E := E) a
  let B := cylinderHomotopyPrecomp (E := E) b
  let P := cylinderHomotopyPrecomp (E := E) p
  have ha : Function.Bijective A := bijective_cylinderHomotopyPrecomp_of_trivialMono J hE a
    (stalkwiseTrivialMonomorphisms_mappingCylinderSource J hf)
  have hb : Function.Bijective B := bijective_cylinderHomotopyPrecomp_of_trivialMono J hE b
    (stalkwiseTrivialMonomorphisms_mappingCylinderTarget J f)
  have hBP : B ∘ P = id := by
    funext q
    refine _root_.Quotient.inductionOn q (fun g ↦ ?_)
    change _root_.Quotient.mk _ (b ≫ p ≫ g) = _root_.Quotient.mk _ g
    exact congrArg (_root_.Quotient.mk _) (mappingCylinderTarget_projection_assoc f g)
  have hp : Function.Bijective P := (Function.Bijective.of_comp_iff' hb P).1
    (hBP.symm ▸ Function.bijective_id)
  have hAP : A ∘ P = cylinderHomotopyPrecomp (E := E) f := by
    funext q
    refine _root_.Quotient.inductionOn q (fun g ↦ ?_)
    change _root_.Quotient.mk _ (a ≫ p ≫ g) = _root_.Quotient.mk _ (f ≫ g)
    exact congrArg (_root_.Quotient.mk _) (mappingCylinderSource_projection_assoc f g)
  rw [← hAP]
  exact ha.comp hp

/-- Cylinder homotopy classes into a fixed pointed target are
contravariantly functorial in the source. -/
def cylinderHomotopyClassesFunctor (E : PointedSimplicialPresheaf.{w} C) :
    (PointedSimplicialPresheaf.{w} C)ᵒᵖ ⥤ Type (max u w) where
  obj X := CylinderHomotopyClasses X.unop E
  map f := ↾cylinderHomotopyPrecomp f.unop
  map_id X := by
    ext q
    refine _root_.Quotient.inductionOn q (fun f ↦ ?_)
    change _root_.Quotient.mk _ ((𝟙 X.unop) ≫ f) = _root_.Quotient.mk _ f
    exact congrArg (_root_.Quotient.mk _) (Category.id_comp f)
  map_comp f g := by
    ext q
    refine _root_.Quotient.inductionOn q (fun h ↦ ?_)
    change _root_.Quotient.mk _ ((g.unop ≫ f.unop) ≫ h) =
      _root_.Quotient.mk _ (g.unop ≫ f.unop ≫ h)
    exact congrArg (_root_.Quotient.mk _) (Category.assoc _ _ _)

omit [LocallySmall.{w} C] in
/-- The strict map comparison sends a morphism to its cylinder class. -/
theorem cylinderHomotopyClassesFunctor_map_mk (i : X ⟶ Y) (f : Y ⟶ E) :
    (cylinderHomotopyClassesFunctor E).map i.op (_root_.Quotient.mk _ f) =
      _root_.Quotient.mk _ (i ≫ f) := by
  change cylinderHomotopyPrecomp i (_root_.Quotient.mk _ f) = _
  rfl

end CategoryTheory.PointedSimplicialPresheaf
