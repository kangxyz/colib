/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Colib.CategoryTheory.QConstruction.Connected
public import Colib.KTheory.Quillen.Localization.Serre.Target
public import Colib.Topology.HomotopyFiber.BasedHomotopyConnecting
public import Colib.KTheory.Quillen.Map.NaturalIso
public import Colib.CategoryTheory.TheoremB.NaturalTransformationFiberCancellation
public import Colib.Topology.ClassifyingSpace.FunctorChain

/-!
# Naturality of the original Serre-localization boundaries

An exact ambient functor preserving one Serre class into another restricts to
an actual exact support functor. Given an exact functor between the actual
localization targets and an ordinary localization-square natural isomorphism,
`actualConnectingHom_naturality` proves naturality of the original
`actualConnectingHom` in every degree.

The formal-quotient functor is constructed using the canonical target-lift
equivalences. Its normalized square retains the actual natural-isomorphism
track. `canonicalComparisonNaturalityHomotopy` constructs the whole comparison
homotopy relative to the actual support zero: the canonical zero arrows make
the transformation triangle commute, and its two-simplex cancels the reversed
square track before moving the source along the support-inclusion comparison.
The full track stays constant at zero by the thin Q-zero-target property.
No boundary or fiber-comparison naturality law is an input.

All categories and hom spaces in this native version use the same universe.
The ordinary target-square natural isomorphism is retained as an explicit input;
its construction for a particular scalar-localization functor belongs to that
application.
-/

/-! Implementation source: `Quillen/Localization/Serre/Naturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; actual maps, basepoints and tracks are retained. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite MonoidalCategory Convexity Topology HomotopyGroup
open scoped Simplicial Topology unitInterval

namespace CategoryTheory.ExactCategory.SerreLocalization.Naturality

variable {A C D E : Type u}
  [SmallCategory A] [SmallCategory C] [SmallCategory D] [SmallCategory E]

/-- Apply the target functor to every component of the specified constant-target transformation. -/
def mapZeroTransformation {K : A ⥤ D} (d : D)
    (ε : K ⟶ (Functor.const A).obj d) (G : D ⥤ E) :
    K ⋙ G ⟶ (Functor.const A).obj (G.obj d) where
  app a := G.map (ε.app a)
  naturality a b f := by
    change G.map (K.map f) ≫ G.map (ε.app b) = G.map (ε.app a) ≫ 𝟙 (G.obj d)
    calc
      _ = G.map (K.map f ≫ ε.app b) := (G.map_comp _ _).symm
      _ = G.map (ε.app a ≫ 𝟙 d) := congrArg G.map (ε.naturality f)
      _ = G.map (ε.app a) ≫ G.map (𝟙 d) := G.map_comp _ _
      _ = _ := congrArg (fun k => G.map (ε.app a) ≫ k) (G.map_id d)

theorem mapZeroTransformation_cylinder {K : A ⥤ D} (d : D)
    (ε : K ⟶ (Functor.const A).obj d) (G : D ⥤ E) :
    naturalTransformationCylinderFunctor (mapZeroTransformation d ε G) =
      naturalTransformationCylinderFunctor ε ⋙ G := by
  apply Functor.curry_obj_injective
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro a b f
    simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
      Functor.uncurry, ComposableArrows.mk₁, mapZeroTransformation]
  · refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro a b f
    simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
      Functor.uncurry, ComposableArrows.mk₁]
  · ext a
    simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
      Functor.uncurry, ComposableArrows.mk₁, ComposableArrows.hom, mapZeroTransformation]

theorem mapZeroTransformation_nerveCylinder {K : A ⥤ D} (d : D)
    (ε : K ⟶ (Functor.const A).obj d) (G : D ⥤ E) :
    naturalTransformationNerveCylinder (mapZeroTransformation d ε G) =
      naturalTransformationNerveCylinder ε ≫ nerveMap G := by
  ext n z
  change _ ⋙ naturalTransformationCylinderFunctor (mapZeroTransformation d ε G) =
    (_ ⋙ naturalTransformationCylinderFunctor ε) ⋙ G
  rw [mapZeroTransformation_cylinder]
  rfl

theorem mapZeroTransformation_homotopy {K : A ⥤ D} (d : D)
    (ε : K ⟶ (Functor.const A).obj d) (G : D ⥤ E)
    (t : unitInterval) (z : ClassifyingSpace A) :
    classifyingSpaceNaturalTransformationHomotopy (mapZeroTransformation d ε G) (t, z) =
      classifyingSpaceMap G (classifyingSpaceNaturalTransformationHomotopy ε (t, z)) := by
  change SSet.toTop.map (naturalTransformationNerveCylinder
    (mapZeroTransformation d ε G)) ((SSet.realizationCylinderIso (nerve A)).inv (z, ULift.up t)) = _
  rw [mapZeroTransformation_nerveCylinder, Functor.map_comp, TopCat.comp_app]
  rfl

theorem triangle_vertex {F₀ F₁ F₂ : A ⥤ E} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂)
    (a : A) (e : E) (h₀ : F₀.obj a = e) (h₁ : F₁.obj a = e) (h₂ : F₂.obj a = e)
    (hthin : ∀ Y : E, Subsingleton (Y ⟶ e)) (z : StdSimplex ℝ (Fin 3)) :
    functorChainBarycentric (ComposableArrows.mk₂ α β)
      (classifyingSpacePoint a, z) = classifyingSpacePoint e := by
  change functorChainRealization (ComposableArrows.mk₂ α β)
    (classifyingSpacePoint a, (SimplexCategory.toTopHomeo ⦋2⦌).symm z) = _
  apply functorChainRealization_vertex_of_subsingleton _ a e _ hthin
  intro i
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂

theorem edge_vertex {F₀ F₁ : A ⥤ E} (α : F₀ ⟶ F₁)
    (a : A) (e : E) (h₀ : F₀.obj a = e) (h₁ : F₁.obj a = e)
    (hthin : ∀ Y : E, Subsingleton (Y ⟶ e)) (t : unitInterval) :
    classifyingSpaceNaturalTransformationHomotopy α (t, classifyingSpacePoint a) =
      classifyingSpacePoint e := by
  rw [← functorChainRealization_one]
  apply functorChainRealization_vertex_of_subsingleton _ a e _ hthin
  intro i
  fin_cases i
  · exact h₀
  · exact h₁

theorem cancellation_vertex {K : A ⥤ D} (P : A ⥤ C) (Q : C ⥤ D) (d : D)
    (α : K ⟶ P ⋙ Q) (β : P ⋙ Q ⟶ (Functor.const A).obj d)
    (a : A) (c : C) (hP : P.obj a = c) (hQ : Q.obj c = d) (hK : K.obj a = d)
    (hthin : ∀ Y : D, Subsingleton (Y ⟶ d)) (s : unitInterval) :
    TheoremB.naturalTransformationFiberCancellationHomotopy P Q d α β
        (s, classifyingSpacePoint a) =
      HomotopyFiber.basepoint (classifyingSpaceMap Q).hom (classifyingSpacePoint d)
        (classifyingSpacePoint c)
        ((classifyingSpaceMap_point Q c).trans (congrArg classifyingSpacePoint hQ)) := by
  apply Subtype.ext
  apply Prod.ext
  · rw [TheoremB.naturalTransformationFiberCancellationHomotopy_source,
      classifyingSpaceMap_point, hP]
    rfl
  · apply ContinuousMap.ext
    intro t
    change functorChainBarycentric (ComposableArrows.mk₂ α β)
      (classifyingSpacePoint a, TheoremB.cancellationTriangleHomotopy (s, t)) =
        classifyingSpacePoint d
    exact triangle_vertex α β a d hK (by simpa only [Functor.comp_obj, hP] using hQ)
      rfl hthin _

theorem movingSource_vertex {P T : A ⥤ C} (η : P ⟶ T) (Q : C ⥤ D) (d : D)
    (ε : T ⋙ Q ⟶ (Functor.const A).obj d) (a : A) (c : C)
    (hP : P.obj a = c) (hT : T.obj a = c) (hQ : Q.obj c = d)
    (hthinC : ∀ Y : C, Subsingleton (Y ⟶ c))
    (hthinD : ∀ Y : D, Subsingleton (Y ⟶ d)) (s : unitInterval) :
    TheoremB.naturalTransformationFiberHomotopy η Q d ε (s, classifyingSpacePoint a) =
      HomotopyFiber.basepoint (classifyingSpaceMap Q).hom (classifyingSpacePoint d)
        (classifyingSpacePoint c)
        ((classifyingSpaceMap_point Q c).trans (congrArg classifyingSpacePoint hQ)) := by
  apply Subtype.ext
  apply Prod.ext
  · exact edge_vertex η a c hP hT hthinC s
  · apply ContinuousMap.ext
    intro t
    rw [TheoremB.naturalTransformationFiberHomotopy_path]
    exact triangle_vertex (Functor.whiskerRight η Q) ε a d
      (by simpa only [Functor.comp_obj, hP] using hQ)
      (by simpa only [Functor.comp_obj, hT] using hQ) rfl hthinD _

section Square

variable {A' C' D' : Type u} [SmallCategory A'] [SmallCategory C'] [SmallCategory D']
  (J : A ⥤ C) (Q : C ⥤ D) (J' : A' ⥤ C') (Q' : C' ⥤ D')
  (S : A ⥤ A') (F : C ⥤ C') (G : D ⥤ D') (d : D)
  (ε : J ⋙ Q ⟶ (Functor.const A).obj d)
  (ε' : J' ⋙ Q' ⟶ (Functor.const A').obj (G.obj d))
  (η : J ⋙ F ⟶ S ⋙ J') (θ : Q ⋙ G ⟶ F ⋙ Q')

/-- The realized homotopy of the given ordinary functor square. -/
def squareHomotopy :
    ((classifyingSpaceMap G).hom.comp (classifyingSpaceMap Q).hom).Homotopy
      ((classifyingSpaceMap Q').hom.comp (classifyingSpaceMap F).hom) :=
  (classifyingSpaceNaturalTransformationHomotopy θ).cast
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])

/-- Compare the two actual fiber lifts by cancellation and movement of their source. -/
def triangleComparisonHomotopy :
    (HomotopyFiber.lift (classifyingSpaceMap Q').hom (classifyingSpacePoint (G.obj d))
      (classifyingSpaceMap (J ⋙ F)).hom
      (TheoremB.naturalTransformationCancellationNullhomotopy (J ⋙ F) Q' (G.obj d)
        (Functor.whiskerLeft J θ)
        (Functor.whiskerRight η Q' ≫ Functor.whiskerLeft S ε'))).Homotopy
      (TheoremB.naturalTransformationFiberLift (S ⋙ J') Q' (G.obj d)
        (Functor.whiskerLeft S ε')) :=
  (TheoremB.naturalTransformationFiberCancellationHomotopy (J ⋙ F) Q' (G.obj d)
    (Functor.whiskerLeft J θ)
    (Functor.whiskerRight η Q' ≫ Functor.whiskerLeft S ε')).trans
      (TheoremB.naturalTransformationFiberHomotopy η Q' (G.obj d)
        (Functor.whiskerLeft S ε'))

theorem triangleTransformation
    (hthin : ∀ Y : D', Subsingleton (Y ⟶ G.obj d)) :
    Functor.whiskerLeft J θ ≫ (Functor.whiskerRight η Q' ≫ Functor.whiskerLeft S ε') =
      mapZeroTransformation d ε G := by
  apply NatTrans.ext
  funext a
  exact (hthin _).elim _ _

theorem triangleComparison_start
    (hthin : ∀ Y : D', Subsingleton (Y ⟶ G.obj d)) :
    HomotopyFiber.lift (classifyingSpaceMap Q').hom (classifyingSpacePoint (G.obj d))
      (classifyingSpaceMap (J ⋙ F)).hom
      (TheoremB.naturalTransformationCancellationNullhomotopy (J ⋙ F) Q' (G.obj d)
        (Functor.whiskerLeft J θ)
        (Functor.whiskerRight η Q' ≫ Functor.whiskerLeft S ε')) =
      (HomotopyFiber.basedHomotopySquareMap (classifyingSpaceMap F).hom
        (classifyingSpaceMap G).hom (squareHomotopy Q Q' F G θ) (classifyingSpacePoint d)
        (classifyingSpacePoint (G.obj d)) (classifyingSpaceMap_point G d)).comp
          (TheoremB.naturalTransformationFiberLift J Q d ε) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · change classifyingSpaceMap (J ⋙ F) z =
      classifyingSpaceMap F (classifyingSpaceMap J z)
    rw [classifyingSpaceMap_comp]
    rfl
  · apply ContinuousMap.ext
    intro t
    change TheoremB.naturalTransformationCancellationNullhomotopy (J ⋙ F) Q' (G.obj d)
        (Functor.whiskerLeft J θ)
        (Functor.whiskerRight η Q' ≫ Functor.whiskerLeft S ε') (t, z) =
      (((squareHomotopy Q Q' F G θ).evalAt (classifyingSpaceMap J z)).symm.trans
        ((HomotopyFiber.toPath _ _ (TheoremB.naturalTransformationFiberLift J Q d ε z)).map
          (classifyingSpaceMap G).hom.continuous)) t
    rw [TheoremB.naturalTransformationCancellationNullhomotopy_apply,
      triangleTransformation J Q J' Q' S F G d ε ε' η θ hthin,
      ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs
    · exact classifyingSpaceNaturalTransformationHomotopy_whiskerLeft J θ _ z
    · exact mapZeroTransformation_homotopy d ε G _ z

theorem triangleComparison_finish :
    TheoremB.naturalTransformationFiberLift (S ⋙ J') Q' (G.obj d)
        (Functor.whiskerLeft S ε') =
      (TheoremB.naturalTransformationFiberLift J' Q' (G.obj d) ε').comp
        (classifyingSpaceMap S).hom := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · change classifyingSpaceMap (S ⋙ J') z =
      classifyingSpaceMap J' (classifyingSpaceMap S z)
    rw [classifyingSpaceMap_comp]
    rfl
  · apply ContinuousMap.ext
    intro t
    exact classifyingSpaceNaturalTransformationHomotopy_whiskerLeft S ε' t z

/-- The original fiber comparison intertwines the realized functor square up to homotopy. -/
def fiberSquareComparisonHomotopy
    (hthin : ∀ Y : D', Subsingleton (Y ⟶ G.obj d)) :
    ((HomotopyFiber.basedHomotopySquareMap (classifyingSpaceMap F).hom
      (classifyingSpaceMap G).hom (squareHomotopy Q Q' F G θ) (classifyingSpacePoint d)
      (classifyingSpacePoint (G.obj d)) (classifyingSpaceMap_point G d)).comp
        (TheoremB.naturalTransformationFiberLift J Q d ε)).Homotopy
      ((TheoremB.naturalTransformationFiberLift J' Q' (G.obj d) ε').comp
        (classifyingSpaceMap S).hom) :=
  (triangleComparisonHomotopy J Q J' Q' S F G d ε' η θ).cast
    (triangleComparison_start J Q J' Q' S F G d ε ε' η θ hthin)
    (triangleComparison_finish J' Q' S G d ε')

theorem triangleComparison_vertex (a : A) (c : C')
    (hP : (J ⋙ F).obj a = c) (hT : (S ⋙ J').obj a = c)
    (hQ : Q'.obj c = G.obj d) (hK : (J ⋙ Q ⋙ G).obj a = G.obj d)
    (hthinC : ∀ Y : C', Subsingleton (Y ⟶ c))
    (hthinD : ∀ Y : D', Subsingleton (Y ⟶ G.obj d)) (s : unitInterval) :
    triangleComparisonHomotopy J Q J' Q' S F G d ε' η θ (s, classifyingSpacePoint a) =
      HomotopyFiber.basepoint (classifyingSpaceMap Q').hom (classifyingSpacePoint (G.obj d))
        (classifyingSpacePoint c)
        ((classifyingSpaceMap_point Q' c).trans (congrArg classifyingSpacePoint hQ)) := by
  unfold triangleComparisonHomotopy
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact cancellation_vertex (J ⋙ F) Q' (G.obj d) (Functor.whiskerLeft J θ)
      (Functor.whiskerRight η Q' ≫ Functor.whiskerLeft S ε') a c hP hQ hK hthinD _
  · exact movingSource_vertex η Q' (G.obj d) (Functor.whiskerLeft S ε')
      a c hP hT hQ hthinC hthinD _

/-- The fiber comparison homotopy fixes the specified zero vertex throughout. -/
def fiberSquareComparisonHomotopyRel
    (a : A) (c : C') (hP : (J ⋙ F).obj a = c) (hT : (S ⋙ J').obj a = c)
    (hQ : Q'.obj c = G.obj d) (hK : (J ⋙ Q ⋙ G).obj a = G.obj d)
    (hthinC : ∀ Y : C', Subsingleton (Y ⟶ c))
    (hthinD : ∀ Y : D', Subsingleton (Y ⟶ G.obj d)) :
    ((HomotopyFiber.basedHomotopySquareMap (classifyingSpaceMap F).hom
      (classifyingSpaceMap G).hom (squareHomotopy Q Q' F G θ) (classifyingSpacePoint d)
      (classifyingSpacePoint (G.obj d)) (classifyingSpaceMap_point G d)).comp
        (TheoremB.naturalTransformationFiberLift J Q d ε)).HomotopyRel
      ((TheoremB.naturalTransformationFiberLift J' Q' (G.obj d) ε').comp
        (classifyingSpaceMap S).hom) {classifyingSpacePoint a} := by
  let H := fiberSquareComparisonHomotopy J Q J' Q' S F G d ε ε' η θ hthinD
  have hfixed (s : unitInterval) : H (s, classifyingSpacePoint a) =
      HomotopyFiber.basepoint (classifyingSpaceMap Q').hom (classifyingSpacePoint (G.obj d))
        (classifyingSpacePoint c)
        ((classifyingSpaceMap_point Q' c).trans (congrArg classifyingSpacePoint hQ)) :=
    triangleComparison_vertex J Q J' Q' S F G d ε' η θ a c hP hT hQ hK hthinC hthinD s
  refine { toHomotopy := H, prop' := ?_ }
  intro s z hz
  have hz' : z = classifyingSpacePoint a := Set.mem_singleton_iff.mp hz
  subst z
  exact (hfixed s).trans ((hfixed 0).symm.trans (H.apply_zero _))

end Square

section SpecifiedTarget

variable {A' C' D' : Type u} [SmallCategory A'] [SmallCategory C'] [SmallCategory D']
  (J : A ⥤ C) (Q : C ⥤ D) (J' : A' ⥤ C') (Q' : C' ⥤ D')
  (S : A ⥤ A') (F : C ⥤ C') (G : D ⥤ D') (d : D) (d' : D')
  (ε : J ⋙ Q ⟶ (Functor.const A).obj d)
  (ε' : J' ⋙ Q' ⟶ (Functor.const A').obj d')
  (η : J ⋙ F ⟶ S ⋙ J') (θ : Q ⋙ G ⟶ F ⋙ Q')

/-- The relative comparison retains the specified equality of target zero objects. -/
def fiberSquareComparisonHomotopyRelAt (hG : G.obj d = d')
    (a : A) (c : C') (hP : (J ⋙ F).obj a = c) (hT : (S ⋙ J').obj a = c)
    (hQ : Q'.obj c = d') (hK : (J ⋙ Q ⋙ G).obj a = d')
    (hthinC : ∀ Y : C', Subsingleton (Y ⟶ c))
    (hthinD : ∀ Y : D', Subsingleton (Y ⟶ d')) :
    ((HomotopyFiber.basedHomotopySquareMap (classifyingSpaceMap F).hom
      (classifyingSpaceMap G).hom (squareHomotopy Q Q' F G θ) (classifyingSpacePoint d)
      (classifyingSpacePoint d')
        ((classifyingSpaceMap_point G d).trans (congrArg classifyingSpacePoint hG))).comp
          (TheoremB.naturalTransformationFiberLift J Q d ε)).HomotopyRel
      ((TheoremB.naturalTransformationFiberLift J' Q' d' ε').comp
        (classifyingSpaceMap S).hom) {classifyingSpacePoint a} := by
  subst d'
  exact fiberSquareComparisonHomotopyRel J Q J' Q' S F G d ε ε' η θ
    a c hP hT hQ hK hthinC hthinD

end SpecifiedTarget

end CategoryTheory.ExactCategory.SerreLocalization.Naturality

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.SerreLocalization

attribute [local instance] Abelian.hasFiniteBiproducts canonicalQuotientAbelian

variable {C C' : Type u} [Category.{u} C] [Category.{u} C'] [Abelian C] [Abelian C']
  (P : ObjectProperty C) [P.IsSerreClass] (Q : ObjectProperty C') [Q.IsSerreClass]
  (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure C'))
  (hF : ∀ X : C, P X → Q (F.toFunctor.obj X))

/-- The actual restriction of the ambient functor to the two Serre subcategories. -/
def inducedSupportFunctor : P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F.toFunctor) (fun X => hF X.obj X.property)

instance inducedSupportFunctor_additive : (inducedSupportFunctor P Q F hF).Additive := by
  unfold inducedSupportFunctor
  infer_instance

/-- The restricted ambient functor is exact for the original subcategory exact structures. -/
def inducedSupportExactFunctor : ExactFunctor (abelianExactStructure P.FullSubcategory)
    (abelianExactStructure Q.FullSubcategory) where
  toFunctor := inducedSupportFunctor P Q F hF
  map_conflation T hT := by
    have h : ((T.map (inducedSupportFunctor P Q F hF)).map Q.ι).ShortExact :=
      F.map_conflation (T.map P.ι) ((ObjectProperty.exactInclusion P).map_conflation T hT)
    exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful Q.ι h

omit [P.IsSerreClass] [Q.IsSerreClass] in
/-- The ordinary support-inclusion square is literal. -/
theorem inducedSupportFunctor_comp_inclusion :
    inducedSupportFunctor P Q F hF ⋙ Q.ι = P.ι ⋙ F.toFunctor := rfl

/-- Canonical comparison of the original normalized support-inclusion square. -/
def supportNormalizedIso :
    (ObjectProperty.exactInclusion P).normalizedQ ⋙ F.normalizedQ ≅
      (inducedSupportExactFunctor P Q F hF).normalizedQ ⋙ (ObjectProperty.exactInclusion
        Q).normalizedQ :=
  ((ObjectProperty.exactInclusion P).normalizedQCompIso F).symm ≪≫
    ExactFunctor.normalizedQIso
      (F := (ObjectProperty.exactInclusion P).comp F)
      (G := (inducedSupportExactFunctor P Q F hF).comp (ObjectProperty.exactInclusion Q))
      (eqToIso (inducedSupportFunctor_comp_inclusion P Q F hF).symm) ≪≫
    (inducedSupportExactFunctor P Q F hF).normalizedQCompIso (ObjectProperty.exactInclusion Q)

variable {D D' : Type u} [Category.{u} D] [Category.{u} D'] [Abelian D] [Abelian D']
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]
  (L' : C' ⥤ D') [L'.IsLocalization Q.isoModSerre] [L'.Additive]
  (U : ExactFunctor (abelianExactStructure D) (abelianExactStructure D'))
  (e : L ⋙ U.toFunctor ≅ F.toFunctor ⋙ L')

/-- The actual inverse of the canonical target lift, equipped with standard exactness. -/
def targetInverseExactFunctor :
    ExactFunctor (abelianExactStructure D') (abelianExactStructure Q.isoModSerre.Localization) := by
  let E := (targetLift Q L').asEquivalence
  letI : E.functor.Additive := by
    change (targetLift Q L').Additive
    infer_instance
  letI : E.inverse.Additive := E.inverse_additive
  exact { toFunctor := E.inverse, map_conflation := fun _ h => h.map_of_exact E.inverse }

/-- The formal quotient functor constructed through the genuine actual-target equivalences. -/
def inducedQuotientExactFunctor : ExactFunctor (abelianExactStructure P.isoModSerre.Localization)
    (abelianExactStructure Q.isoModSerre.Localization) :=
  ((targetLiftExactFunctor P L).comp U).comp (targetInverseExactFunctor Q L')

/-- The ordinary quotient square induced by the given actual-target natural isomorphism. -/
def quotientSquareIso :
    ((ExactFunctor.serreLocalization P P.isoModSerre.Q).comp
      (inducedQuotientExactFunctor P Q L L' U)).toFunctor ≅
    (F.comp (ExactFunctor.serreLocalization Q Q.isoModSerre.Q)).toFunctor := by
  let E := (targetLift Q L').asEquivalence
  change ((P.isoModSerre.Q ⋙ targetLift P L) ⋙ U.toFunctor) ⋙ E.inverse ≅
    F.toFunctor ⋙ Q.isoModSerre.Q
  rw [targetLift_fac]
  refine Functor.isoWhiskerRight e E.inverse ≪≫ ?_
  rw [← targetLift_fac Q L']
  exact Functor.isoWhiskerLeft (F.toFunctor ⋙ Q.isoModSerre.Q) E.unitIso.symm ≪≫
    Functor.rightUnitor _

/-- The actual-target square of the canonical quotient lift, from its genuine counit. -/
def actualTargetSquareIso :
    ((targetLiftExactFunctor P L).comp U).toFunctor ≅
      ((inducedQuotientExactFunctor P Q L L' U).comp
        (targetLiftExactFunctor Q L')).toFunctor := by
  let E := (targetLift Q L').asEquivalence
  exact (Functor.rightUnitor (targetLift P L ⋙ U.toFunctor)).symm ≪≫
    Functor.isoWhiskerLeft (targetLift P L ⋙ U.toFunctor) E.counitIso.symm

/-- Canonical natural isomorphism of the original normalized quotient square. -/
def quotientNaturalityIso :
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ ⋙ (inducedQuotientExactFunctor
      P Q L L' U).normalizedQ ≅
      F.normalizedQ ⋙ (ExactFunctor.serreLocalization Q Q.isoModSerre.Q).normalizedQ :=
  ((ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQCompIso
    (inducedQuotientExactFunctor P Q L L' U)).symm ≪≫
    ExactFunctor.normalizedQIso
      (F := (ExactFunctor.serreLocalization P P.isoModSerre.Q).comp
        (inducedQuotientExactFunctor P Q L L' U))
      (G := F.comp (ExactFunctor.serreLocalization Q Q.isoModSerre.Q))
      (quotientSquareIso P Q F L L' U e) ≪≫
    F.normalizedQCompIso (ExactFunctor.serreLocalization Q Q.isoModSerre.Q)

lemma normalizedQ_obj_zero
    {A B : Type u} [Category.{u} A] [Category.{u} B] [Preadditive A] [Preadditive B]
    [HasFiniteBiproducts A] [HasFiniteBiproducts B]
    {EA : ExactStructure A} {EB : ExactStructure B} (V : ExactFunctor EA EB) :
    V.normalizedQ.obj EA.qZero = EB.qZero :=
  rebaseFunctor_obj_base _ _ _ _

/-- The entire realized track of the canonical normalized quotient comparison. -/
def naturalitySquareHomotopy :
    ((classifyingSpaceMap (inducedQuotientExactFunctor P Q L L' U).normalizedQ).hom.comp
      (classifyingSpaceMap ((ExactFunctor.serreLocalization P
        P.isoModSerre.Q).normalizedQ)).hom).Homotopy
      ((classifyingSpaceMap ((ExactFunctor.serreLocalization Q
        Q.isoModSerre.Q).normalizedQ)).hom.comp
        (classifyingSpaceMap F.normalizedQ).hom) :=
  Naturality.squareHomotopy ((ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ)
    ((ExactFunctor.serreLocalization Q Q.isoModSerre.Q).normalizedQ)
    F.normalizedQ (inducedQuotientExactFunctor P Q L L' U).normalizedQ
    (quotientNaturalityIso P Q F L L' U e).hom

/-- The whole quotient-square track fixes the actual ambient-zero vertex. -/
theorem naturalitySquareHomotopy_basepoint (t : unitInterval) :
    naturalitySquareHomotopy P Q F L L' U e (t, (abelianExactStructure C).kBasepoint) =
      (abelianExactStructure Q.isoModSerre.Localization).kBasepoint := by
  change classifyingSpaceNaturalTransformationHomotopy
    (quotientNaturalityIso P Q F L L' U e).hom
    (t, classifyingSpacePoint (abelianExactStructure C).qZero) =
      classifyingSpacePoint (abelianExactStructure Q.isoModSerre.Localization).qZero
  apply Naturality.edge_vertex _ _ _ _ _
    (fun Y => (abelianExactStructure Q.isoModSerre.Localization).qHom_subsingleton_of_isZero
      Y _ (isZero_zero _)) t
  · change (inducedQuotientExactFunctor P Q L L' U).normalizedQ.obj
      ((ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ.obj
        (abelianExactStructure C).qZero) = _
    rw [normalizedQ_obj_zero, normalizedQ_obj_zero]
  · change (ExactFunctor.serreLocalization Q Q.isoModSerre.Q).normalizedQ.obj
      (F.normalizedQ.obj (abelianExactStructure C).qZero) = _
    rw [normalizedQ_obj_zero, normalizedQ_obj_zero]

theorem basedComparison_eq_naturalFiberLift :
    basedLocalizationFiberComparison P =
      TheoremB.naturalTransformationFiberLift ((ObjectProperty.exactInclusion P).normalizedQ)
        ((ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ)
        (abelianExactStructure P.isoModSerre.Localization).qZero
        (normalizedQuotientInclusionZeroIso P).hom := rfl

/-- The actual path-space fiber map retaining the canonical square track. -/
def naturalityFiberMap : ContinuousMap (NormalizedLocalizationFiber P)
    (NormalizedLocalizationFiber Q) :=
  HomotopyFiber.basedHomotopySquareMap (classifyingSpaceMap F.normalizedQ).hom
    (classifyingSpaceMap (inducedQuotientExactFunctor P Q L L' U).normalizedQ).hom
    (naturalitySquareHomotopy P Q F L L' U e) _ _
    (inducedQuotientExactFunctor P Q L L' U).normalizedQ_map_point

/-- Canonical whole fiber-comparison naturality relative to the actual support zero. -/
def canonicalComparisonNaturalityHomotopy :
    ((naturalityFiberMap P Q F L L' U e).comp (basedLocalizationFiberComparison P)).HomotopyRel
      ((basedLocalizationFiberComparison Q).comp
        (classifyingSpaceMap (inducedSupportExactFunctor P Q F hF).normalizedQ).hom)
      {(abelianExactStructure P.FullSubcategory).kBasepoint} := by
  rw [basedComparison_eq_naturalFiberLift, basedComparison_eq_naturalFiberLift]
  apply Naturality.fiberSquareComparisonHomotopyRelAt
    ((ObjectProperty.exactInclusion P).normalizedQ) ((ExactFunctor.serreLocalization P
      P.isoModSerre.Q).normalizedQ)
    ((ObjectProperty.exactInclusion Q).normalizedQ) ((ExactFunctor.serreLocalization Q
      Q.isoModSerre.Q).normalizedQ)
    (inducedSupportExactFunctor P Q F hF).normalizedQ F.normalizedQ
    (inducedQuotientExactFunctor P Q L L' U).normalizedQ
    (abelianExactStructure P.isoModSerre.Localization).qZero
    (abelianExactStructure Q.isoModSerre.Localization).qZero
    (normalizedQuotientInclusionZeroIso P).hom (normalizedQuotientInclusionZeroIso Q).hom
    (supportNormalizedIso P Q F hF).hom (quotientNaturalityIso P Q F L L' U e).hom
    (normalizedQ_obj_zero _) (abelianExactStructure P.FullSubcategory).qZero
    (abelianExactStructure C').qZero
  · change F.normalizedQ.obj ((ObjectProperty.exactInclusion P).normalizedQ.obj
      (abelianExactStructure P.FullSubcategory).qZero) = _
    rw [normalizedQ_obj_zero, normalizedQ_obj_zero]
  · change (ObjectProperty.exactInclusion Q).normalizedQ.obj
      ((inducedSupportExactFunctor P Q F hF).normalizedQ.obj
        (abelianExactStructure P.FullSubcategory).qZero) = _
    rw [normalizedQ_obj_zero, normalizedQ_obj_zero]
  · exact normalizedQ_obj_zero _
  · change (inducedQuotientExactFunctor P Q L L' U).normalizedQ.obj
      ((ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ.obj
        ((ObjectProperty.exactInclusion P).normalizedQ.obj
          (abelianExactStructure P.FullSubcategory).qZero)) = _
    rw [normalizedQ_obj_zero, normalizedQ_obj_zero, normalizedQ_obj_zero]
  · exact fun Y => (abelianExactStructure C').qHom_subsingleton_of_isZero Y _ (isZero_zero _)
  · exact fun Y => (abelianExactStructure Q.isoModSerre.Localization).qHom_subsingleton_of_isZero
      Y _ (isZero_zero _)

/-- The canonical whole-track fiber map preserves the specified fiber basepoint. -/
theorem naturalityFiberMap_basepoint :
    naturalityFiberMap P Q F L L' U e (normalizedFiberBasepoint P) =
      normalizedFiberBasepoint Q :=
  HomotopyFiber.basedHomotopySquareMap_basepoint (classifyingSpaceMap F.normalizedQ).hom
    (classifyingSpaceMap (inducedQuotientExactFunctor P Q L L' U).normalizedQ).hom
    (naturalitySquareHomotopy P Q F L L' U e)
    (abelianExactStructure C).kBasepoint
    (abelianExactStructure P.isoModSerre.Localization).kBasepoint
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ_map_point
    (abelianExactStructure C').kBasepoint
    (abelianExactStructure Q.isoModSerre.Localization).kBasepoint
    F.normalizedQ_map_point (inducedQuotientExactFunctor P Q L L' U).normalizedQ_map_point
    (ExactFunctor.serreLocalization Q Q.isoModSerre.Q).normalizedQ_map_point
    (naturalitySquareHomotopy_basepoint P Q F L L' U e)

/-- Naturality of the original canonical fiber-comparison homomorphisms. -/
theorem comparisonHom_naturality (n : ℕ) :
    (localizationFiberComparisonHom Q n).comp ((inducedSupportExactFunctor P Q F hF).KMap n) =
      (piMap n (naturalityFiberMap P Q F L L' U e)
        (naturalityFiberMap_basepoint P Q F L L' U e)).comp
          (localizationFiberComparisonHom P n) := by
  let Hc := canonicalComparisonNaturalityHomotopy P Q F hF L L' U e
  have hfixed : ∀ t, Hc.toHomotopy
      (t, (abelianExactStructure P.FullSubcategory).kBasepoint) =
        normalizedFiberBasepoint Q := by
    intro t
    exact (Hc.prop t _ (Set.mem_singleton _)).trans
      ((congrArg (naturalityFiberMap P Q F L L' U e)
        (basedLocalizationFiberComparison_basepoint P)).trans
          (naturalityFiberMap_basepoint P Q F L L' U e))
  rw [ExactFunctor.KMap_eq_piMap]
  unfold localizationFiberComparisonHom
  rw [← HomotopyGroup.mapHom_comp, ← HomotopyGroup.mapHom_comp]
  exact (piMap_eq_of_based_homotopy n _ _ Hc.toHomotopy hfixed).symm

include e in
/-- The original formal-quotient boundary is natural for the constructed quotient functor. -/
theorem formalConnectingHom_naturality (n : ℕ) :
    ((inducedSupportExactFunctor P Q F hF).KMap n).comp (connectingHom P n) =
      (connectingHom Q n).comp ((inducedQuotientExactFunctor P Q L L' U).KMap (n + 1)) := by
  have htop := HomotopyFiber.connectingHom_basedHomotopySquare_natural
    (classifyingSpaceMap F.normalizedQ).hom
    (classifyingSpaceMap (inducedQuotientExactFunctor P Q L L' U).normalizedQ).hom
    (naturalitySquareHomotopy P Q F L L' U e)
    (abelianExactStructure C).kBasepoint
    (abelianExactStructure P.isoModSerre.Localization).kBasepoint
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ_map_point
    (abelianExactStructure C').kBasepoint
    (abelianExactStructure Q.isoModSerre.Localization).kBasepoint
    F.normalizedQ_map_point (inducedQuotientExactFunctor P Q L L' U).normalizedQ_map_point
    (ExactFunctor.serreLocalization Q Q.isoModSerre.Q).normalizedQ_map_point
    (naturalitySquareHomotopy_basepoint P Q F L L' U e) n
  apply MonoidHom.ext
  intro a
  apply (localizationFiberComparisonHom_bijective Q n).injective
  have hc := DFunLike.congr_fun (comparisonHom_naturality P Q F hF L L' U e n)
    (connectingHom P n a)
  have hp := DFunLike.congr_fun (comparison_comp_connectingHom P n) a
  have hq := DFunLike.congr_fun (comparison_comp_connectingHom Q n)
    ((inducedQuotientExactFunctor P Q L L' U).KMap (n + 1) a)
  change localizationFiberComparisonHom Q n
      ((inducedSupportExactFunctor P Q F hF).KMap n (connectingHom P n a)) =
    localizationFiberComparisonHom Q n (connectingHom Q n
      ((inducedQuotientExactFunctor P Q L L' U).KMap (n + 1) a))
  calc
    _ = piMap n (naturalityFiberMap P Q F L L' U e)
        (naturalityFiberMap_basepoint P Q F L L' U e)
          (localizationFiberComparisonHom P n (connectingHom P n a)) := hc
    _ = piMap n (naturalityFiberMap P Q F L L' U e)
        (naturalityFiberMap_basepoint P Q F L L' U e) (fiberConnectingHom P n a) :=
      congrArg _ hp
    _ = fiberConnectingHom Q n
        ((inducedQuotientExactFunctor P Q L L' U).KMap (n + 1) a) :=
      DFunLike.congr_fun htop a
    _ = _ := hq.symm

include e in
/-- The original actual-target connecting maps are natural for an exact ambient
functor preserving the Serre classes and a genuine ordinary localization-square
natural isomorphism. The canonical whole zero-nullhomotopy comparison is proved. -/
theorem actualConnectingHom_naturality (n : ℕ) :
    ((inducedSupportExactFunctor P Q F hF).KMap n).comp (actualConnectingHom P L n) =
      (actualConnectingHom Q L' n).comp (U.KMap (n + 1)) := by
  have ht := ExactFunctor.KMap_eq_of_natIso (actualTargetSquareIso P Q L L' U) (n + 1)
  rw [ExactFunctor.KMap_comp, ExactFunctor.KMap_comp] at ht
  have hc := formalConnectingHom_naturality P Q F hF L L' U e n
  apply MonoidHom.ext
  intro a
  obtain ⟨x, rfl⟩ := (targetKEquiv P L (n + 1)).surjective a
  have hx : U.KMap (n + 1) (targetKEquiv P L (n + 1) x) =
      targetKEquiv Q L' (n + 1) ((inducedQuotientExactFunctor P Q L L' U).KMap (n + 1) x) :=
    DFunLike.congr_fun ht x
  change (inducedSupportExactFunctor P Q F hF).KMap n (connectingHom P n
      ((targetKEquiv P L (n + 1)).symm (targetKEquiv P L (n + 1) x))) =
    connectingHom Q n ((targetKEquiv Q L' (n + 1)).symm
      (U.KMap (n + 1) (targetKEquiv P L (n + 1) x)))
  rw [MulEquiv.symm_apply_apply, hx, MulEquiv.symm_apply_apply]
  exact DFunLike.congr_fun hc x

end CategoryTheory.ExactCategory.SerreLocalization
