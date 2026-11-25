/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerve
public import Colib.Topology.DoubleMappingCylinder.Contractible
public import Colib.Topology.HELP.CubeBoundaryHomeomorph
public import Colib.Topology.HELP.Nullhomotopic
public import Colib.Topology.Realization.DoubleCylinder

/-!
# The two-tip common-reference parameter carrier

Two specified reference maps attach two copies of the polynomial parameter cylinder to
the Laurent parameter nerve. The carrier is the realization of the successive simplicial
double cylinders, with two separate copies of `Δ[0]` as their tips. Both cylinder maps
retain their original interval coordinates. The second pushout height separates the two
tips, even when the two specified reference maps agree. The two displayed pushouts
prove contractibility, and every supplied whole cube boundary extends literally.

Adapted from `CommonReferenceNerveCutOpenCarrier.lean` in Quillen K-theory at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No compatibility of prescribed faces
or evaluation in the Waldhausen levels is asserted here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory TopCat
open scoped Simplicial Topology unitInterval
universe u

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier
open SmallWaldhausenCategory

/-- Each attachment has its own copy of the actual simplicial point. -/
abbrev tipSSet : SSet.{u} := Δ[0]

/-- The unique simplicial map to the actual zero-simplex. -/
def erase {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) : parameterSSet F ⟶ tipSSet :=
  SSet.stdSimplex.isTerminalObj₀.from _

variable {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
  (ε₀ ε₁ : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor)

/-- The first actual simplicial cylinder attachment, with its own terminal tip. -/
def firstSimplicial : SSet.{u} :=
  DoubleCylinder.simplicial (attaching F J G ε₀) (erase F)

/-- The original Laurent summand in the first simplicial attachment. -/
def left₀ : parameterSSet G ⟶ firstSimplicial F J G ε₀ :=
  coprod.inl ≫ DoubleCylinder.simplicialEnds (attaching F J G ε₀) (erase F)

/-- The first tip summand, before the second attachment. -/
def right₀ : tipSSet ⟶ firstSimplicial F J G ε₀ :=
  coprod.inr ≫ DoubleCylinder.simplicialEnds (attaching F J G ε₀) (erase F)

/-- The second specified reference attaches through the unchanged Laurent summand. -/
def secondAttaching : parameterSSet F ⟶ firstSimplicial F J G ε₀ :=
  attaching F J G ε₁ ≫ left₀ F J G ε₀

/-- The two-tip simplicial carrier, defined by the second actual pushout. -/
def simplicial : SSet.{u} :=
  DoubleCylinder.simplicial (secondAttaching F J G ε₀ ε₁) (erase F)

/-- The whole first attachment is retained as the left summand of the second. -/
def left₁ : firstSimplicial F J G ε₀ ⟶ simplicial F J G ε₀ ε₁ :=
  coprod.inl ≫ DoubleCylinder.simplicialEnds (secondAttaching F J G ε₀ ε₁) (erase F)

/-- The second attachment has a new tip summand. -/
def right₁ : tipSSet ⟶ simplicial F J G ε₀ ε₁ :=
  coprod.inr ≫ DoubleCylinder.simplicialEnds (secondAttaching F J G ε₀ ε₁) (erase F)

/-- The parameter space is this exact realization, without replacing its model. -/
abbrev space : TopCat.{u} := |simplicial F J G ε₀ ε₁|

/-- The first realization is an actual displayed topological pushout. -/
theorem first_isPushout :
    IsPushout (TopCat.intervalEndpoints |parameterSSet F|)
      (DoubleCylinder.endMap (SSet.toTop.map (attaching F J G ε₀))
        (SSet.toTop.map (erase F)))
      (DoubleCylinder.realizedCylinder (attaching F J G ε₀) (erase F))
      (DoubleCylinder.realizedEnds (attaching F J G ε₀) (erase F)) :=
  DoubleCylinder.realized_isPushout _ _

/-- The second realization is the actual pushout retaining the entire first attachment. -/
theorem second_isPushout :
    IsPushout (TopCat.intervalEndpoints |parameterSSet F|)
      (DoubleCylinder.endMap (SSet.toTop.map (secondAttaching F J G ε₀ ε₁))
        (SSet.toTop.map (erase F)))
      (DoubleCylinder.realizedCylinder (secondAttaching F J G ε₀ ε₁) (erase F))
      (DoubleCylinder.realizedEnds (secondAttaching F J G ε₀ ε₁) (erase F)) :=
  DoubleCylinder.realized_isPushout _ _

private theorem realized_left {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (y : |Y|) :
    SSet.toTop.map ((coprod.inl : Y ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) y =
        DoubleCylinder.realizedEnds f g (Sum.inl y) := by
  have h : SSet.toTop.map ((coprod.inl : Y ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) =
      (TopCat.binaryCofan |Y| |Z|).inl ≫ DoubleCylinder.realizedEnds f g := by
    simpa only [Functor.map_comp, DoubleCylinder.realizedEnds, Category.assoc,
      Iso.hom_inv_id_assoc] using
      congrArg (fun k ↦ k ≫ (realizationBinarySumIso Y Z).inv ≫
        SSet.toTop.map (DoubleCylinder.simplicialEnds f g))
        (realizationBinarySumIso_inl Y Z)
  exact ConcreteCategory.congr_hom h y

private theorem realized_right {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (z : |Z|) :
    SSet.toTop.map ((coprod.inr : Z ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) z =
        DoubleCylinder.realizedEnds f g (Sum.inr z) := by
  have h : SSet.toTop.map ((coprod.inr : Z ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) =
      (TopCat.binaryCofan |Y| |Z|).inr ≫ DoubleCylinder.realizedEnds f g := by
    simpa only [Functor.map_comp, DoubleCylinder.realizedEnds, Category.assoc,
      Iso.hom_inv_id_assoc] using
      congrArg (fun k ↦ k ≫ (realizationBinarySumIso Y Z).inv ≫
        SSet.toTop.map (DoubleCylinder.simplicialEnds f g))
        (realizationBinarySumIso_inr Y Z)
  exact ConcreteCategory.congr_hom h z

private theorem realized_cylinder_zero {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (x : |X|) :
    DoubleCylinder.realizedCylinder f g (x, ULift.up (0 : I)) =
      SSet.toTop.map ((coprod.inl : Y ⟶ Y ⨿ Z) ≫
        DoubleCylinder.simplicialEnds f g) (SSet.toTop.map f x) := by
  calc
    _ = DoubleCylinder.realizedEnds f g (Sum.inl (SSet.toTop.map f x)) :=
      ConcreteCategory.congr_hom (DoubleCylinder.realized_isPushout f g).w (Sum.inl x)
    _ = _ := (realized_left f g _).symm

private theorem realized_cylinder_one {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (x : |X|) :
    DoubleCylinder.realizedCylinder f g (x, ULift.up (1 : I)) =
      SSet.toTop.map ((coprod.inr : Z ⟶ Y ⨿ Z) ≫
        DoubleCylinder.simplicialEnds f g) (SSet.toTop.map g x) := by
  calc
    _ = DoubleCylinder.realizedEnds f g (Sum.inr (SSet.toTop.map g x)) :=
      ConcreteCategory.congr_hom (DoubleCylinder.realized_isPushout f g).w (Sum.inr x)
    _ = _ := (realized_right f g _).symm

/-- The original Laurent inclusion through the two actual simplicial left summands. -/
def laurentInclusion : C(|parameterSSet G|, space F J G ε₀ ε₁) :=
  (SSet.toTop.map (left₁ F J G ε₀ ε₁)).hom.comp
    (SSet.toTop.map (left₀ F J G ε₀)).hom

/-- This is exactly realization of the original composite simplicial inclusion. -/
theorem laurentInclusion_eq :
    laurentInclusion F J G ε₀ ε₁ =
      (SSet.toTop.map (left₀ F J G ε₀ ≫ left₁ F J G ε₀ ε₁)).hom := by
  rw [Functor.map_comp]
  rfl

/-- The first cylinder retains its independent ordinary interval coordinate via `ULift.up`. -/
def cylinderMinus : C(|parameterSSet F| × I, space F J G ε₀ ε₁) :=
  ⟨fun z ↦ SSet.toTop.map (left₁ F J G ε₀ ε₁)
    (DoubleCylinder.realizedCylinder (attaching F J G ε₀) (erase F)
      (z.1, ULift.up z.2)), by fun_prop⟩

/-- The second cylinder retains the same independent coordinate in the new attachment. -/
def cylinderPlus : C(|parameterSSet F| × I, space F J G ε₀ ε₁) :=
  ⟨fun z ↦ DoubleCylinder.realizedCylinder (secondAttaching F J G ε₀ ε₁) (erase F)
    (z.1, ULift.up z.2), by fun_prop⟩

/-- The first tip remains inside the first summand of the second attachment. -/
def tipMinus : space F J G ε₀ ε₁ :=
  SSet.toTop.map (left₁ F J G ε₀ ε₁)
    (SSet.toTop.map (right₀ F J G ε₀) (default : |tipSSet.{u}|))

/-- The second tip is the point of the new `Δ[0]` summand. -/
def tipPlus : space F J G ε₀ ε₁ :=
  SSet.toTop.map (right₁ F J G ε₀ ε₁) (default : |tipSSet.{u}|)

/-- The complete first attachment face is the specified ordinary reference map. -/
@[simp] theorem cylinderMinus_zero (x : |parameterSSet F|) :
    cylinderMinus F J G ε₀ ε₁ (x, 0) =
      laurentInclusion F J G ε₀ ε₁
        (mapParameter (attachPostcompNode F J G ε₀) x) := by
  change SSet.toTop.map (left₁ F J G ε₀ ε₁)
    (DoubleCylinder.realizedCylinder (attaching F J G ε₀) (erase F)
      (x, ULift.up (0 : I))) = _
  rw [realized_cylinder_zero]
  rfl

/-- The entire first terminal face is its own tip. -/
@[simp] theorem cylinderMinus_one (x : |parameterSSet F|) :
    cylinderMinus F J G ε₀ ε₁ (x, 1) = tipMinus F J G ε₀ ε₁ := by
  change SSet.toTop.map (left₁ F J G ε₀ ε₁)
    (DoubleCylinder.realizedCylinder (attaching F J G ε₀) (erase F)
      (x, ULift.up (1 : I))) = _
  rw [realized_cylinder_one]
  have h : SSet.toTop.map (erase F) x = (default : |tipSSet.{u}|) :=
    Subsingleton.elim _ _
  rw [h]
  rfl

/-- The complete second attachment face uses its own specified full reference. -/
@[simp] theorem cylinderPlus_zero (x : |parameterSSet F|) :
    cylinderPlus F J G ε₀ ε₁ (x, 0) =
      laurentInclusion F J G ε₀ ε₁
        (mapParameter (attachPostcompNode F J G ε₁) x) := by
  change DoubleCylinder.realizedCylinder (secondAttaching F J G ε₀ ε₁) (erase F)
    (x, ULift.up (0 : I)) = _
  rw [realized_cylinder_zero]
  change SSet.toTop.map (left₁ F J G ε₀ ε₁)
    (SSet.toTop.map (attaching F J G ε₁ ≫ left₀ F J G ε₀) x) = _
  rw [Functor.map_comp]
  rfl

/-- The entire second terminal face is the new tip. -/
@[simp] theorem cylinderPlus_one (x : |parameterSSet F|) :
    cylinderPlus F J G ε₀ ε₁ (x, 1) = tipPlus F J G ε₀ ε₁ := by
  change DoubleCylinder.realizedCylinder (secondAttaching F J G ε₀ ε₁) (erase F)
    (x, ULift.up (1 : I)) = _
  rw [realized_cylinder_one]
  have h : SSet.toTop.map (erase F) x = (default : |tipSSet.{u}|) :=
    Subsingleton.elim _ _
  rw [h]
  rfl

/-- The existing height on the actual second displayed pushout. -/
def height : C(space F J G ε₀ ε₁, I) :=
  DoubleCylinder.height (SSet.toTop.map (secondAttaching F J G ε₀ ε₁))
    (SSet.toTop.map (erase F)) (second_isPushout F J G ε₀ ε₁)

/-- The old tip lies on the left, at height zero in the second pushout. -/
@[simp] theorem height_tipMinus : height F J G ε₀ ε₁ (tipMinus F J G ε₀ ε₁) = 0 := by
  exact (congrArg (DoubleCylinder.height
    (SSet.toTop.map (secondAttaching F J G ε₀ ε₁))
    (SSet.toTop.map (erase F)) (second_isPushout F J G ε₀ ε₁))
    (realized_left (secondAttaching F J G ε₀ ε₁) (erase F)
      (SSet.toTop.map (right₀ F J G ε₀) default))).trans
    (DoubleCylinder.height_left _ _ _ _)

/-- The new tip lies on the right, at height one in the second pushout. -/
@[simp] theorem height_tipPlus : height F J G ε₀ ε₁ (tipPlus F J G ε₀ ε₁) = 1 := by
  exact (congrArg (DoubleCylinder.height
    (SSet.toTop.map (secondAttaching F J G ε₀ ε₁))
    (SSet.toTop.map (erase F)) (second_isPushout F J G ε₀ ε₁))
    (realized_right (secondAttaching F J G ε₀ ε₁) (erase F) default)).trans
    (DoubleCylinder.height_right _ _ _ _)

/-- The two tips are distinct, even if the two given reference isomorphisms agree. -/
theorem tips_ne : tipMinus F J G ε₀ ε₁ ≠ tipPlus F J G ε₀ ε₁ := by
  intro h
  have hh := congrArg (height F J G ε₀ ε₁) h
  rw [height_tipMinus, height_tipPlus] at hh
  exact zero_ne_one hh

private theorem tip_contractible : ContractibleSpace |tipSSet.{u}| := by
  let : ContractibleSpace |nerve (ULift.{u} (Fin 1))| := by
    change ContractibleSpace (ClassifyingSpace (ULift.{u} (Fin 1)))
    infer_instance
  exact (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.stdSimplex.isoNerve 0))).contractibleSpace

/-- The first actual attachment is contractible by its displayed realization pushout. -/
theorem first_contractibleSpace : ContractibleSpace |firstSimplicial F J G ε₀| := by
  let : ContractibleSpace |parameterSSet F| := parameter_contractible F
  let : ContractibleSpace |parameterSSet G| := parameter_contractible G
  let : ContractibleSpace |tipSSet.{u}| := tip_contractible
  exact DoubleCylinder.contractibleSpace_of_contractible
    (SSet.toTop.map (attaching F J G ε₀)) (SSet.toTop.map (erase F))
    (first_isPushout F J G ε₀)

/-- Two applications of the actual double-cylinder theorem contract this same realization. -/
theorem contractibleSpace : ContractibleSpace (space F J G ε₀ ε₁) := by
  let : ContractibleSpace |parameterSSet F| := parameter_contractible F
  let : ContractibleSpace |firstSimplicial F J G ε₀| := first_contractibleSpace F J G ε₀
  let : ContractibleSpace |tipSSet.{u}| := tip_contractible
  exact DoubleCylinder.contractibleSpace_of_contractible
    (SSet.toTop.map (secondAttaching F J G ε₀ ε₁)) (SSet.toTop.map (erase F))
    (second_isPushout F J G ε₀ ε₁)

/-- Any already defined whole parameter boundary extends exactly, in every dimension. -/
theorem exists_cube_extension (d : ℕ)
    (b : C({z : Fin d → I // z ∈ Cube.boundary (Fin d)}, space F J G ε₀ ε₁)) :
    ∃ E : C(Fin d → I, space F J G ε₀ ε₁),
      E.restrict (Cube.boundary (Fin d)) = b := by
  let : ContractibleSpace (space F J G ε₀ ε₁) := contractibleSpace F J G ε₀ ε₁
  let b' : C(Topology.CubicalTests.boundary.{u} d, space F J G ε₀ ε₁) :=
    b.comp ⟨Topology.CubicalTests.boundaryULiftHomeomorph d,
      (Topology.CubicalTests.boundaryULiftHomeomorph d).continuous⟩
  have hb : b'.Nullhomotopic := (id_nullhomotopic (space F J G ε₀ ε₁)).comp_left b'
  obtain ⟨E, hE⟩ := Topology.exists_extend_of_nullhomotopic
    (Topology.CubicalTests.boundaryInclusion d)
    (Topology.CubicalTests.boundaryInclusion_hep d) b' hb
  refine ⟨E.comp ⟨ULift.up, continuous_uliftUp⟩, ?_⟩
  ext z
  exact DFunLike.congr_fun hE ⟨⟨z.val⟩, z.property⟩

/-- Choose one extension of the supplied whole parameter boundary. -/
def cubeExtension (d : ℕ)
    (b : C({z : Fin d → I // z ∈ Cube.boundary (Fin d)}, space F J G ε₀ ε₁)) :
    C(Fin d → I, space F J G ε₀ ε₁) :=
  (exists_cube_extension F J G ε₀ ε₁ d b).choose

/-- The chosen extension preserves every point of the original parameter boundary. -/
theorem cubeExtension_restrict (d : ℕ)
    (b : C({z : Fin d → I // z ∈ Cube.boundary (Fin d)}, space F J G ε₀ ε₁)) :
    (cubeExtension F J G ε₀ ε₁ d b).restrict (Cube.boundary (Fin d)) = b :=
  (exists_cube_extension F J G ε₀ ε₁ d b).choose_spec


end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier
