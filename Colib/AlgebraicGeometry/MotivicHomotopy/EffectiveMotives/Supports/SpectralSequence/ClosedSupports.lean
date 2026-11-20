/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Nested
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.RepresentedCohomology
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Indexing
public import Mathlib.CategoryTheory.Triangulated.SpectralObject
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# The spectral object of closed supports

For closed subsets `A ⊆ B` of a smooth scheme `X`, the degree-`n` term is the
represented cohomology of the open pair `(X \ A, X \ B)`. The exact sequence
for `A ⊆ B ⊆ C` comes from the distinguished triangle of the nested opens
`X \ C ⊆ X \ B ⊆ X \ A`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ComposableArrows CategoryTheory.Pretriangulated.Opposite
open AlgebraicGeometry.Scheme Opposite TopologicalSpace
open scoped CategoryTheory.Pretriangulated.Opposite

universe u w w'

namespace CategoryTheory.Triangulated.SpectralObject

variable {C ι : Type*} [Category* C] [Category* ι] [HasShift C ℤ]

private theorem oppositeBoundary_naturality
    (A B : Triangle C) {a : A.obj₁ ⟶ B.obj₁} {c : A.obj₃ ⟶ B.obj₃}
    (h : c ≫ B.mor₃ = A.mor₃ ≫ a⟦(1 : ℤ)⟧') :
    a.op ≫ ((triangleOpEquivalence C).functor.obj (op A)).mor₃ =
      ((triangleOpEquivalence C).functor.obj (op B)).mor₃ ≫ c.op⟦(1 : ℤ)⟧' := by
  symm
  dsimp
  rw [Category.assoc, ← Functor.map_comp, ← op_comp, h, op_comp, Functor.map_comp,
    opShiftFunctorEquivalence_counitIso_inv_naturality_assoc]
  rfl

variable (M : ComposableArrows ι 1 ⥤ Cᵒᵖ)

/-- The triangle in `C` with reversed coface maps and the given connecting morphism. -/
abbrev triangleOfOppositeBoundary (D : ComposableArrows ι 2)
    (d : (M.obj ((functorArrows ι 0 1 2).obj D)).unop ⟶
      (M.obj ((functorArrows ι 1 2 2).obj D)).unop⟦(1 : ℤ)⟧) : Triangle C :=
  Triangle.mk (M.map ((mapFunctorArrows ι 0 2 1 2 2).app D)).unop
    (M.map ((mapFunctorArrows ι 0 1 0 2 2).app D)).unop d

variable [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  (d : ∀ D : ComposableArrows ι 2, (M.obj ((functorArrows ι 0 1 2).obj D)).unop ⟶
    (M.obj ((functorArrows ι 1 2 2).obj D)).unop⟦(1 : ℤ)⟧)
  (hd : ∀ {D E : ComposableArrows ι 2} (f : D ⟶ E),
    (M.map ((functorArrows ι 0 1 2).map f)).unop ≫ d D =
      d E ≫ (M.map ((functorArrows ι 1 2 2).map f)).unop⟦(1 : ℤ)⟧')
  (hT : ∀ D, triangleOfOppositeBoundary M D (d D) ∈ distTriang C)

/-- Construct a spectral object in `Cᵒᵖ` from natural distinguished triangles in `C`. -/
def ofOppositeBoundaries : Triangulated.SpectralObject Cᵒᵖ ι where
  ω₁ := M
  δ'.app D := ((triangleOpEquivalence C).functor.obj
    (op (triangleOfOppositeBoundary M D (d D)))).mor₃
  δ'.naturality D E f := by
    exact oppositeBoundary_naturality (triangleOfOppositeBoundary M E (d E))
      (triangleOfOppositeBoundary M D (d D)) (hd f)
  distinguished' D := by
    exact op_distinguished (triangleOfOppositeBoundary M D (d D)) (hT D)

/-- The homological connecting map only uses the original boundary and its endpoints. -/
theorem ofOppositeBoundaries_mapHomologicalFunctor_δ {A : Type*} [Category* A] [Abelian A]
    (F : Cᵒᵖ ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]
    {i j l : ι} (f : i ⟶ j) (g : j ⟶ l) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) {B : C}
    (a : (M.obj (mk₁ g)).unop ⟶ B) (b : B ⟶ (M.obj (mk₁ f)).unop) :
    ((ofOppositeBoundaries M d hd hT).mapHomologicalFunctor F).δ f g n₀ n₁ h =
      F.homologySequenceδ ((triangleOpEquivalence C).functor.obj
        (op (Triangle.mk a b (d (mk₂ f g))))) n₀ n₁ h :=
  rfl

end CategoryTheory.Triangulated.SpectralObject

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable (X : Sm(k))

local notation "CS" => Closeds X.left

/-- The original complementary-open arrows, contravariant in the closed support pairs. -/
def closedSupportOpenPairs : ComposableArrows CS 1 ⥤ (Arrow Sm(k))ᵒᵖ where
  obj D := op (Arrow.mk (supportOpenMap k X (D.map' 0 1).le))
  map f := (Arrow.homMk' (supportOpenMap k X (f.app 1).le)
    (supportOpenMap k X (f.app 0).le)
    (by rw [supportOpenMap_comp, supportOpenMap_comp])).op
  map_id D := by
    apply Quiver.Hom.unop_inj
    apply Arrow.hom_ext <;> exact (SmoothSite.opensFunctor X).map_id _
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply Arrow.hom_ext
    · exact (supportOpenMap_comp k X (f.app 1).le (g.app 1).le).symm
    · exact (supportOpenMap_comp k X (f.app 0).le (g.app 0).le).symm

section MiddleIso

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

private theorem distinguished_change_middle (T : Triangle C) (hT : T ∈ distTriang C)
    {B : C} (e : T.obj₂ ≅ B) (f : T.obj₁ ⟶ B) (g : B ⟶ T.obj₃)
    (hf : T.mor₁ ≫ e.hom = f) (hg : T.mor₂ = e.hom ≫ g) :
    Triangle.mk f g T.mor₃ ∈ distTriang C := by
  let S := Triangle.mk f g T.mor₃
  have h₁ : T.mor₁ ≫ e.hom = 𝟙 T.obj₁ ≫ f := hf.trans (Category.id_comp f).symm
  have h₂ : T.mor₂ ≫ 𝟙 T.obj₃ = e.hom ≫ g := (Category.comp_id T.mor₂).trans hg
  have h₃ : T.mor₃ ≫ (𝟙 T.obj₁)⟦(1 : ℤ)⟧' = 𝟙 T.obj₃ ≫ T.mor₃ := by
    rw [(shiftFunctor C (1 : ℤ)).map_id, Category.comp_id, Category.id_comp]
  exact isomorphic_distinguished T hT S
    (Triangle.isoMk T S (Iso.refl _) e (Iso.refl _) h₁ h₂ h₃).symm

end MiddleIso

private def closedSupportTriangleMiddleIso (D : ComposableArrows CS 2) :
    Arrow.mk (supportOpenMap k X (D.map' 1 2).le ≫ supportOpenMap k X (D.map' 0 1).le) ≅
      Arrow.mk (supportOpenMap k X (D.map' 0 2).le) :=
  Arrow.isoMk' _ _ (Iso.refl _) (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact (supportOpenMap_comp k X (D.map' 0 1).le (D.map' 1 2).le).symm)

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "DM(" field ")" => EffectiveMotivesMinus field

/-- Use the abelian structure of transfer sheaves in the original relative motive category. -/
local instance closedSupportSpectralObjectAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

private abbrev closedSupportMotivePairs : ComposableArrows CS 1 ⥤ (DM(k))ᵒᵖ :=
  closedSupportOpenPairs k X ⋙ (effectivePairMotiveFunctor k).op

private abbrev closedSupportNestedTriangle (D : ComposableArrows CS 2) : Triangle DM(k) :=
  effectiveNestedPairTriangle k (supportOpenMap k X (D.map' 1 2).le)
    (supportOpenMap k X (D.map' 0 1).le)

/-- The signed boundary of the nested complementary opens for a flag of closed supports. -/
def closedSupportMotiveBoundary (D : ComposableArrows CS 2) :
    effectivePairMotive k (supportOpenMap k X (D.map' 0 1).le) ⟶
      (effectivePairMotive k (supportOpenMap k X (D.map' 1 2).le))⟦(1 : ℤ)⟧ :=
  effectiveNestedPairBoundary k (supportOpenMap k X (D.map' 1 2).le)
    (supportOpenMap k X (D.map' 0 1).le)

private abbrev closedSupportTriangle (D : ComposableArrows CS 2) : Triangle DM(k) :=
  Triangle.mk
    ((closedSupportMotivePairs k X).map ((mapFunctorArrows CS 0 2 1 2 2).app D)).unop
    ((closedSupportMotivePairs k X).map ((mapFunctorArrows CS 0 1 0 2 2).app D)).unop
    (closedSupportNestedTriangle k X D).mor₃

set_option maxHeartbeats 900000 in
-- Factor through the original square maps before applying the relative motive functor.
private theorem closedSupportTriangle_distinguished (D : ComposableArrows CS 2) :
    closedSupportTriangle k X D ∈ distTriang DM(k) := by
  let F := effectivePairMotiveFunctor k
  let i := supportOpenMap k X (D.map' 1 2).le
  let j := supportOpenMap k X (D.map' 0 1).le
  let T := closedSupportNestedTriangle k X D
  let e₀ := closedSupportTriangleMiddleIso k X D
  let e := F.mapIso e₀
  let a₁ := nestedPairFirstArrow k i j
  let a₂ := nestedPairSecondArrow k i j
  let f := ((closedSupportOpenPairs k X).map ((mapFunctorArrows CS 0 2 1 2 2).app D)).unop
  let g := ((closedSupportOpenPairs k X).map ((mapFunctorArrows CS 0 1 0 2 2).app D)).unop
  have hf₀ : a₁ ≫ e₀.hom = f := by
    apply Arrow.hom_ext
    · change 𝟙 _ ≫ 𝟙 _ = supportOpenMap k X (D.map' 2 2).le
      rw [Category.id_comp]
      exact ((SmoothSite.opensFunctor X).map_id _).symm
    · exact Category.comp_id _
  have hg₀ : e₀.hom ≫ g = a₂ := by
    apply Arrow.hom_ext
    · exact Category.id_comp _
    · change 𝟙 _ ≫ supportOpenMap k X (D.map' 0 0).le = 𝟙 _
      rw [Category.id_comp]
      exact (SmoothSite.opensFunctor X).map_id _
  have h₁ : T.mor₁ = F.map a₁ := effectiveNestedPairTriangle_mor₁ k i j
  have h₂ : T.mor₂ = F.map a₂ := effectiveNestedPairTriangle_mor₂ k i j
  have hf : T.mor₁ ≫ e.hom = F.map f :=
    (congrArg (· ≫ e.hom) h₁).trans
      ((F.map_comp a₁ e₀.hom).symm.trans (F.congr_map hf₀))
  have hg : T.mor₂ = e.hom ≫ F.map g :=
    h₂.trans ((F.congr_map hg₀.symm).trans (F.map_comp e₀.hom g))
  have hT : T ∈ distTriang DM(k) := effectiveNestedPairTriangle_distinguished k i j
  exact distinguished_change_middle T hT e (F.map f) (F.map g) hf hg

set_option maxHeartbeats 800000 in
-- Naturality uses the two original maps of the complementary-open pairs.
private theorem closedSupportMotiveBoundary_naturality {D E : ComposableArrows CS 2}
    (f : D ⟶ E) :
    ((closedSupportMotivePairs k X).map ((functorArrows CS 0 1 2).map f)).unop ≫
        closedSupportMotiveBoundary k X D =
      closedSupportMotiveBoundary k X E ≫
        ((closedSupportMotivePairs k X).map ((functorArrows CS 1 2 2).map f)).unop⟦(1 : ℤ)⟧' :=
  effectiveNestedPairBoundary_naturality k
    (supportOpenMap k X (E.map' 1 2).le) (supportOpenMap k X (E.map' 0 1).le)
    (supportOpenMap k X (D.map' 1 2).le) (supportOpenMap k X (D.map' 0 1).le)
    (supportOpenMap k X (f.app 2).le) (supportOpenMap k X (f.app 1).le)
    (supportOpenMap k X (f.app 0).le)
    (by rw [supportOpenMap_comp, supportOpenMap_comp])
    (by rw [supportOpenMap_comp, supportOpenMap_comp])

/-- The triangulated spectral object of relative motives of complementary opens. -/
def closedSupportMotiveSpectralObject :
    CategoryTheory.Triangulated.SpectralObject (DM(k))ᵒᵖ CS :=
  Triangulated.SpectralObject.ofOppositeBoundaries
    (closedSupportOpenPairs k X ⋙ (effectivePairMotiveFunctor k).op)
    (closedSupportMotiveBoundary k X)
    (by exact closedSupportMotiveBoundary_naturality k X)
    (by exact closedSupportTriangle_distinguished k X)

/-- The spectral object on closed supports with represented effective-motive cohomology. -/
def closedSupportSpectralObject (K : DM(k)) : Abelian.SpectralObject AddCommGrpCat.{w'} CS :=
  (closedSupportMotiveSpectralObject k X).mapHomologicalFunctor (preadditiveYoneda.obj K)

/-- Degree-`n` cohomology uses the original complementary-open pairs and their squares. -/
theorem closedSupportSpectralObject_H (K : DM(k)) (n : ℤ) :
    (closedSupportSpectralObject k X K).H n =
      closedSupportOpenPairs k X ⋙ effectivePairCohomology k K n :=
  rfl

/-- The term on a support inclusion is cohomology of its complementary-open pair. -/
theorem closedSupportSpectralObject_H_obj (K : DM(k)) (n : ℤ) {A B : CS} (h : A ≤ B) :
    ((closedSupportSpectralObject k X K).H n).obj (mk₁ (homOfLE h)) =
      (effectivePairCohomology k K n).obj (op (Arrow.mk (supportOpenMap k X h))) :=
  rfl

/-- The map on a support square is induced by the square of complementary opens. -/
theorem closedSupportSpectralObject_H_map (K : DM(k)) (n : ℤ)
    {D E : ComposableArrows CS 1} (f : D ⟶ E) :
    ((closedSupportSpectralObject k X K).H n).map f =
      (effectivePairCohomology k K n).map ((closedSupportOpenPairs k X).map f) :=
  rfl

/-- The connecting homomorphism on a flag is the represented localization boundary. -/
theorem closedSupportSpectralObject_δ (K : DM(k)) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁)
    {A B C : CS} (hAB : A ≤ B) (hBC : B ≤ C) :
    (closedSupportSpectralObject k X K).δ (homOfLE hAB) (homOfLE hBC) n₀ n₁ hn =
      (preadditiveYoneda.obj K).homologySequenceδ ((triangleOpEquivalence DM(k)).functor.obj
        (op (effectiveNestedPairTriangle k (supportOpenMap k X hBC) (supportOpenMap k X hAB))))
        n₀ n₁ hn := by
  let T := effectiveNestedPairTriangle k (supportOpenMap k X hBC) (supportOpenMap k X hAB)
  exact Triangulated.SpectralObject.ofOppositeBoundaries_mapHomologicalFunctor_δ
    (closedSupportMotivePairs k X) (closedSupportMotiveBoundary k X)
    (closedSupportMotiveBoundary_naturality k X) (closedSupportTriangle_distinguished k X)
    (preadditiveYoneda.obj K) (homOfLE hAB) (homOfLE hBC) n₀ n₁ hn T.mor₁ T.mor₂

/-- The localization boundary on a cohomology class uses the signed nested-pair map. -/
theorem closedSupportSpectralObject_δ_apply (K : DM(k)) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁)
    {A B C : CS} (hAB : A ≤ B) (hBC : B ≤ C)
    (x : effectivePairMotive k (supportOpenMap k X hBC) ⟶ K⟦n₀⟧) :
    (closedSupportSpectralObject k X K).δ (homOfLE hAB) (homOfLE hBC) n₀ n₁ hn x =
      effectiveNestedPairBoundary k (supportOpenMap k X hBC) (supportOpenMap k X hAB) ≫
        x⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' DM(k) n₀ 1 n₁ hn).inv.app K := by
  rw [closedSupportSpectralObject_δ]
  exact preadditiveYoneda_homologySequenceδ_apply
    (effectiveNestedPairTriangle k (supportOpenMap k X hBC) (supportOpenMap k X hAB)) n₀ n₁ hn x

end AlgebraicGeometry.MotivicHomotopy
