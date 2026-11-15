/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Comparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.OpenSequence
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.TransferTriangle

/-!
# The cofiber triangle of an open pair

The short exact sequence of the open, the ambient scheme and its actual
transfer quotient gives the relative motive triangle under effective
reflection. The first two arrows are the original smooth motive map and
the quotient projection.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))
local notation "NST(" field ")" => LargeSheaves field
local notation "F" => effectiveTransferSheaf k
local notation "G" => effectiveSmoothMotive k
local notation "e" => smoothTransferRepresentableEffectiveIso k

/-- Use the native transfer abelian structure for the effective shift and triangles. -/
local instance instAbelianEffectivePairTriangle : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

/-- The ambient motive maps to the actual pair quotient. -/
@[expose] def effectivePairMotiveQuotient {U X : Sm(k)} (j : U ⟶ X) :
    (G).obj X ⟶ effectivePairMotive k j :=
  ((e).app X).inv ≫ (F).map ((transferPairProjection k).app (Arrow.mk j))

/-- The original effective transfer sequence underlying the pair triangle. -/
abbrev effectiveOpenPairTransferTriangle {U X : Sm(k)} (j : U ⟶ X)
    [IsOpenImmersion j.left] : Triangle (EffectiveMotivesMinus k) :=
  effectiveTransferSheafTriangle k (transferPairSequence_shortExact k j)

/-- The boundary from the original transfer short exact sequence. -/
@[expose] def effectivePairBoundary {U X : Sm(k)} (j : U ⟶ X) [IsOpenImmersion j.left] :
    effectivePairMotive k j ⟶ ((G).obj U)⟦(1 : ℤ)⟧ :=
  (effectiveOpenPairTransferTriangle k j).mor₃ ≫ (((e).app U).hom)⟦(1 : ℤ)⟧'

/-- The cofiber triangle of the original open immersion and its pair quotient. -/
@[expose] def effectivePairTriangle {U X : Sm(k)} (j : U ⟶ X) [IsOpenImmersion j.left] :
    Triangle (EffectiveMotivesMinus k) where
  obj₁ := (G).obj U
  obj₂ := (G).obj X
  obj₃ := effectivePairMotive k j
  mor₁ := (G).map j
  mor₂ := effectivePairMotiveQuotient k j
  mor₃ := effectivePairBoundary k j

/-- The comparison with the original reflected transfer short exact sequence. -/
@[expose] def effectivePairTriangleIso {U X : Sm(k)} (j : U ⟶ X) [IsOpenImmersion j.left] :
    effectiveTransferSheafTriangle k (transferPairSequence_shortExact k j) ≅
      effectivePairTriangle k j := by
  let T := effectiveOpenPairTransferTriangle k j
  let A : T.obj₁ ≅ (G).obj U := (e).app U
  let B : T.obj₂ ≅ (G).obj X := (e).app X
  let Q : T.obj₃ ≅ effectivePairMotive k j := Iso.refl _
  refine Triangle.isoMk T (effectivePairTriangle k j) A B Q ?_ ?_ ?_
  · exact (e).hom.naturality j
  · exact (Category.comp_id T.mor₂).trans (Iso.hom_inv_id_assoc B T.mor₂).symm
  · exact (Category.id_comp (T.mor₃ ≫ A.hom⟦(1 : ℤ)⟧')).symm

/-- The relative motive is the cofiber of the original open immersion. -/
theorem effectivePairTriangle_distinguished {U X : Sm(k)} (j : U ⟶ X) [IsOpenImmersion j.left] :
    effectivePairTriangle k j ∈ distTriang _ :=
  isomorphic_distinguished _ (effectiveTransferSheafTriangle_distinguished k
    (transferPairSequence_shortExact k j)) _ (effectivePairTriangleIso k j).symm

private theorem naturalIso_lift {Src Tgt Coef : Type*} [Category Src] [Category Tgt]
    [Category Coef] {J : Src ⥤ Coef} {L : Coef ⥤ Tgt} {H : Src ⥤ Tgt}
    (ε : J ⋙ L ≅ H) {A B : Src} (f : A ⟶ B) {Q Q' : Coef}
    (p : J.obj A ⟶ Q) (p' : J.obj B ⟶ Q') (q : Q ⟶ Q') (h : J.map f ≫ p' = p ≫ q) :
    ((ε.app A).inv ≫ L.map p) ≫ L.map q = H.map f ≫ (ε.app B).inv ≫ L.map p' := by
  have he := ε.inv.naturality f
  change H.map f ≫ (ε.app B).inv = (ε.app A).inv ≫ L.map (J.map f) at he
  rw [Category.assoc, ← L.map_comp, ← h, L.map_comp, ← Category.assoc, ← he, Category.assoc]

private theorem transportBoundary_naturality {C : Type*} [Category C] [HasShift C ℤ]
    {X X' U U' V V' : C} (δ : X ⟶ U⟦(1 : ℤ)⟧) (δ' : X' ⟶ U'⟦(1 : ℤ)⟧)
    (a : U ⟶ V) (b : U' ⟶ V') (f : U ⟶ U') (g : V ⟶ V') (q : X ⟶ X')
    (ha : f ≫ b = a ≫ g) (hδ : δ ≫ f⟦(1 : ℤ)⟧' = q ≫ δ') :
    (δ ≫ a⟦(1 : ℤ)⟧') ≫ g⟦(1 : ℤ)⟧' = q ≫ δ' ≫ b⟦(1 : ℤ)⟧' := by
  let H := shiftFunctor C (1 : ℤ)
  change (δ ≫ H.map a) ≫ H.map g = q ≫ δ' ≫ H.map b
  rw [Category.assoc, ← H.map_comp, ← ha, H.map_comp, ← Category.assoc, hδ, Category.assoc]

/-- The ambient graph map commutes with the quotient for a map of open arrows. -/
theorem effectivePairMotiveQuotient_naturality_arrow {U X U' X' : Sm(k)}
    {j : U ⟶ X} {j' : U' ⟶ X'} (a : Arrow.mk j ⟶ Arrow.mk j') :
    let P := effectivePairMotiveFunctor k
    effectivePairMotiveQuotient k j ≫ P.map a =
      (G).map a.right ≫ effectivePairMotiveQuotient k j' := by
  let J := smoothTransferRepresentable k
  let T := transferPairCokernelFunctor k
  let p := transferPairProjection k
  have h : J.map a.right ≫ p.app (Arrow.mk j') = p.app (Arrow.mk j) ≫ T.map a :=
    p.naturality a
  change (((e).app X).inv ≫ (F).map (p.app (Arrow.mk j))) ≫ (F).map (T.map a) =
    (G).map a.right ≫ ((e).app X').inv ≫ (F).map (p.app (Arrow.mk j'))
  exact naturalIso_lift (e) a.right _ _ (T.map a) h

/-- The ambient graph map and the actual map of open-pair quotients commute. -/
theorem effectivePairMotiveQuotient_naturality (sq : Square Sm(k)) :
    effectivePairMotiveQuotient k sq.f₁₃ ≫ effectivePairMotiveMap k sq =
      (G).map sq.f₃₄ ≫ effectivePairMotiveQuotient k sq.f₂₄ :=
  effectivePairMotiveQuotient_naturality_arrow k (j := sq.f₁₃) (j' := sq.f₂₄)
    (Arrow.homMk' sq.f₁₂ sq.f₃₄ sq.fac)

/-- Naturality of the actual boundary under a map of open arrows. -/
theorem effectivePairBoundary_naturality {U X U' X' : Sm(k)}
    {j : U ⟶ X} {j' : U' ⟶ X'} [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (a : Arrow.mk j ⟶ Arrow.mk j') :
    let P := effectivePairMotiveFunctor k
    effectivePairBoundary k j ≫ ((G).map a.left)⟦(1 : ℤ)⟧' =
      P.map a ≫ effectivePairBoundary k j' := by
  let x : ShortComplex NST(k) := transferPairSequence k (Arrow.mk j)
  let y : ShortComplex NST(k) := transferPairSequence k (Arrow.mk j')
  let hx : x.ShortExact := transferPairSequence_shortExact k j
  let hy : y.ShortExact := transferPairSequence_shortExact k j'
  let f : x ⟶ y := transferPairSequenceMap k a
  let H := shiftFunctor (EffectiveMotivesMinus k) (1 : ℤ)
  let δ := effectiveTransferSheafConnecting k hx
  let δ' := effectiveTransferSheafConnecting k hy
  let J := smoothTransferRepresentable k
  let A := (e).app U
  let B := (e).app U'
  have hn : (F).map (J.map a.left) ≫ B.hom = A.hom ≫ (G).map a.left :=
    (e).hom.naturality a.left
  have hb : δ ≫ H.map ((F).map (J.map a.left)) =
      (effectivePairMotiveFunctor k).map a ≫ δ' :=
    (effectiveTransferSheafTriangleMap k (Q := x) (Q' := y) hx hy f).comm₃
  change (δ ≫ H.map A.hom) ≫ H.map ((G).map a.left) =
    (effectivePairMotiveFunctor k).map a ≫ δ' ≫ H.map B.hom
  exact transportBoundary_naturality δ δ' A.hom B.hom _ _ _ hn hb

variable (sq : Square Sm(k)) [IsOpenImmersion sq.f₁₃.left] [IsOpenImmersion sq.f₂₄.left]

/-- The original maps on the open, ambient and relative motives form a map of triangles. -/
@[expose] def effectivePairTriangleMap :
    TriangleMorphism (effectivePairTriangle k sq.f₁₃) (effectivePairTriangle k sq.f₂₄) where
  hom₁ := (G).map sq.f₁₂
  hom₂ := (G).map sq.f₃₄
  hom₃ := effectivePairMotiveMap k sq
  comm₁ := ((G).map_comp _ _).symm.trans (((G).congr_map sq.fac.symm).trans ((G).map_comp _ _))
  comm₂ := effectivePairMotiveQuotient_naturality k sq
  comm₃ := effectivePairBoundary_naturality k (j := sq.f₁₃) (j' := sq.f₂₄)
    (Arrow.homMk' sq.f₁₂ sq.f₃₄ sq.fac)

/-- The first component is the original map on the open pieces. -/
@[simp]
theorem effectivePairTriangleMap_hom₁ :
    (effectivePairTriangleMap k sq).hom₁ = (G).map sq.f₁₂ := rfl

/-- The second component is the original map on the ambient schemes. -/
@[simp]
theorem effectivePairTriangleMap_hom₂ :
    (effectivePairTriangleMap k sq).hom₂ = (G).map sq.f₃₄ := rfl

/-- The third component is the original map on the relative motives. -/
theorem effectivePairTriangleMap_hom₃ :
    (effectivePairTriangleMap k sq).hom₃ = effectivePairMotiveMap k sq := rfl

/-- A map of open pairs whose open and ambient motives are isomorphisms induces
an isomorphism on the original relative motive map. -/
theorem effectivePairMotiveMap_isIso_of_isIso_components
    (h₁ : IsIso ((G).map sq.f₁₂)) (h₂ : IsIso ((G).map sq.f₃₄)) :
    IsIso (effectivePairMotiveMap k sq) := by
  rw [← effectivePairTriangleMap_hom₃ k sq]
  exact isIso₃_of_isIso₁₂ (effectivePairTriangleMap k sq)
    (effectivePairTriangle_distinguished k sq.f₁₃)
    (effectivePairTriangle_distinguished k sq.f₂₄)
    (show IsIso ((G).map sq.f₁₂) from h₁)
    (show IsIso ((G).map sq.f₃₄) from h₂)

end AlgebraicGeometry.MotivicHomotopy
