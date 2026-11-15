/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Coefficients
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Total
public import Mathlib.Algebra.Homology.BifunctorHomotopy
import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution.BoundedAbove

/-!
# Signed total bifunctors on the existing projective model

A biadditive functor of transfer presheaves induces a bifunctor on the
bounded-above derived category by the original projective equivalence.
The total complex is Mathlib's signed cochain totalization. Its bound is
the sum of the two input bounds, and both homotopy relations are respected.
No exactness or motivic-localization assertion is made about an arbitrary
input bifunctor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K

local notation "c" => ComplexShape.up ℤ

variable (F : PST(k) ⥤ PST(k) ⥤ PST(k)) [F.Additive] [∀ P, (F.obj P).Additive]

local instance (P : PST(k)) : (F.flip.obj P).Additive where
  map_add := by
    intro X Y f g
    change (F.map (f + g)).app P = (F.map f).app P + (F.map g).app P
    exact NatTrans.congr_app (F.map_add (f := f) (g := g)) P

/-- The native signed total of bounded-above inputs has the sum of their bounds. -/
theorem mapBifunctor_isStrictlyLE (K L : CochainComplex PST(k) ℤ)
    (a b : ℤ) [K.IsStrictlyLE a] [L.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE (HomologicalComplex.mapBifunctor K L F c) (a + b) := by
  apply (CochainComplex.isStrictlyLE_iff _ (a + b)).2
  intro n hn
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  have hz : IsZero ((F.obj (K.X p)).obj (L.X q)) := by
    by_cases hp : a < p
    · exact (F.flip.obj (L.X q)).map_isZero (K.isZero_of_isStrictlyLE a p hp)
    · exact (F.obj (K.X p)).map_isZero (L.isZero_of_isStrictlyLE b q (by omega))
  exact hz.eq_of_src _ _

/-- Each total degree has only finitely many nonzero summands. -/
theorem finite_mapBifunctor_antidiagonal (K L : CochainComplex PST(k) ℤ)
    (a b : ℤ) [K.IsStrictlyLE a] [L.IsStrictlyLE b] (n : ℤ) :
    {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧
      ¬ IsZero ((F.obj (K.X pq.1)).obj (L.X pq.2))}.Finite := by
  refine ((Set.finite_Icc (n - b) a).image (fun p : ℤ => (p, n - p))).subset ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  have hp : p ≤ a := by
    by_contra h
    exact hz ((F.flip.obj (L.X q)).map_isZero (K.isZero_of_isStrictlyLE a p (by omega)))
  have hq : q ≤ b := by
    by_contra h
    exact hz ((F.obj (K.X p)).map_isZero (L.isZero_of_isStrictlyLE b q (by omega)))
  exact ⟨p, ⟨by omega, hp⟩, Prod.ext rfl (show n - p = q by omega)⟩

/-- For a fixed first complex, signed totalization descends through the second homotopy. -/
def signedTotalHomotopyRight (K : CochainComplex PST(k) ℤ) :
    HomotopyCategory PST(k) c ⥤ HomotopyCategory PST(k) c :=
  CategoryTheory.Quotient.lift (homotopic PST(k) c)
    (F.map₂CochainComplex.obj K ⋙ HomotopyCategory.quotient PST(k) c)
    (fun _ _ _ _ ⟨h⟩ => HomotopyCategory.eq_of_homotopy _ _
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K) h F c))

/-- A map of first complexes induces a natural transformation on signed totalizations
after taking the homotopy quotient in the second variable. -/
def signedTotalRightMap {K L : CochainComplex PST(k) ℤ} (f : K ⟶ L) :
    signedTotalHomotopyRight F K ⟶ signedTotalHomotopyRight F L :=
  CategoryTheory.Quotient.natTransLift (homotopic PST(k) c)
    (Functor.whiskerRight (F.map₂CochainComplex.map f) (HomotopyCategory.quotient PST(k) c))

theorem signedTotalRightMap_id (K : CochainComplex PST(k) ℤ) :
    signedTotalRightMap F (𝟙 K) = 𝟙 (signedTotalHomotopyRight F K) := by
  apply NatTrans.ext
  funext M
  let H := F.map₂CochainComplex
  let Q := HomotopyCategory.quotient PST(k) c
  have h : (H.map (𝟙 K)).app M.as = 𝟙 ((H.obj K).obj M.as) :=
    NatTrans.congr_app (H.map_id K) M.as
  change Q.map ((H.map (𝟙 K)).app M.as) = 𝟙 _
  exact (congrArg Q.map h).trans (Q.map_id _)

theorem signedTotalRightMap_comp {K L M : CochainComplex PST(k) ℤ}
    (f : K ⟶ L) (g : L ⟶ M) :
    signedTotalRightMap F (f ≫ g) = signedTotalRightMap F f ≫ signedTotalRightMap F g := by
  apply NatTrans.ext
  funext N
  let H := F.map₂CochainComplex
  let Q := HomotopyCategory.quotient PST(k) c
  have h : (H.map (f ≫ g)).app N.as = (H.map f).app N.as ≫ (H.map g).app N.as :=
    NatTrans.congr_app (H.map_comp f g) N.as
  change Q.map ((H.map (f ≫ g)).app N.as) =
    Q.map ((H.map f).app N.as) ≫ Q.map ((H.map g).app N.as)
  exact (congrArg Q.map h).trans (Q.map_comp _ _)

/-- Before quotienting the first variable, maps act by their literal signed total maps. -/
def signedTotalComplexHomotopy :
    CochainComplex PST(k) ℤ ⥤ HomotopyCategory PST(k) c ⥤ HomotopyCategory PST(k) c where
  obj := signedTotalHomotopyRight F
  map := signedTotalRightMap F
  map_id := signedTotalRightMap_id F
  map_comp := signedTotalRightMap_comp F

theorem signedTotalRightMap_eq_of_homotopy {K L : CochainComplex PST(k) ℤ}
    {f g : K ⟶ L} (h : Homotopy f g) :
    signedTotalRightMap F f = signedTotalRightMap F g := by
  apply NatTrans.ext
  funext M
  change (HomotopyCategory.quotient PST(k) c).map ((F.map₂CochainComplex.map f).app M.as) =
    (HomotopyCategory.quotient PST(k) c).map ((F.map₂CochainComplex.map g).app M.as)
  exact HomotopyCategory.eq_of_homotopy _ _
    (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 M.as) F c)

/-- The same signed totalization descends through both original homotopy relations. -/
def signedTotalHomotopyBifunctor :
    HomotopyCategory PST(k) c ⥤ HomotopyCategory PST(k) c ⥤ HomotopyCategory PST(k) c :=
  CategoryTheory.Quotient.lift (homotopic PST(k) c) (signedTotalComplexHomotopy F)
    (fun _ _ _ _ ⟨h⟩ => signedTotalRightMap_eq_of_homotopy F h)

/-- The quotient bifunctor uses the native total complex on its actual input representatives. -/
@[simp]
theorem signedTotalHomotopyBifunctor_obj (K L : HomotopyCategory PST(k) c) :
    ((signedTotalHomotopyBifunctor F).obj K).obj L =
      (HomotopyCategory.quotient PST(k) c).obj
        (HomologicalComplex.mapBifunctor K.as L.as F c) := rfl

variable [HasDerivedCategory.{w} PST(k)]

/-- Signed totalization of the chosen projectives followed by the native quotient. -/
def projectiveTotalToDerived :
    BoundedAboveProjectiveHomotopy k ⥤
      BoundedAboveProjectiveHomotopy k ⥤ DerivedCategory PST(k) :=
  (boundedAboveProjectiveCondition k).ι ⋙ signedTotalHomotopyBifunctor F ⋙
    (Functor.whiskeringLeft _ _ _).obj (boundedAboveProjectiveCondition k).ι ⋙
      (Functor.whiskeringRight _ _ _).obj DerivedCategory.Qh

theorem projectiveTotalToDerived_mem_minus
    (K L : BoundedAboveProjectiveHomotopy k) :
    (DerivedCategory.TStructure.t (C := PST(k))).minus
      (((projectiveTotalToDerived F).obj K).obj L) := by
  obtain ⟨a, ha, _⟩ := K.property
  obtain ⟨b, hb, _⟩ := L.property
  let : CochainComplex.IsStrictlyLE K.obj.as a := ha
  let : CochainComplex.IsStrictlyLE L.obj.as b := hb
  let T : CochainComplex PST(k) ℤ := HomologicalComplex.mapBifunctor K.obj.as L.obj.as F c
  let : T.IsStrictlyLE (a + b) := mapBifunctor_isStrictlyLE F K.obj.as L.obj.as a b
  let : (DerivedCategory.Q.obj T).IsLE (a + b) := inferInstance
  exact ⟨a + b, DerivedCategory.TStructure.t.isLE_of_iso
    ((DerivedCategory.quotientCompQhIso PST(k)).app T).symm (a + b)⟩

/-- Signed totalization on the existing bounded-above projective homotopy category. -/
def projectiveHomotopyBifunctorToDerivedMinus :
    BoundedAboveProjectiveHomotopy k ⥤
      BoundedAboveProjectiveHomotopy k ⥤ DerivedCategory.Minus PST(k) where
  obj K := (DerivedCategory.TStructure.t (C := PST(k))).minus.lift
    ((projectiveTotalToDerived F).obj K) (projectiveTotalToDerived_mem_minus F K)
  map f :=
    { app L := ObjectProperty.homMk (((projectiveTotalToDerived F).map f).app L)
      naturality L M g := by
        apply ObjectProperty.hom_ext
        exact ((projectiveTotalToDerived F).map f).naturality g }
  map_id K := by
    apply NatTrans.ext
    funext L
    apply ObjectProperty.hom_ext
    exact congrArg (fun f => f.app L) ((projectiveTotalToDerived F).map_id K)
  map_comp f g := by
    apply NatTrans.ext
    funext L
    apply ObjectProperty.hom_ext
    exact congrArg (fun h => h.app L) ((projectiveTotalToDerived F).map_comp f g)

/-- Derive a biadditive functor using the selected projective equivalence in both variables. -/
def projectiveDerivedMinusBifunctor :
    DerivedCategory.Minus PST(k) ⥤ DerivedCategory.Minus PST(k) ⥤ DerivedCategory.Minus PST(k) :=
  let E := (boundedAboveProjectiveEquivalence k).inverse
  E ⋙ projectiveHomotopyBifunctorToDerivedMinus F ⋙ (Functor.whiskeringLeft _ _ _).obj E

/-- On any given projective representatives, the derived bifunctor is their signed total. -/
def projectiveDerivedMinusBifunctorProjectiveIso
    (K L : BoundedAboveProjectiveHomotopy k) :
    ((projectiveDerivedMinusBifunctor F).obj
      ((projectiveHomotopyToDerivedMinus k).obj K)).obj
        ((projectiveHomotopyToDerivedMinus k).obj L) ≅
      ((projectiveHomotopyBifunctorToDerivedMinus F).obj K).obj L :=
  let e := boundedAboveProjectiveEquivalence k
  let B := projectiveHomotopyBifunctorToDerivedMinus F
  ((evaluation _ _).obj (e.inverse.obj (e.functor.obj L))).mapIso
      (B.mapIso (e.unitIso.app K).symm) ≪≫
    (B.obj K).mapIso (e.unitIso.app L).symm

theorem exists_projectiveRepresentativeAt
    (K : DerivedCategory.Minus PST(k)) (a : ℤ) [K.obj.IsLE a] :
    ∃ P : BoundedAboveProjectiveHomotopy k, CochainComplex.IsStrictlyLE P.obj.as a ∧
      Nonempty ((projectiveHomotopyToDerivedMinus k).obj P ≅ K) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := K.obj.exists_iso_Q_obj_of_isLE a
  obtain ⟨P, _⟩ := ProjectiveResolutionLemma.statement3 a L hL
  let : QuasiIso P.α := P.quasiIso
  refine ⟨⟨(HomotopyCategory.quotient PST(k) c).obj P.complex, a, P.boundedAbove, P.projective⟩,
    P.boundedAbove, ⟨ObjectProperty.isoMk _ ?_⟩⟩
  exact (DerivedCategory.quotientCompQhIso PST(k)).app P.complex ≪≫
    asIso (DerivedCategory.Q.map P.α) ≪≫ e.symm

/-- The signed projective total respects the sum of the prescribed cohomological upper bounds. -/
theorem projectiveDerivedMinusBifunctor_isLE (K L : DerivedCategory.Minus PST(k)) (a b : ℤ)
    [K.obj.IsLE a] [L.obj.IsLE b] :
    (((projectiveDerivedMinusBifunctor F).obj K).obj L).obj.IsLE (a + b) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_projectiveRepresentativeAt K a
  obtain ⟨R, hR, ⟨eR⟩⟩ := exists_projectiveRepresentativeAt L b
  let : CochainComplex.IsStrictlyLE P.obj.as a := hP
  let : CochainComplex.IsStrictlyLE R.obj.as b := hR
  let T : CochainComplex PST(k) ℤ := HomologicalComplex.mapBifunctor P.obj.as R.obj.as F c
  let : T.IsStrictlyLE (a + b) := mapBifunctor_isStrictlyLE F P.obj.as R.obj.as a b
  let : (DerivedCategory.Q.obj T).IsLE (a + b) := inferInstance
  let B := projectiveDerivedMinusBifunctor F
  let t := DerivedCategory.TStructure.t (C := PST(k))
  let i : (((projectiveHomotopyBifunctorToDerivedMinus F).obj P).obj R).obj ≅
      (DerivedCategory.Q.obj T) := (DerivedCategory.quotientCompQhIso PST(k)).app T
  let j := projectiveDerivedMinusBifunctorProjectiveIso F P R
  let r : ((B.obj K).obj L) ≅ _ :=
    ((evaluation _ _).obj L).mapIso (B.mapIso eP.symm) ≪≫
      (B.obj ((projectiveHomotopyToDerivedMinus k).obj P)).mapIso eR.symm ≪≫ j
  exact t.isLE_of_iso (i.symm ≪≫ (DerivedCategory.Minus.ι.mapIso r).symm) (a + b)

end AlgebraicGeometry.PresheafWithTransfers
