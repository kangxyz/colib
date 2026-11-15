/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctor
import Mathlib.Algebra.Homology.BifunctorFlip

/-!
# Symmetry on the signed projective total

A swap of additive coefficient bifunctors induces a swap on the
selected projective model. The sign on each cochain summand is
Mathlib's total-complex symmetry sign.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "c" => ComplexShape.up ℤ
local notation "Ch(" K ")" => CochainComplex PST(K) ℤ
local notation "Ho(" K ")" => HomotopyCategory PST(K) c

variable (F : PST(k) ⥤ PST(k) ⥤ PST(k)) [F.Additive] [∀ P, (F.obj P).Additive]

local instance : F.flip.Additive where
  map_add := by
    intro P Q f g
    apply NatTrans.ext
    funext X
    exact (F.obj X).map_add

local instance (P : PST(k)) : (F.flip.obj P).Additive where
  map_add := by
    intro X Y f g
    change (F.map (f + g)).app P = (F.map f).app P + (F.map g).app P
    exact NatTrans.congr_app (F.map_add (f := f) (g := g)) P

variable (s : F ≅ F.flip)

/-- The bicomplex comparison applies the original swap in every bidegree. -/
def projectiveTensorBicomplexSwap (K L : Ch(k)) :
    ((F.mapBifunctorHomologicalComplex c c).obj K).obj L ≅
      ((F.flip.mapBifunctorHomologicalComplex c c).obj K).obj L :=
  Hom.isoOfComponents
    (fun p => Hom.isoOfComponents (fun q => (s.app (K.X p)).app (L.X q))
      (fun q r _ => ((s.hom.app (K.X p)).naturality (L.d q r)).symm))
    (fun p r _ => by
      apply HomologicalComplex.hom_ext
      intro q
      change (s.hom.app (K.X p)).app (L.X q) ≫ (F.flip.map (K.d p r)).app (L.X q) =
        (F.map (K.d p r)).app (L.X q) ≫ (s.hom.app (K.X r)).app (L.X q)
      exact (NatTrans.congr_app (s.hom.naturality (K.d p r)) (L.X q)).symm)

/-- The cochain swap applies the signed total-complex flip after the coefficient swap. -/
def signedTotalCochainSwap (K L : Ch(k)) :
    mapBifunctor K L F c ≅ mapBifunctor L K F c :=
  (HomologicalComplex₂.totalFunctor PST(k) c c c).mapIso
    (projectiveTensorBicomplexSwap F s K L) ≪≫ (mapBifunctorFlipIso L K F c)

/-- On each antidiagonal summand the swap is the original coefficient swap with its sign. -/
theorem ι_signedTotalCochainSwap_hom (K L : Ch(k)) (p q n : ℤ)
    (h : ComplexShape.π c c c (p, q) = n) :
    ιMapBifunctor K L F c p q n h ≫ (signedTotalCochainSwap F s K L).hom.f n =
      ComplexShape.σ c c c q p • ((s.hom.app (K.X p)).app (L.X q) ≫
        ιMapBifunctor L K F c q p n (by
          change q + p = n
          change p + q = n at h
          omega)) := by
  simp only [signedTotalCochainSwap, Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.comp_f]
  change _ ≫ ((HomologicalComplex₂.total.map (projectiveTensorBicomplexSwap F s K L).hom c).f n ≫
      (mapBifunctorFlipIso L K F c).hom.f n) = _
  rw [HomologicalComplex₂.ιTotal_map_assoc, ι_mapBifunctorFlipIso_hom, Linear.comp_units_smul]
  rfl

/-- An involutive coefficient swap remains involutive with the native cochain signs. -/
theorem signedTotalCochainSwap_involutive
    (hs : ∀ P Q, (s.hom.app P).app Q ≫ (s.hom.app Q).app P = 𝟙 _) (K L : Ch(k)) :
    (signedTotalCochainSwap F s K L).hom ≫ (signedTotalCochainSwap F s L K).hom = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.comp_id, ← Category.assoc]
  rw [ι_signedTotalCochainSwap_hom, Linear.units_smul_comp, Category.assoc,
    ι_signedTotalCochainSwap_hom, Linear.comp_units_smul, ← smul_assoc, ← Category.assoc, hs,
    Category.id_comp]
  change ((q * p).negOnePow * (p * q).negOnePow) • _ = _
  have hsign : (q * p).negOnePow * (p * q).negOnePow = 1 := by
    rw [mul_comm q p, Int.units_mul_self]
  rw [hsign, one_smul]

private theorem projectiveTensorBicomplexSwap_naturality {K K' L L' : Ch(k)}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((F.mapBifunctorHomologicalComplex c c).map f).app L ≫
        ((F.mapBifunctorHomologicalComplex c c).obj K').map g ≫
        (projectiveTensorBicomplexSwap F s K' L').hom =
      (projectiveTensorBicomplexSwap F s K L).hom ≫
        ((F.flip.mapBifunctorHomologicalComplex c c).map f).app L ≫
        ((F.flip.mapBifunctorHomologicalComplex c c).obj K').map g := by
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  change (F.map (f.f p)).app (L.X q) ≫ (F.obj (K'.X p)).map (g.f q) ≫
        (s.hom.app (K'.X p)).app (L'.X q) =
      (s.hom.app (K.X p)).app (L.X q) ≫ (F.flip.map (f.f p)).app (L.X q) ≫
        (F.flip.obj (K'.X p)).map (g.f q)
  rw [(s.hom.app (K'.X p)).naturality (g.f q), ← Category.assoc, ← NatTrans.comp_app,
    s.hom.naturality, NatTrans.comp_app, Category.assoc]

private theorem signedTotalCochainSwap_naturality {K K' L L' : Ch(k)}
    (f : K ⟶ K') (g : L ⟶ L') :
    mapBifunctorMap f g F c ≫ (signedTotalCochainSwap F s K' L').hom =
      (signedTotalCochainSwap F s K L).hom ≫ mapBifunctorMap g f F c := by
  let A := F.mapBifunctorHomologicalComplex c c
  let B := F.flip.mapBifunctorHomologicalComplex c c
  let V := HomologicalComplex₂.totalFunctor PST(k) c c c
  let a := (A.map f).app L ≫ (A.obj K').map g
  let b := (B.map f).app L ≫ (B.obj K').map g
  let t := (projectiveTensorBicomplexSwap F s K L).hom
  let t' := (projectiveTensorBicomplexSwap F s K' L').hom
  have h : a ≫ t' = t ≫ b := (Category.assoc _ _ _).trans
    (projectiveTensorBicomplexSwap_naturality F s f g)
  have h' : mapBifunctorMap f g F c ≫ V.map t' = V.map t ≫ mapBifunctorMap f g F.flip c :=
    (V.map_comp _ _).symm.trans ((V.congr_map h).trans (V.map_comp _ _))
  simp only [signedTotalCochainSwap, Iso.trans_hom, Functor.mapIso_hom]
  change mapBifunctorMap f g F c ≫ V.map t' ≫ (mapBifunctorFlipIso L' K' F c).hom =
    (V.map t ≫ (mapBifunctorFlipIso L K F c).hom) ≫ mapBifunctorMap g f F c
  rw [← Category.assoc, h', Category.assoc, mapBifunctorFlipIso_hom_naturality,
    ← Category.assoc]

/-- The signed swap at a fixed first homotopy representative. -/
def signedTotalHomotopySwapAt (K : Ho(k)) :
    (signedTotalHomotopyBifunctor F).obj K ≅ (signedTotalHomotopyBifunctor F).flip.obj K :=
  CategoryTheory.Quotient.natIsoLift (homotopic PST(k) c)
    (NatIso.ofComponents
      (fun L => (HomotopyCategory.quotient PST(k) c).mapIso (signedTotalCochainSwap F s K.as L))
      (fun g => by
        change (HomotopyCategory.quotient PST(k) c).map (mapBifunctorMap (𝟙 K.as) g F c) ≫
            (HomotopyCategory.quotient PST(k) c).map (signedTotalCochainSwap F s K.as _).hom =
          (HomotopyCategory.quotient PST(k) c).map (signedTotalCochainSwap F s K.as _).hom ≫
            (HomotopyCategory.quotient PST(k) c).map (mapBifunctorMap g (𝟙 K.as) F c)
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg ((HomotopyCategory.quotient PST(k) c).map)
          (signedTotalCochainSwap_naturality F s (𝟙 K.as) g)))

/-- The signed comparison descends through both native homotopy quotients. -/
def signedTotalHomotopySwap :
    signedTotalHomotopyBifunctor F ≅ (signedTotalHomotopyBifunctor F).flip :=
  CategoryTheory.Quotient.natIsoLift (homotopic PST(k) c)
    (NatIso.ofComponents (fun K => signedTotalHomotopySwapAt F s
      ((HomotopyCategory.quotient PST(k) c).obj K)) (fun f => by
        apply NatTrans.ext
        funext L
        change (HomotopyCategory.quotient PST(k) c).map (mapBifunctorMap f (𝟙 L.as) F c) ≫
            (HomotopyCategory.quotient PST(k) c).map (signedTotalCochainSwap F s _ L.as).hom =
          (HomotopyCategory.quotient PST(k) c).map (signedTotalCochainSwap F s _ L.as).hom ≫
            (HomotopyCategory.quotient PST(k) c).map (mapBifunctorMap (𝟙 L.as) f F c)
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg ((HomotopyCategory.quotient PST(k) c).map)
          (signedTotalCochainSwap_naturality F s f (𝟙 L.as))))

/-- Involutivity on the actual homotopy representatives follows from the cochain formula. -/
theorem signedTotalHomotopySwap_involutive
    (hs : ∀ P Q, (s.hom.app P).app Q ≫ (s.hom.app Q).app P = 𝟙 _) (K L : Ho(k)) :
    ((signedTotalHomotopySwap F s).hom.app K).app L ≫
      ((signedTotalHomotopySwap F s).hom.app L).app K = 𝟙 _ := by
  let Q := HomotopyCategory.quotient PST(k) c
  change Q.map (signedTotalCochainSwap F s K.as L.as).hom ≫
    Q.map (signedTotalCochainSwap F s L.as K.as).hom = 𝟙 _
  rw [← Q.map_comp, signedTotalCochainSwap_involutive F s hs, Q.map_id]

variable [HasDerivedCategory.{w} PST(k)]

set_option quotPrecheck false in
local notation "D(" K ")" => DerivedCategory.Minus PST(K)

set_option maxHeartbeats 550000 in
-- The two-variable comparison uses the actual selected projective resolutions.
/-- The swap after applying the inclusion of the original bounded-above derived category. -/
def projectiveDerivedMinusBifunctorSwapComparison :
    let V := DerivedCategory.Minus.ι (C := PST(k))
    let W := (Functor.whiskeringRight D(k) D(k) (DerivedCategory PST(k))).obj V
    projectiveDerivedMinusBifunctor F ⋙ W ≅ (projectiveDerivedMinusBifunctor F).flip ⋙ W := by
  intro V W
  let I := (boundedAboveProjectiveEquivalence k).inverse ⋙
    (boundedAboveProjectiveCondition k).ι
  let Q := DerivedCategory.Qh (C := PST(k))
  let B := signedTotalHomotopyBifunctor F
  let d := signedTotalHomotopySwap F s
  refine NatIso.ofComponents (fun K => NatIso.ofComponents
    (fun L => Q.mapIso ((d.app (I.obj K)).app (I.obj L))) ?_) ?_
  · intro L L' g
    change Q.map ((B.obj (I.obj _)).map (I.map g)) ≫ Q.map ((d.hom.app _).app _) =
      Q.map ((d.hom.app _).app _) ≫ Q.map ((B.flip.obj (I.obj _)).map (I.map g))
    exact (Q.map_comp _ _).symm.trans
      ((Q.congr_map ((d.hom.app _).naturality (I.map g))).trans (Q.map_comp _ _))
  · intro K K' f
    apply NatTrans.ext
    funext L
    change Q.map ((B.map (I.map f)).app (I.obj L)) ≫ Q.map ((d.hom.app _).app _) =
      Q.map ((d.hom.app _).app _) ≫ Q.map ((B.flip.map (I.map f)).app (I.obj L))
    exact (Q.map_comp _ _).symm.trans
      ((Q.congr_map (NatTrans.congr_app (d.hom.naturality (I.map f)) (I.obj L))).trans
        (Q.map_comp _ _))

/-- The native swap on the selected bounded-above derived tensor. -/
def projectiveDerivedMinusBifunctorSwap :
    projectiveDerivedMinusBifunctor F ≅ (projectiveDerivedMinusBifunctor F).flip :=
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let hV := Functor.FullyFaithful.ofFullyFaithful V
  let H := (hV.whiskeringRight D(k)).whiskeringRight D(k)
  H.preimageIso (projectiveDerivedMinusBifunctorSwapComparison F s)

/-- The bounded-above derived swap maps to the literal signed swap of the projective models. -/
theorem projectiveDerivedMinusBifunctorSwap_map_app (K L : D(k)) :
    let I := (boundedAboveProjectiveEquivalence k).inverse ⋙
      (boundedAboveProjectiveCondition k).ι
    DerivedCategory.Minus.ι.map (((projectiveDerivedMinusBifunctorSwap F s).hom.app K).app L) =
      DerivedCategory.Qh.map (((signedTotalHomotopySwap F s).hom.app (I.obj K)).app (I.obj L)) := by
  intro I
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let hV := Functor.FullyFaithful.ofFullyFaithful V
  let H := (hV.whiskeringRight D(k)).whiskeringRight D(k)
  let e := projectiveDerivedMinusBifunctorSwapComparison F s
  have he := H.map_preimage (X := projectiveDerivedMinusBifunctor F)
    (Y := (projectiveDerivedMinusBifunctor F).flip) e.hom
  exact NatTrans.congr_app (NatTrans.congr_app he K) L

/-- Involutivity of the coefficient swap survives on the selected derived bifunctor. -/
theorem projectiveDerivedMinusBifunctorSwap_involutive
    (hs : ∀ P Q, (s.hom.app P).app Q ≫ (s.hom.app Q).app P = 𝟙 _) (K L : D(k)) :
    ((projectiveDerivedMinusBifunctorSwap F s).hom.app K).app L ≫
      ((projectiveDerivedMinusBifunctorSwap F s).hom.app L).app K = 𝟙 _ := by
  let Q := DerivedCategory.Qh (C := PST(k))
  let V := DerivedCategory.Minus.ι (C := PST(k))
  apply V.map_injective
  rw [V.map_comp, V.map_id, projectiveDerivedMinusBifunctorSwap_map_app,
    projectiveDerivedMinusBifunctorSwap_map_app, ← Q.map_comp,
    signedTotalHomotopySwap_involutive F s hs, Q.map_id]
  rfl

end AlgebraicGeometry.PresheafWithTransfers
