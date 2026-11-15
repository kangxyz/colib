/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Functor.FactorizationComparison
public import Mathlib.CategoryTheory.Shift.CommShift
import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-! # Shift compatibility of comparisons formed by whiskering -/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

/-- Pasting two shift-compatible squares gives a shift-compatible comparison. -/
theorem isoSquareRoute_hom_commShift
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*} [Category* A₀] [Category* A₁] [Category* A₂]
    [Category* B₀] [Category* B₁] [Category* B₂] {S : Type*} [AddMonoid S]
    [HasShift A₀ S] [HasShift A₁ S] [HasShift A₂ S]
    [HasShift B₀ S] [HasShift B₁ S] [HasShift B₂ S]
    {a : A₀ ⥤ A₁} {b : A₁ ⥤ A₂} {N : B₀ ⥤ B₁} {M : B₁ ⥤ B₂}
    {E₀ : A₀ ⥤ B₀} {E₁ : A₁ ⥤ B₁} {E₂ : A₂ ⥤ B₂}
    [a.CommShift S] [b.CommShift S] [N.CommShift S] [M.CommShift S]
    [E₀.CommShift S] [E₁.CommShift S] [E₂.CommShift S]
    (s : a ⋙ E₁ ≅ E₀ ⋙ N) (t : b ⋙ E₂ ≅ E₁ ⋙ M)
    [NatTrans.CommShift s.hom S] [NatTrans.CommShift t.hom S] :
    NatTrans.CommShift (isoSquareRoute s t).hom S := by
  let : NatTrans.CommShift (associator a b E₂).hom S :=
    NatTrans.CommShift.associator b E₂ S
  let : NatTrans.CommShift (associator a E₁ M).hom S :=
    NatTrans.CommShift.associator E₁ M S
  let : NatTrans.CommShift (associator a E₁ M).inv S :=
    NatTrans.CommShift.of_iso_inv (associator a E₁ M) S
  let : NatTrans.CommShift (associator E₀ N M).hom S :=
    NatTrans.CommShift.associator N M S
  simp only [isoSquareRoute, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom]
  infer_instance

/-- The factorization comparison preserves the shift when each of its maps does. -/
theorem factorizationComparison_commShift
    {J H D E : Type*} [Category* J] [Category* H] [Category* D] [Category* E]
    {S : Type*} [AddMonoid S] [HasShift J S] [HasShift H S] [HasShift D S] [HasShift E S]
    {U₀ U₁ : J ⥤ J} {U₂ F₀ : H ⥤ H} {V₀ L : J ⥤ D}
    {V : D ⥤ E} {Q : H ⥤ E} {I : J ⥤ H}
    [U₀.CommShift S] [U₁.CommShift S] [U₂.CommShift S] [F₀.CommShift S]
    [V₀.CommShift S] [L.CommShift S] [V.CommShift S] [Q.CommShift S] [I.CommShift S]
    (d : V₀ ⋙ V ≅ I ⋙ Q) (e : U₁ ⋙ I ≅ I ⋙ U₂) (c : L ⋙ V ≅ I ⋙ F₀ ⋙ Q)
    (η : U₀ ⟶ U₁) (θ : U₂ ⟶ F₀) [NatTrans.CommShift d.hom S]
    [NatTrans.CommShift e.hom S] [NatTrans.CommShift c.hom S]
    [NatTrans.CommShift η S] [NatTrans.CommShift θ S] :
    NatTrans.CommShift (factorizationComparison d e c η θ) S := by
  let : NatTrans.CommShift (isoSquareRoute e d).hom S := isoSquareRoute_hom_commShift e d
  let : NatTrans.CommShift c.inv S := NatTrans.CommShift.of_iso_inv c S
  dsimp only [factorizationComparison]
  infer_instance

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

/-- A faithful postcomposition detects shift compatibility when the postcomposed map is
identified with a precomposed shift-compatible map by the two specified isomorphisms. -/
theorem commShift_of_whiskerRight_eq_whiskerLeft
    {C J D E : Type*} [Category* C] [Category* J] [Category* D] [Category* E]
    {S : Type*} [AddMonoid S] [HasShift C S] [HasShift J S] [HasShift D S] [HasShift E S]
    {G L : J ⥤ D} {X Y : C ⥤ D} (I : C ⥤ J) (V : D ⥤ E)
    [G.CommShift S] [L.CommShift S] [X.CommShift S] [Y.CommShift S]
    [I.CommShift S] [V.CommShift S] [V.Faithful]
    (a : X ≅ I ⋙ G) (b : Y ≅ I ⋙ L) (n : G ⋙ V ⟶ L ⋙ V)
    [CommShift a.hom S] [CommShift b.hom S] [CommShift n S]
    (f : X ⟶ Y)
    (h : Functor.whiskerRight f V =
      (Functor.isoWhiskerRight a V ≪≫ Functor.associator I G V).hom ≫
        Functor.whiskerLeft I n ≫
          (Functor.isoWhiskerRight b V ≪≫ Functor.associator I L V).inv) :
    CommShift f S := by
  let a₀ := Functor.isoWhiskerRight a V
  let b₀ := Functor.isoWhiskerRight b V
  let a₁ := Functor.associator I G V
  let b₁ := Functor.associator I L V
  let : CommShift a₀.hom S := CommShift.whiskerRight a.hom V S
  let : CommShift b₀.hom S := CommShift.whiskerRight b.hom V S
  let : CommShift a₁.hom S := CommShift.associator G V S
  let : CommShift b₁.hom S := CommShift.associator L V S
  let : CommShift (a₀ ≪≫ a₁).hom S := CommShift.comp a₀.hom a₁.hom S
  let : CommShift (b₀ ≪≫ b₁).hom S := CommShift.comp b₀.hom b₁.hom S
  let m := Functor.whiskerLeft I n
  let : CommShift m S := CommShift.whiskerLeft (F₁ := I) (G ⋙ V) (L ⋙ V) n S
  exact CommShift.of_comp_faithful (G := V)
    (h := commShift_of_eq_conj (a₀ ≪≫ a₁) (b₀ ≪≫ b₁) m h)

end CategoryTheory.NatTrans
