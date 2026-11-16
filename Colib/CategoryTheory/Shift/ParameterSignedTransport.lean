/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Shift.ParameterTransport
public import Colib.CategoryTheory.Shift.ParameterBoundary

/-! # Signed parameter transport with the original additive-shift boundary -/
@[expose] public section
namespace CategoryTheory
open CategoryTheory.Functor
variable {C D : Type*} [Category* C] [Category* D]
  [HasShift C ℤ] [HasShift D ℤ]
  (E : C ⥤ D) (F : C ⥤ C) (G : D ⥤ D)
  [E.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
  (τ : F ⋙ E ⟶ E ⋙ G) [NatTrans.CommShift τ ℤ]

/-- A genuine cochain parameter square determines its native signed placement.
The comparison remains one-way, and the target shift retains its native sign. -/
theorem parameter_square_signed {M N X Y : C} {M' N' : D}
    (f : M ⟶ F.obj N) (g : M' ⟶ G.obj N')
    (a : E.obj M ≅ M') (b : E.obj N ≅ N')
    (h : E.map f ≫ τ.app N ≫ G.map b.hom = a.hom ≫ g)
    (t s : ℤ) (hs : t + 1 = s) (θ : X ≅ M⟦s⟧) (ψ : Y ≅ N⟦t⟧) :
    let θ' := E.mapIso θ ≪≫ (E.commShiftIso s).app M ≪≫
      (shiftFunctor D s).mapIso a
    let ψ' := E.mapIso ψ ≪≫ (E.commShiftIso t).app N ≪≫
      (shiftFunctor D t).mapIso b
    E.map (θ.hom ≫ f⟦s⟧' ≫ (F.commShiftIso s).inv.app N ≫
      F.map ((shiftFunctorAdd' C t 1 s hs).hom.app N ≫ ψ.inv⟦(1 : ℤ)⟧')) ≫
      τ.app (Y⟦(1 : ℤ)⟧) ≫ G.map ((E.commShiftIso (1 : ℤ)).hom.app Y) =
    θ'.hom ≫ g⟦s⟧' ≫ (G.commShiftIso s).inv.app N' ≫
      G.map ((shiftFunctorAdd' D t 1 s hs).hom.app N' ≫ ψ'.inv⟦(1 : ℤ)⟧') := by
  intro θ' ψ'
  let u := (E.commShiftIso s).hom.app N ≫ b.hom⟦s⟧'
  let v := (shiftFunctorAdd' C t 1 s hs).hom.app N ≫ ψ.inv⟦(1 : ℤ)⟧'
  let w := (shiftFunctorAdd' D t 1 s hs).hom.app N' ≫ ψ'.inv⟦(1 : ℤ)⟧'
  have hb : E.map v ≫ (E.commShiftIso (1 : ℤ)).hom.app Y = u ≫ w :=
    parameter_boundary_transport E t s hs ψ b
  have hn : E.map (F.map v) ≫ τ.app (Y⟦(1 : ℤ)⟧) = τ.app (N⟦s⟧) ≫ G.map (E.map v) :=
    τ.naturality v
  have hshift := parameter_square_shift E F G τ f g a.hom b.hom h s
  change E.map (θ.hom ≫ f⟦s⟧' ≫ (F.commShiftIso s).inv.app N ≫ F.map v) ≫
    τ.app (Y⟦(1 : ℤ)⟧) ≫ G.map ((E.commShiftIso (1 : ℤ)).hom.app Y) =
    θ'.hom ≫ g⟦s⟧' ≫ (G.commShiftIso s).inv.app N' ≫ G.map w
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc, hb, Functor.map_comp]
  have hh := congrArg (fun z => E.map θ.hom ≫ z ≫ G.map w) hshift
  simpa only [θ', Iso.trans_hom, Functor.mapIso_hom, NatIso.app_hom,
    Functor.map_comp, Category.assoc, u] using hh

end CategoryTheory
