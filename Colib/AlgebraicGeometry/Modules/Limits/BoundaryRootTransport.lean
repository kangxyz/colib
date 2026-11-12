/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRoot

/-!
# Original root and boundary transport equations

Canonical descent recovers the original power isomorphism, while the original boundary
trivialization is compatible with successive squares. These concrete equations allow the same
specified full-boundary frame to be used with the actual root chosen by invertible descent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

private theorem root_recovery_aux {D : Type*} [Category D]
    {A B C E F G H I : D} (p : A ≅ B) (q : B ≅ C) (c : A ≅ E) (r : E ≅ F)
    (u : C ≅ F) (t : G ≅ F) (α : G ≅ H) (β : B ≅ I) (l : I ≅ H)
    (hcan : c.symm ≪≫ p ≪≫ q ≪≫ u = r)
    (hroot : p ≪≫ β ≪≫ l = c ≪≫ r ≪≫ t.symm ≪≫ α) :
    t ≪≫ u.symm ≪≫ q.symm ≪≫ β ≪≫ l = α := by
  rw [← hcan] at hroot
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc] at hroot
  simpa [Iso.trans_assoc] using congrArg
    (fun z => t ≪≫ u.symm ≪≫ q.symm ≪≫ p.symm ≪≫ z) hroot

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

private theorem root_map_iso_left {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' : C} {E : D} (a : A ≅ B) (b : B ≅ C') (u : F.obj C' ≅ E) :
    F.mapIso a ≪≫ F.mapIso b ≪≫ u = F.mapIso (a ≪≫ b) ≪≫ u := by
  rw [F.mapIso_trans, Iso.trans_assoc]

/-- Recover the specified root isomorphism from the canonical descent equation. -/
theorem tensorPower_root_recovery {X Y Z : Scheme.{u}} (q : X ⟶ Y) (f : Y ⟶ Z) (p : X ⟶ Z)
    (hp : q ≫ f = p) (Mk : Z.Modules) (M T : X.Modules) (Q : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property Mk]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (eM : M ≅ (Scheme.Modules.pullback p).obj Mk) (n : ℕ)
    (α : tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
      M (n : ℤ) ≅ T)
    (β : tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
      ((Scheme.Modules.pullback f).obj Mk) (n : ℤ) ≅ Q)
    (l : (Scheme.Modules.pullback q).obj Q ≅ T)
    (hβ : (Scheme.Modules.pullback q).mapIso
        (Scheme.Modules.pullbackTensorPowerIso f Mk n ≪≫ β) ≪≫ l =
      canIso q f p hp (tensorPower Z.toRingedSpace.presheaf
        (structureSheafRing Z.toRingedSpace).property Mk (n : ℤ)) ≪≫
        Scheme.Modules.pullbackTensorPowerIso p Mk n ≪≫
        tensorPowerCongr X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
          _ _ eM.symm n ≪≫ α) :
    tensorPowerCongr X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
        _ _ (eM ≪≫ (canIso q f p hp Mk).symm) n ≪≫
      (Scheme.Modules.pullbackTensorPowerIso q ((Scheme.Modules.pullback f).obj Mk) n).symm ≪≫
      (Scheme.Modules.pullback q).mapIso β ≪≫ l = α := by
  let c := canIso q f p hp Mk
  let t := tensorPowerCongr X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property _ _ eM n
  let u := tensorPowerCongr X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property _ _ c n
  have hsym := tensorPowerCongr_symm X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property eM n
  have hr := (root_map_iso_left (Scheme.Modules.pullback q)
    (Scheme.Modules.pullbackTensorPowerIso f Mk n) β l).trans hβ
  have hr' := hr.trans (congrArg (fun z =>
    canIso q f p hp (tensorPower Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property Mk (n : ℤ)) ≪≫
      Scheme.Modules.pullbackTensorPowerIso p Mk n ≪≫ z ≪≫ α) hsym)
  have hrec := root_recovery_aux
    ((Scheme.Modules.pullback q).mapIso (Scheme.Modules.pullbackTensorPowerIso f Mk n))
    (Scheme.Modules.pullbackTensorPowerIso q ((Scheme.Modules.pullback f).obj Mk) n)
    (canIso q f p hp (tensorPower Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property Mk (n : ℤ)))
    (Scheme.Modules.pullbackTensorPowerIso p Mk n) u t α
    ((Scheme.Modules.pullback q).mapIso β) l
    (pullbackTensorPowerIso_can q f p hp Mk n) hr'
  have he := (tensorPowerCongr_trans X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property eM c.symm n).trans
      (congrArg (fun z => t ≪≫ z) (tensorPowerCongr_symm X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property c n))
  have he' := congrArg (fun z => z ≪≫
    (Scheme.Modules.pullbackTensorPowerIso q ((Scheme.Modules.pullback f).obj Mk) n).symm ≪≫
      (Scheme.Modules.pullback q).mapIso β ≪≫ l) he
  exact he'.trans ((Iso.trans_assoc _ _ _).trans hrec)

private theorem square_chain_aux {D : Type*} [Category D]
    {X0 X1 P T R S U V : D}
    (a : X0 ≅ P) (b : X1 ≅ P) (c : P ≅ T) (d : X0 ≅ R) (e : R ≅ T)
    (f : X1 ≅ S) (g : S ≅ T) (h : U ≅ V) (i : V ≅ T) (j : U ≅ S)
    (h1 : a ≪≫ c = d ≪≫ e) (h2 : b ≪≫ c = f ≪≫ g) (h3 : h ≪≫ i = j ≪≫ g) :
    d ≪≫ e ≪≫ i.symm = a ≪≫ b.symm ≪≫ f ≪≫ j.symm ≪≫ h := by
  have hr : (a ≪≫ b.symm ≪≫ f ≪≫ j.symm ≪≫ h) ≪≫ i = d ≪≫ e := by
    simp only [Iso.trans_assoc]
    rw [h3]
    simp only [Iso.symm_self_id_assoc]
    rw [← h2]
    simp only [Iso.symm_self_id_assoc]
    exact h1
  simpa [Iso.trans_assoc] using (congrArg (fun z => z ≪≫ i.symm) hr).symm

private theorem map_square_assoc {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B T : C} {S U V : D} (a : A ≅ T) (b : B ≅ T) (f : F.obj B ≅ S)
    (j : U ≅ S) (h : U ≅ V) :
    F.mapIso (a ≪≫ b.symm) ≪≫ (f ≪≫ j.symm) ≪≫ h =
      F.mapIso a ≪≫ (F.mapIso b).symm ≪≫ f ≪≫ j.symm ≪≫ h := by
  simp [Iso.trans_assoc]

/-- Composition of the actual comparisons of two successive boundary squares. -/
theorem pullbackSquareIso_comp {A B C A' B' C' : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (s : A ⟶ C)
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (p : A' ⟶ B') (q : B' ⟶ C') (r : A' ⟶ C')
    (hfg : f ≫ g = s) (hpq : p ≫ q = r)
    (hf : f ≫ b = a ≫ p) (hg : g ≫ c = b ≫ q) (hs : s ≫ c = a ≫ r)
    (L : C'.Modules) :
    canIso f g s hfg ((Scheme.Modules.pullback c).obj L) ≪≫
      pullbackSquareIso s c a r hs L =
    (Scheme.Modules.pullback f).mapIso (pullbackSquareIso g c b q hg L) ≪≫
      pullbackSquareIso f b a p hf ((Scheme.Modules.pullback q).obj L) ≪≫
      (Scheme.Modules.pullback a).mapIso (canIso p q r hpq L) := by
  have htot : (a ≫ p) ≫ q = a ≫ r := by rw [Category.assoc, hpq]
  have hft : f ≫ (b ≫ q) = a ≫ r := by rw [← Category.assoc, hf, htot]
  have hc := square_chain_aux
    ((Scheme.Modules.pullback f).mapIso (canIso g c (b ≫ q) hg L))
    ((Scheme.Modules.pullback f).mapIso (canIso b q (b ≫ q) rfl L))
    (canIso f (b ≫ q) (a ≫ r) hft L)
    (canIso f g s hfg ((Scheme.Modules.pullback c).obj L))
    (canIso s c (a ≫ r) hs L)
    (canIso f b (a ≫ p) hf ((Scheme.Modules.pullback q).obj L))
    (canIso (a ≫ p) q (a ≫ r) htot L)
    ((Scheme.Modules.pullback a).mapIso (canIso p q r hpq L))
    (canIso a r (a ≫ r) rfl L)
    (canIso a p (a ≫ p) rfl ((Scheme.Modules.pullback q).obj L))
    (Iso.ext (canHom_comp f g c s (b ≫ q) (a ≫ r) hfg hg hs hft L))
    (Iso.ext (canHom_comp f b q (a ≫ p) (b ≫ q) (a ≫ r) hf rfl htot hft L))
    (Iso.ext (canHom_comp a p q (a ≫ p) r (a ≫ r) rfl hpq htot rfl L))
  have hn := map_square_assoc (Scheme.Modules.pullback f)
    (canIso g c (b ≫ q) hg L) (canIso b q (b ≫ q) rfl L)
    (canIso f b (a ≫ p) hf ((Scheme.Modules.pullback q).obj L))
    (canIso a p (a ≫ p) rfl ((Scheme.Modules.pullback q).obj L))
    ((Scheme.Modules.pullback a).mapIso (canIso p q r hpq L))
  exact hc.trans hn.symm

private theorem trivialization_square_aux {D : Type*} [Category D]
    {A B C D' E F G H J : D}
    (x : A ≅ B) (y : B ≅ C) (z : C ≅ D') (d : A ≅ E) (s : E ≅ D')
    (v : A ≅ F) (dU : F ≅ G) (w : E ≅ G) (fu : F ≅ H) (u : H ≅ J) (us : G ≅ J)
    (hs : d ≪≫ s = x ≪≫ y ≪≫ z) (hn : v ≪≫ dU = d ≪≫ w)
    (hu : fu ≪≫ u = dU ≪≫ us) :
    y.symm ≪≫ x.symm ≪≫ v ≪≫ fu ≪≫ u = z ≪≫ s.symm ≪≫ w ≪≫ us := by
  have hc : y.symm ≪≫ x.symm ≪≫ d = z ≪≫ s.symm := by
    simpa [Iso.trans_assoc] using
      congrArg (fun e => y.symm ≪≫ x.symm ≪≫ e ≪≫ s.symm) hs
  rw [hu, ← Iso.trans_assoc v dU us, hn]
  simpa only [Iso.trans_assoc] using congrArg (fun e => e ≪≫ w ≪≫ us) hc

private theorem map_trivialization {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B U V : C} {P Q : D} (s : A ≅ B) (t : A ≅ U) (u : U ≅ V)
    (r : F.obj B ≅ P) (v : F.obj V ≅ Q) :
    r.symm ≪≫ F.mapIso (s.symm ≪≫ t ≪≫ u) ≪≫ v =
      r.symm ≪≫ (F.mapIso s).symm ≪≫ F.mapIso t ≪≫ F.mapIso u ≪≫ v := by
  simp [Iso.trans_assoc]

private theorem unit_comp_aux {D : Type*} [Category D] {A B C U V : D}
    (c : A ≅ B) (d : B ≅ C) (a : A ≅ U) (b : U ≅ V) (e : C ≅ V)
    (h : d.inv ≫ c.inv ≫ a.hom ≫ b.hom = e.hom) :
    a ≪≫ b = (c ≪≫ d) ≪≫ e := by
  apply Iso.ext
  apply (cancel_epi (d.inv ≫ c.inv)).mp
  simpa only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc] using h

/-- The actual structure-sheaf comparison is compatible with the named composite. -/
theorem pullbackUnitIso_can {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (s : A ⟶ C) (hfg : f ≫ g = s) :
    (Scheme.Modules.pullback f).mapIso (Scheme.Modules.pullbackUnitIso g) ≪≫
      Scheme.Modules.pullbackUnitIso f =
    canIso f g s hfg (SheafOfModules.unit C.ringCatSheaf) ≪≫
      Scheme.Modules.pullbackUnitIso s := by
  exact unit_comp_aux
    ((Scheme.Modules.pullbackComp f g).app (SheafOfModules.unit C.ringCatSheaf))
    ((Scheme.Modules.pullbackCongr hfg).app (SheafOfModules.unit C.ringCatSheaf))
    ((Scheme.Modules.pullback f).mapIso (Scheme.Modules.pullbackUnitIso g))
    (Scheme.Modules.pullbackUnitIso f) (Scheme.Modules.pullbackUnitIso s)
    (Scheme.Modules.pullbackUnitIso_comp_eq f g s hfg)

/-- The original boundary trivialization agrees along two successive commutative squares. -/
theorem pullbackBoundaryTrivialization_comp {A B C A' B' C' : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (s : A ⟶ C)
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (p : A' ⟶ B') (q : B' ⟶ C') (r : A' ⟶ C')
    (hfg : f ≫ g = s) (hpq : p ≫ q = r)
    (hf : f ≫ b = a ≫ p) (hg : g ≫ c = b ≫ q) (hs : s ≫ c = a ≫ r)
    (L : C'.Modules)
    (τ : (Scheme.Modules.pullback c).obj L ≅ SheafOfModules.unit C.ringCatSheaf) :
    pullbackBoundaryTrivialization f b a p hf ((Scheme.Modules.pullback q).obj L)
      (pullbackBoundaryTrivialization g c b q hg L τ) =
    (Scheme.Modules.pullback a).mapIso (canIso p q r hpq L) ≪≫
      pullbackBoundaryTrivialization s c a r hs L τ := by
  have he := trivialization_square_aux
    ((Scheme.Modules.pullback f).mapIso (pullbackSquareIso g c b q hg L))
    (pullbackSquareIso f b a p hf ((Scheme.Modules.pullback q).obj L))
    ((Scheme.Modules.pullback a).mapIso (canIso p q r hpq L))
    (canIso f g s hfg ((Scheme.Modules.pullback c).obj L))
    (pullbackSquareIso s c a r hs L)
    ((Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullback g).mapIso τ))
    (canIso f g s hfg (SheafOfModules.unit C.ringCatSheaf))
    ((Scheme.Modules.pullback s).mapIso τ)
    ((Scheme.Modules.pullback f).mapIso (Scheme.Modules.pullbackUnitIso g))
    (Scheme.Modules.pullbackUnitIso f) (Scheme.Modules.pullbackUnitIso s)
    (pullbackSquareIso_comp f g s a b c p q r hfg hpq hf hg hs L)
    (Iso.ext (canHom_naturality f g s hfg τ.hom))
    (pullbackUnitIso_can f g s hfg)
  exact (map_trivialization (Scheme.Modules.pullback f)
    (pullbackSquareIso g c b q hg L) ((Scheme.Modules.pullback g).mapIso τ)
    (Scheme.Modules.pullbackUnitIso g)
    (pullbackSquareIso f b a p hf ((Scheme.Modules.pullback q).obj L))
    (Scheme.Modules.pullbackUnitIso f)).trans he

private theorem root_iso_transport_aux {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {AT AM LT LM : C} {PT PM U V : D}
    (a : AT ≅ LT) (l : LT ≅ LM) (r : AT ≅ AM) (α : AM ≅ LM)
    (pT : F.obj AT ≅ PT) (pM : F.obj AM ≅ PM) (rB : PT ≅ PM)
    (τ : F.obj LM ≅ V) (w : U ≅ V)
    (hroot : a ≪≫ l = r ≪≫ α) (hnat : F.mapIso r ≪≫ pM = pT ≪≫ rB) :
    pT.symm ≪≫ F.mapIso a ≪≫ (F.mapIso l ≪≫ τ) ≪≫ w.symm =
      rB ≪≫ pM.symm ≪≫ F.mapIso α ≪≫ τ ≪≫ w.symm := by
  have hh : F.mapIso a ≪≫ F.mapIso l = F.mapIso r ≪≫ F.mapIso α := by
    simpa using congrArg F.mapIso hroot
  have hn : pT.symm ≪≫ F.mapIso r = rB ≪≫ pM.symm := by
    simpa [Iso.trans_assoc] using congrArg (fun z => pT.symm ≪≫ z ≪≫ pM.symm) hnat
  calc
    _ = pT.symm ≪≫ (F.mapIso a ≪≫ F.mapIso l) ≪≫ τ ≪≫ w.symm := by
      simp only [Iso.trans_assoc]
    _ = pT.symm ≪≫ (F.mapIso r ≪≫ F.mapIso α) ≪≫ τ ≪≫ w.symm := by rw [hh]
    _ = (pT.symm ≪≫ F.mapIso r) ≪≫ F.mapIso α ≪≫ τ ≪≫ w.symm := by
      simp only [Iso.trans_assoc]
    _ = _ := by rw [hn]; simp only [Iso.trans_assoc]

/-- Transport the actual root equation through specified ambient and target isomorphisms. -/
theorem boundaryRootPowerIso_transport {X Y : Scheme.{u}} (b : X ⟶ Y)
    (T M LT LM : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property T]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M]
    (r : T ≅ M) (n : ℕ)
    (αT : tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
      T (n : ℤ) ≅ LT)
    (αM : tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
      M (n : ℤ) ≅ LM) (l : LT ≅ LM)
    (τ : (Scheme.Modules.pullback b).obj LM ≅ SheafOfModules.unit X.ringCatSheaf)
    (hroot : αT ≪≫ l = tensorPowerCongr Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property _ _ r n ≪≫ αM) :
    boundaryRootPowerIso b T LT n αT ((Scheme.Modules.pullback b).mapIso l ≪≫ τ) =
      tensorPowerCongr X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
        _ _ ((Scheme.Modules.pullback b).mapIso r) n ≪≫
      boundaryRootPowerIso b M LM n αM τ := by
  exact root_iso_transport_aux (Scheme.Modules.pullback b) αT l
    (tensorPowerCongr Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property _ _ r n) αM
    (Scheme.Modules.pullbackTensorPowerIso b T n)
    (Scheme.Modules.pullbackTensorPowerIso b M n)
    (tensorPowerCongr X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
      _ _ ((Scheme.Modules.pullback b).mapIso r) n)
    τ (structureSheafTensorPowerIso X n) hroot
    (Scheme.Modules.pullbackTensorPowerIso_naturality b r n)

local instance (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

/-- A specified original full-boundary frame transports with the same root equation. -/
theorem boundary_root_frame_transport {X Y : Scheme.{u}} (b : X ⟶ Y)
    (T M LT LM : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property T]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M]
    (r : T ≅ M) (n : ℕ)
    (αT : tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
      T (n : ℤ) ≅ LT)
    (αM : tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
      M (n : ℤ) ≅ LM) (l : LT ≅ LM)
    (τ : (Scheme.Modules.pullback b).obj LM ≅ SheafOfModules.unit X.ringCatSheaf)
    (e : (Scheme.Modules.pullback b).obj M ≅ SheafOfModules.unit X.ringCatSheaf)
    (hroot : αT ≪≫ l = tensorPowerCongr Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property _ _ r n ≪≫ αM)
    (he : tensorPowerCongr X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property _ _ e n =
        boundaryRootPowerIso b M LM n αM τ) :
    tensorPowerCongr X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property _ _
      ((Scheme.Modules.pullback b).mapIso r ≪≫ e) n =
    boundaryRootPowerIso b T LT n αT ((Scheme.Modules.pullback b).mapIso l ≪≫ τ) := by
  exact (tensorPowerCongr_trans X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback b).mapIso r) e n).trans
      ((congrArg (fun z => tensorPowerCongr X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property _ _
          ((Scheme.Modules.pullback b).mapIso r) n ≪≫ z) he).trans
        (boundaryRootPowerIso_transport b T M LT LM r n αT αM l τ hroot).symm)

end Stacks.AlgebraicGeometry.ModuleLimits
