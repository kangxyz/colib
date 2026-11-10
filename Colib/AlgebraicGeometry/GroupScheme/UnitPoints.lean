/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.GroupScheme.LaurentOpen

/-!
# Actual unit-valued points of the native multiplicative-group base change

These maps use the specified Stacks representation of global units. Their
forward coordinate is proved explicitly, so the construction cannot silently
invert the coordinate or change the torus model. Affine points use the native
`ΓSpecIso`, including its naturality for noninjective ring maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}}

/-- The point of the existing native torus representing an actual global unit. -/
def nativeTorusPoint (f : X ⟶ S) (v : (Γ(X, ⊤))ˣ) :
    Over.mk f ⟶ Scheme.asOver (multiplicativeGroupBaseChange S) S :=
  ((multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv (X := Over.mk f)).symm v

/-- The existing Stacks representation recovers exactly the specified unit. -/
theorem nativeTorusPoint_represents (f : X ⟶ S) (v : (Γ(X, ⊤))ˣ) :
    (multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv
      (nativeTorusPoint f v) = v :=
  ((multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv
    (X := Over.mk f)).apply_symm_apply v

/-- The structural map of the point is the original map to the base. -/
@[reassoc] theorem nativeTorusPoint_over
    (f : X ⟶ S) (v : (Γ(X, ⊤))ˣ) :
    (nativeTorusPoint f v).left ≫
      (multiplicativeGroupBaseChange S ↘ S) = f :=
  Over.w _

/-- Pulling back the forward torus coordinate gives the actual specified unit. -/
theorem nativeTorusPoint_coordinate (f : X ⟶ S) (v : (Γ(X, ⊤))ˣ) :
    Units.map (nativeTorusPoint f v).left.appTop.hom.toMonoidHom
      (multiplicativeGroupBaseChangeCoordinate S) = v := by
  have h := baseChangePointsIsoGlobalUnits_hom_app S (Opposite.op (Over.mk f))
    (nativeTorusPoint f v)
  change (multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv
    (nativeTorusPoint f v) = _ at h
  rw [nativeTorusPoint_represents] at h
  apply Units.ext
  have he := congrArg Units.val h
  change (v : Γ(X, ⊤)) =
    ((nativeTorusPoint f v).left ≫ pullback.fst
      (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S)).appTop.hom multiplicativeCoordinate.val at he
  dsimp only [Scheme.asOver, OverClass.asOver, Over.mk, CostructuredArrow.mk] at he ⊢
  rw [Scheme.Hom.comp_appTop] at he
  exact he.symm

/-- The native point construction is natural in the actual source morphism. -/
theorem nativeTorusPoint_comp (f : X ⟶ S) (a : Y ⟶ X) (v : (Γ(X, ⊤))ˣ) :
    nativeTorusPoint (a ≫ f) (Units.map a.appTop.hom.toMonoidHom v) =
      Over.homMk a rfl ≫ nativeTorusPoint f v := by
  apply (multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv.injective
  rw [nativeTorusPoint_represents,
    (multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv_comp,
    nativeTorusPoint_represents]
  rfl

/-- Naturality also holds after forgetting to schemes. -/
@[reassoc] theorem nativeTorusPoint_comp_left
    (f : X ⟶ S) (a : Y ⟶ X) (v : (Γ(X, ⊤))ˣ) :
    (nativeTorusPoint (a ≫ f) (Units.map a.appTop.hom.toMonoidHom v)).left =
      a ≫ (nativeTorusPoint f v).left :=
  congrArg (fun h => h.left) (nativeTorusPoint_comp f a v)

/-- The unit one is the pullback of the literal identity section over the base. -/
theorem nativeTorusPoint_one (f : X ⟶ S) :
    (nativeTorusPoint f 1).left = f ≫ (nativeTorusPoint (𝟙 S) 1).left := by
  let a : Over.mk f ⟶ Over.mk (𝟙 S) := Over.homMk f (Category.comp_id f)
  have h : nativeTorusPoint f 1 = a ≫ nativeTorusPoint (𝟙 S) 1 := by
    apply ((multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv
      (X := Over.mk f)).injective
    rw [nativeTorusPoint_represents,
      (multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv_comp,
      nativeTorusPoint_represents]
    change (1 : (Γ(X, ⊤))ˣ) = Units.map f.appTop.hom.toMonoidHom 1
    exact (map_one _).symm
  simpa only [Over.comp_left, Over.homMk_left, a] using congrArg (fun k => k.left) h

variable {R A : Type u} [CommRing R] [CommRing A]

/-- An affine ring unit as an actual global unit, using the canonical `ΓSpecIso`. -/
def specGlobalUnit (v : Rˣ) : (Γ(Spec (.of R), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (.of R)).inv.hom.toMonoidHom v

/-- Recovering affine coordinates from this global unit gives the original ring unit. -/
theorem specGlobalUnit_recover (v : Rˣ) :
    Units.map (Scheme.ΓSpecIso (.of R)).hom.hom.toMonoidHom (specGlobalUnit v) = v := by
  apply Units.ext
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of R)).inv_hom_id (v : R)

/-- Global affine units commute with every coefficient map, without injectivity. -/
theorem specGlobalUnit_natural (a : R →+* A) (v : Rˣ) :
    Units.map (Spec.map (CommRingCat.ofHom a)).appTop.hom.toMonoidHom (specGlobalUnit v) =
      specGlobalUnit (Units.map a.toMonoidHom v) := by
  apply Units.ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom a)
  exact (ConcreteCategory.congr_hom h (v : R)).symm

/-- The specified affine unit as a point of the existing native base-change torus. -/
def nativeAffineTorusPoint (f : Spec (.of R) ⟶ S) (v : Rˣ) :
    Over.mk f ⟶ Scheme.asOver (multiplicativeGroupBaseChange S) S :=
  nativeTorusPoint f (specGlobalUnit v)

/-- Its coordinate is literally the original affine ring unit. -/
theorem nativeAffineTorusPoint_coordinate (f : Spec (.of R) ⟶ S) (v : Rˣ) :
    Units.map (Scheme.ΓSpecIso (.of R)).hom.hom.toMonoidHom
      (Units.map (nativeAffineTorusPoint f v).left.appTop.hom.toMonoidHom
        (multiplicativeGroupBaseChangeCoordinate S)) = v := by
  rw [nativeAffineTorusPoint, nativeTorusPoint_coordinate, specGlobalUnit_recover]

/-- Affine unit points commute with arbitrary ring specializations. -/
theorem nativeAffineTorusPoint_natural (f : Spec (.of R) ⟶ S) (a : R →+* A) (v : Rˣ) :
    (nativeAffineTorusPoint (Spec.map (CommRingCat.ofHom a) ≫ f) (Units.map a.toMonoidHom v)).left =
      Spec.map (CommRingCat.ofHom a) ≫ (nativeAffineTorusPoint f v).left := by
  unfold nativeAffineTorusPoint
  rw [← specGlobalUnit_natural]
  exact nativeTorusPoint_comp_left f _ _

end AlgebraicGeometry
