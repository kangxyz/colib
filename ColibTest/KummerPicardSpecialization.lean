module

import Colib.AlgebraicGeometry.EtaleCohomology.KummerPicardSpecialization

open CategoryTheory AlgebraicGeometry
open Stacks.Kummer Stacks.EtaleCohomology

universe w v u

-- The quotient injection needs no Brauer-group vanishing and has independent universes.
example (X : Scheme.{u}) {n : ℕ} (hn0 : n ≠ 0)
    (hX : IsUnit ((n : ℕ) : Γ(X, ⊤)))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    Function.Injective (picardQuotientKummerMap.{w, v, u} X hn0 hX) :=
  injective_picardQuotientKummerMap X hn0 hX

-- Naturality uses the literal scheme pullback of Picard classes.
example {X Y : Scheme.{u}} (π : X ⟶ Y) {n : ℕ} (hn0 : n ≠ 0)
    (hY : IsUnit ((n : ℕ) : Γ(Y, ⊤)))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (L : Stacks.Picard.ofScheme Y) :
    rootsOfUnityPullbackMap.{u, v, w} π n 2 (picardKummerClass.{w, v, u} Y hn0 hY L) =
      picardKummerClass.{w, v, u} X hn0 (isUnit_natCast_of_hom π hY)
        (Stacks.Picard.schemePullbackClassHom π L) :=
  picardKummerClass_naturality π hn0 hY L

attribute [local instance 2000] hasExt_sheaf_smallEtale_succ

variable (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]

-- Arbitrary proper schemes, not only smooth curves; composite exponents are permitted.
example (hX : IsUnit ((6 : ℕ) : Γ(X, ⊤))) (L : Stacks.Picard.ofScheme X) :
    (∃ M, 6 • M = L) ↔
      ∃ M, 6 • M = Stacks.Picard.schemePullbackClassHom (closedFibreInclusion R f) L :=
  picard_nsmul_exists_iff_closedFibre R f (by decide) hX L

-- Exponent one is covered by exactly the same public theorem.
example (L : Stacks.Picard.ofScheme X) :
    (∃ M, 1 • M = L) ↔
      ∃ M, 1 • M = Stacks.Picard.schemePullbackClassHom (closedFibreInclusion R f) L :=
  picard_nsmul_exists_iff_closedFibre R f (by decide) (by simp) L

-- The consequence returns a module and a tensor-power isomorphism, not only a Picard class.
example {n : ℕ} (hn0 : n ≠ 0) (hX : IsUnit ((n : ℕ) : Γ(X, ⊤)))
    (L : X.Modules) (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (M₀ : (closedFibre R f).Modules)
    (hM₀ : Stacks.SheafOfModules.IsInvertible (closedFibre R f).presheaf
      (closedFibre R f).ringCatIsSheaf M₀)
    (e₀ : Stacks.SheafOfModules.schemeTensorPower (closedFibre R f) M₀ hM₀ (n : ℤ) ≅
      (Scheme.Modules.pullback (closedFibreInclusion R f)).obj L) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅ L) :=
  exists_schemeTensorPower_iso_of_closedFibre R f hn0 hX L hL M₀ hM₀ e₀
