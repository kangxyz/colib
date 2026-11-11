/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.EnoughPoints
public import Colib.CategoryTheory.Sites.Simplicial.RealizationChainInvariance
public import Colib.CategoryTheory.Sites.Simplicial.RepresentableHypercohomology
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseKInjectiveReplacement
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-!
# Cohomology representatives in the smooth Nisnevich homotopy category

Apply the actual K-injective resolution and Dold–Kan construction to a
complex of abelian sheaves. The smooth Nisnevich site of a quasi-separated scheme has enough points
in the coefficient universe. Maps from the localized freely pointed
representable compute the original derived Hom from its free sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf Opposite
open AlgebraicGeometry.Scheme Stacks.Cohomology.FreeYonedaUnivLE

universe d u

namespace AlgebraicGeometry.MotivicHomotopy

variable (S : Scheme.{u}) [QuasiSeparatedSpace S]

local notation "Cₛ" => SmoothSite S
local notation "Jₛ" => SmoothSite.nisnevichTopology S

local instance : HasSheafify Jₛ AddCommGrpCat.{u + 1} := by
  let : EssentiallySmall.{u + 1} Cₛ := inferInstance
  exact hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} Jₛ AddCommGrpCat.{u + 1}

local instance : IsGrothendieckAbelian.{u + 1} (Sheaf Jₛ AddCommGrpCat.{u + 1}) := by
  let : EssentiallySmall.{u + 1} Cₛ := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall Jₛ AddCommGrpCat.{u + 1}

/-- The stalkwise localization of pointed simplicial presheaves on the smooth Nisnevich site. -/
abbrev NisnevichHomotopyCategory := StalkwiseHomotopyCategory.{u + 1} Cₛ Jₛ

/-- The localization functor on the chosen pointed presheaves. -/
abbrev toNisnevichHomotopyCategory : PointedSimplicialPresheaf.{u + 1} Cₛ ⥤
    NisnevichHomotopyCategory S :=
  toStalkwiseHomotopyCategory Cₛ Jₛ

/-- Freely pointed smooth representables lifted to the coefficient universe. -/
abbrev liftedSmoothPointedYoneda : Cₛ ⥤ PointedSimplicialPresheaf.{u + 1} Cₛ :=
  PointedSimplicialPresheaf.yoneda Cₛ ⋙ uliftPointed.{u + 1, u} Cₛ

/-- The freely pointed smooth representable in the coefficient universe, after localization. -/
def pointedNisnevichYoneda : Cₛ ⥤ NisnevichHomotopyCategory S :=
  liftedSmoothPointedYoneda S ⋙ toNisnevichHomotopyCategory S

/-- The pointed Nisnevich representative built from the original coefficient complex. -/
def nisnevichCochainRepresentative (p : ℤ)
    (K : CochainComplex (Sheaf Jₛ AddCommGrpCat.{u + 1}) ℤ) :
    NisnevichHomotopyCategory S :=
  (toNisnevichHomotopyCategory S).obj ((pointedKInjectiveCochainRepresentative Cₛ Jₛ p).obj K)

variable [HasDerivedCategory.{d}
  (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

/-- Maps from a pointed presheaf compute its reduced Nisnevich hypercohomology. -/
def nisnevichCochainRepresentativeHomEquiv (p : ℤ)
    (K : CochainComplex (Sheaf Jₛ AddCommGrpCat.{u + 1}) ℤ)
    (X : PointedSimplicialPresheaf.{u + 1} Cₛ) :
    ((toNisnevichHomotopyCategory S).obj X ⟶ nisnevichCochainRepresentative S p K) ≃
      (reducedHypercohomology.{d} Cₛ Jₛ K p).obj (op X) :=
  stalkwiseKInjectiveReplacementHomEquiv Cₛ Jₛ
    pointedSimplicialSetChainsPreserveRealizationWeakEquivalences p K X

/-- On the freely pointed smooth representable the target is ordinary hypercohomology. -/
def nisnevichCochainRepresentativeYonedaHomEquiv
    (p : ℤ) (K : CochainComplex (Sheaf Jₛ AddCommGrpCat.{u + 1}) ℤ) (U : Cₛ) :
    ((pointedNisnevichYoneda S).obj U ⟶ nisnevichCochainRepresentative S p K) ≃
      (hypercohomologyPresheaf.{d, u + 1} Jₛ K p).obj (op U) :=
  (nisnevichCochainRepresentativeHomEquiv S p K ((liftedSmoothPointedYoneda S).obj U)).trans
    (((reducedHypercohomologyYonedaIso.{d, u + 1} Cₛ Jₛ K p).app
      (op U)).addCommGroupIsoToAddEquiv.toEquiv)

/-- The comparison takes precomposition by the original scheme map to its restriction map. -/
theorem nisnevichCochainRepresentativeYonedaHomEquiv_naturality
    (p : ℤ) (K : CochainComplex (Sheaf Jₛ AddCommGrpCat.{u + 1}) ℤ)
    {U V : Cₛ} (f : U ⟶ V)
    (a : (pointedNisnevichYoneda S).obj V ⟶ nisnevichCochainRepresentative S p K) :
    nisnevichCochainRepresentativeYonedaHomEquiv S p K U
        ((pointedNisnevichYoneda S).map f ≫ a) =
      (hypercohomologyPresheaf.{d, u + 1} Jₛ K p).map f.op
        (nisnevichCochainRepresentativeYonedaHomEquiv S p K V a) := by
  let e := reducedHypercohomologyYonedaIso.{d, u + 1} Cₛ Jₛ K p
  let Y := liftedSmoothPointedYoneda S
  let Q := toNisnevichHomotopyCategory S
  let R := (pointedKInjectiveCochainRepresentative Cₛ Jₛ p).obj K
  change Q.obj (Y.obj V) ⟶ Q.obj R at a
  let h := pointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{u + 1}
  let b := stalkwiseKInjectiveReplacementHomEquiv.{d, u + 1} Cₛ Jₛ h p K (Y.obj V) a
  change e.hom.app (op U)
      (stalkwiseKInjectiveReplacementHomEquiv.{d, u + 1} Cₛ Jₛ h p K (Y.obj U)
        (Q.map (Y.map f) ≫ a)) =
    (hypercohomologyPresheaf.{d, u + 1} Jₛ K p).map f.op (e.hom.app (op V) b)
  calc
    _ = e.hom.app (op U) ((reducedHypercohomology.{d} Cₛ Jₛ K p).map (Y.map f).op b) :=
      congrArg (fun x => e.hom.app (op U) x)
        (stalkwiseKInjectiveReplacementHomEquiv_naturality Cₛ Jₛ h p K (Y.map f) a)
    _ = _ := by
      let F := reducedHypercohomology.{d} Cₛ Jₛ K p
      change e.hom.app (op U) (((Y.op ⋙ F).map f.op) b) = _
      simpa only [ConcreteCategory.comp_apply] using
        ConcreteCategory.congr_hom (e.hom.naturality f.op) b

end AlgebraicGeometry.MotivicHomotopy
