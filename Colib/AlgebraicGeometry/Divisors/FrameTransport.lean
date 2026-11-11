/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafPullbackComap
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.GlobalSections

/-!
# Exact ideal and canonical-section transport along a Cartier pullback

The ideal comparison is the native inclusion-compatible comparison. Its being an
isomorphism uses that both the original and the inverse-image ideals are Cartier.
It does not identify an extended ideal with tensor pullback without this argument.
The divisor comparison uses the pinned native canonical-section-preserving map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (D : Y.IdealSheafData)
  (E : X.IdealSheafData) (h : D.comap f = E)
  [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]

/-- The actual ideal-sheaf transport through an equality of inverse-image ideals. -/
def idealComapEqIso :
    (Stacks.RingedSpace.pullbackFunctor f.toLRSHom.toShHom).obj (Eta.idealSheaf D) ≅
      Eta.idealSheaf E := by
  have hD : IsPullbackDefined f D := by
    change IsEffectiveCartierDivisor (D.comap f)
    rw [h]
    infer_instance
  exact pullbackIdealSheafComapIso f D hD ≪≫ eqToIso (congrArg Eta.idealSheaf h)

/-- The transported ideal comparison preserves its actual inclusion into the structure sheaf. -/
theorem idealComapEqIso_hom_inclusion :
    (idealComapEqIso f D E h).hom ≫ Eta.idealSheafι E =
      Stacks.IdealTorsion.Eta.pullbackIdealIncl f.toLRSHom.toShHom (Eta.idealSheaf D)
        (Eta.idealSheafι D) := by
  subst E
  exact pullbackIdealSheafComapIso_hom_comp_idealSheafι f D inferInstance

include h in
/-- Equality of Cartier inverse-image ideals gives an isomorphism preserving the actual
canonical global section. The equality transports both the sheaf and that section. -/
theorem exists_divisorComapEqIso :
    ∃ e : (Scheme.Modules.pullback f).obj (divisorSheaf D) ≅ divisorSheaf E,
      e.hom.app ⊤ (pullbackGlobalSections f (divisorSheaf D) (divisorSheafGlobalSection D)) =
        divisorSheafGlobalSection E := by
  subst E
  exact ⟨invertibleSheafPullbackIso f D,
    invertibleSheafPullbackIso_canonicalSection f D⟩

/-- The native divisor comparison with an identified Cartier inverse image. -/
def divisorComapEqIso :
    (Scheme.Modules.pullback f).obj (divisorSheaf D) ≅ divisorSheaf E :=
  (exists_divisorComapEqIso f D E h).choose

@[simp]
theorem divisorComapEqIso_canonicalSection :
    (divisorComapEqIso f D E h).hom.app ⊤
      (pullbackGlobalSections f (divisorSheaf D) (divisorSheafGlobalSection D)) =
        divisorSheafGlobalSection E :=
  (exists_divisorComapEqIso f D E h).choose_spec

end Stacks.Divisors

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}

/-- Pullback of a specified frame, including the structure-sheaf comparison. -/
def framePullback (e : L ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (pullback f).obj L ≅ SheafOfModules.unit X.ringCatSheaf :=
  (pullback f).mapIso e ≪≫ pullbackUnitIso f

/-- Pulling a frame back pulls its coordinate by the literal ring map on global sections. -/
theorem framePullback_coordinate (e : L ≅ SheafOfModules.unit Y.ringCatSheaf)
    (s : Γ(L, ⊤)) :
    (framePullback f e).hom.app ⊤ (pullbackGlobalSections f L s) =
      f.appTop (e.hom.app ⊤ s) := by
  change (pullbackUnitIso f).hom.app ⊤
    (((pullback f).map e.hom).app ⊤ (pullbackGlobalSections f L s)) = _
  exact (congrArg (fun t => (pullbackUnitIso f).hom.app ⊤ t)
    (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
      f e.hom s).symm).trans
    (AlgebraicGeometry.SectionsEqualizer.pullbackUnitIso_unit f (e.hom.app ⊤ s))

end AlgebraicGeometry.Scheme.Modules
