module

public import Colib.Topology.DoubleMappingCylinder.ComparisonDescent

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory TopCat.DoubleCylinder
open scoped Topology unitInterval
universe u

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
variable {Y : Type u} [TopologicalSpace Y]

example (t : unitInterval) (a : A) : endpointHomotopy f g sq (t, a) = l (a, ULift.up t) :=
  endpointHomotopy_apply f g sq t a

example (h₀ : C(B, Y)) (h₁ : C(C, Y)) (H : (h₀.comp f.hom).Homotopy (h₁.comp g.hom))
    (t : unitInterval) (a : A) :
    homotopyDesc f g sq h₀ h₁ H (l (a, ULift.up t)) = H (t, a) :=
  homotopyDesc_apply_cylinder f g sq h₀ h₁ H t a

noncomputable example (I : ContinuousMap.HomotopyEquiv B D) (J : ContinuousMap.HomotopyEquiv C D)
    (hI : I.toFun = gapLeftEndpoint e) (hJ : J.toFun = gapRightEndpoint e) :
    ((I.trans J.symm).toFun.comp f.hom).Homotopy g.hom :=
  comparisonUnderSourceOfLegEquivs f g sq I J hI hJ

noncomputable example {l₀ : A ⊗ TopCat.I ⟶ D} {e₀ : TopCat.of (B ⊕ B) ⟶ D}
    (sq₀ : IsPushout (TopCat.intervalEndpoints A) (endMap f f) l₀ e₀)
    (I : ContinuousMap.HomotopyEquiv B D) (hI : I.toFun = gapLeftEndpoint e₀)
    (v : C(A, Y)) (h₀ h₁ : C(B, Y))
    (H₀ : (h₀.comp f.hom).Homotopy v) (H₁ : (h₁.comp f.hom).Homotopy v) :
    h₀.Homotopy h₁ :=
  homotopyCancelOfLeftLegEquiv f sq₀ I hI h₀ h₁ (H₀.trans H₁.symm)

#print axioms comparisonUnderSourceOfLegEquivs
#print axioms homotopyCancelOfLeftLegEquiv
