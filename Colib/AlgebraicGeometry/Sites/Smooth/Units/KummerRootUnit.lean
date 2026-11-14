/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Units.KummerRootCover

/-! # The actual root unit on the smooth étale root cover -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.Kummer

/-- The adjoined root, with the unit structure supplied by its power equation. -/
def rootUnit {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ) (n : ℕ) (hn : n ≠ 0) :
    (rootAlgebra v n)ˣ :=
  (Stacks.Kummer.isUnit_root_unit hn v).unit

/-- Its power equals the original unit in the root algebra. -/
theorem rootUnit_pow {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ) (n : ℕ) (hn : n ≠ 0) :
    (rootUnit v n hn : rootAlgebra v n) ^ n =
      algebraMap Γ(T, ⊤) (rootAlgebra v n) (v : Γ(T, ⊤)) := by
  rw [rootUnit, IsUnit.unit_spec, Stacks.Kummer.root_pow_eq_unit]

/-- The root as an actual global unit on the affine spectrum. -/
def rootOnSpec {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ) (n : ℕ) (hn : n ≠ 0) :
    Γ(Spec (.of (rootAlgebra v n)), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (.of (rootAlgebra v n))).inv.hom.toMonoidHom
    (rootUnit v n hn)

/-- The root unit on the original nonaffine pullback cover. -/
def rootOnCover {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ) (n : ℕ) (hn : n ≠ 0) :
    Γ(rootScheme v n, ⊤)ˣ :=
  Units.map (pullback.fst (rootSpecMap v n) (globalSpecMap T)).appTop.hom.toMonoidHom
    (rootOnSpec v n hn)

/-- The canonical global-spectrum map returns the original global section. -/
theorem globalSpecMap_appTop (T : Scheme.{u}) (x : Γ(T, ⊤)) :
    (globalSpecMap T).appTop.hom ((Scheme.ΓSpecIso (Γ(T, ⊤))).inv x) = x := by
  change T.toSpecΓ.appTop.hom ((Scheme.ΓSpecIso Γ(T, ⊤)).inv x) = x
  rw [Scheme.toSpecΓ_appTop]
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(T, ⊤)) x

/-- The root equation after transport to global sections of the affine spectrum. -/
theorem rootOnSpec_pow {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ) (n : ℕ) (hn : n ≠ 0) :
    rootOnSpec v n hn ^ n =
      Units.map (rootSpecMap v n).appTop.hom.toMonoidHom
        (Units.map (Scheme.ΓSpecIso (Γ(T, ⊤))).inv.hom.toMonoidHom v) := by
  have hp : rootUnit v n hn ^ n =
      Units.map (algebraMap Γ(T, ⊤) (rootAlgebra v n)).toMonoidHom v := by
    apply Units.ext
    exact rootUnit_pow v n hn
  let F := Units.map (Scheme.ΓSpecIso (.of (rootAlgebra v n))).inv.hom.toMonoidHom
  have h := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (rootAlgebra v n)))
  have hv := congrArg (fun f => Units.map f.hom.toMonoidHom v) h
  calc
    rootOnSpec v n hn ^ n = F (rootUnit v n hn ^ n) :=
      (map_pow F (rootUnit v n hn) n).symm
    _ = F (Units.map (algebraMap Γ(T, ⊤) (rootAlgebra v n)).toMonoidHom v) :=
      congrArg F hp
    _ = _ := hv

/-- The covering root has power exactly the restriction of the original unit. -/
theorem rootOnCover_pow {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ) (n : ℕ) (hn : n ≠ 0) :
    rootOnCover v n hn ^ n = Units.map (rootProjection v n).appTop.hom.toMonoidHom v := by
  let F := Units.map
    (pullback.fst (rootSpecMap v n) (globalSpecMap T)).appTop.hom.toMonoidHom
  let w := Units.map (Scheme.ΓSpecIso Γ(T, ⊤)).inv.hom.toMonoidHom v
  have hc := congrArg (fun f => Units.map f.appTop.hom.toMonoidHom w)
    (pullback.condition (f := rootSpecMap v n) (g := globalSpecMap T))
  have hg : Units.map (globalSpecMap T).appTop.hom.toMonoidHom w = v := by
    apply Units.ext
    exact globalSpecMap_appTop T (v : Γ(T, ⊤))
  calc
    rootOnCover v n hn ^ n = F (rootOnSpec v n hn ^ n) :=
      (map_pow F (rootOnSpec v n hn) n).symm
    _ = F (Units.map (rootSpecMap v n).appTop.hom.toMonoidHom w) :=
      congrArg F (rootOnSpec_pow v n hn)
    _ = Units.map (rootProjection v n).appTop.hom.toMonoidHom
        (Units.map (globalSpecMap T).appTop.hom.toMonoidHom w) := hc
    _ = _ := congrArg (Units.map (rootProjection v n).appTop.hom.toMonoidHom) hg

end AlgebraicGeometry.Scheme.SmoothSite.Kummer
