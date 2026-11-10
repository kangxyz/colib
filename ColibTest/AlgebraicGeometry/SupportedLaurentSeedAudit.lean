/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionBassSeed
import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionDiagramLaurent
import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetExact
import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetLaurent
import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetModel
import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetSeed
import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionLaurentUnit
import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionUnitHomotopy
import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionUnit
import Colib.RingTheory.KTheory.Bass.StrictUnderDiagram
import Colib.CategoryTheory.Functor.ArrowSquareWhiskering
import Lean

/-! Own public declarations, precise references and transitive native axiom closures. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[
    `Colib.CategoryTheory.Functor.ArrowSquareWhiskering,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionBassSeed,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionDiagramLaurent,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetExact,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetLaurent,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetModel,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetSeed,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionLaurentUnit,
    `Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionUnitHomotopy,
    `Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionUnit,
    `Colib.RingTheory.KTheory.Bass.StrictUnderDiagram]
  let bindings := (Colib.Library.bindings env).filter (fun b =>
    match env.getModuleIdxFor? b.declName with
    | none => false
    | some i => owners.contains env.header.moduleNames[i]!)
  unless bindings.size == 6 && bindings.all (·.id == "COL-0503") do
    throwError "Expected exactly six native COL-0503 bindings, got {bindings.size}"
  for owner in owners do
    unless env.header.moduleNames.contains owner do
      throwError "Explicit production owner not imported: {owner}"
    let mut count := 0
    for index in [:env.header.moduleNames.size] do
      if env.header.moduleNames[index]! == owner then
        for name in env.header.moduleData[index]!.constNames do
          unless isPrivateName name do count := count + 1
    unless count > 0 do
      throwError "Production owner has no audited public declarations: {owner}"
  let mut nativeNames : Array Name := #[]
  for index in [:env.header.moduleNames.size] do
    if owners.contains env.header.moduleNames[index]! then
      for name in env.header.moduleData[index]!.constNames do
        unless isPrivateName name do
          unless nativeNames.contains name do nativeNames := nativeNames.push name
  let mut names : Array (Name × Name) := #[]
  for name in nativeNames do
    let some idx := env.getModuleIdxFor? name | throwError "Missing owner {name}"
    names := names.push (name, env.header.moduleNames[idx]!)
  let extraAxioms : Array Json := #[]
  let citations := Colib.Library.citations env
  let mut rows := #[]
  let mut declarations := #[]
  let mut ownCitations := #[]
  for (name, owner) in names do
    let some info := env.find? name | throwError "Missing public declaration {name}"
    let some idx := env.getModuleIdxFor? name | throwError "Missing owner {name}"
    unless env.header.moduleNames[idx]! == owner do
      throwError "Wrong owner {name}"
    let ownRefs := citations.filter (fun c => c.declName == name)
    if bindings.any (fun b => b.declName == name) then
      unless ownRefs.any (fun c => c.source == "quillen" && c.locator.contains ':') do
        throwError "Missing own precise reference {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected transitive axiom {ax} in {name}"
    let type ← liftTermElabM (Meta.ppExpr info.type)
    declarations := declarations.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson owner.toString),
      ("type", toJson type.pretty),
      ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString))]
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("owner", toJson owner.toString),
      ("axioms", toJson (axioms.map Name.toString))]
    for c in ownRefs do
      ownCitations := ownCitations.push <| Json.mkObj [
        ("name", toJson name.toString), ("source", toJson c.source),
        ("locator", toJson c.locator), ("relation", toJson c.relation),
        ("scope", toJson c.scope)]
  let modules := owners
  let mut moduleRows := #[]
  for index in [:env.header.moduleNames.size] do
    let name := env.header.moduleNames[index]!
    if modules.contains name then
      moduleRows := moduleRows.push <| Json.mkObj [
        ("name", toJson name.toString),
        ("imports", toJson ((env.header.moduleData[index]!).imports.map
          (fun imported => imported.module.toString)))]
  IO.println <| (Json.mkObj [
    ("status", toJson "PASS_EXPLICIT_ELEVEN_OWNER_PUBLIC_AXIOM_CLOSURES_AND_EACH_TAG_REFERENCE"),
    ("axiom_audit", Json.arr rows), ("declarations", Json.arr declarations),
    ("native_public_names", toJson (nativeNames.map Name.toString)),
    ("extra_native_axioms", Json.arr extraAxioms),
    ("bindings", Json.arr (bindings.map fun b => Json.mkObj [
      ("id", toJson b.id), ("name", toJson b.declName.toString)])),
    ("citations", Json.arr ownCitations), ("stacks", Json.arr #[]),
    ("modules", Json.arr moduleRows)]).compress
