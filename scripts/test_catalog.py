"""Regression tests for Library ownership, permanent IDs and compiled reference integrity."""

from pathlib import Path
import shutil
import json
import importlib.util
import subprocess
import sys
import tempfile
import unittest

import catalog
import lint_style


class LibraryTests(unittest.TestCase):
    def assert_test_in_checks(self, module, check_path):
        self.assertIn(module, lint_style.source_modules(catalog.ROOT, "ColibTest"))
        self.assertIn("python3 scripts/lint_style.py", (catalog.ROOT / check_path).read_text())

    def setUp(self):
        self.library = catalog.load_library()
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        shutil.copytree(catalog.ROOT / "docs/library", self.root / "docs/library")
        shutil.copyfile(
            catalog.ROOT / "docs/references.toml", self.root / "docs/references.toml"
        )

    def test_completion_milestone_native_scope_and_ci(self):
        root = catalog.ROOT
        ledger = json.loads((root / "docs/migration/milnor-completion.json").read_text())
        self.assertEqual(ledger["library_item"], "COL-0168")
        self.assertEqual(ledger["source_file"],
                         "Aglib/KTheory/MilnorK/Residue/AdicCompletion.lean")
        source = (root / "Colib/RingTheory/KTheory/MilnorK/Residue/Completion.lean").read_text()
        for declaration in ledger["source_declarations"].values():
            self.assertIn(declaration.removeprefix("Stacks.Chow."), source)
        self.assertIn("IsFractionRing.lift", source)
        self.assertIn("AdicCompletion.residueField_map_bijective", source)
        self.assertIn("dvrMilnorTameSymbol'_completion_eq_zero_iff", source)
        self.assertIn('colib_tag "COL-0168"', source)
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assert_test_in_checks("ColibTest.MilnorCompletion", path)
        self.assertIn("Colib.RingTheory.KTheory.MilnorK.Residue.Completion",
                      (root / "Colib.lean").read_text())

    def test_import_all_keeps_native_dependency_boundary(self):
        source = self.root / "Colib" / "NativeImport.lean"
        source.parent.mkdir()
        for prefix in ("import", "public import", "meta import", "public meta import"):
            with self.subTest(prefix=prefix):
                source.write_text(f"module\n{prefix} all Mathlib.LinearAlgebra.TensorAlgebra.Basic\n")
                catalog.check_sources(self.root)

    def test_import_all_rejects_external_dependency(self):
        source = self.root / "Colib" / "ExternalImport.lean"
        source.parent.mkdir()
        for prefix in ("import", "public import", "meta import", "public meta import"):
            with self.subTest(prefix=prefix):
                source.write_text(f"module\n{prefix} all External.Module\n")
                with self.assertRaisesRegex(ValueError, "outside the dependency boundary"):
                    catalog.check_sources(self.root)

    def test_independent_milestone_ids_keep_their_owners(self):
        expected = {
            "COL-0263": "milnor-k-theory",
            "COL-0264": "milnor-k-theory",
            "COL-0265": "koszul-coefficients",
            "COL-0266": "derived-hom-comparisons",
        }
        for identifier, section in expected.items():
            self.assertEqual(self.library["entries"][identifier]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in expected:
            self.assertTrue(result["entries"][identifier]["references"])

    def test_principal_euler_complete_chain_registration(self):
        root = catalog.ROOT
        leaves = ("Basic", "Additivity", "Support", "Filtration", "Associativity")
        for number, leaf in zip(range(169, 174), leaves):
            identifier = f"COL-{number:04d}"
            self.assertEqual(self.library["entries"][identifier]["section"], "principal-euler")
            module = f"Colib.RingTheory.Multiplicity.PrincipalEuler.{leaf}"
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assert_test_in_checks("ColibTest.PrincipalEuler", path)
        source = (root / "Colib/RingTheory/Multiplicity/PrincipalEuler/Associativity.lean").read_text()
        self.assertIn("principalEuler_quotient_closedPoint_eq_zero", source)
        self.assertIn("principalCokernel_associativity", source)

    def test_finite_algebra_local_length_registration(self):
        root = catalog.ROOT
        for identifier, leaf in (("COL-0180", "FiniteAlgebraFiber"),
                                 ("COL-0181", "FiniteAlgebraLocal")):
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "finite-algebra-coefficients")
            module = f"Colib.RingTheory.Length.{leaf}"
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assert_test_in_checks("ColibTest.FiniteAlgebraLocal", path)
        self.assertIn("specialization", self.library["entries"]["COL-0181"]["scope"])

    def test_finite_algebra_norm_chain_registration(self):
        root = catalog.ROOT
        modules = {"COL-0182": "Colib.LinearAlgebra.Determinant.FiniteLength",
                   "COL-0183": "Colib.RingTheory.Norm.FiniteAlgebra",
                   "COL-0184": "Colib.RingTheory.Norm.PolynomialFiber"}
        for identifier, module in modules.items():
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "finite-algebra-coefficients")
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assert_test_in_checks("ColibTest.FiniteAlgebraNorm", path)

    def test_completion_branches_chain_registration(self):
        root = catalog.ROOT
        leaves = ("FiniteAlgebra", "ChineseRemainder", "SemilocalBranches",
                  "DedekindBranches", "FiniteDedekindBranches")
        for number, leaf in zip(range(185, 190), leaves):
            identifier = f"COL-{number:04d}"
            self.assertEqual(self.library["entries"][identifier]["section"], "adic-completion")
            module = f"Colib.RingTheory.AdicCompletion.{leaf}"
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assert_test_in_checks("ColibTest.CompletionBranches", path)

    def test_fraction_residue_chain_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0190": "Colib.RingTheory.Localization.FiniteProductBaseChange",
            "COL-0191": "Colib.RingTheory.AdicCompletion.BranchFraction",
            "COL-0192": "Colib.RingTheory.AdicCompletion.FractionBranches",
            "COL-0193": "Colib.RingTheory.Norm.DVRResidue",
            "COL-0194": "Colib.RingTheory.Norm.DVRResidue",
        }
        for identifier, module in modules.items():
            section = ("adic-completion" if identifier < "COL-0193"
                       else "finite-algebra-coefficients")
            self.assertEqual(self.library["entries"][identifier]["section"], section)
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for module in ("ColibTest.FractionBranches", "ColibTest.DVRResidueNorm"):
                self.assert_test_in_checks(module, path)

    def test_uniformizer_norm_complete_chain_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0195": "Colib.RingTheory.Henselian.UniformizerNormalization",
            "COL-0196": "Colib.RingTheory.DiscreteValuationRing.RamificationDegree",
            "COL-0197": "Colib.RingTheory.Norm.UniformizerBinomial",
            "COL-0198": "Colib.RingTheory.Norm.DVRUniformizer",
            "COL-0199": "Colib.RingTheory.Norm.DVRPrimeUniformizer",
        }
        for identifier, module in modules.items():
            section = ("henselian-ramification" if identifier < "COL-0197"
                       else "finite-algebra-coefficients")
            self.assertEqual(self.library["entries"][identifier]["section"], section)
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for test in ("HenselianPrincipalRoots", "HenselianUniformizerNormalization",
                         "DVRRamificationDegree", "DVRUniformizerBinomial",
                         "DVRUniformizerNorm", "DVRPrimeUniformizerNorm"):
                self.assert_test_in_checks("ColibTest." + test, path)
        self.assertIn("ordinary norm-order", self.library["entries"]["COL-0199"]["scope"])

    def test_native_dvr_norm_order_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0200": "Colib.RingTheory.DiscreteValuationRing.FractionOrder",
            "COL-0201": "Colib.RingTheory.Norm.DVROrder",
        }
        for identifier, module in modules.items():
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for test in ("DVRFractionOrder", "DVRNormOrder"):
                self.assert_test_in_checks("ColibTest." + test, path)
        source = (root / "Colib/RingTheory/Norm/DVROrder.lean").read_text()
        self.assertIn("theorem neg_log_valuation_norm", source)
        self.assertIn("theorem dvrFracOrd_norm_mk0", source)
        self.assertNotIn("[PerfectField", source)
        self.assertNotIn("[HenselianLocalRing", source)

    def test_charpoly_branch_complete_chain_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0202": "Colib.RingTheory.Charpoly.Basic",
            "COL-0203": "Colib.RingTheory.Charpoly.TensorProduct",
            "COL-0204": "Colib.RingTheory.Charpoly.DVRResidue",
            "COL-0205": "Colib.RingTheory.Charpoly.IntegralTensorProduct",
            "COL-0206": "Colib.RingTheory.Polynomial.PowerFactorCount",
            "COL-0207": "Colib.RingTheory.Charpoly.DVRBranchCount",
        }
        for identifier, module in modules.items():
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "charpoly-branches")
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for module in (
                    "ColibTest.FieldCharpolyPower",
                    "ColibTest.TensorCharpolyProduct",
                    "ColibTest.DVRCharpolyResidue",
                    "ColibTest.IntegralTensorCharpolyProduct",
                    "ColibTest.PolynomialPowerFactorCount",
                    "ColibTest.DVRCharpolyBranchCount",
            ):
                self.assert_test_in_checks(module, path)
        self.assertIn("infinite base field", self.library["entries"]["COL-0202"]["scope"])
        self.assertIn("power basis", self.library["entries"]["COL-0204"]["scope"])
        self.assertIn("Characteristic-zero", self.library["entries"]["COL-0207"]["scope"])

    def test_sylow_branch_native_chain_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0208": "Colib.FieldTheory.SylowFixedField",
            "COL-0209": "Colib.FieldTheory.AdjoinRootSplitBranchEmbedding",
            "COL-0210": "Colib.FieldTheory.PGroupNormalSubfield",
            "COL-0211": "Colib.FieldTheory.PGroupNormalSubfieldEmbedding",
        }
        for identifier, module in modules.items():
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "sylow-field-reduction")
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
            self.assertNotIn("structure ", source)
            self.assertNotIn("def ", source)
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for module in (
                    "ColibTest.SylowFixedField",
                    "ColibTest.AdjoinRootSplitBranchEmbedding",
                    "ColibTest.PGroupNormalSubfield",
                    "ColibTest.PGroupNormalSubfieldEmbedding",
            ):
                self.assert_test_in_checks(module, path)
        self.assertIn("Zero polynomials", self.library["entries"]["COL-0208"]["scope"])
        self.assertIn("No monicity", self.library["entries"]["COL-0209"]["scope"])
        self.assertIn("original field", self.library["entries"]["COL-0211"]["scope"])

    def test_additivity_keeps_actual_maps_scope_and_tests(self):
        expected = {
            "COL-0213": "geometric-realization",
            "COL-0214": "homotopy-colimits",
            "COL-0215": "homotopy-colimits",
            "COL-0216": "geometric-realization",
            "COL-0217": "homotopy-groups",
            "COL-0218": "waldhausen-k-theory",
            "COL-0219": "waldhausen-k-theory",
            "COL-0220": "geometric-realization",
            "COL-0212": "waldhausen-k-theory",
        }
        for identifier, section in expected.items():
            self.assertEqual(self.library["entries"][identifier]["section"], section)
        self.assertIn("unreversed ordinal join", self.library["entries"]["COL-0216"]["scope"])
        self.assertIn("Infinite-dimensional", self.library["entries"]["COL-0216"]["scope"])
        self.assertIn("No comparison-equivalence or surjectivity assumption",
                      self.library["entries"]["COL-0219"]["scope"])
        self.assertIn("quotient-before-subobject", self.library["entries"]["COL-0219"]["scope"])
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in expected:
            self.assertTrue(result["entries"][identifier]["references"])
        ledger = json.loads((catalog.ROOT / "docs/migration/waldhausen/additivity.json").read_text())
        self.assertEqual(ledger["source_revision"], "c561118b7795eb9780be9ed391c3251d6a4d0afd")
        self.assertEqual(len(ledger["production_modules"]), 117)
        self.assertFalse((catalog.ROOT /
                          "Colib/CategoryTheory/Waldhausen/Additivity/NormalizeFunctor.lean").exists())
        self.assertIn("independent", self.library["entries"]["COL-0051"]["scope"])
        for test in ledger["tests"]:
            for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
                self.assert_test_in_checks(test, path)

    def test_ordinary_singular_topic_keeps_native_maps_and_scope(self):
        expected = {"COL-0347", "COL-0348", "COL-0349"}
        for identifier in expected:
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "algebraic-simplices")
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertTrue(expected.issubset(result["entries"]))
        root = catalog.ROOT
        ledger = json.loads((root / "docs/migration/motivic-ordinary-singular-a1.json")
                            .read_text())
        self.assertEqual(len(ledger["modules"]), 13)
        imports = (root / "Colib.lean").read_text()
        for item in ledger["modules"]:
            self.assertIn("public import " + item["module"], imports)
            self.assertTrue((root / item["path"]).is_file())
        endpoint = (root / "Colib/AlgebraicGeometry/Simplex/HomotopyInvariance.lean").read_text()
        self.assertIn("ordinaryIntervalHomotopyEquiv", endpoint)
        self.assertIn("ordinaryIntervalHomologyIso", endpoint)
        self.assertIn('colib_tag "COL-0349"', endpoint)
        self.assertIn("No homotopy-invariance or transfer assumption",
                      self.library["entries"]["COL-0349"]["scope"])

    def native_fixture(self):
        native = {
            "bindings": [],
            "citations": [],
            "stacks": [],
            "declarations": [],
            "modules": [],
        }
        module_names = {
            "finite-correspondences": "Colib.AlgebraicGeometry.Correspondences.Category",
            "transfers-nisnevich": "Colib.AlgebraicGeometry.SheavesWithTransfers.Sheafification",
            "sylow-field-reduction": "Colib.FieldTheory.PGroupNormalSubfieldEmbedding",
            "waldhausen-categories": "Colib.CategoryTheory.Waldhausen.Basic",
            "waldhausen-k-theory": "Colib.KTheory.Waldhausen.Basic",
            "bass-construction": "Colib.KTheory.Bass.StrictDiagram",
            "homology-colimits": "Colib.Algebra.Category.ModuleCat.FilteredColimits",
            "affine-open-pairs": "Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Functor",
            "perfect-complexes": "Colib.AlgebraicGeometry.Modules.PerfectWaldhausen",
            "ext-scalars": "Colib.Algebra.Homology.DerivedCategory.Ext.Quotient",
            "ext-products": "Colib.Algebra.Homology.DerivedCategory.Ext.Bifunctor",
            "nisnevich-sites": "Colib.AlgebraicGeometry.Sites.Nisnevich.Basic",
            "algebraic-simplices": "Colib.RingTheory.AlgebraicSimplex.Basic",
            "projective-dimension": "Colib.RingTheory.Koszul.Ext",
            "koszul-coefficients": "Colib.RingTheory.Koszul.Coefficients",
            "derived-hom-comparisons": "Colib.Algebra.Homology.DerivedCategory.Ext.RightDerived",
            "exact-categories": "Colib.CategoryTheory.ExactCategory.Basic",
            "bicategories": "Colib.CategoryTheory.Bicategory.IsoQuotient",
            "restricted-spans": "Colib.CategoryTheory.QConstruction.Basic",
            "classifying-spaces": "Colib.Topology.ClassifyingSpace.Basic",
            "functor-constructions": "Colib.CategoryTheory.Functor.Rebase",
            "geometric-realization": "Colib.Analysis.Convex.StdSimplex.PathHomotopy",
            "homotopy-groups": "Colib.Topology.Homotopy.HomotopyGroup.Map",
            "homotopy-colimits": "Colib.Topology.Pushout.HomotopyEquivalence",
            "quillen-k-theory": "Colib.KTheory.Quillen.Basic",
            "grothendieck-groups": "Colib.KTheory.GrothendieckGroup.Basic",
            "k-zero-of-fields": "Colib.RingTheory.KTheory.GrothendieckGroup.Field",
            "quillen-k-theory-of-rings": "Colib.RingTheory.KTheory.Quillen.Field.FiniteFieldKTwo",
            "g-theory-of-rings": "Colib.RingTheory.KTheory.GTheory.FiniteModules.Localization",
            "k-theory-of-schemes": "Colib.AlgebraicGeometry.KTheory.PerfectRestriction",
            "milnor-k-theory": "Colib.RingTheory.KTheory.MilnorK.DegreeTwo",
            "adic-completion": "Colib.RingTheory.AdicCompletion.FiniteAlgebra",
            "principal-euler": "Colib.RingTheory.Multiplicity.PrincipalEuler.Basic",
            "charpoly-branches": "Colib.RingTheory.Charpoly.DVRBranchCount",
            "henselian-ramification": "Colib.RingTheory.Henselian.UniformizerNormalization",
            "finite-algebra-coefficients": "Colib.RingTheory.Length.FiniteAlgebra",
        }
        item_modules = {
            "COL-0058": "Colib.Topology.ClassifyingSpace.NerveHomotopy",
            "COL-0098": "Colib.Analysis.Convex.StdSimplex.BoundaryRetraction",
        }
        native["modules"] = [
            {"name": name, "imports": []}
            for name in sorted(set(module_names.values()) | set(item_modules.values()))
        ]
        for identifier, entry in self.library["entries"].items():
            name = entry.get("primary", "CategoryTheory.example_" + identifier.removeprefix("COL-"))
            native["bindings"].append({"name": name, "id": identifier})
            native["declarations"].append(
                {
                    "name": name,
                    "type": "Prop",
                    "module": item_modules.get(identifier, module_names[
                        self.library["entries"][identifier]["section"]
                    ]),
                    "dependencies": [],
                }
            )
            native["citations"].append(
                {
                    "name": name,
                    "source": "stacks",
                    "locator": "fixture",
                    "relation": "comparison",
                    "scope": "Metadata-validation fixture",
                }
            )
        return native

    def test_exact_equivalence_keeps_canonical_maps(self):
        item = self.library["entries"]["COL-0179"]
        self.assertEqual(item["section"], "waldhausen-k-theory")
        self.assertIn("canonical KMap", item["statement"])
        self.assertIn("strict chosen-zero preservation is not required", item["scope"])
        self.assertIn("No equality with archived named PerfectK", item["scope"])
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertTrue(result["entries"]["COL-0179"]["references"])

    def test_cor_transfer_reading_routes_keep_new_items(self):
        expected = {
            "finite-correspondences": ([374, *range(363, 368)], ["COL-0374", "COL-0366"]),
            "transfers-nisnevich": (range(368, 374), ["COL-0368", "COL-0370", "COL-0372"]),
        }
        for section_id, (numbers, starts) in expected.items():
            section = self.library["sections"][section_id]
            identifiers = [f"COL-{number:04d}" for number in numbers]
            self.assertEqual(section["entries"], identifiers)
            self.assertEqual([topic["start"] for topic in section["topics"]], starts)
            self.assertEqual(set(section["transitions"]), set(identifiers))
            for identifier in identifiers:
                item = self.library["entries"][identifier]
                self.assertTrue(item["primary"])

    def test_cor_transfer_section_renders_maps_and_scope(self):
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        output = self.render_site_fixture(built)
        cor = (output / "sections/finite-correspondences/index.html").read_text()
        transfers = (output / "sections/transfers-nisnevich/index.html").read_text()
        self.assertIn('id="cycles-and-composition"', cor)
        self.assertIn('id="category-and-graphs"', cor)
        self.assertIn('id="sheafification-and-comparison"', transfers)
        self.assertIn("Stacks.Chow.incidenceTorPairing_assoc", cor)
        self.assertIn("AlgebraicGeometry.PresheafWithTransfers.nisnevichSheafificationUnderlyingIso",
                      transfers)
        self.assertIn(r"\Gamma(p_1)\circ\beta-\Gamma(p_2)\circ\beta", transfers)
        self.assertIn(r"c_P\circ\eta_{RP}=R(\eta_P)", transfers)
        self.assertIn("one neighborhood at each specified source point", transfers)
        self.assertIn('<details class="scope-details"><summary>Scope and conventions</summary>',
                      transfers)
        self.assertEqual(cor.count('class="section-transition"'), 6)
        self.assertEqual(transfers.count('class="section-transition"'), 6)

    def test_perfect_waldhausen_chain_keeps_owners(self):
        self.assertEqual(self.library["entries"]["COL-0177"]["section"], "waldhausen-categories")
        self.assertEqual(self.library["entries"]["COL-0178"]["section"], "perfect-complexes")
        self.assertIn("every relevant pushout apex", self.library["entries"]["COL-0178"]["statement"])
        self.assertIn("No archived perfectness model", self.library["entries"]["COL-0178"]["scope"])
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0177", "COL-0178"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_perfect_local_comparison_is_retired(self):
        self.assertNotIn("COL-0176", self.library["entries"])
        self.assertEqual(self.library["retired"]["COL-0176"]["status"], "retired")
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertNotIn("COL-0176", result["entries"])
        self.assertIn("COL-0176", result["retired"])
        self.assertEqual(result["sections"]["perfect-complexes"]["modules"],
                         ["Colib.AlgebraicGeometry.Modules.PerfectWaldhausen"])

    def test_retired_id_cannot_be_reused(self):
        path = self.root / "docs/library/entries/algebraic-geometry/COL-0178.toml"
        path.write_text(path.read_text().replace('id = "COL-0178"', 'id = "COL-0176"'))
        with self.assertRaisesRegex(ValueError, "reused retired Library ID"):
            catalog.load_library(self.root)

    def test_retired_id_rejects_compiled_binding(self):
        native = self.native_fixture()
        native["bindings"].append({"id": "COL-0176", "name": native["declarations"][0]["name"]})
        with self.assertRaisesRegex(ValueError, "Unknown compiled Library binding"):
            catalog.compile_library(self.library, native, {}, "main")

    def test_retired_record_requires_safe_history(self):
        path = self.root / "docs/library/retired/COL-0176.toml"
        path.write_text(path.read_text().replace(
            'previous_path = "docs/library/entries/algebraic-geometry/COL-0176.toml"',
            'previous_path = "../../escape.toml"'))
        with self.assertRaisesRegex(ValueError, "previous Library path"):
            catalog.load_library(self.root)

    def render_site_fixture(self, built):
        spec = importlib.util.spec_from_file_location("colib_site", catalog.ROOT / "scripts/site.py")
        site = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(site)
        built["source_hashes"] = catalog.source_hashes()
        library_path = self.root / "library.json"
        library_path.write_text(json.dumps(built))
        output = self.root / "site"
        site.build(library_path, output)
        return output

    def test_retired_item_keeps_page_and_search_record(self):
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        output = self.render_site_fixture(built)
        page = (output / "tag/COL-0176/index.html").read_text()
        self.assertIn("Retired Library item", page)
        self.assertIn("5c0a7ab9c060b7482a3c49056bb9b3284fc47829", page)
        self.assertIn("COL-0178", page)
        records = json.loads((output / "search.json").read_text())
        retired = next(row for row in records if row.get("id") == "COL-0176")
        self.assertEqual(retired["kind"], "retired")
        self.assertEqual(retired["path"], "tag/COL-0176/")

    def test_site_preserves_navigation_rows_and_tex_source(self):
        native = self.native_fixture()
        name = next(b["name"] for b in native["bindings"] if b["id"] == "COL-0004")
        declaration = next(d for d in native["declarations"] if d["name"] == name)
        module = declaration["module"]
        source = catalog.ROOT / (module.replace(".", "/") + ".lean")
        line, code = next(
            (i, line) for i, line in enumerate(source.read_text().splitlines(), 1)
            if line.startswith("def fgModuleRankEquiv ")
        )
        declaration["source_range"] = [line, 0, line, len(code)]
        built = catalog.compile_library(self.library, native, {}, "main")
        item = built["entries"]["COL-0004"]
        item["statement"] = (
            r"Inline \(x < y\) and display \[\text{{revision}}\]. "
            "See [@stacks, Tag 02MU] and COL-0001. The code is `f <x>`."
            "\n\nA separate mathematical paragraph."
        )
        item["proof"] = "First proof paragraph.\n\nSecond proof paragraph."
        item["proof_kind"] = "proof"
        item["used_by"] = ["COL-0001"]
        item["formal_dependencies"] = ["COL-0001"]
        item["source_checked_on"] = "2026-11-05"
        section = built["sections"][item["section"]]
        section["transitions"] = {"COL-0004": r"Consider the case \(x < y\). See COL-0001."}
        output = self.render_site_fixture(built)
        page = (output / "tag/COL-0004/index.html").read_text()
        self.assertIn('href="../../chapters/k-theory-rings-schemes/">Algebraic K-Theory of Rings and Schemes</a>', page)
        self.assertIn(
            f'href="../../sections/{section["id"]}/" aria-current="location">'
            '<span class="nav-section-title">',
            page,
        )
        self.assertIn('aria-label="Chapter contents"', page)
        self.assertIn('data-tex="x &lt; y"', page)
        self.assertIn(r'data-tex="\text{{revision}}"', page)
        self.assertIn('href="https://stacks.math.columbia.edu/tag/02MU">Tag 02MU</a>', page)
        self.assertIn('href="../../tag/COL-0001/">COL-0001</a>', page)
        self.assertIn("<code>f &lt;x&gt;</code>", page)
        self.assertIn("<p>A separate mathematical paragraph.</p>", page)
        self.assertIn(
            '<section class="proof"><h3>Proof</h3><p>First proof paragraph.</p>'
            "<p>Second proof paragraph.</p></section>",
            page,
        )
        correspondence = '<div class="lean" aria-label="Lean declarations">'
        self.assertEqual(page.count(correspondence), 1)
        self.assertLess(page.index('<div class="statement">'), page.index(correspondence))
        self.assertLess(page.index(correspondence), page.index('<section class="proof">'))
        self.assertIn('<details class="source-code"><summary>Lean source</summary>', page)
        self.assertIn('<details class="relations"><summary>Referenced by</summary><p>', page)
        self.assertIn('<details class="relations"><summary>Direct Lean references</summary><p>', page)
        self.assertIn(f'Field.lean#L{line}"', page)
        self.assertIn(f'href="../../modules/{module}/#{name}"', page)
        self.assertIn("<code>def fgModuleRankEquiv ", page)
        self.assertIn("Source correspondence · author-checked · 2026-11-05", page)
        section_page = (output / "sections" / section["id"] / "index.html").read_text()
        self.assertIn(f'href="../../sections/{section["id"]}/" aria-current="page"', section_page)
        transition = '<div class="section-transition"><p>Consider the case'
        self.assertLess(section_page.index(transition), section_page.index('<article class="item" id="COL-0004">'))
        self.assertNotIn(transition, page)
        chapter_page = (output / "chapters/category-theory/index.html").read_text()
        self.assertIn('<nav class="chapter-contents"', chapter_page)
        self.assertNotIn('tag/COL-0015/', chapter_page)
        exact = (output / "sections/exact-categories/index.html").read_text()
        self.assertIn('<section class="topic" id="conflations-and-base-change">', exact)
        self.assertIn('id="quillen-q-category"', exact)
        self.assertLess(exact.index('id="COL-0234"'), exact.index('id="COL-0038"'))
        self.assertRegex(
            exact,
            r'(?s)</article><div class="section-transition">.*?</div><article class="item" id="COL-0073">',
        )
        self.assertIn('<details class="scope-details"><summary>Scope and conventions</summary>', exact)
        records = json.loads((output / "search.json").read_text())
        result = next(row for row in records if row.get("id") == item["id"])
        self.assertEqual(result["statement"], item["statement"])
        self.assertIn('href="../tag/COL-0001/"', result["statement_html"])

    def test_modules_tree_lists_colib_and_preserves_upstream_item_links(self):
        native = self.native_fixture()
        upstream = {
            "COL-0010": "Mathlib.RingTheory.LocalRing.Length",
            "COL-0001": "StacksCore.CategoryTheory.GrothendieckGroup.Basic",
            "COL-0005": "StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKTheory",
        }
        names = {binding["id"]: binding["name"] for binding in native["bindings"]}
        declarations = {row["name"]: row for row in native["declarations"]}
        for identifier, module in upstream.items():
            declarations[names[identifier]]["module"] = module
            native["modules"].append({"name": module, "imports": []})
        manifest = json.loads((catalog.ROOT / "lake-manifest.json").read_text())
        pins = {package["name"]: package for package in manifest["packages"]}
        built = catalog.compile_library(self.library, native, pins, "main")
        output = self.render_site_fixture(built)
        index = (output / "modules/index.html").read_text()
        self.assertIn('href="Colib.CategoryTheory.ExactCategory.Basic/"', index)
        for identifier, module in upstream.items():
            self.assertNotIn(f'href="{module}/"', index)
            page = (output / "tag" / identifier / "index.html").read_text()
            self.assertIn(f'href="../../modules/{module}/#{names[identifier]}"', page)
            detail = (output / "modules" / module / "index.html").read_text()
            self.assertIn(f'id="{names[identifier]}"', detail)

    def test_transition_requires_an_item_of_its_section(self):
        chapter = self.root / "docs/library/chapters/category-theory.toml"
        chapter.write_text(chapter.read_text() + '\nCOL-0015 = "A misplaced transition."\n')
        with self.assertRaisesRegex(ValueError, "must precede an item of the same section"):
            catalog.load_library(self.root)

    def test_prose_rejects_unresolved_links_and_unpaired_math(self):
        for text, message in (
            ("See [@Unknown].", "Unknown bibliography key"),
            ("See COL-9999.", "Unknown Library item"),
            ("See [@stacks, 02MU].", "Use Tag XXXX"),
            (r"Unclosed \(x", "closing delimiter"),
        ):
            with self.subTest(text=text):
                with self.assertRaisesRegex(ValueError, message):
                    catalog.check_prose(text, self.library, "fixture")
        catalog.check_prose(r"`[@Unknown]` and \(\text{COL-9999}\)", self.library, "fixture")

    def test_software_locators_link_each_span_at_the_recorded_commit(self):
        source = self.library["sources"]["aglib_principal_euler_pin"]
        locator = "Algebra/Homology/DerivedCategory/ExtRightDerived.lean:220-258,336-433"
        locations = catalog.reference_locations("aglib_principal_euler_pin", source, locator)
        base = source["url"].replace("/tree/", "/blob/") + "/Aglib/" + locator.split(":")[0]
        self.assertEqual([item["url"] for item in locations], [
            base + "#L220-L258",
            base + "#L336-L433",
        ])
        with self.assertRaisesRegex(ValueError, "Invalid line range"):
            catalog.reference_locations("aglib_principal_euler_pin", source, "Aglib/Test.lean:9-7")
        with self.assertRaisesRegex(ValueError, "Invalid line range"):
            catalog.reference_locations("aglib_principal_euler_pin", source, "Aglib/Test.lean:12-")

    def test_perfect_regressions_use_only_native_objects(self):
        root = catalog.ROOT
        for stem in ("LocalRepresentativeComparison", "LocalRepresentativeEquivalence"):
            self.assertFalse((root / "Colib/AlgebraicGeometry/Modules" / (stem + ".lean")).exists())
            self.assertNotIn(stem, (root / "Colib.lean").read_text())
        for stem in ("PerfectLocalComparison", "PerfectLocalEquivalence", "PerfectKEquivalence"):
            self.assertFalse((root / "ColibTest" / (stem + ".lean")).exists())
            self.assertNotIn("ColibTest." + stem, lint_style.source_modules(root, "ColibTest"))
        for stem in ("PerfectWaldhausen", "PerfectKTheory"):
            source = (root / "ColibTest" / (stem + ".lean")).read_text()
            self.assertIn("RingedSpace.perfectComplexesWaldhausen", source)
            self.assertNotIn("import all", source)
            self.assertNotIn("private def source", source)
            self.assert_test_in_checks("ColibTest." + stem, "scripts/check.sh")

    def test_waldhausen_homotopy_chain_keeps_model_and_owners(self):
        self.assertEqual(self.library["entries"]["COL-0154"]["section"], "waldhausen-categories")
        for number in range(155, 159):
            self.assertEqual(
                self.library["entries"][f"COL-{number:04d}"]["section"], "waldhausen-k-theory"
            )
        self.assertIn("unnormalized", self.library["entries"]["COL-0146"]["scope"])
        self.assertIn("strict chosen-zero", self.library["entries"]["COL-0154"]["scope"])
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for number in range(154, 159):
            self.assertTrue(result["entries"][f"COL-{number:04d}"]["references"])

    def test_three_route_chains_keep_grouped_owners(self):
        for identifier, section in (
            ("COL-0144", "waldhausen-categories"),
            ("COL-0145", "waldhausen-categories"),
            ("COL-0146", "waldhausen-categories"),
            ("COL-0147", "homology-colimits"),
            ("COL-0148", "homology-colimits"),
            ("COL-0149", "affine-open-pairs"),
        ):
            self.assertEqual(self.library["entries"][identifier]["section"], section)
        catalog.compile_library(self.library, self.native_fixture(), {}, "main")

    def test_nerve_cylinder_and_native_simplex_owners_survive_adapter_retirement(self):
        owners = {
            "COL-0058": ("classifying-spaces", "Colib.Topology.ClassifyingSpace.NerveHomotopy"),
            "COL-0082": ("geometric-realization", "Colib.Analysis.Convex.StdSimplex.PathHomotopy"),
            "COL-0098": ("geometric-realization",
                         "Colib.Analysis.Convex.StdSimplex.BoundaryRetraction"),
        }
        root = catalog.ROOT
        root_imports = (root / "Colib.lean").read_text()
        for identifier, (section, module) in owners.items():
            self.assertEqual(self.library["entries"][identifier]["section"], section)
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn("public import " + module, root_imports)
            if identifier != "COL-0058":
                self.assertIn("namespace Convexity.StdSimplex", source)
                self.assertIn("StdSimplex ℝ", source)
                self.assertNotIn("_root_.stdSimplex", source)

        self.assertNotIn("COL-0059", self.library["entries"])
        retired = self.library["retired"]["COL-0059"]
        self.assertEqual(retired["status"], "retired")
        self.assertEqual(retired["previous_path"], "docs/library/entries/topology/COL-0059.toml")
        self.assertEqual(retired["related_items"], ["COL-0082", "COL-0098"])
        self.assertFalse((root / retired["previous_path"]).exists())
        obsolete_module = "Colib.Topology.Realization.FiniteSimplexAdapter"
        self.assertFalse((root / (obsolete_module.replace(".", "/") + ".lean")).exists())
        self.assertNotIn(obsolete_module, root_imports)
        for path in (root / "Colib").rglob("*.lean"):
            source = path.read_text()
            self.assertNotIn(obsolete_module, source, str(path))
            self.assertNotIn('colib_tag "COL-0059"', source, str(path))

        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertEqual(
            result["sections"]["geometric-realization"]["modules"],
            sorted(owners[identifier][1] for identifier in ("COL-0082", "COL-0098")),
        )
        for identifier, (_, module) in owners.items():
            self.assertTrue(result["entries"][identifier]["references"])
            declarations = result["entries"][identifier]["declarations"]
            self.assertTrue(declarations)
            self.assertEqual({result["declarations"][name]["module"] for name in declarations},
                             {module})
        self.assertNotIn("COL-0059", result["entries"])
        self.assertIn("COL-0059", result["retired"])
        self.assertNotIn(obsolete_module, result["modules"])

        native = self.native_fixture()
        native["bindings"].append({"id": "COL-0059", "name": native["declarations"][0]["name"]})
        with self.assertRaisesRegex(ValueError, "Unknown compiled Library binding"):
            catalog.compile_library(self.library, native, {}, "main")
        entry = self.root / "docs/library/entries/topology/COL-0082.toml"
        entry.write_text(entry.read_text().replace('id = "COL-0082"', 'id = "COL-0059"'))
        with self.assertRaisesRegex(ValueError, "reused retired Library ID"):
            catalog.load_library(self.root)

    def test_realization_prerequisite_ids_keep_their_owners(self):
        for index in range(60, 65):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(60, 65):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_finite_prism_id_keeps_its_owner(self):
        self.assertEqual(
            self.library["entries"]["COL-0065"]["section"], "geometric-realization"
        )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertTrue(result["entries"]["COL-0065"]["references"])

    def test_realized_standard_prism_ids_keep_their_owners(self):
        for identifier in ("COL-0066", "COL-0067"):
            self.assertEqual(
                self.library["entries"][identifier]["section"], "geometric-realization"
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0066", "COL-0067"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_realization_bridge_ids_keep_their_owners(self):
        for index in range(68, 71):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(68, 71):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_based_invariance_and_kmap_composition_ids_keep_their_owners(self):
        for identifier, section in (
            ("COL-0071", "homotopy-groups"),
            ("COL-0072", "quillen-k-theory"),
        ):
            self.assertEqual(self.library["entries"][identifier]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0071", "COL-0072"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_split_kernel_and_q_object_class_ids_keep_their_owners(self):
        for index in range(73, 76):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"], "exact-categories"
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(73, 76):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_algebraic_q_groupoid_ids_keep_their_owners(self):
        for index in range(76, 81):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "exact-categories" if index < 78 else "grothendieck-groups",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(76, 81):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_object_loop_bridge_ids_keep_their_owners(self):
        for index in range(81, 87):
            section = (
                "geometric-realization" if index < 84 else
                "classifying-spaces" if index < 86 else "grothendieck-groups"
            )
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(81, 87):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_open_cover_and_sequential_colimit_ids_keep_their_owners(self):
        for index in range(87, 90):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"], "homotopy-groups"
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(87, 90):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_constant_realization_and_completion_ids_keep_their_owners(self):
        for index in range(90, 94):
            section = "geometric-realization" if index < 92 else "classifying-spaces"
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(90, 94):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_pushout_and_open_cover_full_ids_keep_their_owners(self):
        for index in range(94, 98):
            section = "functor-constructions" if index == 96 else "homotopy-groups"
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(94, 98):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_simplex_boundary_and_collar_ids_keep_their_owners(self):
        for index in range(98, 100):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(98, 100):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_simplex_charts_and_annulus_ids_keep_their_owners(self):
        for index in range(100, 102):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(100, 102):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_simplex_attachment_collar_ids_keep_their_owners(self):
        for index in range(102, 104):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(102, 104):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_attachment_cover_generation_fullness_ids_keep_their_owners(self):
        for index in range(104, 107):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(104, 107):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_boundary_endpoints_and_graph_anchors_ids_keep_their_owners(self):
        for index in range(107, 109):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(107, 109):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_initial_ids_keep_their_owners(self):
        self.assertTrue(
            {f"COL-{index:04d}" for index in range(1, 13)}
            <= self.library["entries"].keys()
        )
        self.assertEqual(
            self.library["entries"]["COL-0004"]["section"], "k-zero-of-fields"
        )

    def test_exact_foundations_and_k0_ids_keep_their_owners(self):
        for index in range(15, 18):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "exact-categories",
            )
        for index in range(18, 20):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "grothendieck-groups",
            )
        self.assertEqual(self.library["entries"]["COL-0020"]["section"], "k-zero-of-fields")
        native = self.native_fixture()
        result = catalog.compile_library(self.library, native, {}, "main")
        self.assertEqual(
            result["sections"]["exact-categories"]["modules"],
            ["Colib.CategoryTheory.ExactCategory.Basic"],
        )

    def test_exact_functor_and_subgroup_ids_keep_their_owners(self):
        self.assertEqual(
            self.library["entries"]["COL-0023"]["section"], "exact-categories"
        )
        for index in range(24, 27):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "grothendieck-groups",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(23, 27):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_serre_localization_ids_keep_their_owners(self):
        self.assertEqual(
            self.library["entries"]["COL-0027"]["section"], "exact-categories"
        )
        for index in (28, 29):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "grothendieck-groups",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(27, 30):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_admissible_pullback_ids_keep_their_owners(self):
        for index in (32, 33):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "exact-categories",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in (32, 33):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_quotient_and_restricted_span_ids_keep_their_owners(self):
        self.assertEqual(self.library["entries"]["COL-0034"]["section"], "bicategories")
        self.assertEqual(self.library["entries"]["COL-0035"]["section"], "restricted-spans")
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0034", "COL-0035"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_q_functoriality_ids_keep_their_owners(self):
        self.assertEqual(self.library["entries"]["COL-0036"]["section"], "restricted-spans")
        self.assertEqual(self.library["entries"]["COL-0037"]["section"], "exact-categories")
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0036", "COL-0037"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_q_connectedness_ids_keep_their_owners(self):
        for index in (38, 39, 40):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "exact-categories",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in (38, 39, 40):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_quillen_homotopy_ids_keep_their_owners(self):
        owners = {43: "classifying-spaces", 44: "restricted-spans", 45: "quillen-k-theory"}
        for index, section in owners.items():
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in owners:
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_q_core_ids_keep_their_owners(self):
        self.assertEqual(self.library["entries"]["COL-0046"]["section"], "restricted-spans")
        for index in range(47, 51):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"], "exact-categories"
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(46, 51):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_quillen_map_ids_keep_their_owners(self):
        owners = {
            51: "functor-constructions", 52: "homotopy-groups",
            53: "classifying-spaces", 54: "classifying-spaces", 55: "quillen-k-theory",
        }
        for index, section in owners.items():
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in owners:
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_normalized_q_ids_keep_their_owners(self):
        self.assertEqual(self.library["entries"]["COL-0056"]["section"], "functor-constructions")
        self.assertEqual(self.library["entries"]["COL-0057"]["section"], "exact-categories")
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0056", "COL-0057"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_unknown_reference_is_rejected(self):
        native = self.native_fixture()
        native["citations"][0]["source"] = "missing"
        with self.assertRaisesRegex(ValueError, "Unknown bibliographic key"):
            catalog.compile_library(self.library, native, {}, "main")

    def test_item_requires_a_compiled_binding(self):
        native = self.native_fixture()
        native["bindings"].pop()
        with self.assertRaisesRegex(ValueError, "needs a compiled"):
            catalog.compile_library(self.library, native, {}, "main")

    def test_multiple_literature_references_are_retained(self):
        native = self.native_fixture()
        extra = dict(
            native["citations"][0], source="WeibelKBook", locator="II, Definition 6.1.1"
        )
        native["citations"].append(extra)
        result = catalog.compile_library(self.library, native, {}, "main")
        identifier = native["bindings"][0]["id"]
        self.assertEqual(
            {ref["source"] for ref in result["entries"][identifier]["references"]},
            {"stacks", "WeibelKBook"},
        )

    def test_citation_does_not_require_a_permanent_item_tag(self):
        native = self.native_fixture()
        native["declarations"].append(
            {
                "name": "CategoryTheory.helper",
                "type": "Prop",
                "module": "Colib.RingTheory.KTheory.GrothendieckGroup.Field",
                "dependencies": [],
            }
        )
        native["citations"].append(
            {
                "name": "CategoryTheory.helper",
                "source": "WeibelKBook",
                "locator": "II, section 2",
                "relation": "ingredient",
                "scope": "Fixture",
            }
        )
        result = catalog.compile_library(self.library, native, {}, "main")
        self.assertTrue(
            any(ref["name"] == "CategoryTheory.helper" for ref in result["citations"])
        )
        self.assertFalse(
            any(
                "CategoryTheory.helper" in item["declarations"]
                for item in result["entries"].values()
            )
        )

    def test_duplicate_id_is_rejected(self):
        path = self.root / "docs/library/entries/k-theory/COL-0002.toml"
        path.write_text(path.read_text().replace('id = "COL-0002"', 'id = "COL-0001"'))
        with self.assertRaisesRegex(ValueError, "duplicate Library ID"):
            catalog.load_library(self.root)

    def test_hand_maintained_dependencies_are_rejected(self):
        path = self.root / "docs/library/entries/k-theory/COL-0001.toml"
        path.write_text(path.read_text() + 'requires = ["COL-0002"]\n')
        with self.assertRaisesRegex(ValueError, "dependencies come from Lean"):
            catalog.load_library(self.root)

    def test_hand_maintained_module_routes_are_rejected(self):
        path = self.root / "docs/library/chapters/k-theory.toml"
        path.write_text(path.read_text().replace(
            'id = "bass-construction"\n',
            'id = "bass-construction"\nmodules = ["Colib.KTheory"]\n',
            1,
        ))
        with self.assertRaisesRegex(ValueError, "Module ownership is exported"):
            catalog.load_library(self.root)

    def test_module_ownership_is_exported(self):
        native = self.native_fixture()
        result = catalog.compile_library(self.library, native, {}, "main")
        self.assertIn(
            "Colib.RingTheory.KTheory.GrothendieckGroup.Field",
            result["sections"]["k-zero-of-fields"]["modules"],
        )

    def test_declaration_lists_are_owned_by_lean(self):
        path = self.root / "docs/library/entries/k-theory/COL-0001.toml"
        path.write_text(
            path.read_text() + 'declarations = ["CategoryTheory.GrothendieckGroup"]\n'
        )
        with self.assertRaisesRegex(ValueError, "belong in Lean attributes"):
            catalog.load_library(self.root)

    def test_editorial_move_retains_the_lean_defining_module(self):
        shutil.copytree(catalog.ROOT / "Colib", self.root / "Colib")
        for name in (
            "Colib.lean",
            "lakefile.toml",
            "lake-manifest.json",
            "lean-toolchain",
        ):
            shutil.copyfile(catalog.ROOT / name, self.root / name)
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        built["source_hashes"] = catalog.source_hashes(self.root)
        directory = self.root / "build/library"
        directory.mkdir(parents=True)
        (directory / "library.json").write_text(json.dumps(built))
        entry = self.root / "docs/library/entries/k-theory-rings-schemes/COL-0004.toml"
        entry.write_text(
            entry.read_text().replace(
                'section = "k-zero-of-fields"', 'section = "milnor-k-theory"'
            )
        )
        scripts = self.root / "scripts"
        scripts.mkdir()
        for name in ("catalog.py", "library_text.py"):
            shutil.copyfile(catalog.ROOT / "scripts" / name, scripts / name)
        result = subprocess.run(
            [sys.executable, str(scripts / "catalog.py"), "show", "COL-0004"],
            check=True,
            capture_output=True,
            text=True,
        )
        item = json.loads(result.stdout)
        self.assertEqual(item["section"], "milnor-k-theory")
        self.assertEqual(item["modules"], ["Colib.RingTheory.KTheory.GrothendieckGroup.Field"])

    def test_unsafe_bibliographic_path_is_rejected(self):
        path = self.root / "docs/references.toml"
        path.write_text(path.read_text() + '\n[sources."../../escape"]\n')
        with self.assertRaisesRegex(ValueError, "Unsafe bibliographic key"):
            catalog.load_library(self.root)

    def test_unknown_source_provider_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "Unsupported catalog source"):
            catalog.source_link("OtherLibrary.Result", {}, "main")


if __name__ == "__main__":
    unittest.main()
