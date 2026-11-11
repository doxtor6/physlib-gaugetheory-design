#!/usr/bin/env python3
"""Assign every file of PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/ to a layer of the
design note and report the imports that go from a lower layer to a higher one.

    python3 tools/check_layers.py /path/to/physlib            # the tree as it is
    python3 tools/check_layers.py /path/to/physlib --narrowed # with the checked import fixes

The assignment is by content (design note, section 3). Files of PR #2011 are assigned too,
so the script runs on master and on the branch of that PR.
"""
import pathlib
import re
import sys

PRE = "PhyslibAlpha.ClassicalFieldTheory.GaugeTheory."
ROOT = "PhyslibAlpha/ClassicalFieldTheory/GaugeTheory"

INVARIANTS = {"LocalGaugeData.SU.GellMann", "LocalGaugeData.SU.Adjoint",
              "LocalGaugeData.SU.TensorSpecies"}
JET_TOOLKIT = {"LocalField.Jet", "LocalField.JetRep", "MatterField.RepCoeff"}
CONNECTION = {"GaugeBoson.Basic", "GaugeBoson.GaugeCoeff"}
MATTER = {"MatterField.InfinitesimalAction.Basic", "MatterField.Basic", "MatterField.Charge",
          "MatterField.TransformsIn", "MatterField.MatrixRep.Basic",
          "MatterField.MatrixRep.Constructions", "MatterField.MatrixRep.Factors",
          "MatterField.JetComponent.Basic", "MatterField.JetComponent.GaugeAction",
          "MatterField.JetComponent.TransformsIn", "MatterField.Prod", "MatterField.Pi"}
ALGEBRA_CONNECTION = {"GaugeBoson.LocalGauge.Basic", "GaugeBoson.LocalGauge.JetDeriv",
                      "GaugeBoson.LocalGauge.GaugeAction", "GaugeBoson.LocalGauge.LorentzAction",
                      "GaugeBoson.LocalGauge.GaugeField", "GaugeBoson.LocalGauge.MassDim",
                      "GaugeBoson.LocalGauge.MassWeightPoly", "GaugeBoson.Realization.Basic"}
ALGEBRA_THEORY = {"LocalField.Basic", "LocalField.GaugeAction", "LocalField.LorentzAction",
                  "LocalField.TransformsIn", "LocalField.MassWeight", "LocalField.Sector",
                  "LocalField.GaugeSector"}
ALGEBRA_REALIZATIONS = {"LocalField.Realization", "LocalField.SectorRealization",
                        "LocalField.GaugeSectorRealization", "GaugeBoson.LocalGauge.Realization"}
COVARIANT_MATTER = {"MatterField.CovariantDeriv", "MatterField.InfinitesimalAction",
                    "MatterField.LorentzCovariantDeriv"}

# Import fixes checked by compiling the file with the narrowed import (design note, section 3).
NARROWED = {
    "MatterField.MatrixRep.Basic":
        {"MatterField.InfinitesimalAction": "MatterField.InfinitesimalAction.Basic"},
    "MatterField.JetComponent.TransformsIn": {"MatterField.CovariantDeriv": None},
}


def layer(name):
    """The layer of a module, as (number, part)."""
    if name.startswith("LocalGaugeData.SU.Invariants") or name in INVARIANTS:
        return (6, "invariant theory")
    if name.startswith("LocalGaugeData."):
        return (1, "gauge datum")
    if name in JET_TOOLKIT:
        return (2, "fields: jet toolkit")
    if name in CONNECTION:
        return (2, "fields: connection")
    if name.startswith("Species."):
        return (2, "fields: species type of PR #2011 (dropped)")
    if name in MATTER:
        return (2, "fields: matter")
    if name == "MatterField.MatrixRep.Table" or name.startswith("GaugeFieldData."):
        return (3, "field data")
    if name in ALGEBRA_CONNECTION:
        return (4, "algebra: connection")
    if name in ALGEBRA_THEORY:
        return (4, "algebra: theory")
    if name in ALGEBRA_REALIZATIONS:
        return (4, "algebra: realizations")
    if (name.startswith("GaugeBoson.Realization.") or name.startswith("GaugeBoson.LocalGaugeCov.")
            or name == "GaugeBoson.LocalGauge.FieldStrength"):
        return (5, "covariant algebra: connection")
    if name in COVARIANT_MATTER:
        return (5, "covariant algebra: matter")
    if name == "LocalField.CovariantDeriv" or name.startswith("LocalCovField."):
        return (5, "covariant algebra: theory")
    return (99, "unassigned")


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    root = pathlib.Path(sys.argv[1])
    narrowed = "--narrowed" in sys.argv[2:]
    totals, upward, unassigned = {}, [], []
    for path in sorted((root / ROOT).rglob("*.lean")):
        name = str(path.relative_to(root / ROOT))[:-5].replace("/", ".")
        text = path.read_text()
        here = layer(name)
        if here[0] == 99:
            unassigned.append(name)
        files, lines = totals.get(here, (0, 0))
        totals[here] = (files + 1, lines + len(text.splitlines()))
        for imp in re.findall(r"^(?:public )?import (\S+)", text, flags=re.M):
            if not imp.startswith(PRE):
                continue
            imp = imp[len(PRE):]
            if narrowed and imp in NARROWED.get(name, {}):
                imp = NARROWED[name][imp]
                if imp is None:
                    continue
            there = layer(imp)
            if there[0] > here[0]:
                upward.append((name, here[0], imp, there[0]))
    for key in sorted(totals):
        print(f"layer {key[0]}  {key[1]:<46} {totals[key][0]:>3} files {totals[key][1]:>6} lines")
    print(f"\nupward imports{' (with the checked import fixes)' if narrowed else ''}:")
    for name, a, imp, b in upward:
        print(f"  {name} (layer {a}) imports {imp} (layer {b})")
    if not upward:
        print("  none")
    if unassigned:
        print("\nunassigned:", ", ".join(unassigned))


if __name__ == "__main__":
    main()
