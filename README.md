# Design notes for `GaugeTheory/` in Physlib

Notes on the structure of the `Physlib/ClassicalFieldTheory/GaugeTheory/` library:
the symbolic framework for the local content of a gauge theory (jets of fields,
gauge and Lorentz actions, invariants of a given mass dimension) that models such as
the Standard Model plug into.

The notes are written for discussion first and, later, as the basis of a paper.
Comments are welcome as issues or pull requests here, or on the Zulip thread of
[physlib PR #1415](https://github.com/leanprover-community/physlib/pull/1415).

## Contents

| path | what it is |
| --- | --- |
| [`notes/GaugeTheory-design.tex`](notes/GaugeTheory-design.tex), [`.pdf`](notes/GaugeTheory-design.pdf) | The design of the five layers (gauge datum, fields, field data, the algebra, the covariant algebra), what a review of the code found, the route to the target theorem on the Standard Model card, the decisions for the thread and the plan. |
| [`prototypes/`](prototypes/) | Three Lean files that check proposals of the note: restriction of matter fields and the two conditions under every construction (`MatterFields.lean`), the evaluation law and the covariant reduction theorem for an arbitrary field datum (`Covariance.lean`), and morphisms of field data with the functoriality of the local field algebra (`Morphisms.lean`). A fourth, `CompactMatrixGroup.lean`, was written for the review of [physlib PR #2061](https://github.com/leanprover-community/physlib/pull/2061) and uses Mathlib only: for a closed subgroup of `U(κ)` the generators of one-parameter subgroups form a real subspace (the Lie product formula for unitary matrices), so the Lie algebra of a compact matrix group can be a definition instead of a field. None of them is part of Physlib. |
| [`tools/check_layers.py`](tools/check_layers.py) | The assignment of every gauge-theory file to a layer, and the list of imports that go from a lower layer to a higher one. |

### Running the prototypes

The first three were compiled against the branch of physlib PR #2011 (commit `800e1cf6`, Lean v4.35.0).
From a checkout of that branch with the gauge-theory modules built:

```sh
lake build PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalCovField.Basic \
  PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalField.MassWeight \
  PhyslibAlpha.Particles.StandardModel.Basic
lake env lean /path/to/prototypes/Covariance.lean   # likewise MatterFields.lean, Morphisms.lean
```

`CompactMatrixGroup.lean` imports only Mathlib (v4.35.0, the revision physlib pins), so from
any physlib checkout `lake env lean /path/to/prototypes/CompactMatrixGroup.lean` is enough.

Each file ends with `#print axioms` for its main results; no `sorry` appears.

### Checking the layers

```sh
python3 tools/check_layers.py /path/to/physlib             # the tree as it is
python3 tools/check_layers.py /path/to/physlib --narrowed  # with the checked import fixes
```

## Building

The notes use `fontspec` and need a Unicode-aware engine. With
[tectonic](https://tectonic-typesetting.github.io/):

```sh
make            # builds every notes/*.tex into notes/*.pdf
```

or `tectonic notes/GaugeTheory-design.tex` directly. XeLaTeX or LuaLaTeX also
work. The PDFs are committed so that nothing has to be built to read them. If GitHub's preview does not display one, use the raw file: [GaugeTheory-design.pdf](https://github.com/doxtor6/physlib-gaugetheory-design/raw/main/notes/GaugeTheory-design.pdf).

## License

The text is released under [CC BY 4.0](LICENSE).
