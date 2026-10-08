# Project Reflexive — Talagrand Lean Verifications

This repository collects Lean formalizations and verification artifacts for Talagrand-related theorems and conjectures. Each result lives in an independent project directory with its sources, dependency pins, mathematical scope, and verification records.

## Projects

### Kahn–Kalai conjecture

The complete project is in **[Kahn-Kalai/](Kahn-Kalai/)**.

- [Project README and exact scope](Kahn-Kalai/README.md)
- [KahnKalaiVerified.lean](Kahn-Kalai/KahnKalaiVerified.lean): standalone source, apart from mathlib.
- [Paper.lean](Kahn-Kalai/Paper.lean): paper-specific statements and bridges.
- [KahnKalai/](Kahn-Kalai/KahnKalai/): modular source files.
- [verification/](Kahn-Kalai/verification/): supplied build logs, axiom reports, and checksums.
- [LICENSE](Kahn-Kalai/LICENSE): Apache-2.0 license text.

The quantitative bound is proved through the Tran–Vu route, using Dan Clemens Posch's upstream formalization. Several Park–Pham proof steps are also formalized; the complete original randomized Park–Pham argument is not transcribed line by line. See the project README for the precise statements, attribution, and limitations.

### Talagrand / Park–Pham Conjecture 5.7

The complete project is in **[talagrand-conjecture-5-7/](talagrand-conjecture-5-7/)**. It formalizes the corrected positive-finite-expectation version of Conjecture 5.7 with the explicit constant L = 2048.

- [Project README and exact hypotheses](talagrand-conjecture-5-7/README.md)
- [TalagrandConjecture57.lean](talagrand-conjecture-5-7/TalagrandConjecture57.lean): standalone theorem file.
- [TalagrandSelector/](talagrand-conjecture-5-7/TalagrandSelector/): modular development.
- [verification/](talagrand-conjecture-5-7/verification/): supplied build logs, axiom reports, results, and source hashes.

The public theorem assumes a finite ground set, 0 < p < 1, nonnegative weights, and positive finite extended expectation. The weight collection may be infinite; attainment of the supremum is not assumed.

### Talagrand's five conjectures

The third project is [talagrand-five-conjectures/](talagrand-five-conjectures/). It contains complete Lean proofs for five Talagrand conjectures, together with supporting results by Li, Fang–Wang, and Park–Talagrand.

- [Project README and conjecture scope](talagrand-five-conjectures/README.md)
- [TalagrandFiveConjectures.lean](talagrand-five-conjectures/TalagrandFiveConjectures.lean): standalone source.
- [TalagrandConjectures/](talagrand-five-conjectures/TalagrandConjectures/): modular proofs.
- [verification/](talagrand-five-conjectures/verification/): build, axiom, result, source, and article records.

The project records the exact interpretation of Conjectures 9.1, 7.12, 7.9, 7.3, and 7.2 in its own README. Its theorem and supporting-result names are preserved as Lean declarations; the supplied verification reports document the proof dependencies.

### Small versus weakly small, and Talagrand's discrete-convexity conjecture

The project is in **[small-vs-weakly-small-and-discrete-convexity/](small-vs-weakly-small-and-discrete-convexity/)**. It groups the two related results in one independent Lean project, with the shared dependencies needed by their proofs.

- [Project README: statements and proof scope](small-vs-weakly-small-and-discrete-convexity/README.md)
- [Standalone Lean verification](small-vs-weakly-small-and-discrete-convexity/Small-vs-Weakly-Small-and-Talagrand-Discrete-Convexty-Conjecture.lean)
- [TalagrandIntegral modules](small-vs-weakly-small-and-discrete-convexity/TalagrandIntegral/)
- [Supporting fractional-certificate modules](small-vs-weakly-small-and-discrete-convexity/TalagrandConjectures/)
- [Verification logs, axiom reports, source profile, and SHA-256 checksums](small-vs-weakly-small-and-discrete-convexity/verification/)

The main declarations are `TalagrandIntegral.comparison_theorem_1_1` (comparison constant `25 * 512^4`) and `TalagrandIntegral.discrete_convexity_theorem_1_1` (`k = 2^75`). The package also contains the budget-preserving rounding result, threshold-maximizer statements, and two-union corollary. The discrete-convexity proof uses the comparison theorem, Li's fractional certificate, and finite probability couplings. Its README identifies the original paper arguments that are not formalized.

The project pins Lean 4.32.0 and mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`. The original filenames, including `Convexty` in the supplied standalone filename, are preserved so the build scripts and checksum manifest stay consistent. The supplied logs are retained unchanged; adding this project to the repository is not a fresh Lean compilation.

## Repository layout

```text
Project-Reflexive/
├── README.md
├── Kahn-Kalai/
│   ├── KahnKalai/, verification/
│   └── Lean sources, project README, license, and Lake configuration
├── talagrand-conjecture-5-7/
│   ├── TalagrandSelector/, verification/, scripts/
│   └── TalagrandConjecture57.lean and project configuration
├── talagrand-five-conjectures/
│   ├── TalagrandConjectures/, verification/, scripts/
│   └── TalagrandFiveConjectures.lean and project configuration
└── small-vs-weakly-small-and-discrete-convexity/
    ├── README.md
    ├── Small-vs-Weakly-Small-and-Talagrand-Discrete-Convexty-Conjecture.lean
    ├── TalagrandIntegral.lean
    ├── TalagrandIntegral/, TalagrandConjectures/
    ├── verification/, scripts/
    └── lakefile.toml, lake-manifest.json, lean-toolchain
```

There is no shared Lake project at the repository root. Keep each result's dependencies and audit records within its own directory. The internal directory `Kahn-Kalai/KahnKalai/` retains the Lean module name `KahnKalai`, so existing `import KahnKalai...` declarations still work within that project.

## Reproduce the projects

Install Lean/Elan and Git. Each project's `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin its environment. Run the following blocks separately from the repository root.

Kahn–Kalai (Bash, including Git Bash or WSL on Windows; Python 3 is also used by the audit script):

```sh
cd Kahn-Kalai
lake exe cache get
bash verify.sh
```

Conjecture 5.7:

```sh
cd talagrand-conjecture-5-7
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean TalagrandConjecture57.lean
```

Five conjectures:

~~~sh
cd talagrand-five-conjectures
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean TalagrandFiveConjectures.lean
~~~

Small versus weakly small and discrete convexity (Python 3 and a POSIX shell are required):

```sh
cd small-vs-weakly-small-and-discrete-convexity
lake exe cache get Mathlib.Tactic Mathlib.Analysis.MeanInequalities Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Topology.Order.Compact Mathlib.Data.Fintype.Perm Mathlib.Analysis.SpecificLimits.Normed Mathlib.Analysis.Complex.ExponentialBounds
sh scripts/verify.sh
```

The standalone file and modular library in each project define the same names. Check them separately rather than importing both into one Lean file. The records under `verification/` are supplied build evidence; rerun the checks after editing proofs. The directory migration itself does not constitute a fresh Lean compilation.

## Path migration and existing links

All former root-level Kahn–Kalai project files and the old `KahnKalai/` and `verification/` directories now live under `Kahn-Kalai/`. The collection README remains here; the original Kahn–Kalai README is restored at [Kahn-Kalai/README.md](Kahn-Kalai/README.md).

See the **[complete old-to-new path map](Kahn-Kalai/MIGRATION.md)** for updated file links and a permanent link to the pre-migration snapshot. GitHub does not provide repository-controlled redirects for arbitrary moved file URLs. Update bookmarks or external references that use old `main` paths; links pinned to old commit IDs remain available through Git history.

## Add a future result

Create one top-level directory per theorem or conjecture. Include its own README, Lean sources, Lake configuration, toolchain pin, verification records, and applicable license/attribution information. Then add it to the project list above.

```sh
git clone https://github.com/Mephisto17/Project-Reflexive.git
cd Project-Reflexive
mkdir talagrand-new-result
# Add the complete project under talagrand-new-result/.
# Update this README with links and reproduction commands.
git add talagrand-new-result README.md
git commit -m "Add Talagrand new result"
git push
```

If already cloned, pull the latest changes before adding a result. In the GitHub web interface, open the target project directory before choosing **Add file → Upload files**, and preserve nested directories when uploading modules and reports.

## Licenses and attribution

The Kahn–Kalai license and upstream attribution are kept with that project in [Kahn-Kalai/LICENSE](Kahn-Kalai/LICENSE) and [Kahn-Kalai/README.md](Kahn-Kalai/README.md). Relocating that license does not change any existing license terms. Preserve all applicable licenses and copyright notices when adding future results, and record mathematical sources, code sources, exact revisions, theorem scope, and audited axioms in each project's documentation.
