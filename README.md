# Project Reflexive

**Follow the idea. Trust the proof.**

[Project website](https://project-reflective-organization.github.io/Project-Reflexive/) · [GitHub organization](https://github.com/Project-Reflective-Organization)

[English](#a-way-into-mathematics) · [Collections](#projects) · [Run the page](#run-the-page-locally) · [Verify](#reproduce-the-projects)

## A way into mathematics

Project Reflexive is a collection of Lean formalizations for research mathematics with interactive illustrations. It is designed for a hybrid audience:

- a mathematician can move from a result to its exact Lean declaration, source, dependency record, and reproducible check;
- a student or curious reader can begin with an experiment, illustration, or proof map and build intuition before reading the formal source.

The same theorem should support both journeys. Explanations, diagrams, simulations, and historical notes remain connected to the formal statement and its evidence.

For mathematicians who accept Lean’s foundations and the documented hypotheses, a kernel-checked proof can provide a reliable logical basis for using a formal statement. This lets mathematical attention focus on what the statement means, whether it matches the intended claim, and whether it applies to a new problem.

For everyone else, a theorem can begin as a question worth asking. A graph makes the roles of lemmas and theorems visible. An experiment offers a concrete intuition. A short explanation connects that intuition to the exact result, with the formal source always within reach.

## The experience

- **A map of proofs:** select lemmas, corollaries, and theorems to understand their role and follow their source dependencies. Direct arrows and paths with omitted intermediate steps have distinct labels.
- **An interactive blueprint:** search declarations in all four collections; explore neighbors, all prerequisites, or the whole collection; zoom, pan, and follow references to their Lean statements.
- **Lean source inside the page:** open a read-only source panel with syntax coloring, line numbers, a highlighted declaration, line navigation, and file copying. GitHub remains available as a secondary link.
- **Choose your depth:** move between ordinary-language intuition and precise hypotheses, formulas, and Lean declarations.
- **Explore by question:** search four formalization collections or browse thresholds, covering, and convexity.
- **Learn by interaction:** vary a Bernoulli probability and compare sampled subsets with the exact probability in a small finite example.
- **Keep the history visible:** each collection includes mathematical authors, proof routes, publication or preprint information, formalization credit, and source links.

The working page is [`index.html`](index.html). Its opening map is a curated six-node introduction to smallness and discrete convexity. The larger **interactive blueprint** indexes 789 declarations and 2,731 explicit local source references across the four collections, including shared supporting declarations counted within each collection. It is a source-navigation graph, not an exhaustive extraction of elaborated Lean proof terms: Mathlib declarations, tactic-generated dependencies, and unresolved notation are omitted. The probability lab illustrates an idea rather than proving a general threshold theorem. Read the longer [project vision](PROJECT.md).

## Projects

| Collection | Mathematical focus | Start here |
|---|---|---|
| Kahn-Kalai Conjecture (Park-Pham Theorem) | Expectation thresholds and random containment | [`Kahn-Kalai/README.md`](Kahn-Kalai/README.md) |
| Talagrand / Park–Pham 5.7 | Selector processes and small covers | [`talagrand-conjecture-5-7/README.md`](talagrand-conjecture-5-7/README.md) |
| 5 questions of Talagrand via the kernel method of Li | Thinning, spread, Walsh identities, and fractional covers | [`talagrand-five-conjectures/README.md`](talagrand-five-conjectures/README.md) |
| Talagrand expectation thresholds and discrete convexity | Integral–fractional comparison and same-density union smallness | [`small-vs-weakly-small-and-discrete-convexity/README.md`](small-vs-weakly-small-and-discrete-convexity/README.md) |

### Kahn-Kalai Conjecture (Park-Pham Theorem): from an estimate to a threshold

Jeff Kahn and Gil Kalai proposed the expectation-threshold conjecture in [*Thresholds and Expectation Thresholds*](https://doi.org/10.1017/S0963548307008474), *Combinatorics, Probability and Computing* 16(3), 495–502 (2007). Jinyoung Park and Huy Tuan Pham announced a proof in 2022; [*A Proof of the Kahn–Kalai Conjecture*](https://doi.org/10.1090/jams/1028) appeared in *JAMS* 37(1), 235–243 (2024).

This project proves `p_c(F) ≤ 100000 · q(F) · log₂ ℓ(F)`, with **integral** expectation threshold q. Its complete proof follows Phuc Tran and Van Vu’s [short inductive proof](https://doi.org/10.37236/12266), *Electronic Journal of Combinatorics* 31(3), P3.2 (2024), using [Dan Clemens Posch’s existing Lean formalization](https://github.com/dcposch/kahn-kalai-lean/tree/641aa75f8e873d31442f2f7c317b2e7582a26d94). Selected Park–Pham steps and definition bridges are also formalized; the entire original randomized argument is not transcribed line by line.

### Talagrand / Park–Pham 5.7: explaining large outcomes

The question appears in Jinyoung Park and Huy Tuan Pham’s [selector-process paper](https://doi.org/10.4007/annals.2024.199.3.6), *Annals of Mathematics* 199(3), 1293–1321 (2024), first posted in 2022. The development adapts the witness method in the alternative proof by Witold Bednorz, Rafał Martynek, and Rafał Meller, [arXiv:2212.14636v3](https://arxiv.org/abs/2212.14636v3).

The repository proves the **corrected positive-finite-expectation** version of Conjecture 5.7 with `L = 2048`. Its assumptions are a finite ground set, `0 < p < 1`, nonnegative weights, and `0 < E < ∞`. Weight collections may be infinite; attaining the supremum is not assumed. The printed conjecture and the exact corrected interface are distinguished in the [project scope](talagrand-conjecture-5-7/README.md).

### 5 questions of Talagrand via the kernel method of Li

The original questions come from Michel Talagrand’s [*Are many small sets explicitly small?*](https://doi.org/10.1145/1806689.1806693), STOC 2010, 13–36. This collection formalizes the intended statements of Conjectures 9.1, 7.12, 7.9, 7.3, and 7.2, with supporting results and explicit convention corrections.

Its proof routes include Chen Li’s [*On p-Spread Measures*](https://arxiv.org/abs/2609.08967v1) and Xuan Fang and Tianyu Wang’s [*A Note on a Result of Chen Li*](https://arxiv.org/abs/2609.18458v1), both September 2026 preprints. The 9.1/7.12/7.3 route follows Jinyoung Park and Michel Talagrand’s [*AI’s solution of Conjecture 9.1*](https://arxiv.org/abs/2609.33644v1). That note credits GPT-6 Astra with generating its proofs, says the authors claim no proof credit, and is not intended for journal publication. These are preprints, not asserted journal publications.

The public constants include `(√5 − 1)/2` for 7.9 and `q = 3` for the original cost-1/2 formulation of 7.2. The [collection README](talagrand-five-conjectures/README.md) records the corrected logarithmic sign, numbering differences, and exact scope.

### Smallness and discrete convexity: OpenAI’s new results

OpenAI publicly released these two results in [*Sharing AI progress in mathematics*](https://openai.com/index/sharing-ai-progress-in-mathematics/) on **October 6, 2026**. Its [Math catalogue](https://github.com/openai/math/blob/main/CONTENTS.md) groups them in result family **175**, “Talagrand’s expectation thresholds, discrete convexity, and graph decompositions.” The companion preprints, dated **September 23, 2026**, list **OpenAI** as their author:

- [*Integral and fractional expectation thresholds are equivalent*](https://github.com/openai/math/blob/main/preprints/Integral-and-fractional-expectation-thresholds-are-equivalent-September-23-2026/paper.pdf), with [citation instructions](https://github.com/openai/math/blob/main/preprints/Integral-and-fractional-expectation-thresholds-are-equivalent-September-23-2026/README.md).
- [*Talagrand’s discrete-convexity conjecture*](https://github.com/openai/math/blob/main/preprints/Talagrands-discrete-convexity-conjecture-September-23-2026/paper.pdf), with [citation instructions](https://github.com/openai/math/blob/main/preprints/Talagrands-discrete-convexity-conjecture-September-23-2026/README.md).

They are **OpenAI Math Release preprints published on GitHub**; no journal publication is asserted. OpenAI also provides a [Lean scope note for family 175](https://github.com/openai/math/blob/main/lean/docs/175.md).

The local comparison theorem uses `25 · 512⁴` and applies to finite families excluding the empty set. The discrete-convexity theorem uses `k = 2⁷⁵` and `0 < p < 1`. Both keep cover cost at most `1/2`. The local discrete-convexity proof takes an alternative route through comparison, Chen Li’s fractional certificate, and finite couplings; the paper’s separate hypergraph-covering lemma and signed 32-row kernel are not formalized here. This repository covers the two linked theorems, not the additional graph-decomposition application in the wider release family.

## Run the page locally

The [Pages workflow](.github/workflows/pages.yml) tests and builds the research website on relevant pushes to `main`, then publishes only `dist/`.

Requires **Node.js 20+**. No package installation is needed to run this static site.

```sh
npm run dev
```

Open [http://localhost:5173](http://localhost:5173). Use `npm run build` to create `dist/` for a static host, and `npm run preview` to preview that build. The paths are relative so the build can also be hosted below a repository subpath.

The page uses plain HTML, CSS, and JavaScript. Copy, theorem details, credits, and references live in [`web/data.js`](web/data.js). The exact eight-point probability calculation is in [`web/math.js`](web/math.js).

After editing the modular Lean sources, regenerate the blueprint and local source snapshot with Python 3:

```sh
npm run blueprint
```

[`scripts/build_blueprint.py`](scripts/build_blueprint.py) creates [`web/blueprint-data.json`](web/blueprint-data.json) and [`web/lean-sources.json`](web/lean-sources.json). The committed snapshots let the ordinary site build run without Python or Lean. Source files are displayed unchanged, with their existing comments and notices. The panel is a reader, not a live Lean editor or verification session.

## Read the evidence carefully

The supplied `verification/` directories contain build logs, Lean versions, axiom reports, source hashes, and result records. A successful Lean check establishes the formal statement under its recorded assumptions. It does not, by itself, establish that an informal paper and a formal declaration have identical scope; that correspondence still deserves mathematical review.

The repository keeps mathematical discovery, exposition, formalization, and verification credit separate. The project page adds history and bibliography notes for each collection so readers can see who posed a question, who proved it, which route was formalized, where a result was published or released, and what remains outside the formal scope.

## Checks

```sh
npm test
npm run build
```

`npm test` checks the probability calculation, graph closure and layout, source anchors, syntax coloring, and exact correspondence between source snapshots and local Lean files. `python scripts/check_site.py` checks both languages, collection navigation, graph scopes, search, zoom, keyboard interaction, source reading and copying, result dialogs, and mobile layouts when Playwright Chromium is installed and `npm run dev` is running. Lean reproduction commands are collected in [`PROJECT.md`](PROJECT.md#reproduce-the-projects).

## Reproduce the projects

Install Lean/Elan and Git. Each independent project pins its own toolchain and dependencies; there is no root Lake project. See the [complete reproduction commands](PROJECT.md#reproduce-the-projects) or the individual collection READMEs. Run a modular library and its standalone version separately; they intentionally declare the same names.

The supplied logs report Lean **4.32.0**, with transitive axioms limited to `propext`, `Classical.choice`, and `Quot.sound`. Changing source or dependency pins requires a fresh build and audit. Website checks do not recompile the Lean projects.

## Licenses and attribution

Mathematical discovery, exposition, and Lean formalization are separate contributions. Preserve original authors, upstream sources, exact revisions, and applicable licences. The Kahn–Kalai upstream files and Apache-2.0 licence remain in [`Kahn-Kalai/LICENSE`](Kahn-Kalai/LICENSE). OpenAI’s release has its own [licence](https://github.com/openai/math/blob/main/LICENSE) and manuscript citation instructions.

The original root-level Kahn–Kalai files were moved under `Kahn-Kalai/`; the [migration map](Kahn-Kalai/MIGRATION.md) records old and new paths. Existing links pinned to old commits remain available through Git history.

## Contribute

Review a statement, formalize a lemma, improve a visualization, translate an explanation, add a citation, or make the interface more accessible. Keep original mathematical credit, formalization credit, licences, source revisions, and verification limits visible whenever you add or reuse a result.
