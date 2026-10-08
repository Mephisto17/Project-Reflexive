# Project Reflexive

**Explore the ideas. See how they connect. Check what has been proved.**

Project Reflexive aims to make mathematics at the research frontier easier to approach, understand, and use. We are building toward an interactive, visual, directly checkable home for mathematical results, beginning with theorems and conjectures related to Talagrand.

Our audience includes working mathematicians, mathematics students, and anyone curious about how new mathematical knowledge is established. Readers should be able to choose their depth: a short explanation, a visual account of the ideas, a precise statement, or the formal proof itself.

**Where we are today:** this repository contains Lean source projects, mathematical scope notes, dependency versions, and supplied verification records. The interactive maps, visual explanations, and guided experiences described below are our product direction; they are not yet available as a finished interface.

[Browse the current results](README.md#projects) · [Read the verification instructions](README.md#reproduce-the-projects)

## Why this project exists

A result can be published, important, and still difficult to enter. Researchers spend substantial time checking unfamiliar arguments before they can use a theorem. Students need help seeing which definitions and intermediate results carry the proof. A curious reader may need a clear account of the question before any notation becomes meaningful.

We want to lower these barriers while preserving the substance of the mathematics. Formal verification can reduce the work of checking logical steps. Visual explanations can make structure and intuition easier to grasp. Careful summaries can help readers understand why a question matters and where a result fits.

Our starting point is a collection of formalizations. Our ambition is a product that makes this collection useful to people with different backgrounds, questions, and amounts of time.

## Choose your way into the mathematics

**For researchers: inspect the claim, then use it with confidence.** A result should offer a direct route to its exact statement, hypotheses, provenance, formal declaration, proof dependencies, and reproducible check. Researchers who accept Lean's foundations and the documented assumptions can rely on a kernel-checked proof of that statement, saving time otherwise spent rechecking its logical steps. They can focus their attention on whether the statement captures the intended mathematics and applies to their problem.

**For students: see the architecture of an argument.** A visual map should reveal how definitions, lemmas, and theorems fit together. Selecting a node should explain what it says, why it is useful, and what a reader needs to understand first. Short worked examples and guided routes should let learners move between intuition and formal detail at their own pace.

**For the public: begin with a question worth exploring.** An entry point might be a small puzzle, a surprising pattern, or an experiment with random subsets. A reader should be able to make a prediction, change a parameter, and see what happens before encountering the general statement. Every explanation should offer a natural next step for someone who wants to go deeper.

These are different routes through the same mathematics. Moving between them should be easy, and the formal sources should always remain within reach.

## The experience we want to build

We will treat presentation, navigation, and explanation as essential parts of the project. The first screen should help someone understand the question and choose a useful next step. Technical details should appear where they answer a reader's question, with terminology introduced as it becomes necessary.

The planned experience has three connected elements:

- **A map of mathematical relationships.** Build on ideas and tooling from Lean blueprint to show the structure behind a result. We want readable labels, clear visual hierarchy, focused views, and paths suited to different levels of preparation. Edges should distinguish actual proof dependencies from conceptual connections and historical relationships. An attractive diagram must also be an accurate one.
- **Interactive explanations.** Let readers vary a probability, compare an integral cover with a fractional cover, or inspect a small finite example. Each interaction should explain what changes, what stays fixed, and which assumptions matter. Examples and simulations will be identified as illustrations; the general claim will link to its formal statement and verification evidence.
- **A direct route to verification.** A reader should be able to move from an explanation to the exact Lean declaration and its dependencies, then find the source revision, environment, axiom report, and instructions needed to reproduce the check. We aim to make the evidence easy to inspect and the check straightforward to rerun.

For example, someone exploring smallness and weak smallness could start with a tiny family of sets, try to cover it, and compare whole-set choices with fractional weights. A short explanation could then connect that experiment to the comparison theorem. The same page would offer the theorem's assumptions, its place in the proof map, and the formal source.

The interface should feel calm, inviting, and coherent. Plain language, thoughtful typography, accessible colors, keyboard navigation, and useful views on smaller screens all matter. Reading Lean code should be an available depth of engagement, never a prerequisite for understanding the project's purpose.

## Academic care is part of the design

Every result must preserve a clear account of what has been established, by whom, and under which assumptions.

We will credit the original mathematical work, prior formalizations, and subsequent contributions separately, with appropriate citations, source revisions, and licenses. Formalizing an existing result does not transfer credit for its discovery. When a formal proof takes a different route from a cited paper, or covers a modified statement, that distinction belongs beside the result.

Verification labels must describe evidence precisely. A supplied compiler log, a reproduced build, and an independently reviewed match between a paper and its formal statement are different achievements. We will identify the checked revision and environment, disclose the axioms used, and make limitations or incomplete work visible. A successful Lean check establishes the formal statement under its recorded assumptions; correspondence with an informal claim still deserves mathematical review.

Visuals and summaries will remain connected to that record. Definitions cannot quietly change between a friendly explanation and a technical view. Analogies should state their limits. An illustrative relationship should never be displayed as a verified logical implication without support.

## Make the journey memorable

Enjoyment can help people stay with a difficult idea. We want concise takeaways, annotated examples, historical context, short quizzes, and moments that invite a reader to ask, “What if I change this?” A counterexample or a well-chosen puzzle can make an assumption memorable.

These elements should reward curiosity and leave readers with an accurate understanding. A visitor might leave knowing why a threshold is interesting, what a fractional cover allows, or how a small lemma supports a much larger conclusion. The experience should remain useful and credible to specialists while becoming welcoming to a much wider audience.

## How we will move forward

The next stage is to connect selected formal results to carefully reviewed explanations and a dependency map. We will develop a small number of interactive examples around those results, make verification evidence easier to navigate, and test the experience with researchers, students, and readers without specialist training.

Success will mean that a researcher can quickly assess whether a result is usable, a student can explain an important relationship in the proof, and a curious visitor can describe the question and why it matters. It will also mean that each reader can find the evidence behind a claim.

We welcome contributions in formalization, mathematical review, exposition, visualization, interaction design, and accessibility. The shared aim is to make frontier mathematics easier to enter, easier to examine, and easier to share responsibly.

[Explore Project Reflexive](README.md)
