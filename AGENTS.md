# Repository Guidelines

## Project Structure & Module Organization
- Two independent Lean/Lake projects live at the repo root: `categorical-ml/` and `mdp/`.
- Each project has its own `lakefile.toml`, `lean-toolchain`, and `lake-manifest.json`.
- Source modules:
  - `categorical-ml/CategoricalMl/Basic.lean` (library entry: `categorical-ml/CategoricalMl.lean`).
  - `mdp/Mdp/` (e.g., `MDP_Basic.lean`, `MDP_Semantic.lean`, `MDP_GADT_Proofs.lean`; library entry: `mdp/Mdp.lean`).
- Executable entrypoint: `mdp/Main.lean` builds the `mdp` binary.
- Project notes and references: `mdp/Mdp/GADT.md`, plus root `AUTHORS` and `LICENSE`.

## Architecture Overview
- The repo is split into two standalone Lean libraries: `CategoricalMl` for categorical ML sketches and `Mdp` for Markov decision process models.
- `mdp` combines definitional MDP structures (`MDP_Basic.lean`) with semantic/denotational encodings (`MDP_Semantic.lean`) and proof experiments (`MDP_GADT_Proofs.lean`).
- The `mdp` executable (`Main.lean`) serves as a small runnable demo built atop the library modules.

## Build, Test, and Development Commands
- `cd categorical-ml && lake update` fetches dependencies the first time.
- `cd categorical-ml && lake build` builds the `CategoricalMl` library.
- `cd mdp && lake update` fetches `mathlib` and `LeanCopilot`.
- `cd mdp && lake build` builds the `Mdp` library and the `mdp` executable.
- `cd mdp && lake exe mdp` runs the demo executable after a successful build.

## Coding Style & Naming Conventions
- Lean 4 codebase; keep 2-space indentation, no tabs, and align structure fields where practical.
- Use UpperCamelCase for types/structures/namespaces (e.g., `MDPCategory`).
- Use lowerCamelCase for definitions/lemmas/instances (e.g., `bellmanIter`, `prob_eq`).
- File names mirror namespaces (e.g., `Mdp/MDP_Basic.lean`).

## Testing Guidelines
- No dedicated test framework is configured.
- Treat `lake build` in each subproject as the primary check.
- Keep examples and proofs in the relevant module and ensure they typecheck.

## Commit & Pull Request Guidelines
- Commit history favors short, imperative summaries; occasional Conventional Commit prefixes appear (`fix:`, `chore:`). Keep new messages concise and consistent.
- PRs should include: a brief scope summary, a list of Lean files touched, and commands run (e.g., `lake build`).
- Link relevant issues and call out any toolchain or dependency changes.

## Toolchain & Dependencies
- Each subproject pins its Lean version via its own `lean-toolchain`; use the local toolchain per folder.
- `mdp` links against `ctranslate2` via `moreLinkArgs`; ensure the library is available when building/running the executable.
