# Repository Guidelines

## Project Structure & Module Organization
- This repo contains two independent Lean/Lake projects: `categorical-ml/` and `mdp/`.
- Each project has its own `lakefile.toml`, `lean-toolchain`, and `lake-manifest.json`.
- Source modules live under `categorical-ml/CategoricalMl/` and `mdp/Mdp/`, with entry files `CategoricalMl.lean` and `Mdp.lean`.
- `mdp/Main.lean` defines the executable `mdp` target.
- Supporting docs and metadata live in `mdp/Mdp/GADT.md`, `AUTHORS`, and `LICENSE`.

## Build, Test, and Development Commands
- `cd categorical-ml && lake update` fetches dependencies (mathlib) on first run.
- `cd categorical-ml && lake build` builds the `CategoricalMl` library target.
- `cd mdp && lake update` fetches dependencies (mathlib, LeanCopilot).
- `cd mdp && lake build` builds the `mdp` library and executable.
- `cd mdp && lake exe mdp` runs the `mdp` binary after a successful build.

## Coding Style & Naming Conventions
- Lean 4 codebase; follow existing formatting (2-space indent, no tabs, aligned fields).
- Use UpperCamelCase for types/structures/namespaces (e.g., `MDPCategory`, `NeuralCategory`).
- Use lowerCamelCase for definitions/lemmas/instances (e.g., `normalize_discrete`, `prob_equiv`).
- File names mirror namespaces (e.g., `Mdp/MDP_Basic.lean`, `CategoricalMl/Basic.lean`).

## Testing Guidelines
- No dedicated test framework is configured.
- Treat a clean `lake build` in each subproject as the primary check.
- Keep examples and proofs in the relevant module and ensure they typecheck.

## Commit & Pull Request Guidelines
- Current history uses short, summary-style messages (e.g., `Initial commit`, `init ml libs`). Keep commits concise and imperative.
- PRs should include a scope summary, Lean files touched, and commands run (e.g., `lake build`).
- Link issues when relevant and call out new dependencies or toolchain changes.

## Toolchain & Dependencies
- Each subproject pins its Lean version via `lean-toolchain`; use the specified toolchain per folder.
- `mdp` links against `ctranslate2` via `moreLinkArgs`, so the library must be available when building the executable.
