---
name: harvest_rewrite_patterns
description: Mine the rewrite stage's per-attempt logs for new Hax-incompatibility patterns and archive them under `rewrite_patterns/`.
---

## Goal

Read the previous stage's (rewrite) attempt log, identify each patch that fixed a Hax / `lake build` incompatibility, and contribute new pattern files to the repo-root `rewrite_patterns/` archive when the root cause isn't already covered.

You only *write* to `rewrite_patterns/`. You do not edit the working crate, the source, or anything else.

## Available tools

- Built-in `Read`, `Grep`, `Glob` for inspection
- `Bash` — flexible shell for ad-hoc inspection (`find`, `wc`, `diff`, inline `python3 -c ...`) beyond what `Read`/`Grep`/`Glob` cover.
- `TodoWrite` — track each candidate pattern you're evaluating as a checklist; mark off as each one is either added or rejected as already-covered.
- `Agent` / `Task` — spawn a sub-agent for broad surveys (e.g. *"index the existing `rewrite_patterns/*.rs` headers by error fragment"*).
- `write_rewrite_pattern` for archiving a new pattern.

## What you're reading

The prompt names a per-run log directory like `attempted_changes/<timestamp>/`. Inside it is one subdirectory per patch attempt by the rewrite agent, named:

```
NNNN_stage2_rust_hax_lean_<status>/
```

(status is `patched`, `no_changes`, `written`, or `error`). Each contains:

- `metadata.json` — `path`, `status`, `trigger_error`, `timestamp`, etc.
- `before.<ext>` — full file contents *before* the patch
- `after.<ext>` — full file contents *after* the patch (absent for `error` status)
- `search_replace.txt` — the exact SEARCH/REPLACE patch the agent applied
- `error_context.txt` — the Hax / lake stderr that triggered the change (present when relevant)

Only `stage2_rust_hax_lean` attempts matter. Ignore other stages' attempts even if they're in the same log.

## What counts as a pattern

A patch is pattern-worthy when **all** of these hold:

1. The patch was triggered by a Hax / `lake build` error (`metadata.trigger_error` non-empty, or `error_context.txt` exists).
2. The status is `patched` — the rewrite landed cleanly.
3. The rewrite is **mechanical** — a future agent could apply the same shape to a similar failure without redoing semantic analysis. Wholesale algorithm changes don't count; small idiomatic substitutions do.
4. The root cause is **not already documented** in `rewrite_patterns/`. Read each existing `*.rs` file's header before writing.

If any of these fail, skip.

## Workflow

1. **List existing patterns.** `Glob` `rewrite_patterns/*.rs`. For each file, `Read` the first ~10 lines to capture the `// unsupported:` header. Make a mental index keyed by error fragment / root cause.

2. **Walk the attempt log.** For each `*_stage2_rust_hax_lean_patched/` directory:
   - Read `metadata.json`. If `trigger_error` is empty and there's no `error_context.txt`, skip.
   - Read `error_context.txt` (or the trigger) to identify the *root cause* — usually one of: Hax extraction error, lake build symbol error, `bv_decide` synthesis failure, pureP synthesis failure, keyword collision, missing typeclass.
   - Read `before.<ext>` and `after.<ext>`. Diff them mentally: find the smallest hunk that changed and represents the fix. Files are often large; you want the few lines around the SEARCH/REPLACE block in `search_replace.txt`, not the whole file.
   - Check your mental index: does an existing pattern cover this root cause? If yes, skip.

3. **Write the pattern** via `write_rewrite_pattern`. File content shape:

   ```rust
   // unsupported: <one-line root cause; quote or closely paraphrase the
   // actual Hax / lake error stderr so future agents can grep for it>

   // before

   <the minimal failing Rust shape from before.rs — only the few lines
   that triggered the error, not the whole file>

   // after

   <the minimal Hax-compatible rewrite from after.rs — same lines, fixed>
   ```

   File name: snake_case, ends in `.rs`. Name describes the failure mode (e.g. `bool_to_int_cast.rs`, `assoc_type_equality_on_parent.rs`), not the fix.

4. **Stop conditions.** When you've walked every relevant attempt directory, you're done. Don't invent patterns from imagination — every entry must trace to a real `before.rs`/`after.rs` pair in the log.

## Rules

- The only writable tool you have is `write_rewrite_pattern`. You cannot modify the working crate, the source, or the log. If you find a log entry that confuses you, note it in the final report — don't try to "fix" it.
- Quality over quantity. One well-named, well-explained pattern is worth more than five vague ones. If a patch is borderline, skip — patterns can always be added later from logs.
- Patterns must be `before` + `after` complete. If the log only has `before` (status `error` or no `after.rs`), skip — the rewrite didn't succeed, so there's no known fix to document.
- Use `write_rewrite_pattern`'s overwrite-on-write behavior: if you re-write a file with the same name, the prior contents are replaced. Don't accidentally clobber an existing pattern by reusing its name.

## Final output

- One-line summary per pattern written: name + root cause
- Attempts inspected but skipped (with one-line reason: "already covered by X", "not mechanical", "no trigger_error", etc.)
- Anything in the log you flagged as confusing or worth a human's attention
