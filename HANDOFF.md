# HANDOFF — verus-physics2d (phys-06a, mid-S5a-static-proof)

Written 2026-08-03, after the 06a engine landed and was exec-validated.
Read `../physics-gears/HANDOFF.md` first for repo layout and the phys-01..05
backstory; this file supersedes its "Your task" section.

## Current state

**Everything committed is full-crate green** (`./check.sh verus-physics2d`
— now verifies `--lib` only, see below). The 06a engine is COMPLETE and
exec-validated end-to-end:

- **Manifold construction** (narrowphase.rs + proofs/manifold.rs, 46
  lemmas): incident_edge_exec, clip_halfplane_exec (exact rational
  half-plane clip, no sqrt), build_manifold with full SPEC §5 ensures
  (normal ≡ ref edge_normal, |n|² ≢ 0 via adjacent-vertex distinctness,
  1–2 lex-sorted points, sep ≡ exact axis_sep, on-face span decomposition
  q ≡ p0 + t·d + s·n with t ∈ [0,1]).
- **Solver layer** (solver.rs): build_rows_exec (broadphase → SAT →
  manifold → rows, mEff once, zero-mEff dropped, canonical order),
  pgs_sweep_exec (16 iterations, wf-only per D8).
- **Certificate** (certificate.rs): C1 velocity bookkeeping (per-body
  impulse folds + snap deltas + static-freeze), C2 bounds, C3 restitution,
  C4 non-penetration over the whole post world (per-pair 05d depth check,
  static-static skip), C5 joints (vacuous form), **C7 exact energy
  ledger (no tolerance)**, and check_step with the bidirectional contract
  ok == step_checks_pass && (ok ⟹ step_certified).
- **Pipeline** (step.rs): step() = gravity → rows → PGS → canonicalize →
  integrate → canonicalize → certify, thin ensures; `step_checked()`
  always returns (post, cert, ok) with ok == step_checks_pass directly —
  the acceptance-scene interface.
- **Exec-validated**: `src/bin/s5a_probe.rs` runs the full S5a scene
  (side-2 box dropped gap-1 onto static ground, g = (0,−10), dt = 1/240):
  **all 140 steps certify, ~1.6 ms/step, witnesses ≤ 2 limbs.**

## Design decisions made this session (all recorded in
`../physics-gears/memory/pgs-canonicalize-and-c7-drift.md`)

1. **Canonicalize INSIDE the PGS sweep** — each row update multiplied
   denominators ~50× (16 iterations = 22 CPU-hours, killed). Now
   normalize λ, Δλ, and updated vel/omega per row update
   (pgs_row_update_exec). Value-preserving per D10.
2. **C7 has NO drift allowance** (D13 resolved): SPEC's negative
   W_drift = −(1/inv_m)·|g|²·dt²/2 rejects honest rest (ΔE = 0 there).
   True form: D = E(pre) + W_proj + W_snaps − E(post) ≥ 0, exactly
   computed. Free-flight drift is dissipative so it needs no allowance.
3. **tol_p = 1/100** for S5a (SPEC §11 "raise tol_p — record the
   choice"): impact penetration is EXACTLY 1/320 = 0.003125 (rows form
   the step AFTER impact — row building is pre-integration). Steady
   state pen = g·dt² = 1/5760 ≈ 57× margin.
4. S5a's resting state is an **exact fixed point** (vy ≡ 0, positions
   frozen at pen = 1/320, λ = 1/96/row fresh each step) — no general PGS
   convergence theorem needed for the static proof.

## IN-FLIGHT, UNCOMMITTED: sweep velocity bookkeeping (static C1)

Files dirty: `src/solver.rs`, `src/certificate.rs`, `src/proofs/mod.rs`,
`src/proofs/solver.rs` (new, all-green). **Do not commit until green.**
Do not revert either — the work is 95% done.

Goal: prove statically that PGS's total applied impulse per row is its
final λ (telescoping), so scene proofs get C1 from stage ensures.

What landed and verifies:
- `proofs/solver.rs` (all green): vadd/vscale/veqv micro-lemmas,
  impulse_sum_lin/ang fold-update lemmas (idx-recursion with the
  touching-conditional unfold form), zero-λ base lemmas,
  lemma_sweep_bookkeeping_update (one row update telescopes),
  lemma_sweep_bookkeeping_base, lemma_pgs_row_update_facts (packaged),
  frame lemmas.
- pgs_row_update_exec ensures the exact impulse relation
  (vel_after_impulse with applied = λ′ − λ, plus λ′ ≡ clamped solve).
- Closed (open+opaque) packaging: `bookkeeping_ok` and `sweep_state_ok`
  in solver.rs — the loop boundaries now instantiate ONE predicate.
  pgs_sweep_one_row_exec verifies with the packaged contract.
- impulse_sum_lin/ang are `#[verifier::opaque] pub open spec fn` —
  unfold ONLY via reveal_with_fuel at the fold sites (they already have
  them). Do NOT make them `closed` (blocks cross-module reveal).

**Remaining failure (2 errors, both at the END of pgs_sweep_exec):**
the final unpack for the ensures' bookkeeping forall — the omega
conjunct instantiates and passes, the vel conjunct does NOT (expanded
diagnostics show the per-component cross-mults failing). The final block
is currently:

```rust
proof {
    reveal(sweep_state_ok);
    assert(bookkeeping_ok(bodies@, rs@, bs@));
    assert forall|i2: int| ... by { reveal(crate::solver::bookkeeping_ok); }
}
(bs, rs)
```

Suspicion: the two-#[trigger] clause (`bs[i2]` + `impulse_sum_lin(...)`)
instantiates the omega leg but not the vel leg at the package boundary —
the inner loops verified, so it's purely this final matching. Things to
try, in order:
1. Split bookkeeping_ok into bookkeeping_lin_ok / bookkeeping_ang_ok
   (two closed predicates, one trigger each) — most likely fix.
2. Assert the per-i2 expansion from the package directly:
   `assert(veqv(bs@[i2].vel.model@, ...)) by { reveal(bookkeeping_ok); }`
   per component leg.
3. Check `verus_check` with --expand-errors and compare the vel-side
   term shape to the package's character-by-character (a
   `rs@.len() as int` vs `out.1@.len() as int` mismatch would do it).

Then: full-crate green → commit ("phys-06a: sweep velocity bookkeeping
(C1 static)").

## After that: S5a static acceptance proof

Use `step_checked()` (always exposes post/cert/ok). Scene phases
(exec-confirmed values): falling 0–105 (closed form pos/vel),
impact 106 (pen = 1/320), absorption 107 (λ = 9/8/row, vy = 0, ω = 0),
resting 108+ (exact fixed point). Prove per-phase lemmas; the resting
loop is a one-lemma fixed point. The C3 residual question dissolved
(resting v ≡ 0 exactly). Expected hard part: the absorption step's
16-sweep closed form (induction over sweeps with the exact state
function; the row-update ensures carry everything needed).

## Gotchas from this session (beyond memory/)

- `Seq::len()` is `nat` — fold call sites need `as int`; comparisons
  auto-promote but function args do NOT.
- `let n = vec.len(); while j < n` breaks Verus's loop-condition
  bridge — write `while j < vec.len()` directly or the len invariants
  mysteriously fail.
- `#[verifier::opaque] pub open spec fn` is the working combo;
  `pub closed spec fn` REJECTS reveal_with_fuel cross-module.
- Reveals do NOT propagate into nested assert-forall by-blocks —
  re-reveal inside.
- reflexive lemmas must be called BEFORE congruence lemmas (facts are
  available only after the call); every 3-node chain needs its own
  transitive call; congruence takes FACTORS.
- assert-by (`assert(F) by { lemma(); }`) is a separate Z3 query — the
  working rlimit isolation for big exec fns.
- cargo-verus flags: `-V profile` and `-V expand-errors` are NOT valid;
  `--expand-errors` is (after `--`). Profiling: MCP `verus_profile`
  (client times out; server keeps going — retry).
- check.sh now passes `--lib` (unverified bench bins in src/bin broke
  the all-targets verify path). Rebuild bins with
  `cargo-verus build --release` (see s5a_probe/s5a_diagnose for the
  witness-size probe idiom: `r.numerator.magnitude.limbs_le.len()`).
- Old handoff's gotcha about `verus-physics2df/` still applies (stale
  copy, ignore).
