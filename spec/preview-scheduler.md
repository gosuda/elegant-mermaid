# Preview scheduler

This file fixes the viewer's render scheduler: its revisions, its reducer over three events, its commands, and the TLA+ model that TLC checks against the reducer.

## Revisions

- preview-scheduler-01: `latest` MUST count `Edited` events, numbering them 1, 2, 3, and so on, and revision 0 MUST mean that no revision exists. [just model]
- preview-scheduler-02: `displayed` MUST be the newest revision whose result the viewer has shown, or 0 before the first `Display`. [just go-check]
- preview-scheduler-03: A revision with errors MUST be displayed too; its result MUST have no frame, and the viewer MUST keep the last good frame. [just go-check: TestViewScripts]

## Reducer

- preview-scheduler-04: The scheduler MUST be a pure reducer `step(state, event) -> (state, command)` whose state holds `{latest, inflight, cancelled, displayed}`. [just model]
- preview-scheduler-05: `latest`, `inflight`, and `displayed` MUST be integers that are 64-bit in production, and `cancelled` MUST be a boolean. [just go-check]
- preview-scheduler-06: `inflight = 0` MUST mean that no render runs; at most one render MUST run at a time, and the next render MUST start only after the previous one has ended. [just model]
- preview-scheduler-07: Events MUST be handled one at a time on the viewer loop, and renders MUST run on the render worker. [just go-check]
- preview-scheduler-08: An event MUST carry no revision, so every `RenderDone` and `RenderAborted` MUST refer to `inflight`. [just model]

## Events

- preview-scheduler-09: The reducer MUST accept the three events of this table, with the emitter, the enabled condition, the effect, and the command of each row. [just model]

  |Event|Emitted by|Enabled when|Effect|Command|
  |---|---|---|---|---|
  |`Edited`|The viewer loop only: the startup; the watcher after its 50 ms coalescing (file change, file create, and the poll that finds a returned file); keys `r`, `t`, `c`, `g`, `n`, `p`.|always. The reducer has no cap. The model and the reducer test stop `Edited` at `latest = MaxRev`.|`latest += 1`. If `inflight = 0`: `inflight = latest`, `cancelled = FALSE`. Otherwise: `cancelled = TRUE`.|`StartRender(latest)` if `inflight` was 0. `CancelRender(inflight)` if `inflight` was not 0 and `cancelled` was FALSE. None otherwise.|
  |`RenderDone(result)`|The render worker, when a render returns a result (a frame, or diagnostics only), whether or not it was cancelled.|`inflight != 0`|If `cancelled`: `inflight = latest`, `cancelled = FALSE`, and `result` is discarded. Otherwise: `displayed = inflight`, `inflight = 0`.|If `cancelled` was TRUE: `StartRender(latest)`. Otherwise: `Display(displayed)`.|
  |`RenderAborted`|The render worker, when a render observed the cancel flag and returned without a result.|`inflight != 0` and `cancelled`|`inflight = latest`, `cancelled = FALSE`|`StartRender(latest)`|

- preview-scheduler-10: Each render MUST end with one of `RenderDone` or `RenderAborted`. [just model]
- preview-scheduler-11: A render MUST return `RenderAborted` when it observes the cancel flag at any check, and it MUST check the flag before it parses; otherwise it MUST return `RenderDone`. [just go-check: TestSchedulerReachable]

## Commands

- preview-scheduler-12: `StartRender(v)` MUST read the source, theme, charset, block index, and graphics mode at that moment, then render revision `v`. [just go-check]
- preview-scheduler-13: `CancelRender(v)` MUST set the cancel flag of render `v`. [just go-check]
- preview-scheduler-14: `Display(v)` MUST apply the result of revision `v` as the `Display` effect of `spec/viewer.md`, and it MUST be a command rather than a state change. [just go-check: TestViewScripts]
- preview-scheduler-15: The watcher's 50 ms coalescing MUST sit outside the model. [just go-check: TestViewPTY]

## TLA+ model

- preview-scheduler-16: The model MUST have the four variables and the three actions of the reducer, one to one, and `models/PreviewScheduler.tla` MUST hold exactly this text: [just model]

  ```tla
  ---- MODULE PreviewScheduler ----
  EXTENDS Naturals

  CONSTANT MaxRev

  VARIABLES latest, inflight, cancelled, displayed

  vars == <<latest, inflight, cancelled, displayed>>

  TypeOK ==
    /\ latest \in 0..MaxRev
    /\ inflight \in 0..MaxRev
    /\ cancelled \in BOOLEAN
    /\ displayed \in 0..MaxRev

  Init ==
    /\ latest = 0
    /\ inflight = 0
    /\ cancelled = FALSE
    /\ displayed = 0

  Edited ==
    /\ latest < MaxRev
    /\ latest' = latest + 1
    /\ IF inflight = 0
         THEN /\ inflight' = latest + 1
              /\ cancelled' = FALSE
         ELSE /\ inflight' = inflight
              /\ cancelled' = TRUE
    /\ UNCHANGED displayed

  RenderDone ==
    /\ inflight # 0
    /\ IF cancelled
         THEN /\ inflight' = latest
              /\ cancelled' = FALSE
              /\ UNCHANGED displayed
         ELSE /\ inflight' = 0
              /\ cancelled' = FALSE
              /\ displayed' = inflight
    /\ UNCHANGED latest

  RenderAborted ==
    /\ inflight # 0
    /\ cancelled
    /\ inflight' = latest
    /\ cancelled' = FALSE
    /\ UNCHANGED <<latest, displayed>>

  Next == Edited \/ RenderDone \/ RenderAborted

  Spec == Init /\ [][Next]_vars /\ WF_vars(RenderDone)

  DisplayedNotAhead == displayed <= latest
  IdleMeansCurrent == (inflight = 0) => (displayed = latest)
  InflightIsNewer == (inflight # 0) => (inflight > displayed)
  CancelledMeansStale == cancelled <=> (inflight # 0 /\ inflight < latest)

  DisplayMonotonic == [][displayed' >= displayed]_vars
  EventuallyCurrent == <>[](displayed = latest)
  ====
  ```

- preview-scheduler-17: `models/PreviewScheduler.cfg` MUST hold exactly this text: [just model]

  ```text
  SPECIFICATION Spec
  CONSTANT MaxRev = 4
  INVARIANT TypeOK
  INVARIANT DisplayedNotAhead
  INVARIANT IdleMeansCurrent
  INVARIANT InflightIsNewer
  INVARIANT CancelledMeansStale
  PROPERTY DisplayMonotonic
  PROPERTY EventuallyCurrent
  CHECK_DEADLOCK FALSE
  ```

- preview-scheduler-18: The configuration file MUST end with `CHECK_DEADLOCK FALSE`, because the state `latest = MaxRev, inflight = 0` is an intended terminal state and TLC MUST NOT report it as a deadlock. [just model]
- preview-scheduler-19: `MaxRev` MUST be the constant 4, set by the `.cfg` file. [just model]
- preview-scheduler-20: `just model` MUST run `java -cp .tools/tla2tools.jar tlc2.TLC -config models/PreviewScheduler.cfg -workers auto models/PreviewScheduler.tla`, and it MUST exit 0. [just model]

## Property arguments

- preview-scheduler-21: `DisplayMonotonic` MUST hold because `displayed` changes only in `RenderDone` when `cancelled` is FALSE, and then `displayed` becomes `inflight`, which is greater than `displayed` by `InflightIsNewer`. [just model]
- preview-scheduler-22: `EventuallyCurrent` MUST hold under `WF_vars(RenderDone)`: `RenderDone` stays enabled from the moment `inflight` becomes nonzero until it fires, `latest` stops changing at `MaxRev` or earlier, and after the last `Edited` at most two completion steps (`RenderAborted` clears `cancelled`, then `RenderDone` stores the result) make `displayed = latest` and `inflight = 0`. [just model]
- preview-scheduler-23: The terminal state MUST be `latest = MaxRev`, `inflight = 0`, `cancelled = FALSE`, and `displayed = MaxRev`; no action MUST change `displayed` or `latest` in it, because `Edited` is disabled at `latest = MaxRev` and `RenderDone` and `RenderAborted` are disabled at `inflight = 0`. [just model]

## Recorded model-check run

- preview-scheduler-24: A TLC 1.7.4 run of the model MUST show 45 states generated, 25 distinct states, and a search depth of 8. The run of 2026-11-12 recorded these values and a wall time of 3 s. [just model]
- preview-scheduler-25: The reachable-state count at `MaxRev = 4` MUST be 25 distinct states over `{latest, inflight, cancelled, displayed}`, and that count MUST be the hand-derived count of this file. [just model]
- preview-scheduler-26: The reducer unit test of each language MUST start at `Init`, explore all states reachable under the reducer with the three events, allow `Edited` only while `latest < 4`, assert the five invariants on every state, and assert that the reachable set has 25 states. [just go-check: TestSchedulerReachable]
- preview-scheduler-27: `RenderDone(result)` MUST be explored with an arbitrary `result`, which the reducer MUST NOT inspect. [just go-check: TestSchedulerReachable]
- preview-scheduler-28: The Rust test `scheduler_reachable` MUST enumerate the same states with the same variables and actions and MUST assert the same count of 25. [just rust-check: scheduler_reachable]
