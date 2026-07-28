# Theorem-to-Spec Cheat-Sheet

One page mapping every machine-checked artifact in this repository to the part of the live Gloas (ePBS) consensus spec it validates. This is the quickest way for a reviewer to check what is verified against the real spec.

Spec reference: `ethereum/consensus-specs`, the **Gloas** fork (`specs/gloas/`), commit `8a3df1d7` (retrieved 2026-07-28). Full mapping and abstraction notes: `FIDELITY.md`.

## TLA+ models (checked with TLC)

| Model | Gloas spec element it validates | What it establishes |
|---|---|---|
| `specs/EPBS.tla` | `process_execution_payload_bid`, `builder_pending_payments`; canonical-vs-reorged settlement | Proposer unconditional payment (G1), builder reveal safety (G2), builder withhold safety (G3), commitment binding, equivocation-not-canonical, conservation |
| `specs/EPBSForkChoice.tla` | `fork-choice.md`: `is_head_weak` (`REORG_HEAD_WEIGHT_THRESHOLD`), `is_parent_strong` (`REORG_PARENT_WEIGHT_THRESHOLD`) | The exact reorg threshold; payment guarantees hold on both sides of it |
| `specs/EPBSPTC.tla` | `process_payload_attestation`, `payload_timeliness`, `PAYLOAD_TIMELY_THRESHOLD = PTC_SIZE // 2` | The interleaved, timed PTC tally equals the truth (the atomic tally is a sound abstraction) |
| `specs/EPBSWeightPayment.tla` | `process_builder_pending_payments` weight-quorum settlement; attestation weight accumulation | A canonical block pays the proposer, a non-canonical block charges no one, a Byzantine minority cannot force payment, all emerging from the weight dynamics |
| `specs/EPBSChain.tla` | `builder_pending_withdrawals`, `process_builder_pending_payments` across slots | Cross-slot value conservation and withdrawal-draining liveness |
| `specs/EPBS_fault_*.cfg` | (non-vacuity self-tests) | Injected bugs are caught by the right invariant, so the checks have teeth |

## Coq proofs (axiom-free; generalise to all sizes)

| Proof | Gloas spec element it validates | What it establishes (for all sizes) |
|---|---|---|
| `coq/EPBSPayment.v` | `process_builder_pending_payments` outcome; `can_builder_cover_bid` | G1, G3, conservation, commitment binding, for all bid values and any number of builders |
| `coq/EPBSForkChoice.v` | `is_head_weak` / `is_parent_strong` weight inequality | The reorg threshold, exact and in both directions, for all non-negative weights |
| `coq/EPBSEquivocation.v` | Gloas defines no equivocation slashing (proposer slashing only clears a `BuilderPendingPayment`) | Equivocation is self-punishing (net loss to the builder), the rationale for omitting slashing |
| `coq/EPBSCommittee.v` | `payload_timeliness` tally against `PAYLOAD_TIMELY_THRESHOLD` | The PTC tally equals the truth for all committee sizes |
| `coq/EPBSChain.v` | `builder_pending_withdrawals` settlement | Conservation and withdrawal drainage for all chain lengths |

## How to read it

Each row names a live Gloas function or constant and the artifact that verifies a property of it. Run everything with one command:

```bash
./verify.sh
```

Constants confirmed against the Gloas spec: `PTC_SIZE = 512`, `PAYLOAD_TIMELY_THRESHOLD = PTC_SIZE // 2 = 256`, no equivocation slashing. The reorg weight thresholds (`REORG_HEAD_WEIGHT_THRESHOLD`, `REORG_PARENT_WEIGHT_THRESHOLD`) are committee fractions inherited from prior forks; the models treat them abstractly, which is faithful to the inequality structure. See `FIDELITY.md` for the deltas.
